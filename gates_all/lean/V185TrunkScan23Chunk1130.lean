import V185TrunkScan23Chunk1129

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6693238 : List Nat := [5, 1, 1, 4, 1, 2, 1, 8]
def baseStart_6693238 : Nat := 118140960795 + 6693238 * 2 ^ 59
def prefixEnd_6693238 : Nat := 4983230072969 + 3 ^ 40 * 6693238 * 2
def baseEnd_6693238 : Nat := 127290675145858848490495

theorem tailTrace_6693238 : CollatzResearch.WordTrace tailWord_6693238 prefixEnd_6693238 127290675145858848490495 := by
  unfold tailWord_6693238
  simp only [CollatzResearch.WordTrace]
  refine ⟨15257652832846832180472023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162748296883699543258368245 15257652832846832180472023)
  ·
    refine ⟨22886479249270248270708035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15257652832846832180472023 22886479249270248270708035)
    ·
      refine ⟨34329718873905372406062053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22886479249270248270708035 34329718873905372406062053)
      ·
        refine ⟨6436822288857257326136635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34329718873905372406062053 6436822288857257326136635)
        ·
          refine ⟨9655233433285885989204953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6436822288857257326136635 9655233433285885989204953)
          ·
            refine ⟨7241425074964414491903715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9655233433285885989204953 7241425074964414491903715)
            ·
              refine ⟨10862137612446621737855573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7241425074964414491903715 10862137612446621737855573)
              ·
                refine ⟨127290675145858848490495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10862137612446621737855573 127290675145858848490495)
                ·
                  rfl

theorem cell23_6693238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_6693238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693238 prefixEnd_6693238 := by exact prefixLift 6693238
  have htrace : WordTrace (prefixWord ++ tailWord_6693238) baseStart_6693238 baseEnd_6693238 := by
    simpa [prefixWord, tailWord_6693238, baseEnd_6693238] using wordTrace_append hprefix tailTrace_6693238
  have hstable : (prefixWord ++ tailWord_6693238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693238).length < 2 ^ (prefixWord ++ tailWord_6693238).sum := by decide
  have hdescent : baseEnd_6693238 < baseStart_6693238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693247 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 2, 6]
def baseStart_6693247 : Nat := 118140960795 + 6693247 * 2 ^ 59
def prefixEnd_6693247 : Nat := 4983230072969 + 3 ^ 40 * 6693247 * 2
def baseEnd_6693247 : Nat := 1145617616754693124676941

theorem tailTrace_6693247 : CollatzResearch.WordTrace tailWord_6693247 prefixEnd_6693247 1145617616754693124676941 := by
  unfold tailWord_6693247
  simp only [CollatzResearch.WordTrace]
  refine ⟨244122773582516709424629995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162748515721677806283086663 244122773582516709424629995)
  ·
    refine ⟨366184160373775064136944993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244122773582516709424629995 366184160373775064136944993)
    ·
      refine ⟨274638120280331298102708745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366184160373775064136944993 274638120280331298102708745)
      ·
        refine ⟨205978590210248473577031559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274638120280331298102708745 205978590210248473577031559)
        ·
          refine ⟨308967885315372710365547339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205978590210248473577031559 308967885315372710365547339)
          ·
            refine ⟨463451827973059065548321009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308967885315372710365547339 463451827973059065548321009)
            ·
              refine ⟨347588870979794299161240757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463451827973059065548321009 347588870979794299161240757)
              ·
                refine ⟨32586456654355715546366321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 347588870979794299161240757 32586456654355715546366321)
                ·
                  refine ⟨24439842490766786659774741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32586456654355715546366321 24439842490766786659774741)
                  ·
                    refine ⟨1145617616754693124676941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24439842490766786659774741 1145617616754693124676941)
                    ·
                      rfl

theorem cell23_6693247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 6].length) (baseStart_6693247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693247 prefixEnd_6693247 := by exact prefixLift 6693247
  have htrace : WordTrace (prefixWord ++ tailWord_6693247) baseStart_6693247 baseEnd_6693247 := by
    simpa [prefixWord, tailWord_6693247, baseEnd_6693247] using wordTrace_append hprefix tailTrace_6693247
  have hstable : (prefixWord ++ tailWord_6693247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693247).length < 2 ^ (prefixWord ++ tailWord_6693247).sum := by decide
  have hdescent : baseEnd_6693247 < baseStart_6693247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693271 : List Nat := [1, 1, 3, 3, 1, 1, 4, 2, 1, 4, 2]
def baseStart_6693271 : Nat := 118140960795 + 6693271 * 2 ^ 59
def prefixEnd_6693271 : Nat := 4983230072969 + 3 ^ 40 * 6693271 * 2
def baseEnd_6693271 : Nat := 3436865173799787280130713

theorem tailTrace_6693271 : CollatzResearch.WordTrace tailWord_6693271 prefixEnd_6693271 3436865173799787280130713 := by
  unfold tailWord_6693271
  simp only [CollatzResearch.WordTrace]
  refine ⟨244123648934429761523503667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162749099289619841015669111 244123648934429761523503667)
  ·
    refine ⟨366185473401644642285255501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244123648934429761523503667 366185473401644642285255501)
    ·
      refine ⟨137319552525616740856970813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366185473401644642285255501 137319552525616740856970813)
      ·
        refine ⟨51494832197106277821364055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137319552525616740856970813 51494832197106277821364055)
        ·
          refine ⟨77242248295659416732046083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51494832197106277821364055 77242248295659416732046083)
          ·
            refine ⟨115863372443489125098069125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77242248295659416732046083 115863372443489125098069125)
            ·
              refine ⟨21724382333154210955887961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115863372443489125098069125 21724382333154210955887961)
              ·
                refine ⟨16293286749865658216915971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21724382333154210955887961 16293286749865658216915971)
                ·
                  refine ⟨24439930124798487325373957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16293286749865658216915971 24439930124798487325373957)
                  ·
                    refine ⟨4582486898399716373507617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24439930124798487325373957 4582486898399716373507617)
                    ·
                      refine ⟨3436865173799787280130713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4582486898399716373507617 3436865173799787280130713)
                      ·
                        rfl

theorem cell23_6693271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_6693271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693271 prefixEnd_6693271 := by exact prefixLift 6693271
  have htrace : WordTrace (prefixWord ++ tailWord_6693271) baseStart_6693271 baseEnd_6693271 := by
    simpa [prefixWord, tailWord_6693271, baseEnd_6693271] using wordTrace_append hprefix tailTrace_6693271
  have hstable : (prefixWord ++ tailWord_6693271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693271).length < 2 ^ (prefixWord ++ tailWord_6693271).sum := by decide
  have hdescent : baseEnd_6693271 < baseStart_6693271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693284 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_6693284 : Nat := 118140960795 + 6693284 * 2 ^ 59
def prefixEnd_6693284 : Nat := 4983230072969 + 3 ^ 40 * 6693284 * 2
def baseEnd_6693284 : Nat := 3436871849048295729268153

theorem tailTrace_6693284 : CollatzResearch.WordTrace tailWord_6693284 prefixEnd_6693284 3436871849048295729268153 := by
  unfold tailWord_6693284
  simp only [CollatzResearch.WordTrace]
  refine ⟨122062061541691332371863453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162749415388921776495817937 122062061541691332371863453)
  ·
    refine ⟨45773273078134249639448795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122062061541691332371863453 45773273078134249639448795)
    ·
      refine ⟨68659909617201374459173193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45773273078134249639448795 68659909617201374459173193)
      ·
        refine ⟨51494932212901030844379895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68659909617201374459173193 51494932212901030844379895)
        ·
          refine ⟨77242398319351546266569843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51494932212901030844379895 77242398319351546266569843)
          ·
            refine ⟨115863597479027319399854765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77242398319351546266569843 115863597479027319399854765)
            ·
              refine ⟨43448849054635244774945537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115863597479027319399854765 43448849054635244774945537)
              ·
                refine ⟨32586636790976433581209153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43448849054635244774945537 32586636790976433581209153)
                ·
                  refine ⟨24439977593232325185906865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32586636790976433581209153 24439977593232325185906865)
                  ·
                    refine ⟨18329983194924243889430149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24439977593232325185906865 18329983194924243889430149)
                    ·
                      refine ⟨3436871849048295729268153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18329983194924243889430149 3436871849048295729268153)
                      ·
                        rfl

theorem cell23_6693284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_6693284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693284 prefixEnd_6693284 := by exact prefixLift 6693284
  have htrace : WordTrace (prefixWord ++ tailWord_6693284) baseStart_6693284 baseEnd_6693284 := by
    simpa [prefixWord, tailWord_6693284, baseEnd_6693284] using wordTrace_append hprefix tailTrace_6693284
  have hstable : (prefixWord ++ tailWord_6693284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693284).length < 2 ^ (prefixWord ++ tailWord_6693284).sum := by decide
  have hdescent : baseEnd_6693284 < baseStart_6693284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693341 : List Nat := [1, 4, 3, 1, 1, 1, 3, 2, 2, 5]
def baseStart_6693341 : Nat := 118140960795 + 6693341 * 2 ^ 59
def prefixEnd_6693341 : Nat := 4983230072969 + 3 ^ 40 * 6693341 * 2
def baseEnd_6693341 : Nat := 1145633705815200668751797

theorem tailTrace_6693341 : CollatzResearch.WordTrace tailWord_6693341 prefixEnd_6693341 1145633705815200668751797 := by
  unfold tailWord_6693341
  simp only [CollatzResearch.WordTrace]
  refine ⟨244126202044176163478551877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162750801362784108985701251 244126202044176163478551877)
  ·
    refine ⟨45773662883283030652228477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244126202044176163478551877 45773662883283030652228477)
    ·
      refine ⟨17165123581231136494585679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45773662883283030652228477 17165123581231136494585679)
      ·
        refine ⟨25747685371846704741878519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17165123581231136494585679 25747685371846704741878519)
        ·
          refine ⟨38621528057770057112817779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25747685371846704741878519 38621528057770057112817779)
          ·
            refine ⟨57932292086655085669226669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38621528057770057112817779 57932292086655085669226669)
            ·
              refine ⟨21724609532495657125960001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57932292086655085669226669 21724609532495657125960001)
              ·
                refine ⟨16293457149371742844470001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21724609532495657125960001 16293457149371742844470001)
                ·
                  refine ⟨12220092862028807133352501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16293457149371742844470001 12220092862028807133352501)
                  ·
                    refine ⟨1145633705815200668751797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12220092862028807133352501 1145633705815200668751797)
                    ·
                      rfl

theorem cell23_6693341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_6693341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693341 prefixEnd_6693341 := by exact prefixLift 6693341
  have htrace : WordTrace (prefixWord ++ tailWord_6693341) baseStart_6693341 baseEnd_6693341 := by
    simpa [prefixWord, tailWord_6693341, baseEnd_6693341] using wordTrace_append hprefix tailTrace_6693341
  have hstable : (prefixWord ++ tailWord_6693341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693341).length < 2 ^ (prefixWord ++ tailWord_6693341).sum := by decide
  have hdescent : baseEnd_6693341 < baseStart_6693341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693361 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 1, 6, 2]
def baseStart_6693361 : Nat := 118140960795 + 6693361 * 2 ^ 59
def prefixEnd_6693361 : Nat := 4983230072969 + 3 ^ 40 * 6693361 * 2
def baseEnd_6693361 : Nat := 3436911387058691928005299

theorem tailTrace_6693361 : CollatzResearch.WordTrace tailWord_6693361 prefixEnd_6693361 3436911387058691928005299 := by
  unfold tailWord_6693361
  simp only [CollatzResearch.WordTrace]
  refine ⟨244126931504103706894279937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162751287669402471262853291 244126931504103706894279937)
  ·
    refine ⟨183095198628077780170709953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244126931504103706894279937 183095198628077780170709953)
    ·
      refine ⟨137321398971058335128032465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183095198628077780170709953 137321398971058335128032465)
      ·
        refine ⟨102991049228293751346024349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137321398971058335128032465 102991049228293751346024349)
        ·
          refine ⟨38621643460610156754759131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102991049228293751346024349 38621643460610156754759131)
          ·
            refine ⟨57932465190915235132138697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38621643460610156754759131 57932465190915235132138697)
            ·
              refine ⟨43449348893186426349104023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57932465190915235132138697 43449348893186426349104023)
              ·
                refine ⟨65174023339779639523656035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43449348893186426349104023 65174023339779639523656035)
                ·
                  refine ⟨97761035009669459285484053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65174023339779639523656035 97761035009669459285484053)
                  ·
                    refine ⟨4582548516078255904007065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97761035009669459285484053 4582548516078255904007065)
                    ·
                      refine ⟨3436911387058691928005299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4582548516078255904007065 3436911387058691928005299)
                      ·
                        rfl

theorem cell23_6693361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_6693361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693361 prefixEnd_6693361 := by exact prefixLift 6693361
  have htrace : WordTrace (prefixWord ++ tailWord_6693361) baseStart_6693361 baseEnd_6693361 := by
    simpa [prefixWord, tailWord_6693361, baseEnd_6693361] using wordTrace_append hprefix tailTrace_6693361
  have hstable : (prefixWord ++ tailWord_6693361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693361).length < 2 ^ (prefixWord ++ tailWord_6693361).sum := by decide
  have hdescent : baseEnd_6693361 < baseStart_6693361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693381 : List Nat := [1, 3, 1, 1, 2, 2, 3, 3, 2, 2, 3]
def baseStart_6693381 : Nat := 118140960795 + 6693381 * 2 ^ 59
def prefixEnd_6693381 : Nat := 4983230072969 + 3 ^ 40 * 6693381 * 2
def baseEnd_6693381 : Nat := 3436921656671781849755207

theorem tailTrace_6693381 : CollatzResearch.WordTrace tailWord_6693381 prefixEnd_6693381 3436921656671781849755207 := by
  unfold tailWord_6693381
  simp only [CollatzResearch.WordTrace]
  refine ⟨244127660964031250310007997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162751773976020833540005331 244127660964031250310007997)
  ·
    refine ⟨91547872861511718866252999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244127660964031250310007997 91547872861511718866252999)
    ·
      refine ⟨137321809292267578299379499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91547872861511718866252999 137321809292267578299379499)
      ·
        refine ⟨205982713938401367449069249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137321809292267578299379499 205982713938401367449069249)
        ·
          refine ⟨154487035453801025586801937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205982713938401367449069249 154487035453801025586801937)
          ·
            refine ⟨115865276590350769190101453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154487035453801025586801937 115865276590350769190101453)
            ·
              refine ⟨43449478721381538446288045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115865276590350769190101453 43449478721381538446288045)
              ·
                refine ⟨16293554520518076917358017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43449478721381538446288045 16293554520518076917358017)
                ·
                  refine ⟨12220165890388557688018513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16293554520518076917358017 12220165890388557688018513)
                  ·
                    refine ⟨9165124417791418266013885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12220165890388557688018513 9165124417791418266013885)
                    ·
                      refine ⟨3436921656671781849755207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9165124417791418266013885 3436921656671781849755207)
                      ·
                        rfl

theorem cell23_6693381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_6693381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693381 prefixEnd_6693381 := by exact prefixLift 6693381
  have htrace : WordTrace (prefixWord ++ tailWord_6693381) baseStart_6693381 baseEnd_6693381 := by
    simpa [prefixWord, tailWord_6693381, baseEnd_6693381] using wordTrace_append hprefix tailTrace_6693381
  have hstable : (prefixWord ++ tailWord_6693381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693381).length < 2 ^ (prefixWord ++ tailWord_6693381).sum := by decide
  have hdescent : baseEnd_6693381 < baseStart_6693381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693405 : List Nat := [1, 4, 2, 2, 1, 3, 1, 4, 1, 4]
def baseStart_6693405 : Nat := 118140960795 + 6693405 * 2 ^ 59
def prefixEnd_6693405 : Nat := 4983230072969 + 3 ^ 40 * 6693405 * 2
def baseEnd_6693405 : Nat := 1145644660069163251951699

theorem tailTrace_6693405 : CollatzResearch.WordTrace tailWord_6693405 prefixEnd_6693405 1145644660069163251951699 := by
  unfold tailWord_6693405
  simp only [CollatzResearch.WordTrace]
  refine ⟨244128536315944302408881669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162752357543962868272587779 244128536315944302408881669)
  ·
    refine ⟨45774100559239556701665313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244128536315944302408881669 45774100559239556701665313)
    ·
      refine ⟨34330575419429667526248985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45774100559239556701665313 34330575419429667526248985)
      ·
        refine ⟨25747931564572250644686739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34330575419429667526248985 25747931564572250644686739)
        ·
          refine ⟨38621897346858375967030109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25747931564572250644686739 38621897346858375967030109)
          ·
            refine ⟨14483211505071890987636291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38621897346858375967030109 14483211505071890987636291)
            ·
              refine ⟨21724817257607836481454437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14483211505071890987636291 21724817257607836481454437)
              ·
                refine ⟨4073403235801469340272707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21724817257607836481454437 4073403235801469340272707)
                ·
                  refine ⟨6110104853702204010409061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4073403235801469340272707 6110104853702204010409061)
                  ·
                    refine ⟨1145644660069163251951699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6110104853702204010409061 1145644660069163251951699)
                    ·
                      rfl

theorem cell23_6693405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_6693405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693405 prefixEnd_6693405 := by exact prefixLift 6693405
  have htrace : WordTrace (prefixWord ++ tailWord_6693405) baseStart_6693405 baseEnd_6693405 := by
    simpa [prefixWord, tailWord_6693405, baseEnd_6693405] using wordTrace_append hprefix tailTrace_6693405
  have hstable : (prefixWord ++ tailWord_6693405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693405).length < 2 ^ (prefixWord ++ tailWord_6693405).sum := by decide
  have hdescent : baseEnd_6693405 < baseStart_6693405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693431 : List Nat := [1, 1, 3, 1, 2, 3, 2, 4, 1, 5]
def baseStart_6693431 : Nat := 118140960795 + 6693431 * 2 ^ 59
def prefixEnd_6693431 : Nat := 4983230072969 + 3 ^ 40 * 6693431 * 2
def baseEnd_6693431 : Nat := 1145649110234835551376659

theorem tailTrace_6693431 : CollatzResearch.WordTrace tailWord_6693431 prefixEnd_6693431 1145649110234835551376659 := by
  unfold tailWord_6693431
  simp only [CollatzResearch.WordTrace]
  refine ⟨244129484613850108849328147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162752989742566739232885431 244129484613850108849328147)
  ·
    refine ⟨366194226920775163273992221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244129484613850108849328147 366194226920775163273992221)
    ·
      refine ⟨137322835095290686227747083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366194226920775163273992221 137322835095290686227747083)
      ·
        refine ⟨205984252642936029341620625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137322835095290686227747083 205984252642936029341620625)
        ·
          refine ⟨154488189482202022006215469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205984252642936029341620625 154488189482202022006215469)
          ·
            refine ⟨57933071055825758252330801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154488189482202022006215469 57933071055825758252330801)
            ·
              refine ⟨43449803291869318689248101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57933071055825758252330801 43449803291869318689248101)
              ·
                refine ⟨8146838117225497254234019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43449803291869318689248101 8146838117225497254234019)
                ·
                  refine ⟨12220257175838245881351029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8146838117225497254234019 12220257175838245881351029)
                  ·
                    refine ⟨1145649110234835551376659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12220257175838245881351029 1145649110234835551376659)
                    ·
                      rfl

theorem cell23_6693431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_6693431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693431 prefixEnd_6693431 := by exact prefixLift 6693431
  have htrace : WordTrace (prefixWord ++ tailWord_6693431) baseStart_6693431 baseEnd_6693431 := by
    simpa [prefixWord, tailWord_6693431, baseEnd_6693431] using wordTrace_append hprefix tailTrace_6693431
  have hstable : (prefixWord ++ tailWord_6693431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693431).length < 2 ^ (prefixWord ++ tailWord_6693431).sum := by decide
  have hdescent : baseEnd_6693431 < baseStart_6693431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693445 : List Nat := [1, 3, 1, 1, 1, 5, 1, 5, 1, 1, 3]
def baseStart_6693445 : Nat := 118140960795 + 6693445 * 2 ^ 59
def prefixEnd_6693445 : Nat := 4983230072969 + 3 ^ 40 * 6693445 * 2
def baseEnd_6693445 : Nat := 3436954519433669599354913

theorem tailTrace_6693445 : CollatzResearch.WordTrace tailWord_6693445 prefixEnd_6693445 3436954519433669599354913 := by
  unfold tailWord_6693445
  simp only [CollatzResearch.WordTrace]
  refine ⟨244129995235799389240337789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162753330157199592826891859 244129995235799389240337789)
  ·
    refine ⟨91548748213424770965126671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244129995235799389240337789 91548748213424770965126671)
    ·
      refine ⟨137323122320137156447690007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91548748213424770965126671 137323122320137156447690007)
      ·
        refine ⟨205984683480205734671535011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137323122320137156447690007 205984683480205734671535011)
        ·
          refine ⟨308977025220308602007302517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205984683480205734671535011 308977025220308602007302517)
          ·
            refine ⟨28966596114403931438184611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 308977025220308602007302517 28966596114403931438184611)
            ·
              refine ⟨43449894171605897157276917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28966596114403931438184611 43449894171605897157276917)
              ·
                refine ⟨4073427578588052858494711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43449894171605897157276917 4073427578588052858494711)
                ·
                  refine ⟨6110141367882079287742067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4073427578588052858494711 6110141367882079287742067)
                  ·
                    refine ⟨9165212051823118931613101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6110141367882079287742067 9165212051823118931613101)
                    ·
                      refine ⟨3436954519433669599354913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9165212051823118931613101 3436954519433669599354913)
                      ·
                        rfl

theorem cell23_6693445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 1, 1, 3].length) (baseStart_6693445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693445 prefixEnd_6693445 := by exact prefixLift 6693445
  have htrace : WordTrace (prefixWord ++ tailWord_6693445) baseStart_6693445 baseEnd_6693445 := by
    simpa [prefixWord, tailWord_6693445, baseEnd_6693445] using wordTrace_append hprefix tailTrace_6693445
  have hstable : (prefixWord ++ tailWord_6693445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693445).length < 2 ^ (prefixWord ++ tailWord_6693445).sum := by decide
  have hdescent : baseEnd_6693445 < baseStart_6693445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693471 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 3]
def baseStart_6693471 : Nat := 118140960795 + 6693471 * 2 ^ 59
def prefixEnd_6693471 : Nat := 4983230072969 + 3 ^ 40 * 6693471 * 2
def baseEnd_6693471 : Nat := 3436967869930686497629793

theorem tailTrace_6693471 : CollatzResearch.WordTrace tailWord_6693471 prefixEnd_6693471 3436967869930686497629793 := by
  unfold tailWord_6693471
  simp only [CollatzResearch.WordTrace]
  refine ⟨244130943533705195680784267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162753962355803463787189511 244130943533705195680784267)
  ·
    refine ⟨366196415300557793521176401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244130943533705195680784267 366196415300557793521176401)
    ·
      refine ⟨274647311475418345140882301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366196415300557793521176401 274647311475418345140882301)
      ·
        refine ⟨102992741803281879427830863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274647311475418345140882301 102992741803281879427830863)
        ·
          refine ⟨154489112704922819141746295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102992741803281879427830863 154489112704922819141746295)
          ·
            refine ⟨231733669057384228712619443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154489112704922819141746295 231733669057384228712619443)
            ·
              refine ⟨347600503586076343068929165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231733669057384228712619443 347600503586076343068929165)
              ·
                refine ⟨130350188844778628650848437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347600503586076343068929165 130350188844778628650848437)
                ·
                  refine ⟨12220330204197996436017041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130350188844778628650848437 12220330204197996436017041)
                  ·
                    refine ⟨9165247653148497327012781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12220330204197996436017041 9165247653148497327012781)
                    ·
                      refine ⟨3436967869930686497629793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9165247653148497327012781 3436967869930686497629793)
                      ·
                        rfl

theorem cell23_6693471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_6693471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693471 prefixEnd_6693471 := by exact prefixLift 6693471
  have htrace : WordTrace (prefixWord ++ tailWord_6693471) baseStart_6693471 baseEnd_6693471 := by
    simpa [prefixWord, tailWord_6693471, baseEnd_6693471] using wordTrace_append hprefix tailTrace_6693471
  have hstable : (prefixWord ++ tailWord_6693471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693471).length < 2 ^ (prefixWord ++ tailWord_6693471).sum := by decide
  have hdescent : baseEnd_6693471 < baseStart_6693471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693485 : List Nat := [1, 5, 1, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_6693485 : Nat := 118140960795 + 6693485 * 2 ^ 59
def prefixEnd_6693485 : Nat := 4983230072969 + 3 ^ 40 * 6693485 * 2
def baseEnd_6693485 : Nat := 3436975058659849442854729

theorem tailTrace_6693485 : CollatzResearch.WordTrace tailWord_6693485 prefixEnd_6693485 3436975058659849442854729 := by
  unfold tailWord_6693485
  simp only [CollatzResearch.WordTrace]
  refine ⟨244131454155654476071793909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162754302770436317381195939 244131454155654476071793909)
  ·
    refine ⟨22887323827092607131730679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244131454155654476071793909 22887323827092607131730679)
    ·
      refine ⟨34330985740638910697596019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22887323827092607131730679 34330985740638910697596019)
      ·
        refine ⟨51496478610958366046394029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34330985740638910697596019 51496478610958366046394029)
        ·
          refine ⟨19311179479109387267397761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51496478610958366046394029 19311179479109387267397761)
          ·
            refine ⟨14483384609332040450548321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19311179479109387267397761 14483384609332040450548321)
            ·
              refine ⟨10862538456999030337911241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14483384609332040450548321 10862538456999030337911241)
              ·
                refine ⟨8146903842749272753433431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10862538456999030337911241 8146903842749272753433431)
                ·
                  refine ⟨12220355764123909130150147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8146903842749272753433431 12220355764123909130150147)
                  ·
                    refine ⟨18330533646185863695225221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12220355764123909130150147 18330533646185863695225221)
                    ·
                      refine ⟨3436975058659849442854729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18330533646185863695225221 3436975058659849442854729)
                      ·
                        rfl

theorem cell23_6693485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_6693485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693485 prefixEnd_6693485 := by exact prefixLift 6693485
  have htrace : WordTrace (prefixWord ++ tailWord_6693485) baseStart_6693485 baseEnd_6693485 := by
    simpa [prefixWord, tailWord_6693485, baseEnd_6693485] using wordTrace_append hprefix tailTrace_6693485
  have hstable : (prefixWord ++ tailWord_6693485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693485).length < 2 ^ (prefixWord ++ tailWord_6693485).sum := by decide
  have hdescent : baseEnd_6693485 < baseStart_6693485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693506 : List Nat := [3, 4, 3, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_6693506 : Nat := 118140960795 + 6693506 * 2 ^ 59
def prefixEnd_6693506 : Nat := 4983230072969 + 3 ^ 40 * 6693506 * 2
def baseEnd_6693506 : Nat := 3436985841753593860692133

theorem tailTrace_6693506 : CollatzResearch.WordTrace tailWord_6693506 prefixEnd_6693506 3436985841753593860692133 := by
  unfold tailWord_6693506
  simp only [CollatzResearch.WordTrace]
  refine ⟨61033055022144599164577093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162754813392385597772205581 61033055022144599164577093)
  ·
    refine ⟨11443697816652112343358205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61033055022144599164577093 11443697816652112343358205)
    ·
      refine ⟨4291386681244542128759327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11443697816652112343358205 4291386681244542128759327)
      ·
        refine ⟨6437080021866813193138991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4291386681244542128759327 6437080021866813193138991)
        ·
          refine ⟨9655620032800219789708487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6437080021866813193138991 9655620032800219789708487)
          ·
            refine ⟨14483430049200329684562731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9655620032800219789708487 14483430049200329684562731)
            ·
              refine ⟨21725145073800494526844097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14483430049200329684562731 21725145073800494526844097)
              ·
                refine ⟨16293858805350370895133073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21725145073800494526844097 16293858805350370895133073)
                ·
                  refine ⟨12220394104012778171349805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16293858805350370895133073 12220394104012778171349805)
                  ·
                    refine ⟨4582647789004791814256177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12220394104012778171349805 4582647789004791814256177)
                    ·
                      refine ⟨3436985841753593860692133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4582647789004791814256177 3436985841753593860692133)
                      ·
                        rfl

theorem cell23_6693506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_6693506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693506 prefixEnd_6693506 := by exact prefixLift 6693506
  have htrace : WordTrace (prefixWord ++ tailWord_6693506) baseStart_6693506 baseEnd_6693506 := by
    simpa [prefixWord, tailWord_6693506, baseEnd_6693506] using wordTrace_append hprefix tailTrace_6693506
  have hstable : (prefixWord ++ tailWord_6693506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693506).length < 2 ^ (prefixWord ++ tailWord_6693506).sum := by decide
  have hdescent : baseEnd_6693506 < baseStart_6693506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693562 : List Nat := [3, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2]
def baseStart_6693562 : Nat := 118140960795 + 6693562 * 2 ^ 59
def prefixEnd_6693562 : Nat := 4983230072969 + 3 ^ 40 * 6693562 * 2
def baseEnd_6693562 : Nat := 3437014596670245641591875

theorem tailTrace_6693562 : CollatzResearch.WordTrace tailWord_6693562 prefixEnd_6693562 3437014596670245641591875 := by
  unfold tailWord_6693562
  simp only [CollatzResearch.WordTrace]
  refine ⟨61033565644093879555586735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162756175050917012148231293 61033565644093879555586735)
  ·
    refine ⟨91550348466140819333380103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61033565644093879555586735 91550348466140819333380103)
    ·
      refine ⟨137325522699211229000070155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91550348466140819333380103 137325522699211229000070155)
      ·
        refine ⟨205988284048816843500105233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137325522699211229000070155 205988284048816843500105233)
        ·
          refine ⟨154491213036612632625078925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205988284048816843500105233 154491213036612632625078925)
          ·
            refine ⟨57934204888729737234404597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154491213036612632625078925 57934204888729737234404597)
            ·
              refine ⟨5431331708318412865725431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57934204888729737234404597 5431331708318412865725431)
              ·
                refine ⟨8146997562477619298588147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5431331708318412865725431 8146997562477619298588147)
                ·
                  refine ⟨12220496343716428947882221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8146997562477619298588147 12220496343716428947882221)
                  ·
                    refine ⟨4582686128893660855455833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12220496343716428947882221 4582686128893660855455833)
                    ·
                      refine ⟨3437014596670245641591875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4582686128893660855455833 3437014596670245641591875)
                      ·
                        rfl

theorem cell23_6693562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2].length) (baseStart_6693562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693562 prefixEnd_6693562 := by exact prefixLift 6693562
  have htrace : WordTrace (prefixWord ++ tailWord_6693562) baseStart_6693562 baseEnd_6693562 := by
    simpa [prefixWord, tailWord_6693562, baseEnd_6693562] using wordTrace_append hprefix tailTrace_6693562
  have hstable : (prefixWord ++ tailWord_6693562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693562).length < 2 ^ (prefixWord ++ tailWord_6693562).sum := by decide
  have hdescent : baseEnd_6693562 < baseStart_6693562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693578 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 2, 4, 3]
def baseStart_6693578 : Nat := 118140960795 + 6693578 * 2 ^ 59
def prefixEnd_6693578 : Nat := 4983230072969 + 3 ^ 40 * 6693578 * 2
def baseEnd_6693578 : Nat := 3437022812360717578991801

theorem tailTrace_6693578 : CollatzResearch.WordTrace tailWord_6693578 prefixEnd_6693578 3437022812360717578991801 := by
  unfold tailWord_6693578
  simp only [CollatzResearch.WordTrace]
  refine ⟨61033711536079388238732347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162756564096211701969952925 61033711536079388238732347)
  ·
    refine ⟨91550567304119082358098521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61033711536079388238732347 91550567304119082358098521)
    ·
      refine ⟨68662925478089311768573891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91550567304119082358098521 68662925478089311768573891)
      ·
        refine ⟨102994388217133967652860837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68662925478089311768573891 102994388217133967652860837)
        ·
          refine ⟨19311447790712618934911407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102994388217133967652860837 19311447790712618934911407)
          ·
            refine ⟨28967171686068928402367111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19311447790712618934911407 28967171686068928402367111)
            ·
              refine ⟨43450757529103392603550667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28967171686068928402367111 43450757529103392603550667)
              ·
                refine ⟨65176136293655088905326001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43450757529103392603550667 65176136293655088905326001)
                ·
                  refine ⟨48882102220241316678994501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65176136293655088905326001 48882102220241316678994501)
                  ·
                    refine ⟨9165394166295246877311469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48882102220241316678994501 9165394166295246877311469)
                    ·
                      refine ⟨3437022812360717578991801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9165394166295246877311469 3437022812360717578991801)
                      ·
                        rfl

theorem cell23_6693578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_6693578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693578 prefixEnd_6693578 := by exact prefixLift 6693578
  have htrace : WordTrace (prefixWord ++ tailWord_6693578) baseStart_6693578 baseEnd_6693578 := by
    simpa [prefixWord, tailWord_6693578, baseEnd_6693578] using wordTrace_append hprefix tailTrace_6693578
  have hstable : (prefixWord ++ tailWord_6693578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693578).length < 2 ^ (prefixWord ++ tailWord_6693578).sum := by decide
  have hdescent : baseEnd_6693578 < baseStart_6693578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693592 : List Nat := [2, 1, 2, 2, 3, 2, 2, 3, 2, 2, 2]
def baseStart_6693592 : Nat := 118140960795 + 6693592 * 2 ^ 59
def prefixEnd_6693592 : Nat := 4983230072969 + 3 ^ 40 * 6693592 * 2
def baseEnd_6693592 : Nat := 3437030001089880524216737

theorem tailTrace_6693592 : CollatzResearch.WordTrace tailWord_6693592 prefixEnd_6693592 3437030001089880524216737 := by
  unfold tailWord_6693592
  simp only [CollatzResearch.WordTrace]
  refine ⟨122067678383133416672969515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162756904510844555563959353 122067678383133416672969515)
  ·
    refine ⟨183101517574700125009454273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122067678383133416672969515 183101517574700125009454273)
    ·
      refine ⟨137326138181025093757090705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183101517574700125009454273 137326138181025093757090705)
      ·
        refine ⟨102994603635768820317818029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137326138181025093757090705 102994603635768820317818029)
        ·
          refine ⟨38622976363413307619181761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102994603635768820317818029 38622976363413307619181761)
          ·
            refine ⟨28967232272559980714386321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38622976363413307619181761 28967232272559980714386321)
            ·
              refine ⟨21725424204419985535789741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28967232272559980714386321 21725424204419985535789741)
              ·
                refine ⟨8147034076657494575921153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21725424204419985535789741 8147034076657494575921153)
                ·
                  refine ⟨6110275557493120931940865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8147034076657494575921153 6110275557493120931940865)
                  ·
                    refine ⟨4582706668119840698955649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6110275557493120931940865 4582706668119840698955649)
                    ·
                      refine ⟨3437030001089880524216737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4582706668119840698955649 3437030001089880524216737)
                      ·
                        rfl

theorem cell23_6693592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_6693592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693592 prefixEnd_6693592 := by exact prefixLift 6693592
  have htrace : WordTrace (prefixWord ++ tailWord_6693592) baseStart_6693592 baseEnd_6693592 := by
    simpa [prefixWord, tailWord_6693592, baseEnd_6693592] using wordTrace_append hprefix tailTrace_6693592
  have hstable : (prefixWord ++ tailWord_6693592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693592).length < 2 ^ (prefixWord ++ tailWord_6693592).sum := by decide
  have hdescent : baseEnd_6693592 < baseStart_6693592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693615 : List Nat := [1, 1, 2, 1, 5, 3, 2, 3, 5]
def baseStart_6693615 : Nat := 118140960795 + 6693615 * 2 ^ 59
def prefixEnd_6693615 : Nat := 4983230072969 + 3 ^ 40 * 6693615 * 2
def baseEnd_6693615 : Nat := 381893534571659326025459

theorem tailTrace_6693615 : CollatzResearch.WordTrace tailWord_6693615 prefixEnd_6693615 381893534571659326025459 := by
  unfold tailWord_6693615
  simp only [CollatzResearch.WordTrace]
  refine ⟨244136195645183508274026299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162757463763455672182684199 244136195645183508274026299)
  ·
    refine ⟨366204293467775262411039449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244136195645183508274026299 366204293467775262411039449)
    ·
      refine ⟨274653220100831446808279587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366204293467775262411039449 274653220100831446808279587)
      ·
        refine ⟨411979830151247170212419381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274653220100831446808279587 411979830151247170212419381)
        ·
          refine ⟨38623109076679422207414317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 411979830151247170212419381 38623109076679422207414317)
          ·
            refine ⟨14483665903754783327780369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38623109076679422207414317 14483665903754783327780369)
            ·
              refine ⟨10862749427816087495835277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14483665903754783327780369 10862749427816087495835277)
              ·
                refine ⟨4073531035431032810938229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10862749427816087495835277 4073531035431032810938229)
                ·
                  refine ⟨381893534571659326025459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4073531035431032810938229 381893534571659326025459)
                  ·
                    rfl

theorem cell23_6693615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 5].length) (baseStart_6693615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693615 prefixEnd_6693615 := by exact prefixLift 6693615
  have htrace : WordTrace (prefixWord ++ tailWord_6693615) baseStart_6693615 baseEnd_6693615 := by
    simpa [prefixWord, tailWord_6693615, baseEnd_6693615] using wordTrace_append hprefix tailTrace_6693615
  have hstable : (prefixWord ++ tailWord_6693615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693615).length < 2 ^ (prefixWord ++ tailWord_6693615).sum := by decide
  have hdescent : baseEnd_6693615 < baseStart_6693615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693685 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_6693685 : Nat := 118140960795 + 6693685 * 2 ^ 59
def prefixEnd_6693685 : Nat := 4983230072969 + 3 ^ 40 * 6693685 * 2
def baseEnd_6693685 : Nat := 3437077754790748660353809

theorem tailTrace_6693685 : CollatzResearch.WordTrace tailWord_6693685 prefixEnd_6693685 3437077754790748660353809 := by
  unfold tailWord_6693685
  simp only [CollatzResearch.WordTrace]
  refine ⟨244138748754929910229074509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162759165836619940152716339 244138748754929910229074509)
  ·
    refine ⟨91552030783098716335902941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244138748754929910229074509 91552030783098716335902941)
    ·
      refine ⟨34332011543662018625963603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91552030783098716335902941 34332011543662018625963603)
      ·
        refine ⟨51498017315493027938945405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34332011543662018625963603 51498017315493027938945405)
        ·
          refine ⟨19311756493309885477104527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51498017315493027938945405 19311756493309885477104527)
          ·
            refine ⟨28967634739964828215656791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19311756493309885477104527 28967634739964828215656791)
            ·
              refine ⟨43451452109947242323485187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28967634739964828215656791 43451452109947242323485187)
              ·
                refine ⟨65177178164920863485227781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43451452109947242323485187 65177178164920863485227781)
                ·
                  refine ⟨12220720905922661903480209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65177178164920863485227781 12220720905922661903480209)
                  ·
                    refine ⟨9165540679441996427610157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12220720905922661903480209 9165540679441996427610157)
                    ·
                      refine ⟨3437077754790748660353809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9165540679441996427610157 3437077754790748660353809)
                      ·
                        rfl

theorem cell23_6693685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_6693685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693685 prefixEnd_6693685 := by exact prefixLift 6693685
  have htrace : WordTrace (prefixWord ++ tailWord_6693685) baseStart_6693685 baseEnd_6693685 := by
    simpa [prefixWord, tailWord_6693685, baseEnd_6693685] using wordTrace_append hprefix tailTrace_6693685
  have hstable : (prefixWord ++ tailWord_6693685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693685).length < 2 ^ (prefixWord ++ tailWord_6693685).sum := by decide
  have hdescent : baseEnd_6693685 < baseStart_6693685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693688 : List Nat := [2, 1, 2, 1, 3, 2, 2, 4, 6]
def baseStart_6693688 : Nat := 118140960795 + 6693688 * 2 ^ 59
def prefixEnd_6693688 : Nat := 4983230072969 + 3 ^ 40 * 6693688 * 2
def baseEnd_6693688 : Nat := 381897699470301349846255

theorem tailTrace_6693688 : CollatzResearch.WordTrace tailWord_6693688 prefixEnd_6693688 381897699470301349846255 := by
  unfold tailWord_6693688
  simp only [CollatzResearch.WordTrace]
  refine ⟨122069429086959520870716859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162759238782612694494289145 122069429086959520870716859)
  ·
    refine ⟨183104143630439281306075289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122069429086959520870716859 183104143630439281306075289)
    ·
      refine ⟨137328107722829460979556467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183104143630439281306075289 137328107722829460979556467)
      ·
        refine ⟨205992161584244191469334701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137328107722829460979556467 205992161584244191469334701)
        ·
          refine ⟨77247060594091571801000513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205992161584244191469334701 77247060594091571801000513)
          ·
            refine ⟨57935295445568678850750385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77247060594091571801000513 57935295445568678850750385)
            ·
              refine ⟨43451471584176509138062789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57935295445568678850750385 43451471584176509138062789)
              ·
                refine ⟨8147150922033095463386773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43451471584176509138062789 8147150922033095463386773)
                ·
                  refine ⟨381897699470301349846255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8147150922033095463386773 381897699470301349846255)
                  ·
                    rfl

theorem cell23_6693688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 6].length) (baseStart_6693688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693688 prefixEnd_6693688 := by exact prefixLift 6693688
  have htrace : WordTrace (prefixWord ++ tailWord_6693688) baseStart_6693688 baseEnd_6693688 := by
    simpa [prefixWord, tailWord_6693688, baseEnd_6693688] using wordTrace_append hprefix tailTrace_6693688
  have hstable : (prefixWord ++ tailWord_6693688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693688).length < 2 ^ (prefixWord ++ tailWord_6693688).sum := by decide
  have hdescent : baseEnd_6693688 < baseStart_6693688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693705 : List Nat := [1, 2, 1, 1, 2, 5, 4, 1, 6]
def baseStart_6693705 : Nat := 118140960795 + 6693705 * 2 ^ 59
def prefixEnd_6693705 : Nat := 4983230072969 + 3 ^ 40 * 6693705 * 2
def baseEnd_6693705 : Nat := 381898669378204286900413

theorem tailTrace_6693705 : CollatzResearch.WordTrace tailWord_6693705 prefixEnd_6693705 381898669378204286900413 := by
  unfold tailWord_6693705
  simp only [CollatzResearch.WordTrace]
  refine ⟨244139478214857453644802569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162759652143238302429868379 244139478214857453644802569)
  ·
    refine ⟨183104608661143090233601927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244139478214857453644802569 183104608661143090233601927)
    ·
      refine ⟨274656912991714635350402891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183104608661143090233601927 274656912991714635350402891)
      ·
        refine ⟨411985369487571953025604337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274656912991714635350402891 411985369487571953025604337)
        ·
          refine ⟨308989027115678964769203253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411985369487571953025604337 308989027115678964769203253)
          ·
            refine ⟨28967721292094902947112805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 308989027115678964769203253 28967721292094902947112805)
            ·
              refine ⟨5431447742267794302583651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28967721292094902947112805 5431447742267794302583651)
              ·
                refine ⟨8147171613401691453875477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5431447742267794302583651 8147171613401691453875477)
                ·
                  refine ⟨381898669378204286900413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8147171613401691453875477 381898669378204286900413)
                  ·
                    rfl

theorem cell23_6693705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 6].length) (baseStart_6693705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693705 prefixEnd_6693705 := by exact prefixLift 6693705
  have htrace : WordTrace (prefixWord ++ tailWord_6693705) baseStart_6693705 baseEnd_6693705 := by
    simpa [prefixWord, tailWord_6693705, baseEnd_6693705] using wordTrace_append hprefix tailTrace_6693705
  have hstable : (prefixWord ++ tailWord_6693705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693705).length < 2 ^ (prefixWord ++ tailWord_6693705).sum := by decide
  have hdescent : baseEnd_6693705 < baseStart_6693705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693715 : List Nat := [1, 1, 1, 2, 1, 1, 3, 6, 3, 1, 3]
def baseStart_6693715 : Nat := 118140960795 + 6693715 * 2 ^ 59
def prefixEnd_6693715 : Nat := 4983230072969 + 3 ^ 40 * 6693715 * 2
def baseEnd_6693715 : Nat := 3437093159210383542978671

theorem tailTrace_6693715 : CollatzResearch.WordTrace tailWord_6693715 prefixEnd_6693715 3437093159210383542978671 := by
  unfold tailWord_6693715
  simp only [CollatzResearch.WordTrace]
  refine ⟨244139842944821225352666599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162759895296547483568444399 244139842944821225352666599)
  ·
    refine ⟨366209764417231838028999899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244139842944821225352666599 366209764417231838028999899)
    ·
      refine ⟨549314646625847757043499849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366209764417231838028999899 549314646625847757043499849)
      ·
        refine ⟨411985984969385817782624887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 549314646625847757043499849 411985984969385817782624887)
        ·
          refine ⟨617978977454078726673937331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411985984969385817782624887 617978977454078726673937331)
          ·
            refine ⟨926968466181118090010905997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617978977454078726673937331 926968466181118090010905997)
            ·
              refine ⟨347613174817919283754089749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 926968466181118090010905997 347613174817919283754089749)
              ·
                refine ⟨16294367569589966425972957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 347613174817919283754089749 16294367569589966425972957)
                ·
                  refine ⟨6110387838596237409739859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16294367569589966425972957 6110387838596237409739859)
                  ·
                    refine ⟨9165581757894356114609789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6110387838596237409739859 9165581757894356114609789)
                    ·
                      refine ⟨3437093159210383542978671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9165581757894356114609789 3437093159210383542978671)
                      ·
                        rfl

theorem cell23_6693715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 1, 3].length) (baseStart_6693715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693715 prefixEnd_6693715 := by exact prefixLift 6693715
  have htrace : WordTrace (prefixWord ++ tailWord_6693715) baseStart_6693715 baseEnd_6693715 := by
    simpa [prefixWord, tailWord_6693715, baseEnd_6693715] using wordTrace_append hprefix tailTrace_6693715
  have hstable : (prefixWord ++ tailWord_6693715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693715).length < 2 ^ (prefixWord ++ tailWord_6693715).sum := by decide
  have hdescent : baseEnd_6693715 < baseStart_6693715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693765 : List Nat := [1, 3, 1, 1, 3, 4, 2, 1, 1, 6]
def baseStart_6693765 : Nat := 118140960795 + 6693765 * 2 ^ 59
def prefixEnd_6693765 : Nat := 4983230072969 + 3 ^ 40 * 6693765 * 2
def baseEnd_6693765 : Nat := 1145706277747702782451147

theorem tailTrace_6693765 : CollatzResearch.WordTrace tailWord_6693765 prefixEnd_6693765 1145706277747702782451147 := by
  unfold tailWord_6693765
  simp only [CollatzResearch.WordTrace]
  refine ⟨244141666594640083891986749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162761111063093389261324499 244141666594640083891986749)
  ·
    refine ⟨91553124972990031459495031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244141666594640083891986749 91553124972990031459495031)
    ·
      refine ⟨137329687459485047189242547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91553124972990031459495031 137329687459485047189242547)
      ·
        refine ⟨205994531189227570783863821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137329687459485047189242547 205994531189227570783863821)
        ·
          refine ⟨77247949195960339043948933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205994531189227570783863821 77247949195960339043948933)
          ·
            refine ⟨14483990474242563570740425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77247949195960339043948933 14483990474242563570740425)
            ·
              refine ⟨10862992855681922678055319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14483990474242563570740425 10862992855681922678055319)
              ·
                refine ⟨16294489283522884017082979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10862992855681922678055319 16294489283522884017082979)
                ·
                  refine ⟨24441733925284326025624469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16294489283522884017082979 24441733925284326025624469)
                  ·
                    refine ⟨1145706277747702782451147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24441733925284326025624469 1145706277747702782451147)
                    ·
                      rfl

theorem cell23_6693765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_6693765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693765 prefixEnd_6693765 := by exact prefixLift 6693765
  have htrace : WordTrace (prefixWord ++ tailWord_6693765) baseStart_6693765 baseEnd_6693765 := by
    simpa [prefixWord, tailWord_6693765, baseEnd_6693765] using wordTrace_append hprefix tailTrace_6693765
  have hstable : (prefixWord ++ tailWord_6693765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693765).length < 2 ^ (prefixWord ++ tailWord_6693765).sum := by decide
  have hdescent : baseEnd_6693765 < baseStart_6693765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693772 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 5, 2, 2]
def baseStart_6693772 : Nat := 118140960795 + 6693772 * 2 ^ 59
def prefixEnd_6693772 : Nat := 4983230072969 + 3 ^ 40 * 6693772 * 2
def baseEnd_6693772 : Nat := 3437122427607689819965909

theorem tailTrace_6693772 : CollatzResearch.WordTrace tailWord_6693772 prefixEnd_6693772 3437122427607689819965909 := by
  unfold tailWord_6693772
  simp only [CollatzResearch.WordTrace]
  refine ⟨122070960952807362043745785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162761281270409816058327713 122070960952807362043745785)
  ·
    refine ⟨91553220714605521532809339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122070960952807362043745785 91553220714605521532809339)
    ·
      refine ⟨137329831071908282299214009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91553220714605521532809339 137329831071908282299214009)
      ·
        refine ⟨102997373303931211724410507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137329831071908282299214009 102997373303931211724410507)
        ·
          refine ⟨154496059955896817586615761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102997373303931211724410507 154496059955896817586615761)
          ·
            refine ⟨115872044966922613189961821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154496059955896817586615761 115872044966922613189961821)
            ·
              refine ⟨43452016862595979946235683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115872044966922613189961821 43452016862595979946235683)
              ·
                refine ⟨65178025293893969919353525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43452016862595979946235683 65178025293893969919353525)
                ·
                  refine ⟨6110439871302559679939393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65178025293893969919353525 6110439871302559679939393)
                  ·
                    refine ⟨4582829903476919759954545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6110439871302559679939393 4582829903476919759954545)
                    ·
                      refine ⟨3437122427607689819965909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4582829903476919759954545 3437122427607689819965909)
                      ·
                        rfl

theorem cell23_6693772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_6693772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693772 prefixEnd_6693772 := by exact prefixLift 6693772
  have htrace : WordTrace (prefixWord ++ tailWord_6693772) baseStart_6693772 baseEnd_6693772 := by
    simpa [prefixWord, tailWord_6693772, baseEnd_6693772] using wordTrace_append hprefix tailTrace_6693772
  have hstable : (prefixWord ++ tailWord_6693772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693772).length < 2 ^ (prefixWord ++ tailWord_6693772).sum := by decide
  have hdescent : baseEnd_6693772 < baseStart_6693772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693786 : List Nat := [3, 1, 1, 4, 4, 1, 2, 1, 1, 5]
def baseStart_6693786 : Nat := 118140960795 + 6693786 * 2 ^ 59
def prefixEnd_6693786 : Nat := 4983230072969 + 3 ^ 40 * 6693786 * 2
def baseEnd_6693786 : Nat := 1145709872112284255063615

theorem tailTrace_6693786 : CollatzResearch.WordTrace tailWord_6693786 prefixEnd_6693786 1145709872112284255063615 := by
  unfold tailWord_6693786
  simp only [CollatzResearch.WordTrace]
  refine ⟨61035608131891001119625303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162761621685042669652334141 61035608131891001119625303)
  ·
    refine ⟨91553412197836501679437955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61035608131891001119625303 91553412197836501679437955)
    ·
      refine ⟨137330118296754752519156933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91553412197836501679437955 137330118296754752519156933)
      ·
        refine ⟨25749397180641516097341925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137330118296754752519156933 25749397180641516097341925)
        ·
          refine ⟨4828011971370284268251611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25749397180641516097341925 4828011971370284268251611)
          ·
            refine ⟨7242017957055426402377417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4828011971370284268251611 7242017957055426402377417)
            ·
              refine ⟨5431513467791569801783063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7242017957055426402377417 5431513467791569801783063)
              ·
                refine ⟨8147270201687354702674595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5431513467791569801783063 8147270201687354702674595)
                ·
                  refine ⟨12220905302531032054011893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8147270201687354702674595 12220905302531032054011893)
                  ·
                    refine ⟨1145709872112284255063615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12220905302531032054011893 1145709872112284255063615)
                    ·
                      rfl

theorem cell23_6693786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 1, 5].length) (baseStart_6693786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693786 prefixEnd_6693786 := by exact prefixLift 6693786
  have htrace : WordTrace (prefixWord ++ tailWord_6693786) baseStart_6693786 baseEnd_6693786 := by
    simpa [prefixWord, tailWord_6693786, baseEnd_6693786] using wordTrace_append hprefix tailTrace_6693786
  have hstable : (prefixWord ++ tailWord_6693786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693786).length < 2 ^ (prefixWord ++ tailWord_6693786).sum := by decide
  have hdescent : baseEnd_6693786 < baseStart_6693786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693849 : List Nat := [1, 2, 1, 2, 5, 1, 2, 3, 1, 3, 2]
def baseStart_6693849 : Nat := 118140960795 + 6693849 * 2 ^ 59
def prefixEnd_6693849 : Nat := 4983230072969 + 3 ^ 40 * 6693849 * 2
def baseEnd_6693849 : Nat := 3437161965618086018703055

theorem tailTrace_6693849 : CollatzResearch.WordTrace tailWord_6693849 prefixEnd_6693849 3437161965618086018703055 := by
  unfold tailWord_6693849
  simp only [CollatzResearch.WordTrace]
  refine ⟨244144730326335766238044601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162763153550890510825363067 244144730326335766238044601)
  ·
    refine ⟨183108547744751824678533451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244144730326335766238044601 183108547744751824678533451)
    ·
      refine ⟨274662821617127737017800177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183108547744751824678533451 274662821617127737017800177)
      ·
        refine ⟨205997116212845802763350133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274662821617127737017800177 205997116212845802763350133)
        ·
          refine ⟨19312229644954294009064075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205997116212845802763350133 19312229644954294009064075)
          ·
            refine ⟨28968344467431441013596113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19312229644954294009064075 28968344467431441013596113)
            ·
              refine ⟨21726258350573580760197085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28968344467431441013596113 21726258350573580760197085)
              ·
                refine ⟨8147346881465092785073907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21726258350573580760197085 8147346881465092785073907)
                ·
                  refine ⟨12221020322197639177610861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8147346881465092785073907 12221020322197639177610861)
                  ·
                    refine ⟨4582882620824114691604073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12221020322197639177610861 4582882620824114691604073)
                    ·
                      refine ⟨3437161965618086018703055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4582882620824114691604073 3437161965618086018703055)
                      ·
                        rfl

theorem cell23_6693849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 3, 2].length) (baseStart_6693849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693849 prefixEnd_6693849 := by exact prefixLift 6693849
  have htrace : WordTrace (prefixWord ++ tailWord_6693849) baseStart_6693849 baseEnd_6693849 := by
    simpa [prefixWord, tailWord_6693849, baseEnd_6693849] using wordTrace_append hprefix tailTrace_6693849
  have hstable : (prefixWord ++ tailWord_6693849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693849).length < 2 ^ (prefixWord ++ tailWord_6693849).sum := by decide
  have hdescent : baseEnd_6693849 < baseStart_6693849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693919 : List Nat := [1, 1, 2, 4, 1, 3, 4, 2, 5]
def baseStart_6693919 : Nat := 118140960795 + 6693919 * 2 ^ 59
def prefixEnd_6693919 : Nat := 4983230072969 + 3 ^ 40 * 6693919 * 2
def baseEnd_6693919 : Nat := 381910878807100082758637

theorem tailTrace_6693919 : CollatzResearch.WordTrace tailWord_6693919 prefixEnd_6693919 381910878807100082758637 := by
  unfold tailWord_6693919
  simp only [CollatzResearch.WordTrace]
  refine ⟨244147283436082168193092811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162764855624054778795395207 244147283436082168193092811)
  ·
    refine ⟨366220925154123252289639217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244147283436082168193092811 366220925154123252289639217)
    ·
      refine ⟨274665693865592439217229413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366220925154123252289639217 274665693865592439217229413)
      ·
        refine ⟨51499817599798582353230515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274665693865592439217229413 51499817599798582353230515)
        ·
          refine ⟨77249726399697873529845773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51499817599798582353230515 77249726399697873529845773)
          ·
            refine ⟨28968647399886702573692165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77249726399697873529845773 28968647399886702573692165)
            ·
              refine ⟨5431621387478756732567281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28968647399886702573692165 5431621387478756732567281)
              ·
                refine ⟨4073716040609067549425461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5431621387478756732567281 4073716040609067549425461)
                ·
                  refine ⟨381910878807100082758637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4073716040609067549425461 381910878807100082758637)
                  ·
                    rfl

theorem cell23_6693919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 5].length) (baseStart_6693919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693919 prefixEnd_6693919 := by exact prefixLift 6693919
  have htrace : WordTrace (prefixWord ++ tailWord_6693919) baseStart_6693919 baseEnd_6693919 := by
    simpa [prefixWord, tailWord_6693919, baseEnd_6693919] using wordTrace_append hprefix tailTrace_6693919
  have hstable : (prefixWord ++ tailWord_6693919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693919).length < 2 ^ (prefixWord ++ tailWord_6693919).sum := by decide
  have hdescent : baseEnd_6693919 < baseStart_6693919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693925 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 1, 2, 5]
def baseStart_6693925 : Nat := 118140960795 + 6693925 * 2 ^ 59
def prefixEnd_6693925 : Nat := 4983230072969 + 3 ^ 40 * 6693925 * 2
def baseEnd_6693925 : Nat := 3437200990147827721352705

theorem tailTrace_6693925 : CollatzResearch.WordTrace tailWord_6693925 prefixEnd_6693925 3437200990147827721352705 := by
  unfold tailWord_6693925
  simp only [CollatzResearch.WordTrace]
  refine ⟨244147502274060431217811229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162765001516040287478540819 244147502274060431217811229)
  ·
    refine ⟨91555313352772661706679211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244147502274060431217811229 91555313352772661706679211)
    ·
      refine ⟨137332970029158992560018817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91555313352772661706679211 137332970029158992560018817)
      ·
        refine ⟨102999727521869244420014113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137332970029158992560018817 102999727521869244420014113)
        ·
          refine ⟨77249795641401933315010585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102999727521869244420014113 77249795641401933315010585)
          ·
            refine ⟨57937346731051449986257939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77249795641401933315010585 57937346731051449986257939)
            ·
              refine ⟨86906020096577174979386909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57937346731051449986257939 86906020096577174979386909)
              ·
                refine ⟨32589757536216440617270091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86906020096577174979386909 32589757536216440617270091)
                ·
                  refine ⟨48884636304324660925905137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32589757536216440617270091 48884636304324660925905137)
                  ·
                    refine ⟨36663477228243495694428853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48884636304324660925905137 36663477228243495694428853)
                    ·
                      refine ⟨3437200990147827721352705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36663477228243495694428853 3437200990147827721352705)
                      ·
                        rfl

theorem cell23_6693925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_6693925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693925 prefixEnd_6693925 := by exact prefixLift 6693925
  have htrace : WordTrace (prefixWord ++ tailWord_6693925) baseStart_6693925 baseEnd_6693925 := by
    simpa [prefixWord, tailWord_6693925, baseEnd_6693925] using wordTrace_append hprefix tailTrace_6693925
  have hstable : (prefixWord ++ tailWord_6693925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693925).length < 2 ^ (prefixWord ++ tailWord_6693925).sum := by decide
  have hdescent : baseEnd_6693925 < baseStart_6693925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693949 : List Nat := [1, 4, 1, 3, 1, 4, 1, 1, 2, 5]
def baseStart_6693949 : Nat := 118140960795 + 6693949 * 2 ^ 59
def prefixEnd_6693949 : Nat := 4983230072969 + 3 ^ 40 * 6693949 * 2
def baseEnd_6693949 : Nat := 1145737771227845209150865

theorem tailTrace_6693949 : CollatzResearch.WordTrace tailWord_6693949 prefixEnd_6693949 1145737771227845209150865 := by
  unfold tailWord_6693949
  simp only [CollatzResearch.WordTrace]
  refine ⟨244148377625973483316684901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162765585083982322211123267 244148377625973483316684901)
  ·
    refine ⟨45777820804870028121878419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244148377625973483316684901 45777820804870028121878419)
    ·
      refine ⟨68666731207305042182817629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45777820804870028121878419 68666731207305042182817629)
      ·
        refine ⟨25750024202739390818556611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68666731207305042182817629 25750024202739390818556611)
        ·
          refine ⟨38625036304109086227834917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25750024202739390818556611 38625036304109086227834917)
          ·
            refine ⟨7242194307020453667719047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38625036304109086227834917 7242194307020453667719047)
            ·
              refine ⟨10863291460530680501578571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7242194307020453667719047 10863291460530680501578571)
              ·
                refine ⟨16294937190796020752367857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10863291460530680501578571 16294937190796020752367857)
                ·
                  refine ⟨12221202893097015564275893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16294937190796020752367857 12221202893097015564275893)
                  ·
                    refine ⟨1145737771227845209150865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12221202893097015564275893 1145737771227845209150865)
                    ·
                      rfl

theorem cell23_6693949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_6693949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693949 prefixEnd_6693949 := by exact prefixLift 6693949
  have htrace : WordTrace (prefixWord ++ tailWord_6693949) baseStart_6693949 baseEnd_6693949 := by
    simpa [prefixWord, tailWord_6693949, baseEnd_6693949] using wordTrace_append hprefix tailTrace_6693949
  have hstable : (prefixWord ++ tailWord_6693949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693949).length < 2 ^ (prefixWord ++ tailWord_6693949).sum := by decide
  have hdescent : baseEnd_6693949 < baseStart_6693949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693952 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 1, 6, 2]
def baseStart_6693952 : Nat := 118140960795 + 6693952 * 2 ^ 59
def prefixEnd_6693952 : Nat := 4983230072969 + 3 ^ 40 * 6693952 * 2
def baseEnd_6693952 : Nat := 3437214854125499115715081

theorem tailTrace_6693952 : CollatzResearch.WordTrace tailWord_6693952 prefixEnd_6693952 3437214854125499115715081 := by
  unfold tailWord_6693952
  simp only [CollatzResearch.WordTrace]
  refine ⟨122074243522481307414522055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162765658029975076552696073 122074243522481307414522055)
  ·
    refine ⟨183111365283721961121783083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122074243522481307414522055 183111365283721961121783083)
    ·
      refine ⟨274667047925582941682674625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183111365283721961121783083 274667047925582941682674625)
      ·
        refine ⟨206000285944187206262005969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274667047925582941682674625 206000285944187206262005969)
        ·
          refine ⟨154500214458140404696504477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206000285944187206262005969 154500214458140404696504477)
          ·
            refine ⟨57937580421802651761189179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154500214458140404696504477 57937580421802651761189179)
            ·
              refine ⟨86906370632703977641783769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57937580421802651761189179 86906370632703977641783769)
              ·
                refine ⟨65179777974527983231337827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86906370632703977641783769 65179777974527983231337827)
                ·
                  refine ⟨97769666961791974847006741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65179777974527983231337827 97769666961791974847006741)
                  ·
                    refine ⟨4582953138833998820953441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97769666961791974847006741 4582953138833998820953441)
                    ·
                      refine ⟨3437214854125499115715081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4582953138833998820953441 3437214854125499115715081)
                      ·
                        rfl

theorem cell23_6693952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 6, 2].length) (baseStart_6693952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693952 prefixEnd_6693952 := by exact prefixLift 6693952
  have htrace : WordTrace (prefixWord ++ tailWord_6693952) baseStart_6693952 baseEnd_6693952 := by
    simpa [prefixWord, tailWord_6693952, baseEnd_6693952] using wordTrace_append hprefix tailTrace_6693952
  have hstable : (prefixWord ++ tailWord_6693952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693952).length < 2 ^ (prefixWord ++ tailWord_6693952).sum := by decide
  have hdescent : baseEnd_6693952 < baseStart_6693952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6693986 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_6693986 : Nat := 118140960795 + 6693986 * 2 ^ 59
def prefixEnd_6693986 : Nat := 4983230072969 + 3 ^ 40 * 6693986 * 2
def baseEnd_6693986 : Nat := 3437232312467751982689925

theorem tailTrace_6693986 : CollatzResearch.WordTrace tailWord_6693986 prefixEnd_6693986 3437232312467751982689925 := by
  unfold tailWord_6693986
  simp only [CollatzResearch.WordTrace]
  refine ⟨61037431781709859658945453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162766484751226292423854541 61037431781709859658945453)
  ·
    refine ⟨22889036918141197372104545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61037431781709859658945453 22889036918141197372104545)
    ·
      refine ⟨17166777688605898029078409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22889036918141197372104545 17166777688605898029078409)
      ·
        refine ⟨12875083266454423521808807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17166777688605898029078409 12875083266454423521808807)
        ·
          refine ⟨19312624899681635282713211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12875083266454423521808807 19312624899681635282713211)
          ·
            refine ⟨28968937349522452924069817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19312624899681635282713211 28968937349522452924069817)
            ·
              refine ⟨21726703012141839693052363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28968937349522452924069817 21726703012141839693052363)
              ·
                refine ⟨32590054518212759539578545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21726703012141839693052363 32590054518212759539578545)
                ·
                  refine ⟨24442540888659569654683909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32590054518212759539578545 24442540888659569654683909)
                  ·
                    refine ⟨4582976416623669310253233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24442540888659569654683909 4582976416623669310253233)
                    ·
                      refine ⟨3437232312467751982689925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4582976416623669310253233 3437232312467751982689925)
                      ·
                        rfl

theorem cell23_6693986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_6693986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6693986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6693986 prefixEnd_6693986 := by exact prefixLift 6693986
  have htrace : WordTrace (prefixWord ++ tailWord_6693986) baseStart_6693986 baseEnd_6693986 := by
    simpa [prefixWord, tailWord_6693986, baseEnd_6693986] using wordTrace_append hprefix tailTrace_6693986
  have hstable : (prefixWord ++ tailWord_6693986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6693986).length < 2 ^ (prefixWord ++ tailWord_6693986).sum := by decide
  have hdescent : baseEnd_6693986 < baseStart_6693986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6693986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694002 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 2, 5, 3]
def baseStart_6694002 : Nat := 118140960795 + 6694002 * 2 ^ 59
def prefixEnd_6694002 : Nat := 4983230072969 + 3 ^ 40 * 6694002 * 2
def baseEnd_6694002 : Nat := 3437240528158223920089851

theorem tailTrace_6694002 : CollatzResearch.WordTrace tailWord_6694002 prefixEnd_6694002 3437240528158223920089851 := by
  unfold tailWord_6694002
  simp only [CollatzResearch.WordTrace]
  refine ⟨61037577673695368342091065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162766873796520982245576173 61037577673695368342091065)
  ·
    refine ⟨45778183255271526256568299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61037577673695368342091065 45778183255271526256568299)
    ·
      refine ⟨68667274882907289384852449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45778183255271526256568299 68667274882907289384852449)
      ·
        refine ⟨51500456162180467038639337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68667274882907289384852449 51500456162180467038639337)
        ·
          refine ⟨38625342121635350278979503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51500456162180467038639337 38625342121635350278979503)
          ·
            refine ⟨57938013182453025418469255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38625342121635350278979503 57938013182453025418469255)
            ·
              refine ⟨86907019773679538127703883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57938013182453025418469255 86907019773679538127703883)
              ·
                refine ⟨130360529660519307191555825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86907019773679538127703883 130360529660519307191555825)
                ·
                  refine ⟨97770397245389480393666869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130360529660519307191555825 97770397245389480393666869)
                  ·
                    refine ⟨9165974741755263786906269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97770397245389480393666869 9165974741755263786906269)
                    ·
                      refine ⟨3437240528158223920089851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9165974741755263786906269 3437240528158223920089851)
                      ·
                        rfl

theorem cell23_6694002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_6694002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694002 prefixEnd_6694002 := by exact prefixLift 6694002
  have htrace : WordTrace (prefixWord ++ tailWord_6694002) baseStart_6694002 baseEnd_6694002 := by
    simpa [prefixWord, tailWord_6694002, baseEnd_6694002] using wordTrace_append hprefix tailTrace_6694002
  have hstable : (prefixWord ++ tailWord_6694002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694002).length < 2 ^ (prefixWord ++ tailWord_6694002).sum := by decide
  have hdescent : baseEnd_6694002 < baseStart_6694002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694079 : List Nat := [1, 1, 2, 2, 2, 2, 2, 5, 1, 2, 3]
def baseStart_6694079 : Nat := 118140960795 + 6694079 * 2 ^ 59
def prefixEnd_6694079 : Nat := 4983230072969 + 3 ^ 40 * 6694079 * 2
def baseEnd_6694079 : Nat := 3437280066168620118826997

theorem tailTrace_6694079 : CollatzResearch.WordTrace tailWord_6694079 prefixEnd_6694079 3437280066168620118826997 := by
  unfold tailWord_6694079
  simp only [CollatzResearch.WordTrace]
  refine ⟨244153119115502515518917291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162768746077001677012611527 244153119115502515518917291)
  ·
    refine ⟨366229678673253773278375937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244153119115502515518917291 366229678673253773278375937)
    ·
      refine ⟨274672259004940329958781953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366229678673253773278375937 274672259004940329958781953)
      ·
        refine ⟨206004194253705247469086465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274672259004940329958781953 206004194253705247469086465)
        ·
          refine ⟨154503145690278935601814849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206004194253705247469086465 154503145690278935601814849)
          ·
            refine ⟨115877359267709201701361137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154503145690278935601814849 115877359267709201701361137)
            ·
              refine ⟨86908019450781901276020853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115877359267709201701361137 86908019450781901276020853)
              ·
                refine ⟨8147626823510803244626955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86908019450781901276020853 8147626823510803244626955)
                ·
                  refine ⟨12221440235266204866940433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8147626823510803244626955 12221440235266204866940433)
                  ·
                    refine ⟨9166080176449653650205325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12221440235266204866940433 9166080176449653650205325)
                    ·
                      refine ⟨3437280066168620118826997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9166080176449653650205325 3437280066168620118826997)
                      ·
                        rfl

theorem cell23_6694079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 2, 3].length) (baseStart_6694079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694079 prefixEnd_6694079 := by exact prefixLift 6694079
  have htrace : WordTrace (prefixWord ++ tailWord_6694079) baseStart_6694079 baseEnd_6694079 := by
    simpa [prefixWord, tailWord_6694079, baseEnd_6694079] using wordTrace_append hprefix tailTrace_6694079
  have hstable : (prefixWord ++ tailWord_6694079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694079).length < 2 ^ (prefixWord ++ tailWord_6694079).sum := by decide
  have hdescent : baseEnd_6694079 < baseStart_6694079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694130 : List Nat := [3, 2, 1, 3, 3, 2, 2, 1, 1, 2, 3]
def baseStart_6694130 : Nat := 118140960795 + 6694130 * 2 ^ 59
def prefixEnd_6694130 : Nat := 4983230072969 + 3 ^ 40 * 6694130 * 2
def baseEnd_6694130 : Nat := 3437306253681999419289263

theorem tailTrace_6694130 : CollatzResearch.WordTrace tailWord_6694130 prefixEnd_6694130 3437306253681999419289263 := by
  unfold tailWord_6694130
  simp only [CollatzResearch.WordTrace]
  refine ⟨61038744809579437807255961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162769986158878500819349229 61038744809579437807255961)
  ·
    refine ⟨45779058607184578355441971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61038744809579437807255961 45779058607184578355441971)
    ·
      refine ⟨68668587910776867533162957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45779058607184578355441971 68668587910776867533162957)
      ·
        refine ⟨25750720466541325324936109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68668587910776867533162957 25750720466541325324936109)
        ·
          refine ⟨9656520174952996996851041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25750720466541325324936109 9656520174952996996851041)
          ·
            refine ⟨7242390131214747747638281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9656520174952996996851041 7242390131214747747638281)
            ·
              refine ⟨5431792598411060810728711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7242390131214747747638281 5431792598411060810728711)
              ·
                refine ⟨8147688897616591216093067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5431792598411060810728711 8147688897616591216093067)
                ·
                  refine ⟨12221533346424886824139601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8147688897616591216093067 12221533346424886824139601)
                  ·
                    refine ⟨9166150009818665118104701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12221533346424886824139601 9166150009818665118104701)
                    ·
                      refine ⟨3437306253681999419289263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9166150009818665118104701 3437306253681999419289263)
                      ·
                        rfl

theorem cell23_6694130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_6694130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694130 prefixEnd_6694130 := by exact prefixLift 6694130
  have htrace : WordTrace (prefixWord ++ tailWord_6694130) baseStart_6694130 baseEnd_6694130 := by
    simpa [prefixWord, tailWord_6694130, baseEnd_6694130] using wordTrace_append hprefix tailTrace_6694130
  have hstable : (prefixWord ++ tailWord_6694130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694130).length < 2 ^ (prefixWord ++ tailWord_6694130).sum := by decide
  have hdescent : baseEnd_6694130 < baseStart_6694130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694143 : List Nat := [1, 1, 2, 2, 1, 7, 1, 2, 2, 1, 3]
def baseStart_6694143 : Nat := 118140960795 + 6694143 * 2 ^ 59
def prefixEnd_6694143 : Nat := 4983230072969 + 3 ^ 40 * 6694143 * 2
def baseEnd_6694143 : Nat := 3437312928930507868426703

theorem tailTrace_6694143 : CollatzResearch.WordTrace tailWord_6694143 prefixEnd_6694143 3437312928930507868426703 := by
  unfold tailWord_6694143
  simp only [CollatzResearch.WordTrace]
  refine ⟨244155453387270654449247083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162770302258180436299498055 244155453387270654449247083)
  ·
    refine ⟨366233180080905981673870625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244155453387270654449247083 366233180080905981673870625)
    ·
      refine ⟨274674885060679486255402969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366233180080905981673870625 274674885060679486255402969)
      ·
        refine ⟨206006163795509614691552227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274674885060679486255402969 206006163795509614691552227)
        ·
          refine ⟨309009245693264422037328341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206006163795509614691552227 309009245693264422037328341)
          ·
            refine ⟨7242404195935884891499883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 309009245693264422037328341 7242404195935884891499883)
            ·
              refine ⟨10863606293903827337249825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7242404195935884891499883 10863606293903827337249825)
              ·
                refine ⟨8147704720427870502937369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10863606293903827337249825 8147704720427870502937369)
                ·
                  refine ⟨6110778540320902877203027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8147704720427870502937369 6110778540320902877203027)
                  ·
                    refine ⟨9166167810481354315804541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6110778540320902877203027 9166167810481354315804541)
                    ·
                      refine ⟨3437312928930507868426703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9166167810481354315804541 3437312928930507868426703)
                      ·
                        rfl

theorem cell23_6694143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 1, 3].length) (baseStart_6694143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694143 prefixEnd_6694143 := by exact prefixLift 6694143
  have htrace : WordTrace (prefixWord ++ tailWord_6694143) baseStart_6694143 baseEnd_6694143 := by
    simpa [prefixWord, tailWord_6694143, baseEnd_6694143] using wordTrace_append hprefix tailTrace_6694143
  have hstable : (prefixWord ++ tailWord_6694143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694143).length < 2 ^ (prefixWord ++ tailWord_6694143).sum := by decide
  have hdescent : baseEnd_6694143 < baseStart_6694143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694186 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_6694186 : Nat := 118140960795 + 6694186 * 2 ^ 59
def prefixEnd_6694186 : Nat := 4983230072969 + 3 ^ 40 * 6694186 * 2
def baseEnd_6694186 : Nat := 3437335008598651200189005

theorem tailTrace_6694186 : CollatzResearch.WordTrace tailWord_6694186 prefixEnd_6694186 3437335008598651200189005 := by
  unfold tailWord_6694186
  simp only [CollatzResearch.WordTrace]
  refine ⟨61039255431528718198265603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162771347817409915195374941 61039255431528718198265603)
  ·
    refine ⟨91558883147293077297398405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61039255431528718198265603 91558883147293077297398405)
    ·
      refine ⟨17167290590117451993262201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91558883147293077297398405 17167290590117451993262201)
      ·
        refine ⟨12875467942588088994946651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17167290590117451993262201 12875467942588088994946651)
        ·
          refine ⟨19313201913882133492419977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12875467942588088994946651 19313201913882133492419977)
          ·
            refine ⟨14484901435411600119314983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19313201913882133492419977 14484901435411600119314983)
            ·
              refine ⟨21727352153117400178972475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14484901435411600119314983 21727352153117400178972475)
              ·
                refine ⟨32591028229676100268458713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21727352153117400178972475 32591028229676100268458713)
                ·
                  refine ⟨24443271172257075201344035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32591028229676100268458713 24443271172257075201344035)
                  ·
                    refine ⟨36664906758385612802016053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24443271172257075201344035 36664906758385612802016053)
                    ·
                      refine ⟨3437335008598651200189005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36664906758385612802016053 3437335008598651200189005)
                      ·
                        rfl

theorem cell23_6694186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_6694186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694186 prefixEnd_6694186 := by exact prefixLift 6694186
  have htrace : WordTrace (prefixWord ++ tailWord_6694186) baseStart_6694186 baseEnd_6694186 := by
    simpa [prefixWord, tailWord_6694186, baseEnd_6694186] using wordTrace_append hprefix tailTrace_6694186
  have hstable : (prefixWord ++ tailWord_6694186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694186).length < 2 ^ (prefixWord ++ tailWord_6694186).sum := by decide
  have hdescent : baseEnd_6694186 < baseStart_6694186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694249 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 7, 4]
def baseStart_6694249 : Nat := 118140960795 + 6694249 * 2 ^ 59
def prefixEnd_6694249 : Nat := 4983230072969 + 3 ^ 40 * 6694249 * 2
def baseEnd_6694249 : Nat := 1145789119293294817900405

theorem tailTrace_6694249 : CollatzResearch.WordTrace tailWord_6694249 prefixEnd_6694249 1145789119293294817900405 := by
  unfold tailWord_6694249
  simp only [CollatzResearch.WordTrace]
  refine ⟨244159319524886634552605801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162772879683257756368403867 244159319524886634552605801)
  ·
    refine ⟨183119489643664975914454351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244159319524886634552605801 183119489643664975914454351)
    ·
      refine ⟨274679234465497463871681527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183119489643664975914454351 274679234465497463871681527)
      ·
        refine ⟨412018851698246195807522291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274679234465497463871681527 412018851698246195807522291)
        ·
          refine ⟨618028277547369293711283437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412018851698246195807522291 618028277547369293711283437)
          ·
            refine ⟨231760604080263485141731289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 618028277547369293711283437 231760604080263485141731289)
            ·
              refine ⟨173820453060197613856298467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231760604080263485141731289 173820453060197613856298467)
              ·
                refine ⟨260730679590296420784447701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173820453060197613856298467 260730679590296420784447701)
                ·
                  refine ⟨6110875302897572362135493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 260730679590296420784447701 6110875302897572362135493)
                  ·
                    refine ⟨1145789119293294817900405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6110875302897572362135493 1145789119293294817900405)
                    ·
                      rfl

theorem cell23_6694249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 4].length) (baseStart_6694249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694249 prefixEnd_6694249 := by exact prefixLift 6694249
  have htrace : WordTrace (prefixWord ++ tailWord_6694249) baseStart_6694249 baseEnd_6694249 := by
    simpa [prefixWord, tailWord_6694249, baseEnd_6694249] using wordTrace_append hprefix tailTrace_6694249
  have hstable : (prefixWord ++ tailWord_6694249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694249).length < 2 ^ (prefixWord ++ tailWord_6694249).sum := by decide
  have hdescent : baseEnd_6694249 < baseStart_6694249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694256 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 2, 4, 2]
def baseStart_6694256 : Nat := 118140960795 + 6694256 * 2 ^ 59
def prefixEnd_6694256 : Nat := 4983230072969 + 3 ^ 40 * 6694256 * 2
def baseEnd_6694256 : Nat := 3437370952244465926313683

theorem tailTrace_6694256 : CollatzResearch.WordTrace tailWord_6694256 prefixEnd_6694256 3437370952244465926313683 := by
  unfold tailWord_6694256
  simp only [CollatzResearch.WordTrace]
  refine ⟨122079787417930637374055311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162773049890574183165407081 122079787417930637374055311)
  ·
    refine ⟨183119681126895956061082967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122079787417930637374055311 183119681126895956061082967)
    ·
      refine ⟨274679521690343934091624451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183119681126895956061082967 274679521690343934091624451)
      ·
        refine ⟨412019282535515901137436677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274679521690343934091624451 412019282535515901137436677)
        ·
          refine ⟨77253615475409231463269377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 412019282535515901137436677 77253615475409231463269377)
          ·
            refine ⟨57940211606556923597452033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77253615475409231463269377 57940211606556923597452033)
            ·
              refine ⟨43455158704917692698089025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57940211606556923597452033 43455158704917692698089025)
              ·
                refine ⟨32591369028688269523566769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43455158704917692698089025 32591369028688269523566769)
                ·
                  refine ⟨24443526771516202142675077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32591369028688269523566769 24443526771516202142675077)
                  ·
                    refine ⟨4583161269659287901751577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24443526771516202142675077 4583161269659287901751577)
                    ·
                      refine ⟨3437370952244465926313683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4583161269659287901751577 3437370952244465926313683)
                      ·
                        rfl

theorem cell23_6694256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 2, 4, 2].length) (baseStart_6694256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694256 prefixEnd_6694256 := by exact prefixLift 6694256
  have htrace : WordTrace (prefixWord ++ tailWord_6694256) baseStart_6694256 baseEnd_6694256 := by
    simpa [prefixWord, tailWord_6694256, baseEnd_6694256] using wordTrace_append hprefix tailTrace_6694256
  have hstable : (prefixWord ++ tailWord_6694256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694256).length < 2 ^ (prefixWord ++ tailWord_6694256).sum := by decide
  have hdescent : baseEnd_6694256 < baseStart_6694256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694289 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 3]
def baseStart_6694289 : Nat := 118140960795 + 6694289 * 2 ^ 59
def prefixEnd_6694289 : Nat := 4983230072969 + 3 ^ 40 * 6694289 * 2
def baseEnd_6694289 : Nat := 3437387897106064297201031

theorem tailTrace_6694289 : CollatzResearch.WordTrace tailWord_6694289 prefixEnd_6694289 3437387897106064297201031 := by
  unfold tailWord_6694289
  simp only [CollatzResearch.WordTrace]
  refine ⟨244160778444741721384061921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162773852296494480922707947 244160778444741721384061921)
  ·
    refine ⟨183120583833556291038046441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244160778444741721384061921 183120583833556291038046441)
    ·
      refine ⟨137340437875167218278534831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183120583833556291038046441 137340437875167218278534831)
      ·
        refine ⟨206010656812750827417802247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137340437875167218278534831 206010656812750827417802247)
        ·
          refine ⟨309015985219126241126703371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206010656812750827417802247 309015985219126241126703371)
          ·
            refine ⟨463523977828689361690055057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309015985219126241126703371 463523977828689361690055057)
            ·
              refine ⟨347642983371517021267541293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463523977828689361690055057 347642983371517021267541293)
              ·
                refine ⟨130366118764318882975327985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347642983371517021267541293 130366118764318882975327985)
                ·
                  refine ⟨97774589073239162231495989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130366118764318882975327985 97774589073239162231495989)
                  ·
                    refine ⟨9166367725616171459202749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97774589073239162231495989 9166367725616171459202749)
                    ·
                      refine ⟨3437387897106064297201031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9166367725616171459202749 3437387897106064297201031)
                      ·
                        rfl

theorem cell23_6694289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_6694289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694289 prefixEnd_6694289 := by exact prefixLift 6694289
  have htrace : WordTrace (prefixWord ++ tailWord_6694289) baseStart_6694289 baseEnd_6694289 := by
    simpa [prefixWord, tailWord_6694289, baseEnd_6694289] using wordTrace_append hprefix tailTrace_6694289
  have hstable : (prefixWord ++ tailWord_6694289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694289).length < 2 ^ (prefixWord ++ tailWord_6694289).sum := by decide
  have hdescent : baseEnd_6694289 < baseStart_6694289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694309 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 5, 5]
def baseStart_6694309 : Nat := 118140960795 + 6694309 * 2 ^ 59
def prefixEnd_6694309 : Nat := 4983230072969 + 3 ^ 40 * 6694309 * 2
def baseEnd_6694309 : Nat := 1145799388906384739650313

theorem tailTrace_6694309 : CollatzResearch.WordTrace tailWord_6694309 prefixEnd_6694309 1145799388906384739650313 := by
  unfold tailWord_6694309
  simp only [CollatzResearch.WordTrace]
  refine ⟨244161507904669264799789981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162774338603112843199859987 244161507904669264799789981)
  ·
    refine ⟨91560565464250974299921243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244161507904669264799789981 91560565464250974299921243)
    ·
      refine ⟨137340848196376461449881865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91560565464250974299921243 137340848196376461449881865)
      ·
        refine ⟨103005636147282346087411399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137340848196376461449881865 103005636147282346087411399)
        ·
          refine ⟨154508454220923519131117099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103005636147282346087411399 154508454220923519131117099)
          ·
            refine ⟨231762681331385278696675649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154508454220923519131117099 231762681331385278696675649)
            ·
              refine ⟨173822010998538959022506737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231762681331385278696675649 173822010998538959022506737)
              ·
                refine ⟨130366508248904219266880053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173822010998538959022506737 130366508248904219266880053)
                ·
                  refine ⟨12221860148334770556270005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130366508248904219266880053 12221860148334770556270005)
                  ·
                    refine ⟨1145799388906384739650313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12221860148334770556270005 1145799388906384739650313)
                    ·
                      rfl

theorem cell23_6694309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_6694309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694309 prefixEnd_6694309 := by exact prefixLift 6694309
  have htrace : WordTrace (prefixWord ++ tailWord_6694309) baseStart_6694309 baseEnd_6694309 := by
    simpa [prefixWord, tailWord_6694309, baseEnd_6694309] using wordTrace_append hprefix tailTrace_6694309
  have hstable : (prefixWord ++ tailWord_6694309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694309).length < 2 ^ (prefixWord ++ tailWord_6694309).sum := by decide
  have hdescent : baseEnd_6694309 < baseStart_6694309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694340 : List Nat := [2, 3, 3, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_6694340 : Nat := 118140960795 + 6694340 * 2 ^ 59
def prefixEnd_6694340 : Nat := 4983230072969 + 3 ^ 40 * 6694340 * 2
def baseEnd_6694340 : Nat := 3437414084619443597663297

theorem tailTrace_6694340 : CollatzResearch.WordTrace tailWord_6694340 prefixEnd_6694340 3437414084619443597663297 := by
  unfold tailWord_6694340
  simp only [CollatzResearch.WordTrace]
  refine ⟨122081319283778478547084237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162775092378371304729445649 122081319283778478547084237)
  ·
    refine ⟨45780494731416929455156589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122081319283778478547084237 45780494731416929455156589)
    ·
      refine ⟨17167685524281348545683721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45780494731416929455156589 17167685524281348545683721)
      ·
        refine ⟨12875764143211011409262791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17167685524281348545683721 12875764143211011409262791)
        ·
          refine ⟨19313646214816517113894187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12875764143211011409262791 19313646214816517113894187)
          ·
            refine ⟨28970469322224775670841281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19313646214816517113894187 28970469322224775670841281)
            ·
              refine ⟨21727851991668581753130961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28970469322224775670841281 21727851991668581753130961)
              ·
                refine ⟨16295888993751436314848221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21727851991668581753130961 16295888993751436314848221)
                ·
                  refine ⟨6110958372656788618068083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16295888993751436314848221 6110958372656788618068083)
                  ·
                    refine ⟨9166437558985182927102125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6110958372656788618068083 9166437558985182927102125)
                    ·
                      refine ⟨3437414084619443597663297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9166437558985182927102125 3437414084619443597663297)
                      ·
                        rfl

theorem cell23_6694340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_6694340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694340 prefixEnd_6694340 := by exact prefixLift 6694340
  have htrace : WordTrace (prefixWord ++ tailWord_6694340) baseStart_6694340 baseEnd_6694340 := by
    simpa [prefixWord, tailWord_6694340, baseEnd_6694340] using wordTrace_append hprefix tailTrace_6694340
  have hstable : (prefixWord ++ tailWord_6694340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694340).length < 2 ^ (prefixWord ++ tailWord_6694340).sum := by decide
  have hdescent : baseEnd_6694340 < baseStart_6694340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694369 : List Nat := [1, 2, 3, 1, 2, 3, 11]
def baseStart_6694369 : Nat := 118140960795 + 6694369 * 2 ^ 59
def prefixEnd_6694369 : Nat := 4983230072969 + 3 ^ 40 * 6694369 * 2
def baseEnd_6694369 : Nat := 42437394759980543014823

theorem tailTrace_6694369 : CollatzResearch.WordTrace tailWord_6694369 prefixEnd_6694369 42437394759980543014823 := by
  unfold tailWord_6694369
  simp only [CollatzResearch.WordTrace]
  refine ⟨244163696284451895046974161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162775797522967930031316107 244163696284451895046974161)
  ·
    refine ⟨183122772213338921285230621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244163696284451895046974161 183122772213338921285230621)
    ·
      refine ⟨68671039580002095481961483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183122772213338921285230621 68671039580002095481961483)
      ·
        refine ⟨103006559370003143222942225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68671039580002095481961483 103006559370003143222942225)
        ·
          refine ⟨77254919527502357417206669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103006559370003143222942225 77254919527502357417206669)
          ·
            refine ⟨28970594822813384031452501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77254919527502357417206669 28970594822813384031452501)
            ·
              refine ⟨42437394759980543014823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28970594822813384031452501 42437394759980543014823)
              ·
                rfl

theorem cell23_6694369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 11].length) (baseStart_6694369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694369 prefixEnd_6694369 := by exact prefixLift 6694369
  have htrace : WordTrace (prefixWord ++ tailWord_6694369) baseStart_6694369 baseEnd_6694369 := by
    simpa [prefixWord, tailWord_6694369, baseEnd_6694369] using wordTrace_append hprefix tailTrace_6694369
  have hstable : (prefixWord ++ tailWord_6694369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694369).length < 2 ^ (prefixWord ++ tailWord_6694369).sum := by decide
  have hdescent : baseEnd_6694369 < baseStart_6694369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694373 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 4, 4]
def baseStart_6694373 : Nat := 118140960795 + 6694373 * 2 ^ 59
def prefixEnd_6694373 : Nat := 4983230072969 + 3 ^ 40 * 6694373 * 2
def baseEnd_6694373 : Nat := 1145810343160347322850215

theorem tailTrace_6694373 : CollatzResearch.WordTrace tailWord_6694373 prefixEnd_6694373 1145810343160347322850215 := by
  unfold tailWord_6694373
  simp only [CollatzResearch.WordTrace]
  refine ⟨244163842176437403730119773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162775894784291602486746515 244163842176437403730119773)
  ·
    refine ⟨91561440816164026398794915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244163842176437403730119773 91561440816164026398794915)
    ·
      refine ⟨137342161224246039598192373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91561440816164026398794915 137342161224246039598192373)
      ·
        refine ⟨12875827614773066212330535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137342161224246039598192373 12875827614773066212330535)
        ·
          refine ⟨19313741422159599318495803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12875827614773066212330535 19313741422159599318495803)
          ·
            refine ⟨28970612133239398977743705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19313741422159599318495803 28970612133239398977743705)
            ·
              refine ⟨21727959099929549233307779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28970612133239398977743705 21727959099929549233307779)
              ·
                refine ⟨32591938649894323849961669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21727959099929549233307779 32591938649894323849961669)
                ·
                  refine ⟨6110988496855185721867813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32591938649894323849961669 6110988496855185721867813)
                  ·
                    refine ⟨1145810343160347322850215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6110988496855185721867813 1145810343160347322850215)
                    ·
                      rfl

theorem cell23_6694373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_6694373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694373 prefixEnd_6694373 := by exact prefixLift 6694373
  have htrace : WordTrace (prefixWord ++ tailWord_6694373) baseStart_6694373 baseEnd_6694373 := by
    simpa [prefixWord, tailWord_6694373, baseEnd_6694373] using wordTrace_append hprefix tailTrace_6694373
  have hstable : (prefixWord ++ tailWord_6694373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694373).length < 2 ^ (prefixWord ++ tailWord_6694373).sum := by decide
  have hdescent : baseEnd_6694373 < baseStart_6694373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694386 : List Nat := [3, 2, 1, 4, 1, 1, 1, 10]
def baseStart_6694386 : Nat := 118140960795 + 6694386 * 2 ^ 59
def prefixEnd_6694386 : Nat := 4983230072969 + 3 ^ 40 * 6694386 * 2
def baseEnd_6694386 : Nat := 127312507582575941395855

theorem tailTrace_6694386 : CollatzResearch.WordTrace tailWord_6694386 prefixEnd_6694386 127312507582575941395855 := by
  unfold tailWord_6694386
  simp only [CollatzResearch.WordTrace]
  refine ⟨61041079081347576737585753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162776210883593537966895341 61041079081347576737585753)
  ·
    refine ⟨45780809311010682553189315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61041079081347576737585753 45780809311010682553189315)
    ·
      refine ⟨68671213966516023829783973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45780809311010682553189315 68671213966516023829783973)
      ·
        refine ⟨12875852618721754468084495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68671213966516023829783973 12875852618721754468084495)
        ·
          refine ⟨19313778928082631702126743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12875852618721754468084495 19313778928082631702126743)
          ·
            refine ⟨28970668392123947553190115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19313778928082631702126743 28970668392123947553190115)
            ·
              refine ⟨43456002588185921329785173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28970668392123947553190115 43456002588185921329785173)
              ·
                refine ⟨127312507582575941395855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43456002588185921329785173 127312507582575941395855)
                ·
                  rfl

theorem cell23_6694386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 10].length) (baseStart_6694386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694386 prefixEnd_6694386 := by exact prefixLift 6694386
  have htrace : WordTrace (prefixWord ++ tailWord_6694386) baseStart_6694386 baseEnd_6694386 := by
    simpa [prefixWord, tailWord_6694386, baseEnd_6694386] using wordTrace_append hprefix tailTrace_6694386
  have hstable : (prefixWord ++ tailWord_6694386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694386).length < 2 ^ (prefixWord ++ tailWord_6694386).sum := by decide
  have hdescent : baseEnd_6694386 < baseStart_6694386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694390 : List Nat := [5, 1, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_6694390 : Nat := 118140960795 + 6694390 * 2 ^ 59
def prefixEnd_6694390 : Nat := 4983230072969 + 3 ^ 40 * 6694390 * 2
def baseEnd_6694390 : Nat := 1145813252884056134012689

theorem tailTrace_6694390 : CollatzResearch.WordTrace tailWord_6694390 prefixEnd_6694390 1145813252884056134012689 := by
  unfold tailWord_6694390
  simp only [CollatzResearch.WordTrace]
  refine ⟨15260278888585988477093039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162776308144917210422325749 15260278888585988477093039)
  ·
    refine ⟨22890418332878982715639559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15260278888585988477093039 22890418332878982715639559)
    ·
      refine ⟨34335627499318474073459339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22890418332878982715639559 34335627499318474073459339)
      ·
        refine ⟨51503441248977711110189009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34335627499318474073459339 51503441248977711110189009)
        ·
          refine ⟨38627580936733283332641757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51503441248977711110189009 38627580936733283332641757)
          ·
            refine ⟨14485342851274981249740659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38627580936733283332641757 14485342851274981249740659)
            ·
              refine ⟨21728014276912471874610989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14485342851274981249740659 21728014276912471874610989)
              ·
                refine ⟨8148005353842176952979121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21728014276912471874610989 8148005353842176952979121)
                ·
                  refine ⟨6111004015381632714734341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8148005353842176952979121 6111004015381632714734341)
                  ·
                    refine ⟨1145813252884056134012689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6111004015381632714734341 1145813252884056134012689)
                    ·
                      rfl

theorem cell23_6694390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_6694390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694390 prefixEnd_6694390 := by exact prefixLift 6694390
  have htrace : WordTrace (prefixWord ++ tailWord_6694390) baseStart_6694390 baseEnd_6694390 := by
    simpa [prefixWord, tailWord_6694390, baseEnd_6694390] using wordTrace_append hprefix tailTrace_6694390
  have hstable : (prefixWord ++ tailWord_6694390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694390).length < 2 ^ (prefixWord ++ tailWord_6694390).sum := by decide
  have hdescent : baseEnd_6694390 < baseStart_6694390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694399 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 4, 7]
def baseStart_6694399 : Nat := 118140960795 + 6694399 * 2 ^ 59
def prefixEnd_6694399 : Nat := 4983230072969 + 3 ^ 40 * 6694399 * 2
def baseEnd_6694399 : Nat := 1145814793326019622275175

theorem tailTrace_6694399 : CollatzResearch.WordTrace tailWord_6694399 prefixEnd_6694399 1145814793326019622275175 := by
  unfold tailWord_6694399
  simp only [CollatzResearch.WordTrace]
  refine ⟨244164790474343210170566251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162776526982895473447044167 244164790474343210170566251)
  ·
    refine ⟨366247185711514815255849377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244164790474343210170566251 366247185711514815255849377)
    ·
      refine ⟨274685389283636111441887033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366247185711514815255849377 274685389283636111441887033)
      ·
        refine ⟨206014041962727083581415275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274685389283636111441887033 206014041962727083581415275)
        ·
          refine ⟨309021062944090625372122913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206014041962727083581415275 309021062944090625372122913)
          ·
            refine ⟨231765797208067969029092185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309021062944090625372122913 231765797208067969029092185)
            ·
              refine ⟨173824347906050976771819139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231765797208067969029092185 173824347906050976771819139)
              ·
                refine ⟨260736521859076465157728709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173824347906050976771819139 260736521859076465157728709)
                ·
                  refine ⟨48888097848576837217074133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 260736521859076465157728709 48888097848576837217074133)
                  ·
                    refine ⟨1145814793326019622275175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48888097848576837217074133 1145814793326019622275175)
                    ·
                      rfl

theorem cell23_6694399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 7].length) (baseStart_6694399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694399 prefixEnd_6694399 := by exact prefixLift 6694399
  have htrace : WordTrace (prefixWord ++ tailWord_6694399) baseStart_6694399 baseEnd_6694399 := by
    simpa [prefixWord, tailWord_6694399, baseEnd_6694399] using wordTrace_append hprefix tailTrace_6694399
  have hstable : (prefixWord ++ tailWord_6694399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694399).length < 2 ^ (prefixWord ++ tailWord_6694399).sum := by decide
  have hdescent : baseEnd_6694399 < baseStart_6694399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694487 : List Nat := [1, 1, 3, 2, 2, 3, 3, 2, 2, 2, 2]
def baseStart_6694487 : Nat := 118140960795 + 6694487 * 2 ^ 59
def prefixEnd_6694487 : Nat := 4983230072969 + 3 ^ 40 * 6694487 * 2
def baseEnd_6694487 : Nat := 3437489566275654522525121

theorem tailTrace_6694487 : CollatzResearch.WordTrace tailWord_6694487 prefixEnd_6694487 3437489566275654522525121 := by
  unfold tailWord_6694487
  simp only [CollatzResearch.WordTrace]
  refine ⟨244168000098024401199769715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162778666732016267466513143 244168000098024401199769715)
  ·
    refine ⟨366252000147036601799654573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244168000098024401199769715 366252000147036601799654573)
    ·
      refine ⟨137344500055138725674870465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366252000147036601799654573 137344500055138725674870465)
      ·
        refine ⟨103008375041354044256152849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137344500055138725674870465 103008375041354044256152849)
        ·
          refine ⟨77256281281015533192114637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103008375041354044256152849 77256281281015533192114637)
          ·
            refine ⟨28971105480380824947042989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77256281281015533192114637 28971105480380824947042989)
            ·
              refine ⟨10864164555142809355141121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28971105480380824947042989 10864164555142809355141121)
              ·
                refine ⟨8148123416357107016355841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10864164555142809355141121 8148123416357107016355841)
                ·
                  refine ⟨6111092562267830262266881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8148123416357107016355841 6111092562267830262266881)
                  ·
                    refine ⟨4583319421700872696700161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6111092562267830262266881 4583319421700872696700161)
                    ·
                      refine ⟨3437489566275654522525121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4583319421700872696700161 3437489566275654522525121)
                      ·
                        rfl

theorem cell23_6694487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_6694487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694487 prefixEnd_6694487 := by exact prefixLift 6694487
  have htrace : WordTrace (prefixWord ++ tailWord_6694487) baseStart_6694487 baseEnd_6694487 := by
    simpa [prefixWord, tailWord_6694487, baseEnd_6694487] using wordTrace_append hprefix tailTrace_6694487
  have hstable : (prefixWord ++ tailWord_6694487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694487).length < 2 ^ (prefixWord ++ tailWord_6694487).sum := by decide
  have hdescent : baseEnd_6694487 < baseStart_6694487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694503 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_6694503 : Nat := 118140960795 + 6694503 * 2 ^ 59
def prefixEnd_6694503 : Nat := 4983230072969 + 3 ^ 40 * 6694503 * 2
def baseEnd_6694503 : Nat := 3437497781966126459925047

theorem tailTrace_6694503 : CollatzResearch.WordTrace tailWord_6694503 prefixEnd_6694503 3437497781966126459925047 := by
  unfold tailWord_6694503
  simp only [CollatzResearch.WordTrace]
  refine ⟨244168583665966435932352163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162779055777310957288234775 244168583665966435932352163)
  ·
    refine ⟨366252875498949653898528245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244168583665966435932352163 366252875498949653898528245)
    ·
      refine ⟨34336207078026530052987023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 366252875498949653898528245 34336207078026530052987023)
      ·
        refine ⟨51504310617039795079480535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34336207078026530052987023 51504310617039795079480535)
        ·
          refine ⟨77256465925559692619220803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51504310617039795079480535 77256465925559692619220803)
          ·
            refine ⟨115884698888339538928831205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77256465925559692619220803 115884698888339538928831205)
            ·
              refine ⟨21728381041563663549155851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115884698888339538928831205 21728381041563663549155851)
              ·
                refine ⟨32592571562345495323733777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21728381041563663549155851 32592571562345495323733777)
                ·
                  refine ⟨24444428671759121492800333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32592571562345495323733777 24444428671759121492800333)
                  ·
                    refine ⟨9166660751909670559800125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24444428671759121492800333 9166660751909670559800125)
                    ·
                      refine ⟨3437497781966126459925047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9166660751909670559800125 3437497781966126459925047)
                      ·
                        rfl

theorem cell23_6694503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_6694503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694503 prefixEnd_6694503 := by exact prefixLift 6694503
  have htrace : WordTrace (prefixWord ++ tailWord_6694503) baseStart_6694503 baseEnd_6694503 := by
    simpa [prefixWord, tailWord_6694503, baseEnd_6694503] using wordTrace_append hprefix tailTrace_6694503
  have hstable : (prefixWord ++ tailWord_6694503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694503).length < 2 ^ (prefixWord ++ tailWord_6694503).sum := by decide
  have hdescent : baseEnd_6694503 < baseStart_6694503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694513 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 2, 5, 2]
def baseStart_6694513 : Nat := 118140960795 + 6694513 * 2 ^ 59
def prefixEnd_6694513 : Nat := 4983230072969 + 3 ^ 40 * 6694513 * 2
def baseEnd_6694513 : Nat := 3437502916772671420800001

theorem tailTrace_6694513 : CollatzResearch.WordTrace tailWord_6694513 prefixEnd_6694513 3437502916772671420800001 := by
  unfold tailWord_6694513
  simp only [CollatzResearch.WordTrace]
  refine ⟨244168948395930207640216193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162779298930620138426810795 244168948395930207640216193)
  ·
    refine ⟨183126711296947655730162145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244168948395930207640216193 183126711296947655730162145)
    ·
      refine ⟨137345033472710741797621609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183126711296947655730162145 137345033472710741797621609)
      ·
        refine ⟨103008775104533056348216207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137345033472710741797621609 103008775104533056348216207)
        ·
          refine ⟨154513162656799584522324311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103008775104533056348216207 154513162656799584522324311)
          ·
            refine ⟨231769743985199376783486467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154513162656799584522324311 231769743985199376783486467)
            ·
              refine ⟨347654615977799065175229701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231769743985199376783486467 347654615977799065175229701)
              ·
                refine ⟨65185240495837324720355569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 347654615977799065175229701 65185240495837324720355569)
                ·
                  refine ⟨48888930371877993540266677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65185240495837324720355569 48888930371877993540266677)
                  ·
                    refine ⟨4583337222363561894400001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48888930371877993540266677 4583337222363561894400001)
                    ·
                      refine ⟨3437502916772671420800001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4583337222363561894400001 3437502916772671420800001)
                      ·
                        rfl

theorem cell23_6694513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_6694513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694513 prefixEnd_6694513 := by exact prefixLift 6694513
  have htrace : WordTrace (prefixWord ++ tailWord_6694513) baseStart_6694513 baseEnd_6694513 := by
    simpa [prefixWord, tailWord_6694513, baseEnd_6694513] using wordTrace_append hprefix tailTrace_6694513
  have hstable : (prefixWord ++ tailWord_6694513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694513).length < 2 ^ (prefixWord ++ tailWord_6694513).sum := by decide
  have hdescent : baseEnd_6694513 < baseStart_6694513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694553 : List Nat := [1, 2, 1, 2, 1, 2, 2, 5, 3, 4]
def baseStart_6694553 : Nat := 118140960795 + 6694553 * 2 ^ 59
def prefixEnd_6694553 : Nat := 4983230072969 + 3 ^ 40 * 6694553 * 2
def baseEnd_6694553 : Nat := 1145841151999617088099939

theorem tailTrace_6694553 : CollatzResearch.WordTrace tailWord_6694553 prefixEnd_6694553 1145841151999617088099939 := by
  unfold tailWord_6694553
  simp only [CollatzResearch.WordTrace]
  refine ⟨244170407315785294471672313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162780271543856862981114875 244170407315785294471672313)
  ·
    refine ⟨183127805486838970853754235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244170407315785294471672313 183127805486838970853754235)
    ·
      refine ⟨274691708230258456280631353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183127805486838970853754235 274691708230258456280631353)
      ·
        refine ⟨206018781172693842210473515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274691708230258456280631353 206018781172693842210473515)
        ·
          refine ⟨309028171759040763315710273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206018781172693842210473515 309028171759040763315710273)
          ·
            refine ⟨231771128819280572486782705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309028171759040763315710273 231771128819280572486782705)
            ·
              refine ⟨173828346614460429365087029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231771128819280572486782705 173828346614460429365087029)
              ·
                refine ⟨16296407495105665252976909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173828346614460429365087029 16296407495105665252976909)
                ·
                  refine ⟨6111152810664624469866341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16296407495105665252976909 6111152810664624469866341)
                  ·
                    refine ⟨1145841151999617088099939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6111152810664624469866341 1145841151999617088099939)
                    ·
                      rfl

theorem cell23_6694553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 4].length) (baseStart_6694553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694553 prefixEnd_6694553 := by exact prefixLift 6694553
  have htrace : WordTrace (prefixWord ++ tailWord_6694553) baseStart_6694553 baseEnd_6694553 := by
    simpa [prefixWord, tailWord_6694553, baseEnd_6694553] using wordTrace_append hprefix tailTrace_6694553
  have hstable : (prefixWord ++ tailWord_6694553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694553).length < 2 ^ (prefixWord ++ tailWord_6694553).sum := by decide
  have hdescent : baseEnd_6694553 < baseStart_6694553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694563 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 3]
def baseStart_6694563 : Nat := 118140960795 + 6694563 * 2 ^ 59
def prefixEnd_6694563 : Nat := 4983230072969 + 3 ^ 40 * 6694563 * 2
def baseEnd_6694563 : Nat := 3437528590805396225174771

theorem tailTrace_6694563 : CollatzResearch.WordTrace tailWord_6694563 prefixEnd_6694563 3437528590805396225174771 := by
  unfold tailWord_6694563
  simp only [CollatzResearch.WordTrace]
  refine ⟨244170772045749066179536343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162780514697166044119690895 244170772045749066179536343)
  ·
    refine ⟨366256158068623599269304515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244170772045749066179536343 366256158068623599269304515)
    ·
      refine ⟨549384237102935398903956773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366256158068623599269304515 549384237102935398903956773)
      ·
        refine ⟨103009544456800387294491895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 549384237102935398903956773 103009544456800387294491895)
        ·
          refine ⟨154514316685200580941737843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103009544456800387294491895 154514316685200580941737843)
          ·
            refine ⟨231771475027800871412606765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154514316685200580941737843 231771475027800871412606765)
            ·
              refine ⟨86914303135425326779727537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231771475027800871412606765 86914303135425326779727537)
              ·
                refine ⟨65185727351568995084795653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86914303135425326779727537 65185727351568995084795653)
                ·
                  refine ⟨12222323878419186578399185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65185727351568995084795653 12222323878419186578399185)
                  ·
                    refine ⟨9166742908814389933799389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12222323878419186578399185 9166742908814389933799389)
                    ·
                      refine ⟨3437528590805396225174771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9166742908814389933799389 3437528590805396225174771)
                      ·
                        rfl

theorem cell23_6694563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_6694563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694563 prefixEnd_6694563 := by exact prefixLift 6694563
  have htrace : WordTrace (prefixWord ++ tailWord_6694563) baseStart_6694563 baseEnd_6694563 := by
    simpa [prefixWord, tailWord_6694563, baseEnd_6694563] using wordTrace_append hprefix tailTrace_6694563
  have hstable : (prefixWord ++ tailWord_6694563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694563).length < 2 ^ (prefixWord ++ tailWord_6694563).sum := by decide
  have hdescent : baseEnd_6694563 < baseStart_6694563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694604 : List Nat := [2, 2, 1, 5, 2, 1, 1, 4, 1, 4]
def baseStart_6694604 : Nat := 118140960795 + 6694604 * 2 ^ 59
def prefixEnd_6694604 : Nat := 4983230072969 + 3 ^ 40 * 6694604 * 2
def baseEnd_6694604 : Nat := 1145849881170743521587361

theorem tailTrace_6694604 : CollatzResearch.WordTrace tailWord_6694604 prefixEnd_6694604 1145849881170743521587361 := by
  unfold tailWord_6694604
  simp only [CollatzResearch.WordTrace]
  refine ⟨122086133719300265090889433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162781511625733686787852577 122086133719300265090889433)
  ·
    refine ⟨91564600289475198818167075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122086133719300265090889433 91564600289475198818167075)
    ·
      refine ⟨137346900434212798227250613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91564600289475198818167075 137346900434212798227250613)
      ·
        refine ⟨12876271915707449833804745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137346900434212798227250613 12876271915707449833804745)
        ·
          refine ⟨9657203936780587375353559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12876271915707449833804745 9657203936780587375353559)
          ·
            refine ⟨14485805905170881063030339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9657203936780587375353559 14485805905170881063030339)
            ·
              refine ⟨21728708857756321594545509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14485805905170881063030339 21728708857756321594545509)
              ·
                refine ⟨4074132910829310298977283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21728708857756321594545509 4074132910829310298977283)
                ·
                  refine ⟨6111199366243965448465925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4074132910829310298977283 6111199366243965448465925)
                  ·
                    refine ⟨1145849881170743521587361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6111199366243965448465925 1145849881170743521587361)
                    ·
                      rfl

theorem cell23_6694604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 1, 4].length) (baseStart_6694604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694604 prefixEnd_6694604 := by exact prefixLift 6694604
  have htrace : WordTrace (prefixWord ++ tailWord_6694604) baseStart_6694604 baseEnd_6694604 := by
    simpa [prefixWord, tailWord_6694604, baseEnd_6694604] using wordTrace_append hprefix tailTrace_6694604
  have hstable : (prefixWord ++ tailWord_6694604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694604).length < 2 ^ (prefixWord ++ tailWord_6694604).sum := by decide
  have hdescent : baseEnd_6694604 < baseStart_6694604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694631 : List Nat := [1, 1, 5, 4, 2, 1, 1, 1, 2, 2, 3]
def baseStart_6694631 : Nat := 118140960795 + 6694631 * 2 ^ 59
def prefixEnd_6694631 : Nat := 4983230072969 + 3 ^ 40 * 6694631 * 2
def baseEnd_6694631 : Nat := 3437563507489901959124459

theorem tailTrace_6694631 : CollatzResearch.WordTrace tailWord_6694631 prefixEnd_6694631 3437563507489901959124459 := by
  unfold tailWord_6694631
  simp only [CollatzResearch.WordTrace]
  refine ⟨244173252209502713793011747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162782168139668475862007831 244173252209502713793011747)
  ·
    refine ⟨366259878314254070689517621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244173252209502713793011747 366259878314254070689517621)
    ·
      refine ⟨34336863591961319127142277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 366259878314254070689517621 34336863591961319127142277)
      ·
        refine ⟨6438161923492747336339177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34336863591961319127142277 6438161923492747336339177)
        ·
          refine ⟨4828621442619560502254383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6438161923492747336339177 4828621442619560502254383)
          ·
            refine ⟨7242932163929340753381575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4828621442619560502254383 7242932163929340753381575)
            ·
              refine ⟨10864398245894011130072363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7242932163929340753381575 10864398245894011130072363)
              ·
                refine ⟨16296597368841016695108545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10864398245894011130072363 16296597368841016695108545)
                ·
                  refine ⟨12222448026630762521331409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16296597368841016695108545 12222448026630762521331409)
                  ·
                    refine ⟨9166836019973071890998557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12222448026630762521331409 9166836019973071890998557)
                    ·
                      refine ⟨3437563507489901959124459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9166836019973071890998557 3437563507489901959124459)
                      ·
                        rfl

theorem cell23_6694631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_6694631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694631 prefixEnd_6694631 := by exact prefixLift 6694631
  have htrace : WordTrace (prefixWord ++ tailWord_6694631) baseStart_6694631 baseEnd_6694631 := by
    simpa [prefixWord, tailWord_6694631, baseEnd_6694631] using wordTrace_append hprefix tailTrace_6694631
  have hstable : (prefixWord ++ tailWord_6694631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694631).length < 2 ^ (prefixWord ++ tailWord_6694631).sum := by decide
  have hdescent : baseEnd_6694631 < baseStart_6694631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694637 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 1, 5, 2]
def baseStart_6694637 : Nat := 118140960795 + 6694637 * 2 ^ 59
def prefixEnd_6694637 : Nat := 4983230072969 + 3 ^ 40 * 6694637 * 2
def baseEnd_6694637 : Nat := 3437566588373828935649431

theorem tailTrace_6694637 : CollatzResearch.WordTrace tailWord_6694637 prefixEnd_6694637 3437566588373828935649431 := by
  unfold tailWord_6694637
  simp only [CollatzResearch.WordTrace]
  refine ⟨244173471047480976817730165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162782314031653984545153443 244173471047480976817730165)
  ·
    refine ⟨22891262910701341576662203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244173471047480976817730165 22891262910701341576662203)
    ·
      refine ⟨34336894366052012364993305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22891262910701341576662203 34336894366052012364993305)
      ·
        refine ⟨25752670774539009273744979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34336894366052012364993305 25752670774539009273744979)
        ·
          refine ⟨38629006161808513910617469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25752670774539009273744979 38629006161808513910617469)
          ·
            refine ⟨14485877310678192716481551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38629006161808513910617469 14485877310678192716481551)
            ·
              refine ⟨21728815966017289074722327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14485877310678192716481551 21728815966017289074722327)
              ·
                refine ⟨32593223949025933612083491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21728815966017289074722327 32593223949025933612083491)
                ·
                  refine ⟨48889835923538900418125237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32593223949025933612083491 48889835923538900418125237)
                  ·
                    refine ⟨4583422117831771914199241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48889835923538900418125237 4583422117831771914199241)
                    ·
                      refine ⟨3437566588373828935649431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4583422117831771914199241 3437566588373828935649431)
                      ·
                        rfl

theorem cell23_6694637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_6694637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694637 prefixEnd_6694637 := by exact prefixLift 6694637
  have htrace : WordTrace (prefixWord ++ tailWord_6694637) baseStart_6694637 baseEnd_6694637 := by
    simpa [prefixWord, tailWord_6694637, baseEnd_6694637] using wordTrace_append hprefix tailTrace_6694637
  have hstable : (prefixWord ++ tailWord_6694637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694637).length < 2 ^ (prefixWord ++ tailWord_6694637).sum := by decide
  have hdescent : baseEnd_6694637 < baseStart_6694637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694643 : List Nat := [1, 1, 1, 2, 2, 3, 4, 2, 1, 6]
def baseStart_6694643 : Nat := 118140960795 + 6694643 * 2 ^ 59
def prefixEnd_6694643 : Nat := 4983230072969 + 3 ^ 40 * 6694643 * 2
def baseEnd_6694643 : Nat := 1145856556419251970724801

theorem tailTrace_6694643 : CollatzResearch.WordTrace tailWord_6694643 prefixEnd_6694643 1145856556419251970724801 := by
  unfold tailWord_6694643
  simp only [CollatzResearch.WordTrace]
  refine ⟨244173689885459239842448583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162782459923639493228299055 244173689885459239842448583)
  ·
    refine ⟨366260534828188859763672875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244173689885459239842448583 366260534828188859763672875)
    ·
      refine ⟨549390802242283289645509313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366260534828188859763672875 549390802242283289645509313)
      ·
        refine ⟨412043101681712467234131985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 549390802242283289645509313 412043101681712467234131985)
        ·
          refine ⟨309032326261284350425598989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412043101681712467234131985 309032326261284350425598989)
          ·
            refine ⟨115887122347981631409599621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309032326261284350425598989 115887122347981631409599621)
            ·
              refine ⟨21728835440246555889299929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115887122347981631409599621 21728835440246555889299929)
              ·
                refine ⟨16296626580184916916974947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21728835440246555889299929 16296626580184916916974947)
                ·
                  refine ⟨24444939870277375375462421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16296626580184916916974947 24444939870277375375462421)
                  ·
                    refine ⟨1145856556419251970724801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24444939870277375375462421 1145856556419251970724801)
                    ·
                      rfl

theorem cell23_6694643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 6].length) (baseStart_6694643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694643 prefixEnd_6694643 := by exact prefixLift 6694643
  have htrace : WordTrace (prefixWord ++ tailWord_6694643) baseStart_6694643 baseEnd_6694643 := by
    simpa [prefixWord, tailWord_6694643, baseEnd_6694643] using wordTrace_append hprefix tailTrace_6694643
  have hstable : (prefixWord ++ tailWord_6694643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694643).length < 2 ^ (prefixWord ++ tailWord_6694643).sum := by decide
  have hdescent : baseEnd_6694643 < baseStart_6694643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694667 : List Nat := [1, 1, 1, 1, 5, 1, 3, 3, 3, 2, 2]
def baseStart_6694667 : Nat := 118140960795 + 6694667 * 2 ^ 59
def prefixEnd_6694667 : Nat := 4983230072969 + 3 ^ 40 * 6694667 * 2
def baseEnd_6694667 : Nat := 3437581992793463818274293

theorem tailTrace_6694667 : CollatzResearch.WordTrace tailWord_6694667 prefixEnd_6694667 3437581992793463818274293 := by
  unfold tailWord_6694667
  simp only [CollatzResearch.WordTrace]
  refine ⟨244174565237372291941322255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162783043491581527960881503 244174565237372291941322255)
  ·
    refine ⟨366261847856058437911983383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244174565237372291941322255 366261847856058437911983383)
    ·
      refine ⟨549392771784087656867975075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366261847856058437911983383 549392771784087656867975075)
      ·
        refine ⟨824089157676131485301962613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549392771784087656867975075 824089157676131485301962613)
        ·
          refine ⟨77258358532137326747058995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 824089157676131485301962613 77258358532137326747058995)
          ·
            refine ⟨115887537798205990120588493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77258358532137326747058995 115887537798205990120588493)
            ·
              refine ⟨43457826674327246295220685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115887537798205990120588493 43457826674327246295220685)
              ·
                refine ⟨16296685002872717360707757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43457826674327246295220685 16296685002872717360707757)
                ·
                  refine ⟨6111256876077269010265409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16296685002872717360707757 6111256876077269010265409)
                  ·
                    refine ⟨4583442657057951757699057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6111256876077269010265409 4583442657057951757699057)
                    ·
                      refine ⟨3437581992793463818274293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4583442657057951757699057 3437581992793463818274293)
                      ·
                        rfl

theorem cell23_6694667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 2, 2].length) (baseStart_6694667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694667 prefixEnd_6694667 := by exact prefixLift 6694667
  have htrace : WordTrace (prefixWord ++ tailWord_6694667) baseStart_6694667 baseEnd_6694667 := by
    simpa [prefixWord, tailWord_6694667, baseEnd_6694667] using wordTrace_append hprefix tailTrace_6694667
  have hstable : (prefixWord ++ tailWord_6694667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694667).length < 2 ^ (prefixWord ++ tailWord_6694667).sum := by decide
  have hdescent : baseEnd_6694667 < baseStart_6694667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694670 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3]
def baseStart_6694670 : Nat := 118140960795 + 6694670 * 2 ^ 59
def prefixEnd_6694670 : Nat := 4983230072969 + 3 ^ 40 * 6694670 * 2
def baseEnd_6694670 : Nat := 3437583533235427306536779

theorem tailTrace_6694670 : CollatzResearch.WordTrace tailWord_6694670 prefixEnd_6694670 3437583533235427306536779 := by
  unfold tailWord_6694670
  simp only [CollatzResearch.WordTrace]
  refine ⟨30521834332045177931710183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162783116437574282302454309 30521834332045177931710183)
  ·
    refine ⟨45782751498067766897565275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30521834332045177931710183 45782751498067766897565275)
    ·
      refine ⟨68674127247101650346347913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45782751498067766897565275 68674127247101650346347913)
      ·
        refine ⟨51505595435326237759760935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68674127247101650346347913 51505595435326237759760935)
        ·
          refine ⟨77258393152989356639641403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51505595435326237759760935 77258393152989356639641403)
          ·
            refine ⟨115887589729484034959462105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77258393152989356639641403 115887589729484034959462105)
            ·
              refine ⟨86915692297113026219596579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115887589729484034959462105 86915692297113026219596579)
              ·
                refine ⟨130373538445669539329394869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86915692297113026219596579 130373538445669539329394869)
                ·
                  refine ⟨12222519229281519312130769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130373538445669539329394869 12222519229281519312130769)
                  ·
                    refine ⟨9166889421961139484098077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12222519229281519312130769 9166889421961139484098077)
                    ·
                      refine ⟨3437583533235427306536779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9166889421961139484098077 3437583533235427306536779)
                      ·
                        rfl

theorem cell23_6694670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_6694670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694670 prefixEnd_6694670 := by exact prefixLift 6694670
  have htrace : WordTrace (prefixWord ++ tailWord_6694670) baseStart_6694670 baseEnd_6694670 := by
    simpa [prefixWord, tailWord_6694670, baseEnd_6694670] using wordTrace_append hprefix tailTrace_6694670
  have hstable : (prefixWord ++ tailWord_6694670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694670).length < 2 ^ (prefixWord ++ tailWord_6694670).sum := by decide
  have hdescent : baseEnd_6694670 < baseStart_6694670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694680 : List Nat := [2, 1, 2, 3, 1, 1, 5, 1, 1, 2, 4]
def baseStart_6694680 : Nat := 118140960795 + 6694680 * 2 ^ 59
def prefixEnd_6694680 : Nat := 4983230072969 + 3 ^ 40 * 6694680 * 2
def baseEnd_6694680 : Nat := 3437588668041972267411733

theorem tailTrace_6694680 : CollatzResearch.WordTrace tailWord_6694680 prefixEnd_6694680 3437588668041972267411733 := by
  unfold tailWord_6694680
  simp only [CollatzResearch.WordTrace]
  refine ⟨122087519693162597580772747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162783359590883463441030329 122087519693162597580772747)
  ·
    refine ⟨183131279539743896371159121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122087519693162597580772747 183131279539743896371159121)
    ·
      refine ⟨137348459654807922278369341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183131279539743896371159121 137348459654807922278369341)
      ·
        refine ⟨51505672370552970854388503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137348459654807922278369341 51505672370552970854388503)
        ·
          refine ⟨77258508555829456281582755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51505672370552970854388503 77258508555829456281582755)
          ·
            refine ⟨115887762833744184422374133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77258508555829456281582755 115887762833744184422374133)
            ·
              refine ⟨10864477765663517289597575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115887762833744184422374133 10864477765663517289597575)
              ·
                refine ⟨16296716648495275934396363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10864477765663517289597575 16296716648495275934396363)
                ·
                  refine ⟨24445074972742913901594545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16296716648495275934396363 24445074972742913901594545)
                  ·
                    refine ⟨18333806229557185426195909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24445074972742913901594545 18333806229557185426195909)
                    ·
                      refine ⟨3437588668041972267411733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18333806229557185426195909 3437588668041972267411733)
                      ·
                        rfl

theorem cell23_6694680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_6694680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694680 prefixEnd_6694680 := by exact prefixLift 6694680
  have htrace : WordTrace (prefixWord ++ tailWord_6694680) baseStart_6694680 baseEnd_6694680 := by
    simpa [prefixWord, tailWord_6694680, baseEnd_6694680] using wordTrace_append hprefix tailTrace_6694680
  have hstable : (prefixWord ++ tailWord_6694680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694680).length < 2 ^ (prefixWord ++ tailWord_6694680).sum := by decide
  have hdescent : baseEnd_6694680 < baseStart_6694680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694687 : List Nat := [1, 1, 2, 4, 2, 1, 4, 2, 1, 2, 3]
def baseStart_6694687 : Nat := 118140960795 + 6694687 * 2 ^ 59
def prefixEnd_6694687 : Nat := 4983230072969 + 3 ^ 40 * 6694687 * 2
def baseEnd_6694687 : Nat := 3437592262406553740024201

theorem tailTrace_6694687 : CollatzResearch.WordTrace tailWord_6694687 prefixEnd_6694687 3437592262406553740024201 := by
  unfold tailWord_6694687
  simp only [CollatzResearch.WordTrace]
  refine ⟨244175294697299835357050315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162783529798199890238033543 244175294697299835357050315)
  ·
    refine ⟨366262942045949753035575473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244175294697299835357050315 366262942045949753035575473)
    ·
      refine ⟨274697206534462314776681605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366262942045949753035575473 274697206534462314776681605)
      ·
        refine ⟨51505726225211684020627801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274697206534462314776681605 51505726225211684020627801)
        ·
          refine ⟨38629294668908763015470851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51505726225211684020627801 38629294668908763015470851)
          ·
            refine ⟨57943942003363144523206277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38629294668908763015470851 57943942003363144523206277)
            ·
              refine ⟨10864489125630589598101177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57943942003363144523206277 10864489125630589598101177)
              ·
                refine ⟨8148366844222942198575883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10864489125630589598101177 8148366844222942198575883)
                ·
                  refine ⟨12222550266334413297863825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8148366844222942198575883 12222550266334413297863825)
                  ·
                    refine ⟨9166912699750809973397869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12222550266334413297863825 9166912699750809973397869)
                    ·
                      refine ⟨3437592262406553740024201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9166912699750809973397869 3437592262406553740024201)
                      ·
                        rfl

theorem cell23_6694687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_6694687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694687 prefixEnd_6694687 := by exact prefixLift 6694687
  have htrace : WordTrace (prefixWord ++ tailWord_6694687) baseStart_6694687 baseEnd_6694687 := by
    simpa [prefixWord, tailWord_6694687, baseEnd_6694687] using wordTrace_append hprefix tailTrace_6694687
  have hstable : (prefixWord ++ tailWord_6694687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694687).length < 2 ^ (prefixWord ++ tailWord_6694687).sum := by decide
  have hdescent : baseEnd_6694687 < baseStart_6694687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694760 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_6694760 : Nat := 118140960795 + 6694760 * 2 ^ 59
def prefixEnd_6694760 : Nat := 4983230072969 + 3 ^ 40 * 6694760 * 2
def baseEnd_6694760 : Nat := 3437629746494331954411365

theorem tailTrace_6694760 : CollatzResearch.WordTrace tailWord_6694760 prefixEnd_6694760 3437629746494331954411365 := by
  unfold tailWord_6694760
  simp only [CollatzResearch.WordTrace]
  refine ⟨122088978613017684412228867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162785304817356912549638489 122088978613017684412228867)
  ·
    refine ⟨183133467919526526618343301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122088978613017684412228867 183133467919526526618343301)
    ·
      refine ⟨34337525234911223740939369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183133467919526526618343301 34337525234911223740939369)
      ·
        refine ⟨25753143926183417805704527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34337525234911223740939369 25753143926183417805704527)
        ·
          refine ⟨38629715889275126708556791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25753143926183417805704527 38629715889275126708556791)
          ·
            refine ⟨57944573833912690062835187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38629715889275126708556791 57944573833912690062835187)
            ·
              refine ⟨86916860750869035094252781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57944573833912690062835187 86916860750869035094252781)
              ·
                refine ⟨32593822781575888160344793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86916860750869035094252781 32593822781575888160344793)
                ·
                  refine ⟨24445367086181916120258595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32593822781575888160344793 24445367086181916120258595)
                  ·
                    refine ⟨36668050629272874180387893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24445367086181916120258595 36668050629272874180387893)
                    ·
                      refine ⟨3437629746494331954411365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36668050629272874180387893 3437629746494331954411365)
                      ·
                        rfl

theorem cell23_6694760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_6694760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694760 prefixEnd_6694760 := by exact prefixLift 6694760
  have htrace : WordTrace (prefixWord ++ tailWord_6694760) baseStart_6694760 baseEnd_6694760 := by
    simpa [prefixWord, tailWord_6694760, baseEnd_6694760] using wordTrace_append hprefix tailTrace_6694760
  have hstable : (prefixWord ++ tailWord_6694760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694760).length < 2 ^ (prefixWord ++ tailWord_6694760).sum := by decide
  have hdescent : baseEnd_6694760 < baseStart_6694760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694770 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_6694770 : Nat := 118140960795 + 6694770 * 2 ^ 59
def prefixEnd_6694770 : Nat := 4983230072969 + 3 ^ 40 * 6694770 * 2
def baseEnd_6694770 : Nat := 3437634881300876915286319

theorem tailTrace_6694770 : CollatzResearch.WordTrace tailWord_6694770 prefixEnd_6694770 3437634881300876915286319 := by
  unfold tailWord_6694770
  simp only [CollatzResearch.WordTrace]
  refine ⟨61044580488999785133080441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162785547970666093688214509 61044580488999785133080441)
  ·
    refine ⟨45783435366749838849810331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61044580488999785133080441 45783435366749838849810331)
    ·
      refine ⟨68675153050124758274715497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45783435366749838849810331 68675153050124758274715497)
      ·
        refine ⟨51506364787593568706036623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68675153050124758274715497 51506364787593568706036623)
        ·
          refine ⟨77259547181390353059054935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51506364787593568706036623 77259547181390353059054935)
          ·
            refine ⟨115889320772085529588582403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77259547181390353059054935 115889320772085529588582403)
            ·
              refine ⟨173833981158128294382873605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115889320772085529588582403 173833981158128294382873605)
              ·
                refine ⟨32593871467149055196788801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173833981158128294382873605 32593871467149055196788801)
                ·
                  refine ⟨24445403600361791397591601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32593871467149055196788801 24445403600361791397591601)
                  ·
                    refine ⟨18334052700271343548193701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24445403600361791397591601 18334052700271343548193701)
                    ·
                      refine ⟨3437634881300876915286319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18334052700271343548193701 3437634881300876915286319)
                      ·
                        rfl

theorem cell23_6694770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_6694770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694770 prefixEnd_6694770 := by exact prefixLift 6694770
  have htrace : WordTrace (prefixWord ++ tailWord_6694770) baseStart_6694770 baseEnd_6694770 := by
    simpa [prefixWord, tailWord_6694770, baseEnd_6694770] using wordTrace_append hprefix tailTrace_6694770
  have hstable : (prefixWord ++ tailWord_6694770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694770).length < 2 ^ (prefixWord ++ tailWord_6694770).sum := by decide
  have hdescent : baseEnd_6694770 < baseStart_6694770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694783 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 8]
def baseStart_6694783 : Nat := 118140960795 + 6694783 * 2 ^ 59
def prefixEnd_6694783 : Nat := 4983230072969 + 3 ^ 40 * 6694783 * 2
def baseEnd_6694783 : Nat := 3437641556549385364423759

theorem tailTrace_6694783 : CollatzResearch.WordTrace tailWord_6694783 prefixEnd_6694783 3437641556549385364423759 := by
  unfold tailWord_6694783
  simp only [CollatzResearch.WordTrace]
  refine ⟨244178796104952043752545003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162785864069968029168363335 244178796104952043752545003)
  ·
    refine ⟨366268194157428065628817505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244178796104952043752545003 366268194157428065628817505)
    ·
      refine ⟨274701145618071049221613129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366268194157428065628817505 274701145618071049221613129)
      ·
        refine ⟨206025859213553286916209847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274701145618071049221613129 206025859213553286916209847)
        ·
          refine ⟨309038788820329930374314771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206025859213553286916209847 309038788820329930374314771)
          ·
            refine ⟨463558183230494895561472157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309038788820329930374314771 463558183230494895561472157)
            ·
              refine ⟨173834318711435585835552059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 463558183230494895561472157 173834318711435585835552059)
              ·
                refine ⟨260751478067153378753328089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173834318711435585835552059 260751478067153378753328089)
                ·
                  refine ⟨195563608550365034064996067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260751478067153378753328089 195563608550365034064996067)
                  ·
                    refine ⟨293345412825547551097494101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 195563608550365034064996067 293345412825547551097494101)
                    ·
                      refine ⟨3437641556549385364423759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 293345412825547551097494101 3437641556549385364423759)
                      ·
                        rfl

theorem cell23_6694783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_6694783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694783 prefixEnd_6694783 := by exact prefixLift 6694783
  have htrace : WordTrace (prefixWord ++ tailWord_6694783) baseStart_6694783 baseEnd_6694783 := by
    simpa [prefixWord, tailWord_6694783, baseEnd_6694783] using wordTrace_append hprefix tailTrace_6694783
  have hstable : (prefixWord ++ tailWord_6694783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694783).length < 2 ^ (prefixWord ++ tailWord_6694783).sum := by decide
  have hdescent : baseEnd_6694783 < baseStart_6694783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694847 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 2, 4, 2]
def baseStart_6694847 : Nat := 118140960795 + 6694847 * 2 ^ 59
def prefixEnd_6694847 : Nat := 4983230072969 + 3 ^ 40 * 6694847 * 2
def baseEnd_6694847 : Nat := 3437674419311273114023465

theorem tailTrace_6694847 : CollatzResearch.WordTrace tailWord_6694847 prefixEnd_6694847 3437674419311273114023465 := by
  unfold tailWord_6694847
  simp only [CollatzResearch.WordTrace]
  refine ⟨244181130376720182682874795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162787420251146788455249863 244181130376720182682874795)
  ·
    refine ⟨366271695565080274024312193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244181130376720182682874795 366271695565080274024312193)
    ·
      refine ⟨274703771673810205518234145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366271695565080274024312193 274703771673810205518234145)
      ·
        refine ⟨206027828755357654138675609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274703771673810205518234145 206027828755357654138675609)
        ·
          refine ⟨154520871566518240604006707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206027828755357654138675609 154520871566518240604006707)
          ·
            refine ⟨231781307349777360906010061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154520871566518240604006707 231781307349777360906010061)
            ·
              refine ⟨86917990256166510339753773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231781307349777360906010061 86917990256166510339753773)
              ·
                refine ⟨32594246346062441377407665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86917990256166510339753773 32594246346062441377407665)
                ·
                  refine ⟨24445684759546831033055749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32594246346062441377407665 24445684759546831033055749)
                  ·
                    refine ⟨4583565892415030818697953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24445684759546831033055749 4583565892415030818697953)
                    ·
                      refine ⟨3437674419311273114023465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4583565892415030818697953 3437674419311273114023465)
                      ·
                        rfl

theorem cell23_6694847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 4, 2].length) (baseStart_6694847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694847 prefixEnd_6694847 := by exact prefixLift 6694847
  have htrace : WordTrace (prefixWord ++ tailWord_6694847) baseStart_6694847 baseEnd_6694847 := by
    simpa [prefixWord, tailWord_6694847, baseEnd_6694847] using wordTrace_append hprefix tailTrace_6694847
  have hstable : (prefixWord ++ tailWord_6694847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694847).length < 2 ^ (prefixWord ++ tailWord_6694847).sum := by decide
  have hdescent : baseEnd_6694847 < baseStart_6694847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694907 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 3, 5, 2]
def baseStart_6694907 : Nat := 118140960795 + 6694907 * 2 ^ 59
def prefixEnd_6694907 : Nat := 4983230072969 + 3 ^ 40 * 6694907 * 2
def baseEnd_6694907 : Nat := 3437705228150542879273189

theorem tailTrace_6694907 : CollatzResearch.WordTrace tailWord_6694907 prefixEnd_6694907 3437705228150542879273189 := by
  unfold tailWord_6694907
  simp only [CollatzResearch.WordTrace]
  refine ⟨244183318756502812930058975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162788879171001875286705983 244183318756502812930058975)
  ·
    refine ⟨366274978134754219395088463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244183318756502812930058975 366274978134754219395088463)
    ·
      refine ⟨549412467202131329092632695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366274978134754219395088463 549412467202131329092632695)
      ·
        refine ⟨824118700803196993638949043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549412467202131329092632695 824118700803196993638949043)
        ·
          refine ⟨1236178051204795490458423565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824118700803196993638949043 1236178051204795490458423565)
          ·
            refine ⟨463566769201798308921908837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1236178051204795490458423565 463566769201798308921908837)
            ·
              refine ⟨86918769225337182922857907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 463566769201798308921908837 86918769225337182922857907)
              ·
                refine ⟨130378153838005774384286861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86918769225337182922857907 130378153838005774384286861)
                ·
                  refine ⟨48891807689252165394107573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130378153838005774384286861 48891807689252165394107573)
                  ·
                    refine ⟨4583606970867390505697585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48891807689252165394107573 4583606970867390505697585)
                    ·
                      refine ⟨3437705228150542879273189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4583606970867390505697585 3437705228150542879273189)
                      ·
                        rfl

theorem cell23_6694907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 5, 2].length) (baseStart_6694907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694907 prefixEnd_6694907 := by exact prefixLift 6694907
  have htrace : WordTrace (prefixWord ++ tailWord_6694907) baseStart_6694907 baseEnd_6694907 := by
    simpa [prefixWord, tailWord_6694907, baseEnd_6694907] using wordTrace_append hprefix tailTrace_6694907
  have hstable : (prefixWord ++ tailWord_6694907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694907).length < 2 ^ (prefixWord ++ tailWord_6694907).sum := by decide
  have hdescent : baseEnd_6694907 < baseStart_6694907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694917 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 3, 5]
def baseStart_6694917 : Nat := 118140960795 + 6694917 * 2 ^ 59
def prefixEnd_6694917 : Nat := 4983230072969 + 3 ^ 40 * 6694917 * 2
def baseEnd_6694917 : Nat := 1145903454319029280049381

theorem tailTrace_6694917 : CollatzResearch.WordTrace tailWord_6694917 prefixEnd_6694917 1145903454319029280049381 := by
  unfold tailWord_6694917
  simp only [CollatzResearch.WordTrace]
  refine ⟨244183683486466584637923005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162789122324311056425282003 244183683486466584637923005)
  ·
    refine ⟨91568881307424969239221127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244183683486466584637923005 91568881307424969239221127)
    ·
      refine ⟨137353321961137453858831691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91568881307424969239221127 137353321961137453858831691)
      ·
        refine ⟨206029982941706180788247537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137353321961137453858831691 206029982941706180788247537)
        ·
          refine ⟨154522487206279635591185653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206029982941706180788247537 154522487206279635591185653)
          ·
            refine ⟨14486483175588715836673655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154522487206279635591185653 14486483175588715836673655)
            ·
              refine ⟨21729724763383073755010483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14486483175588715836673655 21729724763383073755010483)
              ·
                refine ⟨32594587145074610632515725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21729724763383073755010483 32594587145074610632515725)
                ·
                  refine ⟨12222970179402978987193397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32594587145074610632515725 12222970179402978987193397)
                  ·
                    refine ⟨1145903454319029280049381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12222970179402978987193397 1145903454319029280049381)
                    ·
                      rfl

theorem cell23_6694917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_6694917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694917 prefixEnd_6694917 := by exact prefixLift 6694917
  have htrace : WordTrace (prefixWord ++ tailWord_6694917) baseStart_6694917 baseEnd_6694917 := by
    simpa [prefixWord, tailWord_6694917, baseEnd_6694917] using wordTrace_append hprefix tailTrace_6694917
  have hstable : (prefixWord ++ tailWord_6694917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694917).length < 2 ^ (prefixWord ++ tailWord_6694917).sum := by decide
  have hdescent : baseEnd_6694917 < baseStart_6694917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694941 : List Nat := [1, 4, 2, 2, 2, 1, 2, 2, 2, 3, 2]
def baseStart_6694941 : Nat := 118140960795 + 6694941 * 2 ^ 59
def prefixEnd_6694941 : Nat := 4983230072969 + 3 ^ 40 * 6694941 * 2
def baseEnd_6694941 : Nat := 3437722686492795746248033

theorem tailTrace_6694941 : CollatzResearch.WordTrace tailWord_6694941 prefixEnd_6694941 3437722686492795746248033 := by
  unfold tailWord_6694941
  simp only [CollatzResearch.WordTrace]
  refine ⟨244184558838379636736796677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162789705892253091157864451 244184558838379636736796677)
  ·
    refine ⟨45784604782196181888149377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244184558838379636736796677 45784604782196181888149377)
    ·
      refine ⟨34338453586647136416112033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45784604782196181888149377 34338453586647136416112033)
      ·
        refine ⟨25753840189985352312084025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34338453586647136416112033 25753840189985352312084025)
        ·
          refine ⟨19315380142489014234063019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25753840189985352312084025 19315380142489014234063019)
          ·
            refine ⟨28973070213733521351094529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19315380142489014234063019 28973070213733521351094529)
            ·
              refine ⟨21729802660300141013320897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28973070213733521351094529 21729802660300141013320897)
              ·
                refine ⟨16297351995225105759990673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21729802660300141013320897 16297351995225105759990673)
                ·
                  refine ⟨12223013996418829319993005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16297351995225105759990673 12223013996418829319993005)
                  ·
                    refine ⟨4583630248657060994997377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12223013996418829319993005 4583630248657060994997377)
                    ·
                      refine ⟨3437722686492795746248033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4583630248657060994997377 3437722686492795746248033)
                      ·
                        rfl

theorem cell23_6694941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_6694941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694941 prefixEnd_6694941 := by exact prefixLift 6694941
  have htrace : WordTrace (prefixWord ++ tailWord_6694941) baseStart_6694941 baseEnd_6694941 := by
    simpa [prefixWord, tailWord_6694941, baseEnd_6694941] using wordTrace_append hprefix tailTrace_6694941
  have hstable : (prefixWord ++ tailWord_6694941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694941).length < 2 ^ (prefixWord ++ tailWord_6694941).sum := by decide
  have hdescent : baseEnd_6694941 < baseStart_6694941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694954 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_6694954 : Nat := 118140960795 + 6694954 * 2 ^ 59
def prefixEnd_6694954 : Nat := 4983230072969 + 3 ^ 40 * 6694954 * 2
def baseEnd_6694954 : Nat := 3437729361741304195385473

theorem tailTrace_6694954 : CollatzResearch.WordTrace tailWord_6694954 prefixEnd_6694954 3437729361741304195385473 := by
  unfold tailWord_6694954
  simp only [CollatzResearch.WordTrace]
  refine ⟨61046258246833134989254979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162790021991555026638013277 61046258246833134989254979)
  ·
    refine ⟨91569387370249702483882469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61046258246833134989254979 91569387370249702483882469)
    ·
      refine ⟨17169260131921819215727963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91569387370249702483882469 17169260131921819215727963)
      ·
        refine ⟨25753890197882728823591945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17169260131921819215727963 25753890197882728823591945)
        ·
          refine ⟨19315417648412046617693959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25753890197882728823591945 19315417648412046617693959)
          ·
            refine ⟨28973126472618069926540939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19315417648412046617693959 28973126472618069926540939)
            ·
              refine ⟨43459689708927104889811409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28973126472618069926540939 43459689708927104889811409)
              ·
                refine ⟨32594767281695328667358557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43459689708927104889811409 32594767281695328667358557)
                ·
                  refine ⟨12223037730635748250259459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32594767281695328667358557 12223037730635748250259459)
                  ·
                    refine ⟨18334556595953622375389189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12223037730635748250259459 18334556595953622375389189)
                    ·
                      refine ⟨3437729361741304195385473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18334556595953622375389189 3437729361741304195385473)
                      ·
                        rfl

theorem cell23_6694954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_6694954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694954 prefixEnd_6694954 := by exact prefixLift 6694954
  have htrace : WordTrace (prefixWord ++ tailWord_6694954) baseStart_6694954 baseEnd_6694954 := by
    simpa [prefixWord, tailWord_6694954, baseEnd_6694954] using wordTrace_append hprefix tailTrace_6694954
  have hstable : (prefixWord ++ tailWord_6694954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694954).length < 2 ^ (prefixWord ++ tailWord_6694954).sum := by decide
  have hdescent : baseEnd_6694954 < baseStart_6694954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694967 : List Nat := [1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 4]
def baseStart_6694967 : Nat := 118140960795 + 6694967 * 2 ^ 59
def prefixEnd_6694967 : Nat := 4983230072969 + 3 ^ 40 * 6694967 * 2
def baseEnd_6694967 : Nat := 3437736036989812644522913

theorem tailTrace_6694967 : CollatzResearch.WordTrace tailWord_6694967 prefixEnd_6694967 3437736036989812644522913 := by
  unfold tailWord_6694967
  simp only [CollatzResearch.WordTrace]
  refine ⟨244185507136285443177243155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162790338090856962118162103 244185507136285443177243155)
  ·
    refine ⟨366278260704428164765864733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244185507136285443177243155 366278260704428164765864733)
    ·
      refine ⟨137354347764160561787199275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366278260704428164765864733 137354347764160561787199275)
      ·
        refine ⟨206031521646240842680798913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137354347764160561787199275 206031521646240842680798913)
        ·
          refine ⟨154523641234680632010599185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206031521646240842680798913 154523641234680632010599185)
          ·
            refine ⟨115892730926010474007949389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154523641234680632010599185 115892730926010474007949389)
            ·
              refine ⟨43459774097253927752981021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115892730926010474007949389 43459774097253927752981021)
              ·
                refine ⟨16297415286470222907367883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43459774097253927752981021 16297415286470222907367883)
                ·
                  refine ⟨24446122929705334361051825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16297415286470222907367883 24446122929705334361051825)
                  ·
                    refine ⟨18334592197279000770788869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24446122929705334361051825 18334592197279000770788869)
                    ·
                      refine ⟨3437736036989812644522913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18334592197279000770788869 3437736036989812644522913)
                      ·
                        rfl

theorem cell23_6694967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_6694967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694967 prefixEnd_6694967 := by exact prefixLift 6694967
  have htrace : WordTrace (prefixWord ++ tailWord_6694967) baseStart_6694967 baseEnd_6694967 := by
    simpa [prefixWord, tailWord_6694967, baseEnd_6694967] using wordTrace_append hprefix tailTrace_6694967
  have hstable : (prefixWord ++ tailWord_6694967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694967).length < 2 ^ (prefixWord ++ tailWord_6694967).sum := by decide
  have hdescent : baseEnd_6694967 < baseStart_6694967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694988 : List Nat := [2, 2, 1, 3, 1, 1, 3, 5, 1, 2, 2]
def baseStart_6694988 : Nat := 118140960795 + 6694988 * 2 ^ 59
def prefixEnd_6694988 : Nat := 4983230072969 + 3 ^ 40 * 6694988 * 2
def baseEnd_6694988 : Nat := 3437746820083557062360317

theorem tailTrace_6694988 : CollatzResearch.WordTrace tailWord_6694988 prefixEnd_6694988 3437746820083557062360317 := by
  unfold tailWord_6694988
  simp only [CollatzResearch.WordTrace]
  refine ⟨122093136534604681881878809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162790848712806242509171745 122093136534604681881878809)
  ·
    refine ⟨91569852400953511411409107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122093136534604681881878809 91569852400953511411409107)
    ·
      refine ⟨137354778601430267117113661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91569852400953511411409107 137354778601430267117113661)
      ·
        refine ⟨51508041975536350168917623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137354778601430267117113661 51508041975536350168917623)
        ·
          refine ⟨77262062963304525253376435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51508041975536350168917623 77262062963304525253376435)
          ·
            refine ⟨115893094444956787880064653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77262062963304525253376435 115893094444956787880064653)
            ·
              refine ⟨43459910416858795455024245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115893094444956787880064653 43459910416858795455024245)
              ·
                refine ⟨4074366601580512073908523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43459910416858795455024245 4074366601580512073908523)
                ·
                  refine ⟨6111549902370768110862785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4074366601580512073908523 6111549902370768110862785)
                  ·
                    refine ⟨4583662426778076083147089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6111549902370768110862785 4583662426778076083147089)
                    ·
                      refine ⟨3437746820083557062360317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4583662426778076083147089 3437746820083557062360317)
                      ·
                        rfl

theorem cell23_6694988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_6694988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694988 prefixEnd_6694988 := by exact prefixLift 6694988
  have htrace : WordTrace (prefixWord ++ tailWord_6694988) baseStart_6694988 baseEnd_6694988 := by
    simpa [prefixWord, tailWord_6694988, baseEnd_6694988] using wordTrace_append hprefix tailTrace_6694988
  have hstable : (prefixWord ++ tailWord_6694988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694988).length < 2 ^ (prefixWord ++ tailWord_6694988).sum := by decide
  have hdescent : baseEnd_6694988 < baseStart_6694988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6694998 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_6694998 : Nat := 118140960795 + 6694998 * 2 ^ 59
def prefixEnd_6694998 : Nat := 4983230072969 + 3 ^ 40 * 6694998 * 2
def baseEnd_6694998 : Nat := 1145917318296700674411757

theorem tailTrace_6694998 : CollatzResearch.WordTrace tailWord_6694998 prefixEnd_6694998 1145917318296700674411757 := by
  unfold tailWord_6694998
  simp only [CollatzResearch.WordTrace]
  refine ⟨15261664862448320966976353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162791091866115423647747765 15261664862448320966976353)
  ·
    refine ⟨11446248646836240725232265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15261664862448320966976353 11446248646836240725232265)
    ·
      refine ⟨8584686485127180543924199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11446248646836240725232265 8584686485127180543924199)
      ·
        refine ⟨12877029727690770815886299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8584686485127180543924199 12877029727690770815886299)
        ·
          refine ⟨19315544591536156223829449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12877029727690770815886299 19315544591536156223829449)
          ·
            refine ⟨14486658443652117167872087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19315544591536156223829449 14486658443652117167872087)
            ·
              refine ⟨21729987665478175751808131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14486658443652117167872087 21729987665478175751808131)
              ·
                refine ⟨32594981498217263627712197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21729987665478175751808131 32594981498217263627712197)
                ·
                  refine ⟨6111559030915736930196037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32594981498217263627712197 6111559030915736930196037)
                  ·
                    refine ⟨1145917318296700674411757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6111559030915736930196037 1145917318296700674411757)
                    ·
                      rfl

theorem cell23_6694998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_6694998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6694998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6694998 prefixEnd_6694998 := by exact prefixLift 6694998
  have htrace : WordTrace (prefixWord ++ tailWord_6694998) baseStart_6694998 baseEnd_6694998 := by
    simpa [prefixWord, tailWord_6694998, baseEnd_6694998] using wordTrace_append hprefix tailTrace_6694998
  have hstable : (prefixWord ++ tailWord_6694998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6694998).length < 2 ^ (prefixWord ++ tailWord_6694998).sum := by decide
  have hdescent : baseEnd_6694998 < baseStart_6694998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6694998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695005 : List Nat := [1, 4, 4, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_6695005 : Nat := 118140960795 + 6695005 * 2 ^ 59
def prefixEnd_6695005 : Nat := 4983230072969 + 3 ^ 40 * 6695005 * 2
def baseEnd_6695005 : Nat := 3437755549254683495847739

theorem tailTrace_6695005 : CollatzResearch.WordTrace tailWord_6695005 prefixEnd_6695005 3437755549254683495847739 := by
  unfold tailWord_6695005
  simp only [CollatzResearch.WordTrace]
  refine ⟨244186893110147775667126469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162791262073431850444750979 244186893110147775667126469)
  ·
    refine ⟨45785042458152707937586213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244186893110147775667126469 45785042458152707937586213)
    ·
      refine ⟨8584695460903632738297415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45785042458152707937586213 8584695460903632738297415)
      ·
        refine ⟨12877043191355449107446123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8584695460903632738297415 12877043191355449107446123)
        ·
          refine ⟨19315564787033173661169185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12877043191355449107446123 19315564787033173661169185)
          ·
            refine ⟨14486673590274880245876889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19315564787033173661169185 14486673590274880245876889)
            ·
              refine ⟨10865005192706160184407667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14486673590274880245876889 10865005192706160184407667)
              ·
                refine ⟨16297507789059240276611501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10865005192706160184407667 16297507789059240276611501)
                ·
                  refine ⟨6111565420897215103729313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16297507789059240276611501 6111565420897215103729313)
                  ·
                    refine ⟨4583674065672911327796985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6111565420897215103729313 4583674065672911327796985)
                    ·
                      refine ⟨3437755549254683495847739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4583674065672911327796985 3437755549254683495847739)
                      ·
                        rfl

theorem cell23_6695005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_6695005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695005 prefixEnd_6695005 := by exact prefixLift 6695005
  have htrace : WordTrace (prefixWord ++ tailWord_6695005) baseStart_6695005 baseEnd_6695005 := by
    simpa [prefixWord, tailWord_6695005, baseEnd_6695005] using wordTrace_append hprefix tailTrace_6695005
  have hstable : (prefixWord ++ tailWord_6695005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695005).length < 2 ^ (prefixWord ++ tailWord_6695005).sum := by decide
  have hdescent : baseEnd_6695005 < baseStart_6695005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695018 : List Nat := [3, 1, 3, 2, 4, 1, 1, 1, 1, 2, 4]
def baseStart_6695018 : Nat := 118140960795 + 6695018 * 2 ^ 59
def prefixEnd_6695018 : Nat := 4983230072969 + 3 ^ 40 * 6695018 * 2
def baseEnd_6695018 : Nat := 3437762224503191944985179

theorem tailTrace_6695018 : CollatzResearch.WordTrace tailWord_6695018 prefixEnd_6695018 3437762224503191944985179 := by
  unfold tailWord_6695018
  simp only [CollatzResearch.WordTrace]
  refine ⟨61046841814775169721837427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162791578172733785924899805 61046841814775169721837427)
  ·
    refine ⟨91570262722162754582756141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61046841814775169721837427 91570262722162754582756141)
    ·
      refine ⟨34338848520811032968533553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91570262722162754582756141 34338848520811032968533553)
      ·
        refine ⟨25754136390608274726400165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34338848520811032968533553 25754136390608274726400165)
        ·
          refine ⟨4828900573239051511200031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25754136390608274726400165 4828900573239051511200031)
          ·
            refine ⟨7243350859858577266800047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4828900573239051511200031 7243350859858577266800047)
            ·
              refine ⟨10865026289787865900200071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7243350859858577266800047 10865026289787865900200071)
              ·
                refine ⟨16297539434681798850300107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10865026289787865900200071 16297539434681798850300107)
                ·
                  refine ⟨24446309152022698275450161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16297539434681798850300107 24446309152022698275450161)
                  ·
                    refine ⟨18334731864017023706587621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24446309152022698275450161 18334731864017023706587621)
                    ·
                      refine ⟨3437762224503191944985179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18334731864017023706587621 3437762224503191944985179)
                      ·
                        rfl

theorem cell23_6695018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_6695018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695018 prefixEnd_6695018 := by exact prefixLift 6695018
  have htrace : WordTrace (prefixWord ++ tailWord_6695018) baseStart_6695018 baseEnd_6695018 := by
    simpa [prefixWord, tailWord_6695018, baseEnd_6695018] using wordTrace_append hprefix tailTrace_6695018
  have hstable : (prefixWord ++ tailWord_6695018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695018).length < 2 ^ (prefixWord ++ tailWord_6695018).sum := by decide
  have hdescent : baseEnd_6695018 < baseStart_6695018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695031 : List Nat := [1, 1, 3, 1, 1, 5, 1, 4, 1, 3, 2]
def baseStart_6695031 : Nat := 118140960795 + 6695031 * 2 ^ 59
def prefixEnd_6695031 : Nat := 4983230072969 + 3 ^ 40 * 6695031 * 2
def baseEnd_6695031 : Nat := 3437768899751700394122619

theorem tailTrace_6695031 : CollatzResearch.WordTrace tailWord_6695031 prefixEnd_6695031 3437768899751700394122619 := by
  unfold tailWord_6695031
  simp only [CollatzResearch.WordTrace]
  refine ⟨244187841408053582107572947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162791894272035721405048631 244187841408053582107572947)
  ·
    refine ⟨366281762112080373161359421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244187841408053582107572947 366281762112080373161359421)
    ·
      refine ⟨137355660792030139935509783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366281762112080373161359421 137355660792030139935509783)
      ·
        refine ⟨206033491188045209903264675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137355660792030139935509783 206033491188045209903264675)
        ·
          refine ⟨309050236782067814854897013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206033491188045209903264675 309050236782067814854897013)
          ·
            refine ⟨28973459698318857642646595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 309050236782067814854897013 28973459698318857642646595)
            ·
              refine ⟨43460189547478286463969893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28973459698318857642646595 43460189547478286463969893)
              ·
                refine ⟨8148785540152178711994355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43460189547478286463969893 8148785540152178711994355)
                ·
                  refine ⟨12223178310228268067991533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8148785540152178711994355 12223178310228268067991533)
                  ·
                    refine ⟨4583691866335600525496825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12223178310228268067991533 4583691866335600525496825)
                    ·
                      refine ⟨3437768899751700394122619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4583691866335600525496825 3437768899751700394122619)
                      ·
                        rfl

theorem cell23_6695031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 3, 2].length) (baseStart_6695031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695031 prefixEnd_6695031 := by exact prefixLift 6695031
  have htrace : WordTrace (prefixWord ++ tailWord_6695031) baseStart_6695031 baseEnd_6695031 := by
    simpa [prefixWord, tailWord_6695031, baseEnd_6695031] using wordTrace_append hprefix tailTrace_6695031
  have hstable : (prefixWord ++ tailWord_6695031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695031).length < 2 ^ (prefixWord ++ tailWord_6695031).sum := by decide
  have hdescent : baseEnd_6695031 < baseStart_6695031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695047 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_6695047 : Nat := 118140960795 + 6695047 * 2 ^ 59
def prefixEnd_6695047 : Nat := 4983230072969 + 3 ^ 40 * 6695047 * 2
def baseEnd_6695047 : Nat := 3437777115442172331522545

theorem tailTrace_6695047 : CollatzResearch.WordTrace tailWord_6695047 prefixEnd_6695047 3437777115442172331522545 := by
  unfold tailWord_6695047
  simp only [CollatzResearch.WordTrace]
  refine ⟨244188424975995616840155395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162792283317330411226770263 244188424975995616840155395)
  ·
    refine ⟨366282637463993425260233093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244188424975995616840155395 366282637463993425260233093)
    ·
      refine ⟨68677994524498767236293705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 366282637463993425260233093 68677994524498767236293705)
      ·
        refine ⟨51508495893374075427220279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68677994524498767236293705 51508495893374075427220279)
        ·
          refine ⟨77262743840061113140830419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51508495893374075427220279 77262743840061113140830419)
          ·
            refine ⟨115894115760091669711245629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77262743840061113140830419 115894115760091669711245629)
            ·
              refine ⟨43460293410034376141717111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115894115760091669711245629 43460293410034376141717111)
              ·
                refine ⟨65190440115051564212575667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43460293410034376141717111 65190440115051564212575667)
                ·
                  refine ⟨97785660172577346318863501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65190440115051564212575667 97785660172577346318863501)
                  ·
                    refine ⟨36669622564716504869573813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97785660172577346318863501 36669622564716504869573813)
                    ·
                      refine ⟨3437777115442172331522545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36669622564716504869573813 3437777115442172331522545)
                      ·
                        rfl

theorem cell23_6695047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_6695047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695047 prefixEnd_6695047 := by exact prefixLift 6695047
  have htrace : WordTrace (prefixWord ++ tailWord_6695047) baseStart_6695047 baseEnd_6695047 := by
    simpa [prefixWord, tailWord_6695047, baseEnd_6695047] using wordTrace_append hprefix tailTrace_6695047
  have hstable : (prefixWord ++ tailWord_6695047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695047).length < 2 ^ (prefixWord ++ tailWord_6695047).sum := by decide
  have hdescent : baseEnd_6695047 < baseStart_6695047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695048 : List Nat := [2, 1, 3, 4, 1, 1, 2, 3, 1, 3, 2]
def baseStart_6695048 : Nat := 118140960795 + 6695048 * 2 ^ 59
def prefixEnd_6695048 : Nat := 4983230072969 + 3 ^ 40 * 6695048 * 2
def baseEnd_6695048 : Nat := 3437777628922826827610041

theorem tailTrace_6695048 : CollatzResearch.WordTrace tailWord_6695048 prefixEnd_6695048 3437777628922826827610041 := by
  unfold tailWord_6695048
  simp only [CollatzResearch.WordTrace]
  refine ⟨122094230724495997005470899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162792307632661329340627865 122094230724495997005470899)
  ·
    refine ⟨183141346086743995508206349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122094230724495997005470899 183141346086743995508206349)
    ·
      refine ⟨68678004782528998315577381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183141346086743995508206349 68678004782528998315577381)
      ·
        refine ⟨12877125896724187184170759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68678004782528998315577381 12877125896724187184170759)
        ·
          refine ⟨19315688845086280776256139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12877125896724187184170759 19315688845086280776256139)
          ·
            refine ⟨28973533267629421164384209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19315688845086280776256139 28973533267629421164384209)
            ·
              refine ⟨21730149950722065873288157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28973533267629421164384209 21730149950722065873288157)
              ·
                refine ⟨8148806231520774702483059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21730149950722065873288157 8148806231520774702483059)
                ·
                  refine ⟨12223209347281162053724589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8148806231520774702483059 12223209347281162053724589)
                  ·
                    refine ⟨4583703505230435770146721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12223209347281162053724589 4583703505230435770146721)
                    ·
                      refine ⟨3437777628922826827610041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4583703505230435770146721 3437777628922826827610041)
                      ·
                        rfl

theorem cell23_6695048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_6695048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695048 prefixEnd_6695048 := by exact prefixLift 6695048
  have htrace : WordTrace (prefixWord ++ tailWord_6695048) baseStart_6695048 baseEnd_6695048 := by
    simpa [prefixWord, tailWord_6695048, baseEnd_6695048] using wordTrace_append hprefix tailTrace_6695048
  have hstable : (prefixWord ++ tailWord_6695048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695048).length < 2 ^ (prefixWord ++ tailWord_6695048).sum := by decide
  have hdescent : baseEnd_6695048 < baseStart_6695048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695061 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 4, 2, 2]
def baseStart_6695061 : Nat := 118140960795 + 6695061 * 2 ^ 59
def prefixEnd_6695061 : Nat := 4983230072969 + 3 ^ 40 * 6695061 * 2
def baseEnd_6695061 : Nat := 3437784304171335276747481

theorem tailTrace_6695061 : CollatzResearch.WordTrace tailWord_6695061 prefixEnd_6695061 3437784304171335276747481 := by
  unfold tailWord_6695061
  simp only [CollatzResearch.WordTrace]
  refine ⟨244188935597944897231165037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162792623731963264820776691 244188935597944897231165037)
  ·
    refine ⟨91570850849229336461686889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244188935597944897231165037 91570850849229336461686889)
    ·
      refine ⟨68678138136922002346265167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91570850849229336461686889 68678138136922002346265167)
      ·
        refine ⟨103017207205383003519397751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68678138136922002346265167 103017207205383003519397751)
        ·
          refine ⟨154525810808074505279096627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103017207205383003519397751 154525810808074505279096627)
          ·
            refine ⟨231788716212111757918644941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154525810808074505279096627 231788716212111757918644941)
            ·
              refine ⟨86920768579541909219491853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231788716212111757918644941 86920768579541909219491853)
              ·
                refine ⟨32595288217328215957309445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86920768579541909219491853 32595288217328215957309445)
                ·
                  refine ⟨6111616540749040491995521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32595288217328215957309445 6111616540749040491995521)
                  ·
                    refine ⟨4583712405561780368996641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6111616540749040491995521 4583712405561780368996641)
                    ·
                      refine ⟨3437784304171335276747481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4583712405561780368996641 3437784304171335276747481)
                      ·
                        rfl

theorem cell23_6695061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_6695061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695061 prefixEnd_6695061 := by exact prefixLift 6695061
  have htrace : WordTrace (prefixWord ++ tailWord_6695061) baseStart_6695061 baseEnd_6695061 := by
    simpa [prefixWord, tailWord_6695061, baseEnd_6695061] using wordTrace_append hprefix tailTrace_6695061
  have hstable : (prefixWord ++ tailWord_6695061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695061).length < 2 ^ (prefixWord ++ tailWord_6695061).sum := by decide
  have hdescent : baseEnd_6695061 < baseStart_6695061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695082 : List Nat := [3, 1, 5, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_6695082 : Nat := 118140960795 + 6695082 * 2 ^ 59
def prefixEnd_6695082 : Nat := 4983230072969 + 3 ^ 40 * 6695082 * 2
def baseEnd_6695082 : Nat := 3437795087265079694584885

theorem tailTrace_6695082 : CollatzResearch.WordTrace tailWord_6695082 prefixEnd_6695082 3437795087265079694584885 := by
  unfold tailWord_6695082
  simp only [CollatzResearch.WordTrace]
  refine ⟨61047425382717204454419875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162793134353912545211786333 61047425382717204454419875)
  ·
    refine ⟨91571138074075806681629813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61047425382717204454419875 91571138074075806681629813)
    ·
      refine ⟨8584794194444606876402795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91571138074075806681629813 8584794194444606876402795)
      ·
        refine ⟨12877191291666910314604193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8584794194444606876402795 12877191291666910314604193)
        ·
          refine ⟨9657893468750182735953145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12877191291666910314604193 9657893468750182735953145)
          ·
            refine ⟨7243420101562637051964859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9657893468750182735953145 7243420101562637051964859)
            ·
              refine ⟨10865130152343955577947289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7243420101562637051964859 10865130152343955577947289)
              ·
                refine ⟨8148847614257966683460467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10865130152343955577947289 8148847614257966683460467)
                ·
                  refine ⟨12223271421386950025190701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8148847614257966683460467 12223271421386950025190701)
                  ·
                    refine ⟨4583726783020106259446513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12223271421386950025190701 4583726783020106259446513)
                    ·
                      refine ⟨3437795087265079694584885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4583726783020106259446513 3437795087265079694584885)
                      ·
                        rfl

theorem cell23_6695082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_6695082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695082 prefixEnd_6695082 := by exact prefixLift 6695082
  have htrace : WordTrace (prefixWord ++ tailWord_6695082) baseStart_6695082 baseEnd_6695082 := by
    simpa [prefixWord, tailWord_6695082, baseEnd_6695082] using wordTrace_append hprefix tailTrace_6695082
  have hstable : (prefixWord ++ tailWord_6695082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695082).length < 2 ^ (prefixWord ++ tailWord_6695082).sum := by decide
  have hdescent : baseEnd_6695082 < baseStart_6695082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695114 : List Nat := [3, 1, 2, 1, 3, 1, 1, 4, 2, 5]
def baseStart_6695114 : Nat := 118140960795 + 6695114 * 2 ^ 59
def prefixEnd_6695114 : Nat := 4983230072969 + 3 ^ 40 * 6695114 * 2
def baseEnd_6695114 : Nat := 1145937172882007856461579

theorem tailTrace_6695114 : CollatzResearch.WordTrace tailWord_6695114 prefixEnd_6695114 1145937172882007856461579 := by
  unfold tailWord_6695114
  simp only [CollatzResearch.WordTrace]
  refine ⟨61047717166688221820711099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162793912444501924855229597 61047717166688221820711099)
  ·
    refine ⟨91571575750032332731066649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61047717166688221820711099 91571575750032332731066649)
    ·
      refine ⟨68678681812524249548299987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91571575750032332731066649 68678681812524249548299987)
      ·
        refine ⟨103018022718786374322449981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68678681812524249548299987 103018022718786374322449981)
        ·
          refine ⟨38631758519544890370918743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103018022718786374322449981 38631758519544890370918743)
          ·
            refine ⟨57947637779317335556378115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38631758519544890370918743 57947637779317335556378115)
            ·
              refine ⟨86921456668976003334567173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57947637779317335556378115 86921456668976003334567173)
              ·
                refine ⟨16297773125433000625231345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86921456668976003334567173 16297773125433000625231345)
                ·
                  refine ⟨12223329844074750468923509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16297773125433000625231345 12223329844074750468923509)
                  ·
                    refine ⟨1145937172882007856461579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12223329844074750468923509 1145937172882007856461579)
                    ·
                      rfl

theorem cell23_6695114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_6695114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695114 prefixEnd_6695114 := by exact prefixLift 6695114
  have htrace : WordTrace (prefixWord ++ tailWord_6695114) baseStart_6695114 baseEnd_6695114 := by
    simpa [prefixWord, tailWord_6695114, baseEnd_6695114] using wordTrace_append hprefix tailTrace_6695114
  have hstable : (prefixWord ++ tailWord_6695114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695114).length < 2 ^ (prefixWord ++ tailWord_6695114).sum := by decide
  have hdescent : baseEnd_6695114 < baseStart_6695114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695118 : List Nat := [4, 1, 1, 1, 4, 1, 4, 2, 5]
def baseStart_6695118 : Nat := 118140960795 + 6695118 * 2 ^ 59
def prefixEnd_6695118 : Nat := 4983230072969 + 3 ^ 40 * 6695118 * 2
def baseEnd_6695118 : Nat := 381979285840960172637191

theorem tailTrace_6695118 : CollatzResearch.WordTrace tailWord_6695118 prefixEnd_6695118 381979285840960172637191 := by
  unfold tailWord_6695118
  simp only [CollatzResearch.WordTrace]
  refine ⟨30523876819842299495748751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162794009705825597310660005 30523876819842299495748751)
  ·
    refine ⟨45785815229763449243623127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30523876819842299495748751 45785815229763449243623127)
    ·
      refine ⟨68678722844645173865434691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45785815229763449243623127 68678722844645173865434691)
      ·
        refine ⟨103018084266967760798152037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68678722844645173865434691 103018084266967760798152037)
        ·
          refine ⟨19315890800056455149653507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103018084266967760798152037 19315890800056455149653507)
          ·
            refine ⟨28973836200084682724480261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19315890800056455149653507 28973836200084682724480261)
            ·
              refine ⟨5432594287515878010840049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28973836200084682724480261 5432594287515878010840049)
              ·
                refine ⟨4074445715636908508130037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5432594287515878010840049 4074445715636908508130037)
                ·
                  refine ⟨381979285840960172637191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4074445715636908508130037 381979285840960172637191)
                  ·
                    rfl

theorem cell23_6695118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_6695118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695118 prefixEnd_6695118 := by exact prefixLift 6695118
  have htrace : WordTrace (prefixWord ++ tailWord_6695118) baseStart_6695118 baseEnd_6695118 := by
    simpa [prefixWord, tailWord_6695118, baseEnd_6695118] using wordTrace_append hprefix tailTrace_6695118
  have hstable : (prefixWord ++ tailWord_6695118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695118).length < 2 ^ (prefixWord ++ tailWord_6695118).sum := by decide
  have hdescent : baseEnd_6695118 < baseStart_6695118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695127 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 2, 8]
def baseStart_6695127 : Nat := 118140960795 + 6695127 * 2 ^ 59
def prefixEnd_6695127 : Nat := 4983230072969 + 3 ^ 40 * 6695127 * 2
def baseEnd_6695127 : Nat := 1145939397964844006174059

theorem tailTrace_6695127 : CollatzResearch.WordTrace tailWord_6695127 prefixEnd_6695127 1145939397964844006174059 := by
  unfold tailWord_6695127
  simp only [CollatzResearch.WordTrace]
  refine ⟨244191342815705790503067635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162794228543803860335378423 244191342815705790503067635)
  ·
    refine ⟨366287014223558685754601453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244191342815705790503067635 366287014223558685754601453)
    ·
      refine ⟨137357630333834507157975545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366287014223558685754601453 137357630333834507157975545)
      ·
        refine ⟨103018222750375880368481659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137357630333834507157975545 103018222750375880368481659)
        ·
          refine ⟨154527334125563820552722489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103018222750375880368481659 154527334125563820552722489)
          ·
            refine ⟨115895500594172865414541867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154527334125563820552722489 115895500594172865414541867)
            ·
              refine ⟨173843250891259298121812801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115895500594172865414541867 173843250891259298121812801)
              ·
                refine ⟨130382438168444473591359601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173843250891259298121812801 130382438168444473591359601)
                ·
                  refine ⟨97786828626333355193519701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130382438168444473591359601 97786828626333355193519701)
                  ·
                    refine ⟨1145939397964844006174059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97786828626333355193519701 1145939397964844006174059)
                    ·
                      rfl

theorem cell23_6695127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_6695127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695127 prefixEnd_6695127 := by exact prefixLift 6695127
  have htrace : WordTrace (prefixWord ++ tailWord_6695127) baseStart_6695127 baseEnd_6695127 := by
    simpa [prefixWord, tailWord_6695127, baseEnd_6695127] using wordTrace_append hprefix tailTrace_6695127
  have hstable : (prefixWord ++ tailWord_6695127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695127).length < 2 ^ (prefixWord ++ tailWord_6695127).sum := by decide
  have hdescent : baseEnd_6695127 < baseStart_6695127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695151 : List Nat := [1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 4]
def baseStart_6695151 : Nat := 118140960795 + 6695151 * 2 ^ 59
def prefixEnd_6695151 : Nat := 4983230072969 + 3 ^ 40 * 6695151 * 2
def baseEnd_6695151 : Nat := 3437830517430239924622067

theorem tailTrace_6695151 : CollatzResearch.WordTrace tailWord_6695151 prefixEnd_6695151 3437830517430239924622067 := by
  unfold tailWord_6695151
  simp only [CollatzResearch.WordTrace]
  refine ⟨244192218167618842601941307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162794812111745895067960871 244192218167618842601941307)
  ·
    refine ⟨366288327251428263902911961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244192218167618842601941307 366288327251428263902911961)
    ·
      refine ⟨274716245438571197927183971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366288327251428263902911961 274716245438571197927183971)
      ·
        refine ⟨412074368157856796890775957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274716245438571197927183971 412074368157856796890775957)
        ·
          refine ⟨19315986007399537354255123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 412074368157856796890775957 19315986007399537354255123)
          ·
            refine ⟨28973979011099306031382685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19315986007399537354255123 28973979011099306031382685)
            ·
              refine ⟨10865242129162239761768507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28973979011099306031382685 10865242129162239761768507)
              ·
                refine ⟨16297863193743359642652761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10865242129162239761768507 16297863193743359642652761)
                ·
                  refine ⟨12223397395307519731989571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16297863193743359642652761 12223397395307519731989571)
                  ·
                    refine ⟨18335096092961279597984357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12223397395307519731989571 18335096092961279597984357)
                    ·
                      refine ⟨3437830517430239924622067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18335096092961279597984357 3437830517430239924622067)
                      ·
                        rfl

theorem cell23_6695151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 4].length) (baseStart_6695151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695151 prefixEnd_6695151 := by exact prefixLift 6695151
  have htrace : WordTrace (prefixWord ++ tailWord_6695151) baseStart_6695151 baseEnd_6695151 := by
    simpa [prefixWord, tailWord_6695151, baseEnd_6695151] using wordTrace_append hprefix tailTrace_6695151
  have hstable : (prefixWord ++ tailWord_6695151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695151).length < 2 ^ (prefixWord ++ tailWord_6695151).sum := by decide
  have hdescent : baseEnd_6695151 < baseStart_6695151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695164 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_6695164 : Nat := 118140960795 + 6695164 * 2 ^ 59
def prefixEnd_6695164 : Nat := 4983230072969 + 3 ^ 40 * 6695164 * 2
def baseEnd_6695164 : Nat := 3437837192678748373759507

theorem tailTrace_6695164 : CollatzResearch.WordTrace tailWord_6695164 prefixEnd_6695164 3437837192678748373759507 := by
  unfold tailWord_6695164
  simp only [CollatzResearch.WordTrace]
  refine ⟨122096346158285872911082273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162795128211047830548109697 122096346158285872911082273)
  ·
    refine ⟨91572259618714404683311705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122096346158285872911082273 91572259618714404683311705)
    ·
      refine ⟨68679194714035803512483779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91572259618714404683311705 68679194714035803512483779)
      ·
        refine ⟨103018792071053705268725669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68679194714035803512483779 103018792071053705268725669)
        ·
          refine ⟨19316023513322569737886063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103018792071053705268725669 19316023513322569737886063)
          ·
            refine ⟨28974035269983854606829095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19316023513322569737886063 28974035269983854606829095)
            ·
              refine ⟨43461052904975781910243643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28974035269983854606829095 43461052904975781910243643)
              ·
                refine ⟨65191579357463672865365465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43461052904975781910243643 65191579357463672865365465)
                ·
                  refine ⟨48893684518097754649024099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65191579357463672865365465 48893684518097754649024099)
                  ·
                    refine ⟨73340526777146631973536149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48893684518097754649024099 73340526777146631973536149)
                    ·
                      refine ⟨3437837192678748373759507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73340526777146631973536149 3437837192678748373759507)
                      ·
                        rfl

theorem cell23_6695164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_6695164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695164 prefixEnd_6695164 := by exact prefixLift 6695164
  have htrace : WordTrace (prefixWord ++ tailWord_6695164) baseStart_6695164 baseEnd_6695164 := by
    simpa [prefixWord, tailWord_6695164, baseEnd_6695164] using wordTrace_append hprefix tailTrace_6695164
  have hstable : (prefixWord ++ tailWord_6695164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695164).length < 2 ^ (prefixWord ++ tailWord_6695164).sum := by decide
  have hdescent : baseEnd_6695164 < baseStart_6695164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695178 : List Nat := [3, 1, 2, 2, 1, 1, 4, 4, 1, 4]
def baseStart_6695178 : Nat := 118140960795 + 6695178 * 2 ^ 59
def prefixEnd_6695178 : Nat := 4983230072969 + 3 ^ 40 * 6695178 * 2
def baseEnd_6695178 : Nat := 1145948127135970439661481

theorem tailTrace_6695178 : CollatzResearch.WordTrace tailWord_6695178 prefixEnd_6695178 1145948127135970439661481 := by
  unfold tailWord_6695178
  simp only [CollatzResearch.WordTrace]
  refine ⟨61048300734630256553293547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162795468625680684142116125 61048300734630256553293547)
  ·
    refine ⟨91572451101945384829940321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61048300734630256553293547 91572451101945384829940321)
    ·
      refine ⟨68679338326459038622455241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91572451101945384829940321 68679338326459038622455241)
      ·
        refine ⟨51509503744844278966841431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68679338326459038622455241 51509503744844278966841431)
        ·
          refine ⟨77264255617266418450262147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51509503744844278966841431 77264255617266418450262147)
          ·
            refine ⟨115896383425899627675393221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77264255617266418450262147 115896383425899627675393221)
            ·
              refine ⟨21730571892356180189136229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115896383425899627675393221 21730571892356180189136229)
              ·
                refine ⟨4074482229816783785463043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21730571892356180189136229 4074482229816783785463043)
                ·
                  refine ⟨6111723344725175678194565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4074482229816783785463043 6111723344725175678194565)
                  ·
                    refine ⟨1145948127135970439661481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6111723344725175678194565 1145948127135970439661481)
                    ·
                      rfl

theorem cell23_6695178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_6695178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695178 prefixEnd_6695178 := by exact prefixLift 6695178
  have htrace : WordTrace (prefixWord ++ tailWord_6695178) baseStart_6695178 baseEnd_6695178 := by
    simpa [prefixWord, tailWord_6695178, baseEnd_6695178] using wordTrace_append hprefix tailTrace_6695178
  have hstable : (prefixWord ++ tailWord_6695178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695178).length < 2 ^ (prefixWord ++ tailWord_6695178).sum := by decide
  have hdescent : baseEnd_6695178 < baseStart_6695178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695221 : List Nat := [1, 3, 3, 1, 2, 1, 1, 5, 1, 5]
def baseStart_6695221 : Nat := 118140960795 + 6695221 * 2 ^ 59
def prefixEnd_6695221 : Nat := 4983230072969 + 3 ^ 40 * 6695221 * 2
def baseEnd_6695221 : Nat := 1145955487025351550248915

theorem tailTrace_6695221 : CollatzResearch.WordTrace tailWord_6695221 prefixEnd_6695221 1145955487025351550248915 := by
  unfold tailWord_6695221
  simp only [CollatzResearch.WordTrace]
  refine ⟨244194771277365244556989517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162796514184910163037993011 244194771277365244556989517)
  ·
    refine ⟨91573039229011966708871069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244194771277365244556989517 91573039229011966708871069)
    ·
      refine ⟨34339889710879487515826651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91573039229011966708871069 34339889710879487515826651)
      ·
        refine ⟨51509834566319231273739977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34339889710879487515826651 51509834566319231273739977)
        ·
          refine ⟨38632375924739423455304983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51509834566319231273739977 38632375924739423455304983)
          ·
            refine ⟨57948563887109135182957475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38632375924739423455304983 57948563887109135182957475)
            ·
              refine ⟨86922845830663702774436213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57948563887109135182957475 86922845830663702774436213)
              ·
                refine ⟨8149016796624722135103395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86922845830663702774436213 8149016796624722135103395)
                ·
                  refine ⟨12223525194937083202655093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8149016796624722135103395 12223525194937083202655093)
                  ·
                    refine ⟨1145955487025351550248915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12223525194937083202655093 1145955487025351550248915)
                    ·
                      rfl

theorem cell23_6695221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_6695221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695221 prefixEnd_6695221 := by exact prefixLift 6695221
  have htrace : WordTrace (prefixWord ++ tailWord_6695221) baseStart_6695221 baseEnd_6695221 := by
    simpa [prefixWord, tailWord_6695221, baseEnd_6695221] using wordTrace_append hprefix tailTrace_6695221
  have hstable : (prefixWord ++ tailWord_6695221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695221).length < 2 ^ (prefixWord ++ tailWord_6695221).sum := by decide
  have hdescent : baseEnd_6695221 < baseStart_6695221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695228 : List Nat := [2, 2, 2, 2, 1, 2, 3, 2, 2, 3, 2]
def baseStart_6695228 : Nat := 118140960795 + 6695228 * 2 ^ 59
def prefixEnd_6695228 : Nat := 4983230072969 + 3 ^ 40 * 6695228 * 2
def baseEnd_6695228 : Nat := 3437870055440636123359213

theorem tailTrace_6695228 : CollatzResearch.WordTrace tailWord_6695228 prefixEnd_6695228 3437870055440636123359213 := by
  unfold tailWord_6695228
  simp only [CollatzResearch.WordTrace]
  refine ⟨122097513294169942376247169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162796684392226589834996225 122097513294169942376247169)
  ·
    refine ⟨91573134970627456782185377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122097513294169942376247169 91573134970627456782185377)
    ·
      refine ⟨68679851227970592586639033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91573134970627456782185377 68679851227970592586639033)
      ·
        refine ⟨51509888420977944439979275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68679851227970592586639033 51509888420977944439979275)
        ·
          refine ⟨77264832631466916659968913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51509888420977944439979275 77264832631466916659968913)
          ·
            refine ⟨57948624473600187494976685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77264832631466916659968913 57948624473600187494976685)
            ·
              refine ⟨21730734177600070310616257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57948624473600187494976685 21730734177600070310616257)
              ·
                refine ⟨16298050633200052732962193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21730734177600070310616257 16298050633200052732962193)
                ·
                  refine ⟨12223537974900039549721645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16298050633200052732962193 12223537974900039549721645)
                  ·
                    refine ⟨4583826740587514831145617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12223537974900039549721645 4583826740587514831145617)
                    ·
                      refine ⟨3437870055440636123359213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4583826740587514831145617 3437870055440636123359213)
                      ·
                        rfl

theorem cell23_6695228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_6695228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695228 prefixEnd_6695228 := by exact prefixLift 6695228
  have htrace : WordTrace (prefixWord ++ tailWord_6695228) baseStart_6695228 baseEnd_6695228 := by
    simpa [prefixWord, tailWord_6695228, baseEnd_6695228] using wordTrace_append hprefix tailTrace_6695228
  have hstable : (prefixWord ++ tailWord_6695228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695228).length < 2 ^ (prefixWord ++ tailWord_6695228).sum := by decide
  have hdescent : baseEnd_6695228 < baseStart_6695228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695258 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2]
def baseStart_6695258 : Nat := 118140960795 + 6695258 * 2 ^ 59
def prefixEnd_6695258 : Nat := 4983230072969 + 3 ^ 40 * 6695258 * 2
def baseEnd_6695258 : Nat := 3437885459860271005984075

theorem tailTrace_6695258 : CollatzResearch.WordTrace tailWord_6695258 prefixEnd_6695258 3437885459860271005984075 := by
  unfold tailWord_6695258
  simp only [CollatzResearch.WordTrace]
  refine ⟨61049030194557799969021607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162797413852154133250724285 61049030194557799969021607)
  ·
    refine ⟨91573545291836699953532411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61049030194557799969021607 91573545291836699953532411)
    ·
      refine ⟨137360317937755049930298617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91573545291836699953532411 137360317937755049930298617)
      ·
        refine ⟨103020238453316287447723963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137360317937755049930298617 103020238453316287447723963)
        ·
          refine ⟨154530357679974431171585945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103020238453316287447723963 154530357679974431171585945)
          ·
            refine ⟨115897768259980823378689459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154530357679974431171585945 115897768259980823378689459)
            ·
              refine ⟨173846652389971235068034189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115897768259980823378689459 173846652389971235068034189)
              ·
                refine ⟨65192494646239213150512821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173846652389971235068034189 65192494646239213150512821)
                ·
                  refine ⟨6111796373084926232860577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65192494646239213150512821 6111796373084926232860577)
                  ·
                    refine ⟨4583847279813694674645433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6111796373084926232860577 4583847279813694674645433)
                    ·
                      refine ⟨3437885459860271005984075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4583847279813694674645433 3437885459860271005984075)
                      ·
                        rfl

theorem cell23_6695258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_6695258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695258 prefixEnd_6695258 := by exact prefixLift 6695258
  have htrace : WordTrace (prefixWord ++ tailWord_6695258) baseStart_6695258 baseEnd_6695258 := by
    simpa [prefixWord, tailWord_6695258, baseEnd_6695258] using wordTrace_append hprefix tailTrace_6695258
  have hstable : (prefixWord ++ tailWord_6695258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695258).length < 2 ^ (prefixWord ++ tailWord_6695258).sum := by decide
  have hdescent : baseEnd_6695258 < baseStart_6695258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695271 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_6695271 : Nat := 118140960795 + 6695271 * 2 ^ 59
def prefixEnd_6695271 : Nat := 4983230072969 + 3 ^ 40 * 6695271 * 2
def baseEnd_6695271 : Nat := 3437892135108779455121515

theorem tailTrace_6695271 : CollatzResearch.WordTrace tailWord_6695271 prefixEnd_6695271 3437892135108779455121515 := by
  unfold tailWord_6695271
  simp only [CollatzResearch.WordTrace]
  refine ⟨244196594927184103096309667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162797729951456068730873111 244196594927184103096309667)
  ·
    refine ⟨366294892390776154644464501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244196594927184103096309667 366294892390776154644464501)
    ·
      refine ⟨34340146161635264497918547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 366294892390776154644464501 34340146161635264497918547)
      ·
        refine ⟨51510219242452896746877821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34340146161635264497918547 51510219242452896746877821)
        ·
          refine ⟨19316332215919836280079183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51510219242452896746877821 19316332215919836280079183)
          ·
            refine ⟨28974498323879754420118775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19316332215919836280079183 28974498323879754420118775)
            ·
              refine ⟨43461747485819631630178163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28974498323879754420118775 43461747485819631630178163)
              ·
                refine ⟨65192621228729447445267245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43461747485819631630178163 65192621228729447445267245)
                ·
                  refine ⟨24447232960773542791975217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65192621228729447445267245 24447232960773542791975217)
                  ·
                    refine ⟨18335424720580157093981413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24447232960773542791975217 18335424720580157093981413)
                    ·
                      refine ⟨3437892135108779455121515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18335424720580157093981413 3437892135108779455121515)
                      ·
                        rfl

theorem cell23_6695271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_6695271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695271 prefixEnd_6695271 := by exact prefixLift 6695271
  have htrace : WordTrace (prefixWord ++ tailWord_6695271) baseStart_6695271 baseEnd_6695271 := by
    simpa [prefixWord, tailWord_6695271, baseEnd_6695271] using wordTrace_append hprefix tailTrace_6695271
  have hstable : (prefixWord ++ tailWord_6695271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695271).length < 2 ^ (prefixWord ++ tailWord_6695271).sum := by decide
  have hdescent : baseEnd_6695271 < baseStart_6695271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695285 : List Nat := [1, 3, 4, 1, 2, 2, 2, 2, 2, 4]
def baseStart_6695285 : Nat := 118140960795 + 6695285 * 2 ^ 59
def prefixEnd_6695285 : Nat := 4983230072969 + 3 ^ 40 * 6695285 * 2
def baseEnd_6695285 : Nat := 1145966441279314133448817

theorem tailTrace_6695285 : CollatzResearch.WordTrace tailWord_6695285 prefixEnd_6695285 1145966441279314133448817 := by
  unfold tailWord_6695285
  simp only [CollatzResearch.WordTrace]
  refine ⟨244197105549133383487319309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162798070366088922324879539 244197105549133383487319309)
  ·
    refine ⟨91573914580925018807744741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244197105549133383487319309 91573914580925018807744741)
    ·
      refine ⟨17170108983923441026452139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91573914580925018807744741 17170108983923441026452139)
      ·
        refine ⟨25755163475885161539678209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17170108983923441026452139 25755163475885161539678209)
        ·
          refine ⟨19316372606913871154758657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25755163475885161539678209 19316372606913871154758657)
          ·
            refine ⟨14487279455185403366068993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19316372606913871154758657 14487279455185403366068993)
            ·
              refine ⟨10865459591389052524551745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14487279455185403366068993 10865459591389052524551745)
              ·
                refine ⟨8149094693541789393413809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10865459591389052524551745 8149094693541789393413809)
                ·
                  refine ⟨6111821020156342045060357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8149094693541789393413809 6111821020156342045060357)
                  ·
                    refine ⟨1145966441279314133448817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6111821020156342045060357 1145966441279314133448817)
                    ·
                      rfl

theorem cell23_6695285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_6695285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695285 prefixEnd_6695285 := by exact prefixLift 6695285
  have htrace : WordTrace (prefixWord ++ tailWord_6695285) baseStart_6695285 baseEnd_6695285 := by
    simpa [prefixWord, tailWord_6695285, baseEnd_6695285] using wordTrace_append hprefix tailTrace_6695285
  have hstable : (prefixWord ++ tailWord_6695285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695285).length < 2 ^ (prefixWord ++ tailWord_6695285).sum := by decide
  have hdescent : baseEnd_6695285 < baseStart_6695285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695308 : List Nat := [2, 2, 1, 2, 1, 5, 2, 1, 1, 3, 3]
def baseStart_6695308 : Nat := 118140960795 + 6695308 * 2 ^ 59
def prefixEnd_6695308 : Nat := 4983230072969 + 3 ^ 40 * 6695308 * 2
def baseEnd_6695308 : Nat := 3437911133892995810358845

theorem tailTrace_6695308 : CollatzResearch.WordTrace tailWord_6695308 prefixEnd_6695308 3437911133892995810358845 := by
  unfold tailWord_6695308
  simp only [CollatzResearch.WordTrace]
  refine ⟨122098972214025029207703289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162798629618700038943604385 122098972214025029207703289)
  ·
    refine ⟨91574229160518771905777467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122098972214025029207703289 91574229160518771905777467)
    ·
      refine ⟨137361343740778157858666201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91574229160518771905777467 137361343740778157858666201)
      ·
        refine ⟨103021007805583618393999651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137361343740778157858666201 103021007805583618393999651)
        ·
          refine ⟨154531511708375427590999477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103021007805583618393999651 154531511708375427590999477)
          ·
            refine ⟨14487329222660196336656201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154531511708375427590999477 14487329222660196336656201)
            ·
              refine ⟨10865496916995147252492151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14487329222660196336656201 10865496916995147252492151)
              ·
                refine ⟨16298245375492720878738227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10865496916995147252492151 16298245375492720878738227)
                ·
                  refine ⟨24447368063239081318107341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16298245375492720878738227 24447368063239081318107341)
                  ·
                    refine ⟨9167763023714655494290253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24447368063239081318107341 9167763023714655494290253)
                    ·
                      refine ⟨3437911133892995810358845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9167763023714655494290253 3437911133892995810358845)
                      ·
                        rfl

theorem cell23_6695308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_6695308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695308 prefixEnd_6695308 := by exact prefixLift 6695308
  have htrace : WordTrace (prefixWord ++ tailWord_6695308) baseStart_6695308 baseEnd_6695308 := by
    simpa [prefixWord, tailWord_6695308, baseEnd_6695308] using wordTrace_append hprefix tailTrace_6695308
  have hstable : (prefixWord ++ tailWord_6695308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695308).length < 2 ^ (prefixWord ++ tailWord_6695308).sum := by decide
  have hdescent : baseEnd_6695308 < baseStart_6695308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695326 : List Nat := [4, 3, 1, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_6695326 : Nat := 118140960795 + 6695326 * 2 ^ 59
def prefixEnd_6695326 : Nat := 4983230072969 + 3 ^ 40 * 6695326 * 2
def baseEnd_6695326 : Nat := 3437920376544776739933763

theorem tailTrace_6695326 : CollatzResearch.WordTrace tailWord_6695326 prefixEnd_6695326 3437920376544776739933763 := by
  unfold tailWord_6695326
  simp only [CollatzResearch.WordTrace]
  refine ⟨30524825117748105936195229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162799067294656564993041221 30524825117748105936195229)
  ·
    refine ⟨11446809419155539726073211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30524825117748105936195229 11446809419155539726073211)
    ·
      refine ⟨17170214128733309589109817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11446809419155539726073211 17170214128733309589109817)
      ·
        refine ⟨12877660596549982191832363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17170214128733309589109817 12877660596549982191832363)
        ·
          refine ⟨19316490894824973287748545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12877660596549982191832363 19316490894824973287748545)
          ·
            refine ⟨14487368171118729965811409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19316490894824973287748545 14487368171118729965811409)
            ·
              refine ⟨10865526128339047474358557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14487368171118729965811409 10865526128339047474358557)
              ·
                refine ⟨4074572298127142802884459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10865526128339047474358557 4074572298127142802884459)
                ·
                  refine ⟨6111858447190714204326689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4074572298127142802884459 6111858447190714204326689)
                  ·
                    refine ⟨4583893835393035653245017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6111858447190714204326689 4583893835393035653245017)
                    ·
                      refine ⟨3437920376544776739933763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4583893835393035653245017 3437920376544776739933763)
                      ·
                        rfl

theorem cell23_6695326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_6695326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695326 prefixEnd_6695326 := by exact prefixLift 6695326
  have htrace : WordTrace (prefixWord ++ tailWord_6695326) baseStart_6695326 baseEnd_6695326 := by
    simpa [prefixWord, tailWord_6695326, baseEnd_6695326] using wordTrace_append hprefix tailTrace_6695326
  have hstable : (prefixWord ++ tailWord_6695326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695326).length < 2 ^ (prefixWord ++ tailWord_6695326).sum := by decide
  have hdescent : baseEnd_6695326 < baseStart_6695326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695329 : List Nat := [1, 2, 3, 5, 1, 2, 2, 1, 1, 2, 3]
def baseStart_6695329 : Nat := 118140960795 + 6695329 * 2 ^ 59
def prefixEnd_6695329 : Nat := 4983230072969 + 3 ^ 40 * 6695329 * 2
def baseEnd_6695329 : Nat := 3437921916986740228196249

theorem tailTrace_6695329 : CollatzResearch.WordTrace tailWord_6695329 prefixEnd_6695329 3437921916986740228196249 := by
  unfold tailWord_6695329
  simp only [CollatzResearch.WordTrace]
  refine ⟨244198710360973979001921041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162799140240649319334614027 244198710360973979001921041)
  ·
    refine ⟨183149032770730484251440781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244198710360973979001921041 183149032770730484251440781)
    ·
      refine ⟨68680887289023931594290293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183149032770730484251440781 68680887289023931594290293)
      ·
        refine ⟨6438833183345993586964715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68680887289023931594290293 6438833183345993586964715)
        ·
          refine ⟨9658249775018990380447073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6438833183345993586964715 9658249775018990380447073)
          ·
            refine ⟨7243687331264242785335305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9658249775018990380447073 7243687331264242785335305)
            ·
              refine ⟨5432765498448182089001479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7243687331264242785335305 5432765498448182089001479)
              ·
                refine ⟨8149148247672273133502219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5432765498448182089001479 8149148247672273133502219)
                ·
                  refine ⟨12223722371508409700253329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8149148247672273133502219 12223722371508409700253329)
                  ·
                    refine ⟨9167791778631307275189997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12223722371508409700253329 9167791778631307275189997)
                    ·
                      refine ⟨3437921916986740228196249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9167791778631307275189997 3437921916986740228196249)
                      ·
                        rfl

theorem cell23_6695329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_6695329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695329 prefixEnd_6695329 := by exact prefixLift 6695329
  have htrace : WordTrace (prefixWord ++ tailWord_6695329) baseStart_6695329 baseEnd_6695329 := by
    simpa [prefixWord, tailWord_6695329, baseEnd_6695329] using wordTrace_append hprefix tailTrace_6695329
  have hstable : (prefixWord ++ tailWord_6695329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695329).length < 2 ^ (prefixWord ++ tailWord_6695329).sum := by decide
  have hdescent : baseEnd_6695329 < baseStart_6695329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695382 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_6695382 : Nat := 118140960795 + 6695382 * 2 ^ 59
def prefixEnd_6695382 : Nat := 4983230072969 + 3 ^ 40 * 6695382 * 2
def baseEnd_6695382 : Nat := 3437949131461428520833505

theorem tailTrace_6695382 : CollatzResearch.WordTrace tailWord_6695382 prefixEnd_6695382 3437949131461428520833505 := by
  unfold tailWord_6695382
  simp only [CollatzResearch.WordTrace]
  refine ⟨15262540214361373065850025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162800428953187979369066933 15262540214361373065850025)
  ·
    refine ⟨11446905160771029799387519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15262540214361373065850025 11446905160771029799387519)
    ·
      refine ⟨17170357741156544699081279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11446905160771029799387519 17170357741156544699081279)
      ·
        refine ⟨25755536611734817048621919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17170357741156544699081279 25755536611734817048621919)
        ·
          refine ⟨38633304917602225572932879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25755536611734817048621919 38633304917602225572932879)
          ·
            refine ⟨57949957376403338359399319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38633304917602225572932879 57949957376403338359399319)
            ·
              refine ⟨86924936064605007539098979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57949957376403338359399319 86924936064605007539098979)
              ·
                refine ⟨130387404096907511308648469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86924936064605007539098979 130387404096907511308648469)
                ·
                  refine ⟨6111909567042539592592897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130387404096907511308648469 6111909567042539592592897)
                  ·
                    refine ⟨4583932175281904694444673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6111909567042539592592897 4583932175281904694444673)
                    ·
                      refine ⟨3437949131461428520833505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4583932175281904694444673 3437949131461428520833505)
                      ·
                        rfl

theorem cell23_6695382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_6695382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695382 prefixEnd_6695382 := by exact prefixLift 6695382
  have htrace : WordTrace (prefixWord ++ tailWord_6695382) baseStart_6695382 baseEnd_6695382 := by
    simpa [prefixWord, tailWord_6695382, baseEnd_6695382] using wordTrace_append hprefix tailTrace_6695382
  have hstable : (prefixWord ++ tailWord_6695382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695382).length < 2 ^ (prefixWord ++ tailWord_6695382).sum := by decide
  have hdescent : baseEnd_6695382 < baseStart_6695382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695405 : List Nat := [1, 5, 1, 3, 1, 3, 1, 1, 7]
def baseStart_6695405 : Nat := 118140960795 + 6695405 * 2 ^ 59
def prefixEnd_6695405 : Nat := 4983230072969 + 3 ^ 40 * 6695405 * 2
def baseEnd_6695405 : Nat := 381995660168497992316211

theorem tailTrace_6695405 : CollatzResearch.WordTrace tailWord_6695405 prefixEnd_6695405 381995660168497992316211 := by
  unfold tailWord_6695405
  simp only [CollatzResearch.WordTrace]
  refine ⟨244201482308698643981687669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162800988205799095987791779 244201482308698643981687669)
  ·
    refine ⟨22893888966440497873283219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244201482308698643981687669 22893888966440497873283219)
    ·
      refine ⟨34340833449660746809924829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22893888966440497873283219 34340833449660746809924829)
      ·
        refine ⟨12877812543622780053721811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34340833449660746809924829 12877812543622780053721811)
        ·
          refine ⟨19316718815434170080582717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12877812543622780053721811 19316718815434170080582717)
          ·
            refine ⟨7243769555787813780218519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19316718815434170080582717 7243769555787813780218519)
            ·
              refine ⟨10865654333681720670327779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7243769555787813780218519 10865654333681720670327779)
              ·
                refine ⟨16298481500522581005491669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10865654333681720670327779 16298481500522581005491669)
                ·
                  refine ⟨381995660168497992316211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16298481500522581005491669 381995660168497992316211)
                  ·
                    rfl

theorem cell23_6695405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_6695405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695405 prefixEnd_6695405 := by exact prefixLift 6695405
  have htrace : WordTrace (prefixWord ++ tailWord_6695405) baseStart_6695405 baseEnd_6695405 := by
    simpa [prefixWord, tailWord_6695405, baseEnd_6695405] using wordTrace_append hprefix tailTrace_6695405
  have hstable : (prefixWord ++ tailWord_6695405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695405).length < 2 ^ (prefixWord ++ tailWord_6695405).sum := by decide
  have hdescent : baseEnd_6695405 < baseStart_6695405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695408 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 2, 5, 2]
def baseStart_6695408 : Nat := 118140960795 + 6695408 * 2 ^ 59
def prefixEnd_6695408 : Nat := 4983230072969 + 3 ^ 40 * 6695408 * 2
def baseEnd_6695408 : Nat := 3437962481958445419108385

theorem tailTrace_6695408 : CollatzResearch.WordTrace tailWord_6695408 prefixEnd_6695408 3437962481958445419108385 := by
  unfold tailWord_6695408
  simp only [CollatzResearch.WordTrace]
  refine ⟨122100795863843887747023439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162801061151791850329364585 122100795863843887747023439)
  ·
    refine ⟨183151193795765831620535159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122100795863843887747023439 183151193795765831620535159)
    ·
      refine ⟨274726790693648747430802739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183151193795765831620535159 274726790693648747430802739)
      ·
        refine ⟨412090186040473121146204109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274726790693648747430802739 412090186040473121146204109)
        ·
          refine ⟨154533819765177420429826541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 412090186040473121146204109 154533819765177420429826541)
          ·
            refine ⟨57950182411941532661184953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154533819765177420429826541 57950182411941532661184953)
            ·
              refine ⟨43462636808956149495888715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57950182411941532661184953 43462636808956149495888715)
              ·
                refine ⟨65193955213434224243833073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43462636808956149495888715 65193955213434224243833073)
                ·
                  refine ⟨48895466410075668182874805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65193955213434224243833073 48895466410075668182874805)
                  ·
                    refine ⟨4583949975944593892144513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48895466410075668182874805 4583949975944593892144513)
                    ·
                      refine ⟨3437962481958445419108385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4583949975944593892144513 3437962481958445419108385)
                      ·
                        rfl

theorem cell23_6695408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 2, 5, 2].length) (baseStart_6695408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695408 prefixEnd_6695408 := by exact prefixLift 6695408
  have htrace : WordTrace (prefixWord ++ tailWord_6695408) baseStart_6695408 baseEnd_6695408 := by
    simpa [prefixWord, tailWord_6695408, baseEnd_6695408] using wordTrace_append hprefix tailTrace_6695408
  have hstable : (prefixWord ++ tailWord_6695408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695408).length < 2 ^ (prefixWord ++ tailWord_6695408).sum := by decide
  have hdescent : baseEnd_6695408 < baseStart_6695408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695411 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 5]
def baseStart_6695411 : Nat := 118140960795 + 6695411 * 2 ^ 59
def prefixEnd_6695411 : Nat := 4983230072969 + 3 ^ 40 * 6695411 * 2
def baseEnd_6695411 : Nat := 3437964022400408907370871

theorem tailTrace_6695411 : CollatzResearch.WordTrace tailWord_6695411 prefixEnd_6695411 3437964022400408907370871 := by
  unfold tailWord_6695411
  simp only [CollatzResearch.WordTrace]
  refine ⟨244201701146676907006406087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162801134097784604670937391 244201701146676907006406087)
  ·
    refine ⟨366302551720015360509609131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244201701146676907006406087 366302551720015360509609131)
    ·
      refine ⟨549453827580023040764413697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366302551720015360509609131 549453827580023040764413697)
      ·
        refine ⟨412090370685017280573310273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 549453827580023040764413697 412090370685017280573310273)
        ·
          refine ⟨309067778013762960429982705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412090370685017280573310273 309067778013762960429982705)
          ·
            refine ⟨231800833510322220322487029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309067778013762960429982705 231800833510322220322487029)
            ·
              refine ⟨21731328141592708155233159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231800833510322220322487029 21731328141592708155233159)
              ·
                refine ⟨32596992212389062232849739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21731328141592708155233159 32596992212389062232849739)
                ·
                  refine ⟨48895488318583593349274609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32596992212389062232849739 48895488318583593349274609)
                  ·
                    refine ⟨36671616238937695011955957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48895488318583593349274609 36671616238937695011955957)
                    ·
                      refine ⟨3437964022400408907370871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36671616238937695011955957 3437964022400408907370871)
                      ·
                        rfl

theorem cell23_6695411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_6695411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695411 prefixEnd_6695411 := by exact prefixLift 6695411
  have htrace : WordTrace (prefixWord ++ tailWord_6695411) baseStart_6695411 baseEnd_6695411 := by
    simpa [prefixWord, tailWord_6695411, baseEnd_6695411] using wordTrace_append hprefix tailTrace_6695411
  have hstable : (prefixWord ++ tailWord_6695411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695411).length < 2 ^ (prefixWord ++ tailWord_6695411).sum := by decide
  have hdescent : baseEnd_6695411 < baseStart_6695411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695458 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_6695458 : Nat := 118140960795 + 6695458 * 2 ^ 59
def prefixEnd_6695458 : Nat := 4983230072969 + 3 ^ 40 * 6695458 * 2
def baseEnd_6695458 : Nat := 3437988155991170223483155

theorem tailTrace_6695458 : CollatzResearch.WordTrace tailWord_6695458 prefixEnd_6695458 3437988155991170223483155 := by
  unfold tailWord_6695458
  simp only [CollatzResearch.WordTrace]
  refine ⟨61050853844376658508341757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162802276918337756022244685 61050853844376658508341757)
  ·
    refine ⟨22894070191641246940628159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61050853844376658508341757 22894070191641246940628159)
    ·
      refine ⟨34341105287461870410942239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22894070191641246940628159 34341105287461870410942239)
      ·
        refine ⟨51511657931192805616413359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34341105287461870410942239 51511657931192805616413359)
        ·
          refine ⟨77267486896789208424620039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51511657931192805616413359 77267486896789208424620039)
          ·
            refine ⟨115901230345183812636930059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77267486896789208424620039 115901230345183812636930059)
            ·
              refine ⟨173851845517775718955395089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115901230345183812636930059 173851845517775718955395089)
              ·
                refine ⟨130388884138331789216546317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173851845517775718955395089 130388884138331789216546317)
                ·
                  refine ⟨48895831551874420956204869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130388884138331789216546317 48895831551874420956204869)
                  ·
                    refine ⟨9167968415976453929288413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48895831551874420956204869 9167968415976453929288413)
                    ·
                      refine ⟨3437988155991170223483155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9167968415976453929288413 3437988155991170223483155)
                      ·
                        rfl

theorem cell23_6695458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_6695458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695458 prefixEnd_6695458 := by exact prefixLift 6695458
  have htrace : WordTrace (prefixWord ++ tailWord_6695458) baseStart_6695458 baseEnd_6695458 := by
    simpa [prefixWord, tailWord_6695458, baseEnd_6695458] using wordTrace_append hprefix tailTrace_6695458
  have hstable : (prefixWord ++ tailWord_6695458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695458).length < 2 ^ (prefixWord ++ tailWord_6695458).sum := by decide
  have hdescent : baseEnd_6695458 < baseStart_6695458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695461 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 8]
def baseStart_6695461 : Nat := 118140960795 + 6695461 * 2 ^ 59
def prefixEnd_6695461 : Nat := 4983230072969 + 3 ^ 40 * 6695461 * 2
def baseEnd_6695461 : Nat := 381998855159237079082849

theorem tailTrace_6695461 : CollatzResearch.WordTrace tailWord_6695461 prefixEnd_6695461 381998855159237079082849 := by
  unfold tailWord_6695461
  simp only [CollatzResearch.WordTrace]
  refine ⟨244203524796495765545726237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162802349864330510363817491 244203524796495765545726237)
  ·
    refine ⟨91576321798685912079647339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244203524796495765545726237 91576321798685912079647339)
    ·
      refine ⟨137364482698028868119471009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91576321798685912079647339 137364482698028868119471009)
      ·
        refine ⟨103023362023521651089603257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137364482698028868119471009 103023362023521651089603257)
        ·
          refine ⟨77267521517641238317202443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103023362023521651089603257 77267521517641238317202443)
          ·
            refine ⟨115901282276461857475803665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77267521517641238317202443 115901282276461857475803665)
            ·
              refine ⟨86925961707346393106852749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115901282276461857475803665 86925961707346393106852749)
              ·
                refine ⟨32597235640254897415069781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86925961707346393106852749 32597235640254897415069781)
                ·
                  refine ⟨381998855159237079082849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32597235640254897415069781 381998855159237079082849)
                  ·
                    rfl

theorem cell23_6695461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 8].length) (baseStart_6695461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695461 prefixEnd_6695461 := by exact prefixLift 6695461
  have htrace : WordTrace (prefixWord ++ tailWord_6695461) baseStart_6695461 baseEnd_6695461 := by
    simpa [prefixWord, tailWord_6695461, baseEnd_6695461] using wordTrace_append hprefix tailTrace_6695461
  have hstable : (prefixWord ++ tailWord_6695461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695461).length < 2 ^ (prefixWord ++ tailWord_6695461).sum := by decide
  have hdescent : baseEnd_6695461 < baseStart_6695461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695545 : List Nat := [1, 2, 1, 3, 3, 2, 1, 4, 1, 1, 4]
def baseStart_6695545 : Nat := 118140960795 + 6695545 * 2 ^ 59
def prefixEnd_6695545 : Nat := 4983230072969 + 3 ^ 40 * 6695545 * 2
def baseEnd_6695545 : Nat := 3438032828808111383095255

theorem tailTrace_6695545 : CollatzResearch.WordTrace tailWord_6695545 prefixEnd_6695545 3438032828808111383095255 := by
  unfold tailWord_6695545
  simp only [CollatzResearch.WordTrace]
  refine ⟨244206588528191447891784089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162804392352127631927856059 244206588528191447891784089)
  ·
    refine ⟨183154941396143585918838067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244206588528191447891784089 183154941396143585918838067)
    ·
      refine ⟨274732412094215378878257101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183154941396143585918838067 274732412094215378878257101)
      ·
        refine ⟨103024654535330767079346413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274732412094215378878257101 103024654535330767079346413)
        ·
          refine ⟨38634245450749037654754905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103024654535330767079346413 38634245450749037654754905)
          ·
            refine ⟨28975684088061778241066179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38634245450749037654754905 28975684088061778241066179)
            ·
              refine ⟨43463526132092667361599269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28975684088061778241066179 43463526132092667361599269)
              ·
                refine ⟨8149411149767375130299863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43463526132092667361599269 8149411149767375130299863)
                ·
                  refine ⟨12224116724651062695449795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8149411149767375130299863 12224116724651062695449795)
                  ·
                    refine ⟨18336175086976594043174693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12224116724651062695449795 18336175086976594043174693)
                    ·
                      refine ⟨3438032828808111383095255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18336175086976594043174693 3438032828808111383095255)
                      ·
                        rfl

theorem cell23_6695545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_6695545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695545 prefixEnd_6695545 := by exact prefixLift 6695545
  have htrace : WordTrace (prefixWord ++ tailWord_6695545) baseStart_6695545 baseEnd_6695545 := by
    simpa [prefixWord, tailWord_6695545, baseEnd_6695545] using wordTrace_append hprefix tailTrace_6695545
  have hstable : (prefixWord ++ tailWord_6695545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695545).length < 2 ^ (prefixWord ++ tailWord_6695545).sum := by decide
  have hdescent : baseEnd_6695545 < baseStart_6695545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695556 : List Nat := [2, 3, 2, 1, 3, 3, 1, 3, 1, 1, 3]
def baseStart_6695556 : Nat := 118140960795 + 6695556 * 2 ^ 59
def prefixEnd_6695556 : Nat := 4983230072969 + 3 ^ 40 * 6695556 * 2
def baseEnd_6695556 : Nat := 3438038477095310840057705

theorem tailTrace_6695556 : CollatzResearch.WordTrace tailWord_6695556 prefixEnd_6695556 3438038477095310840057705 := by
  unfold tailWord_6695556
  simp only [CollatzResearch.WordTrace]
  refine ⟨122103494865575798385217261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162804659820767731180289681 122103494865575798385217261)
  ·
    refine ⟨45788810574590924394456473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122103494865575798385217261 45788810574590924394456473)
    ·
      refine ⟨34341607930943193295842355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45788810574590924394456473 34341607930943193295842355)
      ·
        refine ⟨51512411896414789943763533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34341607930943193295842355 51512411896414789943763533)
        ·
          refine ⟨19317154461155546228911325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51512411896414789943763533 19317154461155546228911325)
          ·
            refine ⟨7243932922933329835841747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19317154461155546228911325 7243932922933329835841747)
            ·
              refine ⟨10865899384399994753762621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7243932922933329835841747 10865899384399994753762621)
              ·
                refine ⟨4074712269149998032660983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10865899384399994753762621 4074712269149998032660983)
                ·
                  refine ⟨6112068403724997048991475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4074712269149998032660983 6112068403724997048991475)
                  ·
                    refine ⟨9168102605587495573487213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6112068403724997048991475 9168102605587495573487213)
                    ·
                      refine ⟨3438038477095310840057705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9168102605587495573487213 3438038477095310840057705)
                      ·
                        rfl

theorem cell23_6695556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_6695556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695556 prefixEnd_6695556 := by exact prefixLift 6695556
  have htrace : WordTrace (prefixWord ++ tailWord_6695556) baseStart_6695556 baseEnd_6695556 := by
    simpa [prefixWord, tailWord_6695556, baseEnd_6695556] using wordTrace_append hprefix tailTrace_6695556
  have hstable : (prefixWord ++ tailWord_6695556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695556).length < 2 ^ (prefixWord ++ tailWord_6695556).sum := by decide
  have hdescent : baseEnd_6695556 < baseStart_6695556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695572 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_6695572 : Nat := 118140960795 + 6695572 * 2 ^ 59
def prefixEnd_6695572 : Nat := 4983230072969 + 3 ^ 40 * 6695572 * 2
def baseEnd_6695572 : Nat := 1146015564261927592485877

theorem tailTrace_6695572 : CollatzResearch.WordTrace tailWord_6695572 prefixEnd_6695572 1146015564261927592485877 := by
  unfold tailWord_6695572
  simp only [CollatzResearch.WordTrace]
  refine ⟨122103786649546815751508485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162805048866062421002011313 122103786649546815751508485)
  ·
    refine ⟨22894459996790027953407841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122103786649546815751508485 22894459996790027953407841)
    ·
      refine ⟨17170844997592520965055881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22894459996790027953407841 17170844997592520965055881)
      ·
        refine ⟨12878133748194390723791911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17170844997592520965055881 12878133748194390723791911)
        ·
          refine ⟨19317200622291586085687867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12878133748194390723791911 19317200622291586085687867)
          ·
            refine ⟨28975800933437379128531801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19317200622291586085687867 28975800933437379128531801)
            ·
              refine ⟨21731850700078034346398851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28975800933437379128531801 21731850700078034346398851)
              ·
                refine ⟨32597776050117051519598277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21731850700078034346398851 32597776050117051519598277)
                ·
                  refine ⟨6112083009396947159924677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32597776050117051519598277 6112083009396947159924677)
                  ·
                    refine ⟨1146015564261927592485877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6112083009396947159924677 1146015564261927592485877)
                    ·
                      rfl

theorem cell23_6695572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_6695572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695572 prefixEnd_6695572 := by exact prefixLift 6695572
  have htrace : WordTrace (prefixWord ++ tailWord_6695572) baseStart_6695572 baseEnd_6695572 := by
    simpa [prefixWord, tailWord_6695572, baseEnd_6695572] using wordTrace_append hprefix tailTrace_6695572
  have hstable : (prefixWord ++ tailWord_6695572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695572).length < 2 ^ (prefixWord ++ tailWord_6695572).sum := by decide
  have hdescent : baseEnd_6695572 < baseStart_6695572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695582 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_6695582 : Nat := 118140960795 + 6695582 * 2 ^ 59
def prefixEnd_6695582 : Nat := 4983230072969 + 3 ^ 40 * 6695582 * 2
def baseEnd_6695582 : Nat := 3438051827592327738332585

theorem tailTrace_6695582 : CollatzResearch.WordTrace tailWord_6695582 prefixEnd_6695582 3438051827592327738332585 := by
  unfold tailWord_6695582
  simp only [CollatzResearch.WordTrace]
  refine ⟨30525992253632175401360125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162805292019371602140587333 30525992253632175401360125)
  ·
    refine ⟨11447247095112065775510047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30525992253632175401360125 11447247095112065775510047)
    ·
      refine ⟨17170870642668098663265071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11447247095112065775510047 17170870642668098663265071)
      ·
        refine ⟨25756305964002147994897607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17170870642668098663265071 25756305964002147994897607)
        ·
          refine ⟨38634458946003221992346411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25756305964002147994897607 38634458946003221992346411)
          ·
            refine ⟨57951688419004832988519617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38634458946003221992346411 57951688419004832988519617)
            ·
              refine ⟨43463766314253624741389713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57951688419004832988519617 43463766314253624741389713)
              ·
                refine ⟨32597824735690218556042285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43463766314253624741389713 32597824735690218556042285)
                ·
                  refine ⟨12224184275883831958515857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32597824735690218556042285 12224184275883831958515857)
                  ·
                    refine ⟨9168138206912873968886893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12224184275883831958515857 9168138206912873968886893)
                    ·
                      refine ⟨3438051827592327738332585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9168138206912873968886893 3438051827592327738332585)
                      ·
                        rfl

theorem cell23_6695582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_6695582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695582 prefixEnd_6695582 := by exact prefixLift 6695582
  have htrace : WordTrace (prefixWord ++ tailWord_6695582) baseStart_6695582 baseEnd_6695582 := by
    simpa [prefixWord, tailWord_6695582, baseEnd_6695582] using wordTrace_append hprefix tailTrace_6695582
  have hstable : (prefixWord ++ tailWord_6695582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695582).length < 2 ^ (prefixWord ++ tailWord_6695582).sum := by decide
  have hdescent : baseEnd_6695582 < baseStart_6695582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695585 : List Nat := [1, 2, 3, 3, 3, 1, 2, 8]
def baseStart_6695585 : Nat := 118140960795 + 6695585 * 2 ^ 59
def prefixEnd_6695585 : Nat := 4983230072969 + 3 ^ 40 * 6695585 * 2
def baseEnd_6695585 : Nat := 127335309927195971355373

theorem tailTrace_6695585 : CollatzResearch.WordTrace tailWord_6695585 prefixEnd_6695585 127335309927195971355373 := by
  unfold tailWord_6695585
  simp only [CollatzResearch.WordTrace]
  refine ⟨244208047448046534723240209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162805364965364356482160139 244208047448046534723240209)
  ·
    refine ⟨183156035586034901042430157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244208047448046534723240209 183156035586034901042430157)
    ·
      refine ⟨68683513344763087890911309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183156035586034901042430157 68683513344763087890911309)
      ·
        refine ⟨25756317504286157959091741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68683513344763087890911309 25756317504286157959091741)
        ·
          refine ⟨9658619064107309234659403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25756317504286157959091741 9658619064107309234659403)
          ·
            refine ⟨14487928596160963851989105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9658619064107309234659403 14487928596160963851989105)
            ·
              refine ⟨10865946447120722888991829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14487928596160963851989105 10865946447120722888991829)
              ·
                refine ⟨127335309927195971355373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10865946447120722888991829 127335309927195971355373)
                ·
                  rfl

theorem cell23_6695585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 8].length) (baseStart_6695585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695585 prefixEnd_6695585 := by exact prefixLift 6695585
  have htrace : WordTrace (prefixWord ++ tailWord_6695585) baseStart_6695585 baseEnd_6695585 := by
    simpa [prefixWord, tailWord_6695585, baseEnd_6695585] using wordTrace_append hprefix tailTrace_6695585
  have hstable : (prefixWord ++ tailWord_6695585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695585).length < 2 ^ (prefixWord ++ tailWord_6695585).sum := by decide
  have hdescent : baseEnd_6695585 < baseStart_6695585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695588 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_6695588 : Nat := 118140960795 + 6695588 * 2 ^ 59
def prefixEnd_6695588 : Nat := 4983230072969 + 3 ^ 40 * 6695588 * 2
def baseEnd_6695588 : Nat := 3438054908476254714857557

theorem tailTrace_6695588 : CollatzResearch.WordTrace tailWord_6695588 prefixEnd_6695588 3438054908476254714857557 := by
  unfold tailWord_6695588
  simp only [CollatzResearch.WordTrace]
  refine ⟨122104078433517833117799709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162805437911357110823732945 122104078433517833117799709)
  ·
    refine ⟨45789029412569187419174891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122104078433517833117799709 45789029412569187419174891)
    ·
      refine ⟨68683544118853781128762337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45789029412569187419174891 68683544118853781128762337)
      ·
        refine ⟨51512658089140335846571753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68683544118853781128762337 51512658089140335846571753)
        ·
          refine ⟨38634493566855251884928815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51512658089140335846571753 38634493566855251884928815)
          ·
            refine ⟨57951740350282877827393223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38634493566855251884928815 57951740350282877827393223)
            ·
              refine ⟨86927610525424316741089835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57951740350282877827393223 86927610525424316741089835)
              ·
                refine ⟨130391415788136475111634753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86927610525424316741089835 130391415788136475111634753)
                ·
                  refine ⟨97793561841102356333726065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130391415788136475111634753 97793561841102356333726065)
                  ·
                    refine ⟨73345171380826767250294549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97793561841102356333726065 73345171380826767250294549)
                    ·
                      refine ⟨3438054908476254714857557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73345171380826767250294549 3438054908476254714857557)
                      ·
                        rfl

theorem cell23_6695588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_6695588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695588 prefixEnd_6695588 := by exact prefixLift 6695588
  have htrace : WordTrace (prefixWord ++ tailWord_6695588) baseStart_6695588 baseEnd_6695588 := by
    simpa [prefixWord, tailWord_6695588, baseEnd_6695588] using wordTrace_append hprefix tailTrace_6695588
  have hstable : (prefixWord ++ tailWord_6695588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695588).length < 2 ^ (prefixWord ++ tailWord_6695588).sum := by decide
  have hdescent : baseEnd_6695588 < baseStart_6695588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695652 : List Nat := [2, 3, 1, 1, 1, 4, 1, 3, 1, 4, 2]
def baseStart_6695652 : Nat := 118140960795 + 6695652 * 2 ^ 59
def prefixEnd_6695652 : Nat := 4983230072969 + 3 ^ 40 * 6695652 * 2
def baseEnd_6695652 : Nat := 3438087771238142464457263

theorem tailTrace_6695652 : CollatzResearch.WordTrace tailWord_6695652 prefixEnd_6695652 3438087771238142464457263 := by
  unfold tailWord_6695652
  simp only [CollatzResearch.WordTrace]
  refine ⟨122105245569401902582964605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162806994092535870110619473 122105245569401902582964605)
  ·
    refine ⟨45789467088525713468611727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122105245569401902582964605 45789467088525713468611727)
    ·
      refine ⟨68684200632788570202917591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45789467088525713468611727 68684200632788570202917591)
      ·
        refine ⟨103026300949182855304376387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68684200632788570202917591 103026300949182855304376387)
        ·
          refine ⟨154539451423774282956564581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103026300949182855304376387 154539451423774282956564581)
          ·
            refine ⟨28976147141957678054355859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154539451423774282956564581 28976147141957678054355859)
            ·
              refine ⟨43464220712936517081533789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28976147141957678054355859 43464220712936517081533789)
              ·
                refine ⟨16299082767351193905575171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43464220712936517081533789 16299082767351193905575171)
                ·
                  refine ⟨24448624151026790858362757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16299082767351193905575171 24448624151026790858362757)
                  ·
                    refine ⟨4584117028317523285943017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24448624151026790858362757 4584117028317523285943017)
                    ·
                      refine ⟨3438087771238142464457263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4584117028317523285943017 3438087771238142464457263)
                      ·
                        rfl

theorem cell23_6695652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_6695652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695652 prefixEnd_6695652 := by exact prefixLift 6695652
  have htrace : WordTrace (prefixWord ++ tailWord_6695652) baseStart_6695652 baseEnd_6695652 := by
    simpa [prefixWord, tailWord_6695652, baseEnd_6695652] using wordTrace_append hprefix tailTrace_6695652
  have hstable : (prefixWord ++ tailWord_6695652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695652).length < 2 ^ (prefixWord ++ tailWord_6695652).sum := by decide
  have hdescent : baseEnd_6695652 < baseStart_6695652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695682 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_6695682 : Nat := 118140960795 + 6695682 * 2 ^ 59
def prefixEnd_6695682 : Nat := 4983230072969 + 3 ^ 40 * 6695682 * 2
def baseEnd_6695682 : Nat := 3438103175657777347082125

theorem tailTrace_6695682 : CollatzResearch.WordTrace tailWord_6695682 prefixEnd_6695682 3438103175657777347082125 := by
  unfold tailWord_6695682
  simp only [CollatzResearch.WordTrace]
  refine ⟨61052896332173780072380325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162807723552463413526347533 61052896332173780072380325)
  ·
    refine ⟨11447418062282583763571311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61052896332173780072380325 11447418062282583763571311)
    ·
      refine ⟨17171127093423875645356967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11447418062282583763571311 17171127093423875645356967)
      ·
        refine ⟨25756690640135813468035451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17171127093423875645356967 25756690640135813468035451)
        ·
          refine ⟨38635035960203720202053177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25756690640135813468035451 38635035960203720202053177)
          ·
            refine ⟨28976276970152790151539883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38635035960203720202053177 28976276970152790151539883)
            ·
              refine ⟨43464415455229185227309825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28976276970152790151539883 43464415455229185227309825)
              ·
                refine ⟨32598311591421888920482369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43464415455229185227309825 32598311591421888920482369)
                ·
                  refine ⟨24448733693566416690361777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32598311591421888920482369 24448733693566416690361777)
                  ·
                    refine ⟨18336550270174812517771333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24448733693566416690361777 18336550270174812517771333)
                    ·
                      refine ⟨3438103175657777347082125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18336550270174812517771333 3438103175657777347082125)
                      ·
                        rfl

theorem cell23_6695682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_6695682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695682 prefixEnd_6695682 := by exact prefixLift 6695682
  have htrace : WordTrace (prefixWord ++ tailWord_6695682) baseStart_6695682 baseEnd_6695682 := by
    simpa [prefixWord, tailWord_6695682, baseEnd_6695682] using wordTrace_append hprefix tailTrace_6695682
  have hstable : (prefixWord ++ tailWord_6695682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695682).length < 2 ^ (prefixWord ++ tailWord_6695682).sum := by decide
  have hdescent : baseEnd_6695682 < baseStart_6695682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695703 : List Nat := [1, 1, 3, 4, 3, 1, 3, 1, 2, 2, 2]
def baseStart_6695703 : Nat := 118140960795 + 6695703 * 2 ^ 59
def prefixEnd_6695703 : Nat := 4983230072969 + 3 ^ 40 * 6695703 * 2
def baseEnd_6695703 : Nat := 3438113958751521764919529

theorem tailTrace_6695703 : CollatzResearch.WordTrace tailWord_6695703 prefixEnd_6695703 3438113958751521764919529 := by
  unfold tailWord_6695703
  simp only [CollatzResearch.WordTrace]
  refine ⟨244212351261619040876035763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162808234174412693917357175 244212351261619040876035763)
  ·
    refine ⟨366318526892428561314053645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244212351261619040876035763 366318526892428561314053645)
    ·
      refine ⟨137369447584660710492770117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366318526892428561314053645 137369447584660710492770117)
      ·
        refine ⟨25756771422123883217394397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137369447584660710492770117 25756771422123883217394397)
        ·
          refine ⟨9658789283296456206522899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25756771422123883217394397 9658789283296456206522899)
          ·
            refine ⟨14488183924944684309784349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9658789283296456206522899 14488183924944684309784349)
            ·
              refine ⟨5433068971854256616169131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14488183924944684309784349 5433068971854256616169131)
              ·
                refine ⟨8149603457781384924253697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5433068971854256616169131 8149603457781384924253697)
                ·
                  refine ⟨6112202593336038693190273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8149603457781384924253697 6112202593336038693190273)
                  ·
                    refine ⟨4584151945002029019892705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6112202593336038693190273 4584151945002029019892705)
                    ·
                      refine ⟨3438113958751521764919529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4584151945002029019892705 3438113958751521764919529)
                      ·
                        rfl

theorem cell23_6695703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_6695703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695703 prefixEnd_6695703 := by exact prefixLift 6695703
  have htrace : WordTrace (prefixWord ++ tailWord_6695703) baseStart_6695703 baseEnd_6695703 := by
    simpa [prefixWord, tailWord_6695703, baseEnd_6695703] using wordTrace_append hprefix tailTrace_6695703
  have hstable : (prefixWord ++ tailWord_6695703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695703).length < 2 ^ (prefixWord ++ tailWord_6695703).sum := by decide
  have hdescent : baseEnd_6695703 < baseStart_6695703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695726 : List Nat := [4, 1, 3, 2, 1, 3, 1, 3, 5]
def baseStart_6695726 : Nat := 118140960795 + 6695726 * 2 ^ 59
def prefixEnd_6695726 : Nat := 4983230072969 + 3 ^ 40 * 6695726 * 2
def baseEnd_6695726 : Nat := 382013974311841686103547

theorem tailTrace_6695726 : CollatzResearch.WordTrace tailWord_6695726 prefixEnd_6695726 382013974311841686103547 := by
  unfold tailWord_6695726
  simp only [CollatzResearch.WordTrace]
  refine ⟨30526648767566964475515379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162808793427023810536082021 30526648767566964475515379)
  ·
    refine ⟨45789973151350446713273069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30526648767566964475515379 45789973151350446713273069)
    ·
      refine ⟨17171239931756417517477401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45789973151350446713273069 17171239931756417517477401)
      ·
        refine ⟨12878429948817313138108051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17171239931756417517477401 12878429948817313138108051)
        ·
          refine ⟨19317644923225969707162077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12878429948817313138108051 19317644923225969707162077)
          ·
            refine ⟨7244116846209738640185779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19317644923225969707162077 7244116846209738640185779)
            ·
              refine ⟨10866175269314607960278669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7244116846209738640185779 10866175269314607960278669)
              ·
                refine ⟨4074815725992977985104501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10866175269314607960278669 4074815725992977985104501)
                ·
                  refine ⟨382013974311841686103547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4074815725992977985104501 382013974311841686103547)
                  ·
                    rfl

theorem cell23_6695726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_6695726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695726 prefixEnd_6695726 := by exact prefixLift 6695726
  have htrace : WordTrace (prefixWord ++ tailWord_6695726) baseStart_6695726 baseEnd_6695726 := by
    simpa [prefixWord, tailWord_6695726, baseEnd_6695726] using wordTrace_append hprefix tailTrace_6695726
  have hstable : (prefixWord ++ tailWord_6695726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695726).length < 2 ^ (prefixWord ++ tailWord_6695726).sum := by decide
  have hdescent : baseEnd_6695726 < baseStart_6695726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695762 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_6695762 : Nat := 118140960795 + 6695762 * 2 ^ 59
def prefixEnd_6695762 : Nat := 4983230072969 + 3 ^ 40 * 6695762 * 2
def baseEnd_6695762 : Nat := 3438144254110137034081757

theorem tailTrace_6695762 : CollatzResearch.WordTrace tailWord_6695762 prefixEnd_6695762 3438144254110137034081757 := by
  unfold tailWord_6695762
  simp only [CollatzResearch.WordTrace]
  refine ⟨61053625792101323488108385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162809668778936862634955693 61053625792101323488108385)
  ·
    refine ⟨45790219344075992616081289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61053625792101323488108385 45790219344075992616081289)
    ·
      refine ⟨34342664508056994462060967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45790219344075992616081289 34342664508056994462060967)
      ·
        refine ⟨51513996762085491693091451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34342664508056994462060967 51513996762085491693091451)
        ·
          refine ⟨77270995143128237539637177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51513996762085491693091451 77270995143128237539637177)
          ·
            refine ⟨57953246357346178154727883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77270995143128237539637177 57953246357346178154727883)
            ·
              refine ⟨86929869536019267232091825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57953246357346178154727883 86929869536019267232091825)
              ·
                refine ⟨65197402152014450424068869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86929869536019267232091825 65197402152014450424068869)
                ·
                  refine ⟨12224512903502709454512913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65197402152014450424068869 12224512903502709454512913)
                  ·
                    refine ⟨9168384677627032090884685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12224512903502709454512913 9168384677627032090884685)
                    ·
                      refine ⟨3438144254110137034081757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9168384677627032090884685 3438144254110137034081757)
                      ·
                        rfl

theorem cell23_6695762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_6695762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695762 prefixEnd_6695762 := by exact prefixLift 6695762
  have htrace : WordTrace (prefixWord ++ tailWord_6695762) baseStart_6695762 baseEnd_6695762 := by
    simpa [prefixWord, tailWord_6695762, baseEnd_6695762] using wordTrace_append hprefix tailTrace_6695762
  have hstable : (prefixWord ++ tailWord_6695762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695762).length < 2 ^ (prefixWord ++ tailWord_6695762).sum := by decide
  have hdescent : baseEnd_6695762 < baseStart_6695762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695779 : List Nat := [1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 3]
def baseStart_6695779 : Nat := 118140960795 + 6695779 * 2 ^ 59
def prefixEnd_6695779 : Nat := 4983230072969 + 3 ^ 40 * 6695779 * 2
def baseEnd_6695779 : Nat := 3438152983281263467569179

theorem tailTrace_6695779 : CollatzResearch.WordTrace tailWord_6695779 prefixEnd_6695779 3438152983281263467569179 := by
  unfold tailWord_6695779
  simp only [CollatzResearch.WordTrace]
  refine ⟨244215123209343705855802391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162810082139562470570534927 244215123209343705855802391)
  ·
    refine ⟨366322684814015558783703587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244215123209343705855802391 366322684814015558783703587)
    ·
      refine ⟨549484027221023338175555381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366322684814015558783703587 549484027221023338175555381)
      ·
        refine ⟨51514127551970937953958317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 549484027221023338175555381 51514127551970937953958317)
        ·
          refine ⟨19317797831989101732734369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51514127551970937953958317 19317797831989101732734369)
          ·
            refine ⟨14488348373991826299550777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19317797831989101732734369 14488348373991826299550777)
            ·
              refine ⟨10866261280493869724663083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14488348373991826299550777 10866261280493869724663083)
              ·
                refine ⟨16299391920740804586994625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10866261280493869724663083 16299391920740804586994625)
                ·
                  refine ⟨12224543940555603440245969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16299391920740804586994625 12224543940555603440245969)
                  ·
                    refine ⟨9168407955416702580184477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12224543940555603440245969 9168407955416702580184477)
                    ·
                      refine ⟨3438152983281263467569179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9168407955416702580184477 3438152983281263467569179)
                      ·
                        rfl

theorem cell23_6695779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_6695779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695779 prefixEnd_6695779 := by exact prefixLift 6695779
  have htrace : WordTrace (prefixWord ++ tailWord_6695779) baseStart_6695779 baseEnd_6695779 := by
    simpa [prefixWord, tailWord_6695779, baseEnd_6695779] using wordTrace_append hprefix tailTrace_6695779
  have hstable : (prefixWord ++ tailWord_6695779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695779).length < 2 ^ (prefixWord ++ tailWord_6695779).sum := by decide
  have hdescent : baseEnd_6695779 < baseStart_6695779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695802 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2]
def baseStart_6695802 : Nat := 118140960795 + 6695802 * 2 ^ 59
def prefixEnd_6695802 : Nat := 4983230072969 + 3 ^ 40 * 6695802 * 2
def baseEnd_6695802 : Nat := 3438164793336316877581573

theorem tailTrace_6695802 : CollatzResearch.WordTrace tailWord_6695802 prefixEnd_6695802 3438164793336316877581573 := by
  unfold tailWord_6695802
  simp only [CollatzResearch.WordTrace]
  refine ⟨61053990522065095195972415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162810641392173587189259773 61053990522065095195972415)
  ·
    refine ⟨91580985783097642793958623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61053990522065095195972415 91580985783097642793958623)
    ·
      refine ⟨137371478674646464190937935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91580985783097642793958623 137371478674646464190937935)
      ·
        refine ⟨206057218011969696286406903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137371478674646464190937935 206057218011969696286406903)
        ·
          refine ⟨309085827017954544429610355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206057218011969696286406903 309085827017954544429610355)
          ·
            refine ⟨463628740526931816644415533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309085827017954544429610355 463628740526931816644415533)
            ·
              refine ⟨173860777697599431241655825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 463628740526931816644415533 173860777697599431241655825)
              ·
                refine ⟨130395583273199573431241869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173860777697599431241655825 130395583273199573431241869)
                ·
                  refine ⟨48898343727449840036715701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130395583273199573431241869 48898343727449840036715701)
                  ·
                    refine ⟨4584219724448422503442097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48898343727449840036715701 4584219724448422503442097)
                    ·
                      refine ⟨3438164793336316877581573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4584219724448422503442097 3438164793336316877581573)
                      ·
                        rfl

theorem cell23_6695802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2].length) (baseStart_6695802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695802 prefixEnd_6695802 := by exact prefixLift 6695802
  have htrace : WordTrace (prefixWord ++ tailWord_6695802) baseStart_6695802 baseEnd_6695802 := by
    simpa [prefixWord, tailWord_6695802, baseEnd_6695802] using wordTrace_append hprefix tailTrace_6695802
  have hstable : (prefixWord ++ tailWord_6695802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695802).length < 2 ^ (prefixWord ++ tailWord_6695802).sum := by decide
  have hdescent : baseEnd_6695802 < baseStart_6695802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695830 : List Nat := [5, 3, 1, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_6695830 : Nat := 118140960795 + 6695830 * 2 ^ 59
def prefixEnd_6695830 : Nat := 4983230072969 + 3 ^ 40 * 6695830 * 2
def baseEnd_6695830 : Nat := 3438179170794642768031445

theorem tailTrace_6695830 : CollatzResearch.WordTrace tailWord_6695830 prefixEnd_6695830 3438179170794642768031445 := by
  unfold tailWord_6695830
  simp only [CollatzResearch.WordTrace]
  refine ⟨15263561458259933847869309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162811322221439294377272629 15263561458259933847869309)
  ·
    refine ⟨5723835546847475192950991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15263561458259933847869309 5723835546847475192950991)
    ·
      refine ⟨8585753320271212789426487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5723835546847475192950991 8585753320271212789426487)
      ·
        refine ⟨12878629980406819184139731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8585753320271212789426487 12878629980406819184139731)
        ·
          refine ⟨19317944970610228776209597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12878629980406819184139731 19317944970610228776209597)
          ·
            refine ⟨7244229363978835791078599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19317944970610228776209597 7244229363978835791078599)
            ·
              refine ⟨10866344045968253686617899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7244229363978835791078599 10866344045968253686617899)
              ·
                refine ⟨16299516068952380529926849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10866344045968253686617899 16299516068952380529926849)
                ·
                  refine ⟨12224637051714285397445137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16299516068952380529926849 12224637051714285397445137)
                  ·
                    refine ⟨9168477788785714048083853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12224637051714285397445137 9168477788785714048083853)
                    ·
                      refine ⟨3438179170794642768031445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9168477788785714048083853 3438179170794642768031445)
                      ·
                        rfl

theorem cell23_6695830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_6695830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695830 prefixEnd_6695830 := by exact prefixLift 6695830
  have htrace : WordTrace (prefixWord ++ tailWord_6695830) baseStart_6695830 baseEnd_6695830 := by
    simpa [prefixWord, tailWord_6695830, baseEnd_6695830] using wordTrace_append hprefix tailTrace_6695830
  have hstable : (prefixWord ++ tailWord_6695830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695830).length < 2 ^ (prefixWord ++ tailWord_6695830).sum := by decide
  have hdescent : baseEnd_6695830 < baseStart_6695830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695836 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 1, 5, 2]
def baseStart_6695836 : Nat := 118140960795 + 6695836 * 2 ^ 59
def prefixEnd_6695836 : Nat := 4983230072969 + 3 ^ 40 * 6695836 * 2
def baseEnd_6695836 : Nat := 3438182251678569744556417

theorem tailTrace_6695836 : CollatzResearch.WordTrace tailWord_6695836 prefixEnd_6695836 3438182251678569744556417 := by
  unfold tailWord_6695836
  simp only [CollatzResearch.WordTrace]
  refine ⟨122108601085068602295313681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162811468113424803060418241 122108601085068602295313681)
  ·
    refine ⟨91581450813801451721485261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122108601085068602295313681 91581450813801451721485261)
    ·
      refine ⟨34343044055175544395556973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91581450813801451721485261 34343044055175544395556973)
      ·
        refine ⟨12878641520690829148333865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34343044055175544395556973 12878641520690829148333865)
        ·
          refine ⟨9658981140518121861250399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12878641520690829148333865 9658981140518121861250399)
          ·
            refine ⟨14488471710777182791875599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9658981140518121861250399 14488471710777182791875599)
            ·
              refine ⟨21732707566165774187813399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14488471710777182791875599 21732707566165774187813399)
              ·
                refine ⟨32599061349248661281720099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21732707566165774187813399 32599061349248661281720099)
                ·
                  refine ⟨48898592023872991922580149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32599061349248661281720099 48898592023872991922580149)
                  ·
                    refine ⟨4584243002238092992741889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48898592023872991922580149 4584243002238092992741889)
                    ·
                      refine ⟨3438182251678569744556417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4584243002238092992741889 3438182251678569744556417)
                      ·
                        rfl

theorem cell23_6695836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_6695836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695836 prefixEnd_6695836 := by exact prefixLift 6695836
  have htrace : WordTrace (prefixWord ++ tailWord_6695836) baseStart_6695836 baseEnd_6695836 := by
    simpa [prefixWord, tailWord_6695836, baseEnd_6695836] using wordTrace_append hprefix tailTrace_6695836
  have hstable : (prefixWord ++ tailWord_6695836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695836).length < 2 ^ (prefixWord ++ tailWord_6695836).sum := by decide
  have hdescent : baseEnd_6695836 < baseStart_6695836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695845 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 5, 1, 6]
def baseStart_6695845 : Nat := 118140960795 + 6695845 * 2 ^ 59
def prefixEnd_6695845 : Nat := 4983230072969 + 3 ^ 40 * 6695845 * 2
def baseEnd_6695845 : Nat := 3438186873004460209343875

theorem tailTrace_6695845 : CollatzResearch.WordTrace tailWord_6695845 prefixEnd_6695845 3438186873004460209343875 := by
  unfold tailWord_6695845
  simp only [CollatzResearch.WordTrace]
  refine ⟨244217530427104599127704989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162811686951403066085136659 244217530427104599127704989)
  ·
    refine ⟨91581573910164224672889371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244217530427104599127704989 91581573910164224672889371)
    ·
      refine ⟨137372360865246337009334057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91581573910164224672889371 137372360865246337009334057)
      ·
        refine ⟨103029270648934752757000543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137372360865246337009334057 103029270648934752757000543)
        ·
          refine ⟨154543905973402129135500815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103029270648934752757000543 154543905973402129135500815)
          ·
            refine ⟨231815858960103193703251223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154543905973402129135500815 231815858960103193703251223)
            ·
              refine ⟨347723788440154790554876835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231815858960103193703251223 347723788440154790554876835)
              ·
                refine ⟨521585682660232185832315253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347723788440154790554876835 521585682660232185832315253)
                ·
                  refine ⟨48898657749396767421779555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 521585682660232185832315253 48898657749396767421779555)
                  ·
                    refine ⟨73347986624095151132669333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48898657749396767421779555 73347986624095151132669333)
                    ·
                      refine ⟨3438186873004460209343875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73347986624095151132669333 3438186873004460209343875)
                      ·
                        rfl

theorem cell23_6695845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_6695845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695845 prefixEnd_6695845 := by exact prefixLift 6695845
  have htrace : WordTrace (prefixWord ++ tailWord_6695845) baseStart_6695845 baseEnd_6695845 := by
    simpa [prefixWord, tailWord_6695845, baseEnd_6695845] using wordTrace_append hprefix tailTrace_6695845
  have hstable : (prefixWord ++ tailWord_6695845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695845).length < 2 ^ (prefixWord ++ tailWord_6695845).sum := by decide
  have hdescent : baseEnd_6695845 < baseStart_6695845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695849 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 5, 2, 2]
def baseStart_6695849 : Nat := 118140960795 + 6695849 * 2 ^ 59
def prefixEnd_6695849 : Nat := 4983230072969 + 3 ^ 40 * 6695849 * 2
def baseEnd_6695849 : Nat := 3438188926927078193693857

theorem tailTrace_6695849 : CollatzResearch.WordTrace tailWord_6695849 prefixEnd_6695849 3438188926927078193693857 := by
  unfold tailWord_6695849
  simp only [CollatzResearch.WordTrace]
  refine ⟨244217676319090107810850601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162811784212726738540567067 244217676319090107810850601)
  ·
    refine ⟨183163257239317580858137951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244217676319090107810850601 183163257239317580858137951)
    ·
      refine ⟨274744885858976371287206927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183163257239317580858137951 274744885858976371287206927)
      ·
        refine ⟨412117328788464556930810391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274744885858976371287206927 412117328788464556930810391)
        ·
          refine ⟨618175993182696835396215587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412117328788464556930810391 618175993182696835396215587)
          ·
            refine ⟨927263989774045253094323381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618175993182696835396215587 927263989774045253094323381)
            ·
              refine ⟨86930999041316742477592817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 927263989774045253094323381 86930999041316742477592817)
              ·
                refine ⟨65198249280987556858194613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86930999041316742477592817 65198249280987556858194613)
                ·
                  refine ⟨6112335870092583455455745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65198249280987556858194613 6112335870092583455455745)
                  ·
                    refine ⟨4584251902569437591591809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6112335870092583455455745 4584251902569437591591809)
                    ·
                      refine ⟨3438188926927078193693857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4584251902569437591591809 3438188926927078193693857)
                      ·
                        rfl

theorem cell23_6695849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 2, 2].length) (baseStart_6695849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695849 prefixEnd_6695849 := by exact prefixLift 6695849
  have htrace : WordTrace (prefixWord ++ tailWord_6695849) baseStart_6695849 baseEnd_6695849 := by
    simpa [prefixWord, tailWord_6695849, baseEnd_6695849] using wordTrace_append hprefix tailTrace_6695849
  have hstable : (prefixWord ++ tailWord_6695849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695849).length < 2 ^ (prefixWord ++ tailWord_6695849).sum := by decide
  have hdescent : baseEnd_6695849 < baseStart_6695849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695860 : List Nat := [2, 5, 2, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_6695860 : Nat := 118140960795 + 6695860 * 2 ^ 59
def prefixEnd_6695860 : Nat := 4983230072969 + 3 ^ 40 * 6695860 * 2
def baseEnd_6695860 : Nat := 3438194575214277650656307

theorem tailTrace_6695860 : CollatzResearch.WordTrace tailWord_6695860 prefixEnd_6695860 3438194575214277650656307 := by
  unfold tailWord_6695860
  simp only [CollatzResearch.WordTrace]
  refine ⟨122109038761025128344750517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162812051681366837793000689 122109038761025128344750517)
  ·
    refine ⟨11447722383846105782320361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122109038761025128344750517 11447722383846105782320361)
    ·
      refine ⟨8585791787884579336740271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11447722383846105782320361 8585791787884579336740271)
      ·
        refine ⟨12878687681826869005110407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8585791787884579336740271 12878687681826869005110407)
        ·
          refine ⟨19318031522740303507665611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12878687681826869005110407 19318031522740303507665611)
          ·
            refine ⟨28977047284110455261498417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19318031522740303507665611 28977047284110455261498417)
            ·
              refine ⟨21732785463082841446123813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28977047284110455261498417 21732785463082841446123813)
              ·
                refine ⟨4074897274328032771148215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21732785463082841446123813 4074897274328032771148215)
                ·
                  refine ⟨6112345911492049156722323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4074897274328032771148215 6112345911492049156722323)
                  ·
                    refine ⟨9168518867238073735083485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6112345911492049156722323 9168518867238073735083485)
                    ·
                      refine ⟨3438194575214277650656307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9168518867238073735083485 3438194575214277650656307)
                      ·
                        rfl

theorem cell23_6695860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_6695860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695860 prefixEnd_6695860 := by exact prefixLift 6695860
  have htrace : WordTrace (prefixWord ++ tailWord_6695860) baseStart_6695860 baseEnd_6695860 := by
    simpa [prefixWord, tailWord_6695860, baseEnd_6695860] using wordTrace_append hprefix tailTrace_6695860
  have hstable : (prefixWord ++ tailWord_6695860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695860).length < 2 ^ (prefixWord ++ tailWord_6695860).sum := by decide
  have hdescent : baseEnd_6695860 < baseStart_6695860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695866 : List Nat := [3, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2]
def baseStart_6695866 : Nat := 118140960795 + 6695866 * 2 ^ 59
def prefixEnd_6695866 : Nat := 4983230072969 + 3 ^ 40 * 6695866 * 2
def baseEnd_6695866 : Nat := 3438197656098204627181279

theorem tailTrace_6695866 : CollatzResearch.WordTrace tailWord_6695866 prefixEnd_6695866 3438197656098204627181279 := by
  unfold tailWord_6695866
  simp only [CollatzResearch.WordTrace]
  refine ⟨61054574090007129928554863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162812197573352346476146301 61054574090007129928554863)
  ·
    refine ⟨91581861135010694892832295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61054574090007129928554863 91581861135010694892832295)
    ·
      refine ⟨137372791702516042339248443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91581861135010694892832295 137372791702516042339248443)
      ·
        refine ⟨206059187553774063508872665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137372791702516042339248443 206059187553774063508872665)
        ·
          refine ⟨154544390665330547631654499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206059187553774063508872665 154544390665330547631654499)
          ·
            refine ⟨231816585997995821447481749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154544390665330547631654499 231816585997995821447481749)
            ·
              refine ⟨10866402468656054130350707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 231816585997995821447481749 10866402468656054130350707)
              ·
                refine ⟨16299603702984081195526061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10866402468656054130350707 16299603702984081195526061)
                ·
                  refine ⟨6112351388619030448322273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16299603702984081195526061 6112351388619030448322273)
                  ·
                    refine ⟨4584263541464272836241705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6112351388619030448322273 4584263541464272836241705)
                    ·
                      refine ⟨3438197656098204627181279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4584263541464272836241705 3438197656098204627181279)
                      ·
                        rfl

theorem cell23_6695866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2].length) (baseStart_6695866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695866 prefixEnd_6695866 := by exact prefixLift 6695866
  have htrace : WordTrace (prefixWord ++ tailWord_6695866) baseStart_6695866 baseEnd_6695866 := by
    simpa [prefixWord, tailWord_6695866, baseEnd_6695866] using wordTrace_append hprefix tailTrace_6695866
  have hstable : (prefixWord ++ tailWord_6695866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695866).length < 2 ^ (prefixWord ++ tailWord_6695866).sum := by decide
  have hdescent : baseEnd_6695866 < baseStart_6695866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695869 : List Nat := [1, 4, 1, 2, 4, 1, 1, 2, 1, 1, 5]
def baseStart_6695869 : Nat := 118140960795 + 6695869 * 2 ^ 59
def prefixEnd_6695869 : Nat := 4983230072969 + 3 ^ 40 * 6695869 * 2
def baseEnd_6695869 : Nat := 3438199196540168115443765

theorem tailTrace_6695869 : CollatzResearch.WordTrace tailWord_6695869 prefixEnd_6695869 3438199196540168115443765 := by
  unfold tailWord_6695869
  simp only [CollatzResearch.WordTrace]
  refine ⟨244218405779017651226578661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162812270519345100817719107 244218405779017651226578661)
  ·
    refine ⟨45790951083565809604983499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244218405779017651226578661 45790951083565809604983499)
    ·
      refine ⟨68686426625348714407475249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45790951083565809604983499 68686426625348714407475249)
      ·
        refine ⟨51514819969011535805606437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68686426625348714407475249 51514819969011535805606437)
        ·
          refine ⟨9659028744189662963551207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51514819969011535805606437 9659028744189662963551207)
          ·
            refine ⟨14488543116284494445326811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9659028744189662963551207 14488543116284494445326811)
            ·
              refine ⟨21732814674426741667990217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14488543116284494445326811 21732814674426741667990217)
              ·
                refine ⟨16299611005820056250992663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21732814674426741667990217 16299611005820056250992663)
                ·
                  refine ⟨24449416508730084376488995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16299611005820056250992663 24449416508730084376488995)
                  ·
                    refine ⟨36674124763095126564733493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24449416508730084376488995 36674124763095126564733493)
                    ·
                      refine ⟨3438199196540168115443765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36674124763095126564733493 3438199196540168115443765)
                      ·
                        rfl

theorem cell23_6695869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_6695869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695869 prefixEnd_6695869 := by exact prefixLift 6695869
  have htrace : WordTrace (prefixWord ++ tailWord_6695869) baseStart_6695869 baseEnd_6695869 := by
    simpa [prefixWord, tailWord_6695869, baseEnd_6695869] using wordTrace_append hprefix tailTrace_6695869
  have hstable : (prefixWord ++ tailWord_6695869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695869).length < 2 ^ (prefixWord ++ tailWord_6695869).sum := by decide
  have hdescent : baseEnd_6695869 < baseStart_6695869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695875 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 6]
def baseStart_6695875 : Nat := 118140960795 + 6695875 * 2 ^ 59
def prefixEnd_6695875 : Nat := 4983230072969 + 3 ^ 40 * 6695875 * 2
def baseEnd_6695875 : Nat := 3438202277424095091968737

theorem tailTrace_6695875 : CollatzResearch.WordTrace tailWord_6695875 prefixEnd_6695875 3438202277424095091968737 := by
  unfold tailWord_6695875
  simp only [CollatzResearch.WordTrace]
  refine ⟨244218624616995914251297079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162812416411330609500864719 244218624616995914251297079)
  ·
    refine ⟨366327936925493871376945619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244218624616995914251297079 366327936925493871376945619)
    ·
      refine ⟨549491905388240807065418429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366327936925493871376945619 549491905388240807065418429)
      ·
        refine ⟨206059464520590302649531911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 549491905388240807065418429 206059464520590302649531911)
        ·
          refine ⟨309089196780885453974297867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206059464520590302649531911 309089196780885453974297867)
          ·
            refine ⟨463633795171328180961446801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309089196780885453974297867 463633795171328180961446801)
            ·
              refine ⟨347725346378496135721085101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463633795171328180961446801 347725346378496135721085101)
              ·
                refine ⟨130397004891936050895406913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347725346378496135721085101 130397004891936050895406913)
                ·
                  refine ⟨97797753668952038171555185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130397004891936050895406913 97797753668952038171555185)
                  ·
                    refine ⟨73348315251714028628666389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97797753668952038171555185 73348315251714028628666389)
                    ·
                      refine ⟨3438202277424095091968737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73348315251714028628666389 3438202277424095091968737)
                      ·
                        rfl

theorem cell23_6695875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_6695875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695875 prefixEnd_6695875 := by exact prefixLift 6695875
  have htrace : WordTrace (prefixWord ++ tailWord_6695875) baseStart_6695875 baseEnd_6695875 := by
    simpa [prefixWord, tailWord_6695875, baseEnd_6695875] using wordTrace_append hprefix tailTrace_6695875
  have hstable : (prefixWord ++ tailWord_6695875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695875).length < 2 ^ (prefixWord ++ tailWord_6695875).sum := by decide
  have hdescent : baseEnd_6695875 < baseStart_6695875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695886 : List Nat := [4, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3]
def baseStart_6695886 : Nat := 118140960795 + 6695886 * 2 ^ 59
def prefixEnd_6695886 : Nat := 4983230072969 + 3 ^ 40 * 6695886 * 2
def baseEnd_6695886 : Nat := 3438207925711294548931187

theorem tailTrace_6695886 : CollatzResearch.WordTrace tailWord_6695886 prefixEnd_6695886 3438207925711294548931187 := by
  unfold tailWord_6695886
  simp only [CollatzResearch.WordTrace]
  refine ⟨30527378227494507891243439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162812683879970708753298341 30527378227494507891243439)
  ·
    refine ⟨45791067341241761836865159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30527378227494507891243439 45791067341241761836865159)
    ·
      refine ⟨68686601011862642755297739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45791067341241761836865159 68686601011862642755297739)
      ·
        refine ⟨103029901517793964132946609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68686601011862642755297739 103029901517793964132946609)
        ·
          refine ⟨77272426138345473099709957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103029901517793964132946609 77272426138345473099709957)
          ·
            refine ⟨14488579900939776206195617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77272426138345473099709957 14488579900939776206195617)
            ·
              refine ⟨10866434925704832154646713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14488579900939776206195617 10866434925704832154646713)
              ·
                refine ⟨8149826194278624115985035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10866434925704832154646713 8149826194278624115985035)
                ·
                  refine ⟨12224739291417936173977553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8149826194278624115985035 12224739291417936173977553)
                  ·
                    refine ⟨9168554468563452130483165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12224739291417936173977553 9168554468563452130483165)
                    ·
                      refine ⟨3438207925711294548931187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9168554468563452130483165 3438207925711294548931187)
                      ·
                        rfl

theorem cell23_6695886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_6695886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695886 prefixEnd_6695886 := by exact prefixLift 6695886
  have htrace : WordTrace (prefixWord ++ tailWord_6695886) baseStart_6695886 baseEnd_6695886 := by
    simpa [prefixWord, tailWord_6695886, baseEnd_6695886] using wordTrace_append hprefix tailTrace_6695886
  have hstable : (prefixWord ++ tailWord_6695886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695886).length < 2 ^ (prefixWord ++ tailWord_6695886).sum := by decide
  have hdescent : baseEnd_6695886 < baseStart_6695886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695959 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 5]
def baseStart_6695959 : Nat := 118140960795 + 6695959 * 2 ^ 59
def prefixEnd_6695959 : Nat := 4983230072969 + 3 ^ 40 * 6695959 * 2
def baseEnd_6695959 : Nat := 3438245409799072763318351

theorem tailTrace_6695959 : CollatzResearch.WordTrace tailWord_6695959 prefixEnd_6695959 3438245409799072763318351 := by
  unfold tailWord_6695959
  simp only [CollatzResearch.WordTrace]
  refine ⟨244221688348691596597354931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162814458899127731064903287 244221688348691596597354931)
  ·
    refine ⟨366332532523037394896032397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244221688348691596597354931 366332532523037394896032397)
    ·
      refine ⟨137374699696139023086012149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366332532523037394896032397 137374699696139023086012149)
      ·
        refine ⟨12878878096513033414313639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137374699696139023086012149 12878878096513033414313639)
        ·
          refine ⟨19318317144769550121470459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12878878096513033414313639 19318317144769550121470459)
          ·
            refine ⟨28977475717154325182205689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19318317144769550121470459 28977475717154325182205689)
            ·
              refine ⟨21733106787865743886654267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28977475717154325182205689 21733106787865743886654267)
              ·
                refine ⟨32599660181798615829981401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21733106787865743886654267 32599660181798615829981401)
                ·
                  refine ⟨24449745136348961872486051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32599660181798615829981401 24449745136348961872486051)
                  ·
                    refine ⟨36674617704523442808729077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24449745136348961872486051 36674617704523442808729077)
                    ·
                      refine ⟨3438245409799072763318351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36674617704523442808729077 3438245409799072763318351)
                      ·
                        rfl

theorem cell23_6695959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_6695959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695959 prefixEnd_6695959 := by exact prefixLift 6695959
  have htrace : WordTrace (prefixWord ++ tailWord_6695959) baseStart_6695959 baseEnd_6695959 := by
    simpa [prefixWord, tailWord_6695959, baseEnd_6695959] using wordTrace_append hprefix tailTrace_6695959
  have hstable : (prefixWord ++ tailWord_6695959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695959).length < 2 ^ (prefixWord ++ tailWord_6695959).sum := by decide
  have hdescent : baseEnd_6695959 < baseStart_6695959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695973 : List Nat := [1, 3, 1, 2, 2, 2, 4, 2, 2, 2, 2]
def baseStart_6695973 : Nat := 118140960795 + 6695973 * 2 ^ 59
def prefixEnd_6695973 : Nat := 4983230072969 + 3 ^ 40 * 6695973 * 2
def baseEnd_6695973 : Nat := 3438252598528235708543287

theorem tailTrace_6695973 : CollatzResearch.WordTrace tailWord_6695973 prefixEnd_6695973 3438252598528235708543287 := by
  unfold tailWord_6695973
  simp only [CollatzResearch.WordTrace]
  refine ⟨244222198970640876988364573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162814799313760584658909715 244222198970640876988364573)
  ·
    refine ⟨91583324613990328870636715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244222198970640876988364573 91583324613990328870636715)
    ·
      refine ⟨137374986920985493305955073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91583324613990328870636715 137374986920985493305955073)
      ·
        refine ⟨103031240190739119979466305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137374986920985493305955073 103031240190739119979466305)
        ·
          refine ⟨77273430143054339984599729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103031240190739119979466305 77273430143054339984599729)
          ·
            refine ⟨57955072607290754988449797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77273430143054339984599729 57955072607290754988449797)
            ·
              refine ⟨10866576113867016560334337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57955072607290754988449797 10866576113867016560334337)
              ·
                refine ⟨8149932085400262420250753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10866576113867016560334337 8149932085400262420250753)
                ·
                  refine ⟨6112449064050196815188065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8149932085400262420250753 6112449064050196815188065)
                  ·
                    refine ⟨4584336798037647611391049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6112449064050196815188065 4584336798037647611391049)
                    ·
                      refine ⟨3438252598528235708543287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4584336798037647611391049 3438252598528235708543287)
                      ·
                        rfl

theorem cell23_6695973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_6695973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695973 prefixEnd_6695973 := by exact prefixLift 6695973
  have htrace : WordTrace (prefixWord ++ tailWord_6695973) baseStart_6695973 baseEnd_6695973 := by
    simpa [prefixWord, tailWord_6695973, baseEnd_6695973] using wordTrace_append hprefix tailTrace_6695973
  have hstable : (prefixWord ++ tailWord_6695973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695973).length < 2 ^ (prefixWord ++ tailWord_6695973).sum := by decide
  have hdescent : baseEnd_6695973 < baseStart_6695973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695979 : List Nat := [1, 1, 1, 1, 2, 1, 7, 4, 5]
def baseStart_6695979 : Nat := 118140960795 + 6695979 * 2 ^ 59
def prefixEnd_6695979 : Nat := 4983230072969 + 3 ^ 40 * 6695979 * 2
def baseEnd_6695979 : Nat := 382028408823573631674251

theorem tailTrace_6695979 : CollatzResearch.WordTrace tailWord_6695979 prefixEnd_6695979 382028408823573631674251 := by
  unfold tailWord_6695979
  simp only [CollatzResearch.WordTrace]
  refine ⟨244222417808619140013082991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162814945205746093342055327 244222417808619140013082991)
  ·
    refine ⟨366333626712928710019624487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244222417808619140013082991 366333626712928710019624487)
    ·
      refine ⟨549500440069393065029436731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366333626712928710019624487 549500440069393065029436731)
      ·
        refine ⟨824250660104089597544155097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549500440069393065029436731 824250660104089597544155097)
        ·
          refine ⟨618187995078067198158116323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 824250660104089597544155097 618187995078067198158116323)
          ·
            refine ⟨927281992617100797237174485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618187995078067198158116323 927281992617100797237174485)
            ·
              refine ⟨21733171701963299935246277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 927281992617100797237174485 21733171701963299935246277)
              ·
                refine ⟨4074969694118118737858677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21733171701963299935246277 4074969694118118737858677)
                ·
                  refine ⟨382028408823573631674251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4074969694118118737858677 382028408823573631674251)
                  ·
                    rfl

theorem cell23_6695979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 5].length) (baseStart_6695979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695979 prefixEnd_6695979 := by exact prefixLift 6695979
  have htrace : WordTrace (prefixWord ++ tailWord_6695979) baseStart_6695979 baseEnd_6695979 := by
    simpa [prefixWord, tailWord_6695979, baseEnd_6695979] using wordTrace_append hprefix tailTrace_6695979
  have hstable : (prefixWord ++ tailWord_6695979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695979).length < 2 ^ (prefixWord ++ tailWord_6695979).sum := by decide
  have hdescent : baseEnd_6695979 < baseStart_6695979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695990 : List Nat := [5, 1, 2, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_6695990 : Nat := 118140960795 + 6695990 * 2 ^ 59
def prefixEnd_6695990 : Nat := 4983230072969 + 3 ^ 40 * 6695990 * 2
def baseEnd_6695990 : Nat := 3438261327699362142030709

theorem tailTrace_6695990 : CollatzResearch.WordTrace tailWord_6695990 prefixEnd_6695990 3438261327699362142030709 := by
  unfold tailWord_6695990
  simp only [CollatzResearch.WordTrace]
  refine ⟨15263926188223705555733339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162815212674386192594488949 15263926188223705555733339)
  ·
    refine ⟨22895889282335558333600009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15263926188223705555733339 22895889282335558333600009)
    ·
      refine ⟨17171916961751668750200007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22895889282335558333600009 17171916961751668750200007)
      ·
        refine ⟨25757875442627503125300011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17171916961751668750200007 25757875442627503125300011)
        ·
          refine ⟨38636813163941254687950017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25757875442627503125300011 38636813163941254687950017)
          ·
            refine ⟨28977609872955941015962513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38636813163941254687950017 28977609872955941015962513)
            ·
              refine ⟨21733207404716955761971885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28977609872955941015962513 21733207404716955761971885)
              ·
                refine ⟨8149952776768858410739457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21733207404716955761971885 8149952776768858410739457)
                ·
                  refine ⟨6112464582576643808054593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8149952776768858410739457 6112464582576643808054593)
                  ·
                    refine ⟨4584348436932482856040945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6112464582576643808054593 4584348436932482856040945)
                    ·
                      refine ⟨3438261327699362142030709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4584348436932482856040945 3438261327699362142030709)
                      ·
                        rfl

theorem cell23_6695990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_6695990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695990 prefixEnd_6695990 := by exact prefixLift 6695990
  have htrace : WordTrace (prefixWord ++ tailWord_6695990) baseStart_6695990 baseEnd_6695990 := by
    simpa [prefixWord, tailWord_6695990, baseEnd_6695990] using wordTrace_append hprefix tailTrace_6695990
  have hstable : (prefixWord ++ tailWord_6695990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695990).length < 2 ^ (prefixWord ++ tailWord_6695990).sum := by decide
  have hdescent : baseEnd_6695990 < baseStart_6695990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6695999 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 4, 5, 2]
def baseStart_6695999 : Nat := 118140960795 + 6695999 * 2 ^ 59
def prefixEnd_6695999 : Nat := 4983230072969 + 3 ^ 40 * 6695999 * 2
def baseEnd_6695999 : Nat := 3438265949025252606818167

theorem tailTrace_6695999 : CollatzResearch.WordTrace tailWord_6695999 prefixEnd_6695999 3438265949025252606818167 := by
  unfold tailWord_6695999
  simp only [CollatzResearch.WordTrace]
  refine ⟨244223147268546683428811051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162815431512364455619207367 244223147268546683428811051)
  ·
    refine ⟨366334720902820025143216577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244223147268546683428811051 366334720902820025143216577)
    ·
      refine ⟨274751040677115018857412433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366334720902820025143216577 274751040677115018857412433)
      ·
        refine ⟨206063280507836264143059325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274751040677115018857412433 206063280507836264143059325)
        ·
          refine ⟨77273730190438599053647247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206063280507836264143059325 77273730190438599053647247)
          ·
            refine ⟨115910595285657898580470871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77273730190438599053647247 115910595285657898580470871)
            ·
              refine ⟨173865892928486847870706307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115910595285657898580470871 173865892928486847870706307)
              ·
                refine ⟨260798839392730271806059461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173865892928486847870706307 260798839392730271806059461)
                ·
                  refine ⟨48899782386136925963636149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 260798839392730271806059461 48899782386136925963636149)
                  ·
                    refine ⟨4584354598700336809090889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48899782386136925963636149 4584354598700336809090889)
                    ·
                      refine ⟨3438265949025252606818167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4584354598700336809090889 3438265949025252606818167)
                      ·
                        rfl

theorem cell23_6695999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 5, 2].length) (baseStart_6695999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6695999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6695999 prefixEnd_6695999 := by exact prefixLift 6695999
  have htrace : WordTrace (prefixWord ++ tailWord_6695999) baseStart_6695999 baseEnd_6695999 := by
    simpa [prefixWord, tailWord_6695999, baseEnd_6695999] using wordTrace_append hprefix tailTrace_6695999
  have hstable : (prefixWord ++ tailWord_6695999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6695999).length < 2 ^ (prefixWord ++ tailWord_6695999).sum := by decide
  have hdescent : baseEnd_6695999 < baseStart_6695999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6695999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696013 : List Nat := [1, 6, 1, 1, 1, 3, 2, 3, 5]
def baseStart_6696013 : Nat := 118140960795 + 6696013 * 2 ^ 59
def prefixEnd_6696013 : Nat := 4983230072969 + 3 ^ 40 * 6696013 * 2
def baseEnd_6696013 : Nat := 382030348639379505782567

theorem tailTrace_6696013 : CollatzResearch.WordTrace tailWord_6696013 prefixEnd_6696013 382030348639379505782567 := by
  unfold tailWord_6696013
  simp only [CollatzResearch.WordTrace]
  refine ⟨244223657890495963819820693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162815771926997309213213795 244223657890495963819820693)
  ·
    refine ⟨11447983963616998304054095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 244223657890495963819820693 11447983963616998304054095)
    ·
      refine ⟨17171975945425497456081143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11447983963616998304054095 17171975945425497456081143)
      ·
        refine ⟨25757963918138246184121715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17171975945425497456081143 25757963918138246184121715)
        ·
          refine ⟨38636945877207369276182573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25757963918138246184121715 38636945877207369276182573)
          ·
            refine ⟨14488854703952763478568465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38636945877207369276182573 14488854703952763478568465)
            ·
              refine ⟨10866641027964572608926349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14488854703952763478568465 10866641027964572608926349)
              ·
                refine ⟨4074990385486714728347381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10866641027964572608926349 4074990385486714728347381)
                ·
                  refine ⟨382030348639379505782567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4074990385486714728347381 382030348639379505782567)
                  ·
                    rfl

theorem cell23_6696013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_6696013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696013 prefixEnd_6696013 := by exact prefixLift 6696013
  have htrace : WordTrace (prefixWord ++ tailWord_6696013) baseStart_6696013 baseEnd_6696013 := by
    simpa [prefixWord, tailWord_6696013, baseEnd_6696013] using wordTrace_append hprefix tailTrace_6696013
  have hstable : (prefixWord ++ tailWord_6696013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696013).length < 2 ^ (prefixWord ++ tailWord_6696013).sum := by decide
  have hdescent : baseEnd_6696013 < baseStart_6696013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696030 : List Nat := [4, 4, 1, 1, 1, 1, 2, 4, 5]
def baseStart_6696030 : Nat := 118140960795 + 6696030 * 2 ^ 59
def prefixEnd_6696030 : Nat := 4983230072969 + 3 ^ 40 * 6696030 * 2
def baseEnd_6696030 : Nat := 382031318547282442836725

theorem tailTrace_6696030 : CollatzResearch.WordTrace tailWord_6696030 prefixEnd_6696030 382031318547282442836725 := by
  unfold tailWord_6696030
  simp only [CollatzResearch.WordTrace]
  refine ⟨30528034741429296965398693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162816185287622917148793029 30528034741429296965398693)
  ·
    refine ⟨5724006514017993181012255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30528034741429296965398693 5724006514017993181012255)
    ·
      refine ⟨8586009771026989771518383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5724006514017993181012255 8586009771026989771518383)
      ·
        refine ⟨12879014656540484657277575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8586009771026989771518383 12879014656540484657277575)
        ·
          refine ⟨19318521984810726985916363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12879014656540484657277575 19318521984810726985916363)
          ·
            refine ⟨28977782977216090478874545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19318521984810726985916363 28977782977216090478874545)
            ·
              refine ⟨21733337232912067859155909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28977782977216090478874545 21733337232912067859155909)
              ·
                refine ⟨4075000731171012723591733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21733337232912067859155909 4075000731171012723591733)
                ·
                  refine ⟨382031318547282442836725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4075000731171012723591733 382031318547282442836725)
                  ·
                    rfl

theorem cell23_6696030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_6696030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696030 prefixEnd_6696030 := by exact prefixLift 6696030
  have htrace : WordTrace (prefixWord ++ tailWord_6696030) baseStart_6696030 baseEnd_6696030 := by
    simpa [prefixWord, tailWord_6696030, baseEnd_6696030] using wordTrace_append hprefix tailTrace_6696030
  have hstable : (prefixWord ++ tailWord_6696030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696030).length < 2 ^ (prefixWord ++ tailWord_6696030).sum := by decide
  have hdescent : baseEnd_6696030 < baseStart_6696030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696049 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 6, 2, 3]
def baseStart_6696049 : Nat := 118140960795 + 6696049 * 2 ^ 59
def prefixEnd_6696049 : Nat := 4983230072969 + 3 ^ 40 * 6696049 * 2
def baseEnd_6696049 : Nat := 3438291623057977411192937

theorem tailTrace_6696049 : CollatzResearch.WordTrace tailWord_6696049 prefixEnd_6696049 3438291623057977411192937 := by
  unfold tailWord_6696049
  simp only [CollatzResearch.WordTrace]
  refine ⟨244224970918365541968131201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162816647278910361312087467 244224970918365541968131201)
  ·
    refine ⟨183168728188774156476098401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244224970918365541968131201 183168728188774156476098401)
    ·
      refine ⟨137376546141580617357073801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183168728188774156476098401 137376546141580617357073801)
      ·
        refine ⟨103032409606185463017805351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137376546141580617357073801 103032409606185463017805351)
        ·
          refine ⟨154548614409278194526708027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103032409606185463017805351 154548614409278194526708027)
          ·
            refine ⟨231822921613917291790062041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154548614409278194526708027 231822921613917291790062041)
            ·
              refine ⟨173867191210437968842546531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231822921613917291790062041 173867191210437968842546531)
              ·
                refine ⟨260800786815656953263819797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173867191210437968842546531 260800786815656953263819797)
                ·
                  refine ⟨12225036881983919684241553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 260800786815656953263819797 12225036881983919684241553)
                  ·
                    refine ⟨9168777661487939763181165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12225036881983919684241553 9168777661487939763181165)
                    ·
                      refine ⟨3438291623057977411192937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9168777661487939763181165 3438291623057977411192937)
                      ·
                        rfl

theorem cell23_6696049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_6696049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696049 prefixEnd_6696049 := by exact prefixLift 6696049
  have htrace : WordTrace (prefixWord ++ tailWord_6696049) baseStart_6696049 baseEnd_6696049 := by
    simpa [prefixWord, tailWord_6696049, baseEnd_6696049] using wordTrace_append hprefix tailTrace_6696049
  have hstable : (prefixWord ++ tailWord_6696049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696049).length < 2 ^ (prefixWord ++ tailWord_6696049).sum := by decide
  have hdescent : baseEnd_6696049 < baseStart_6696049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696073 : List Nat := [1, 2, 1, 1, 4, 3, 3, 3, 1, 4]
def baseStart_6696073 : Nat := 118140960795 + 6696073 * 2 ^ 59
def prefixEnd_6696073 : Nat := 4983230072969 + 3 ^ 40 * 6696073 * 2
def baseEnd_6696073 : Nat := 1146101315531228439097609

theorem tailTrace_6696073 : CollatzResearch.WordTrace tailWord_6696073 prefixEnd_6696073 1146101315531228439097609 := by
  unfold tailWord_6696073
  simp only [CollatzResearch.WordTrace]
  refine ⟨244225846270278594067004873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162817230846852396044669915 244225846270278594067004873)
  ·
    refine ⟨183169384702708945550253655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244225846270278594067004873 183169384702708945550253655)
    ·
      refine ⟨274754077054063418325380483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183169384702708945550253655 274754077054063418325380483)
      ·
        refine ⟨412131115581095127488070725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274754077054063418325380483 412131115581095127488070725)
        ·
          refine ⟨77274584171455336404013261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 412131115581095127488070725 77274584171455336404013261)
          ·
            refine ⟨28977969064295751151504973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77274584171455336404013261 28977969064295751151504973)
            ·
              refine ⟨10866738399110906681814365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28977969064295751151504973 10866738399110906681814365)
              ·
                refine ⟨4075026899666590005680387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10866738399110906681814365 4075026899666590005680387)
                ·
                  refine ⟨6112540349499885008520581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4075026899666590005680387 6112540349499885008520581)
                  ·
                    refine ⟨1146101315531228439097609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6112540349499885008520581 1146101315531228439097609)
                    ·
                      rfl

theorem cell23_6696073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 1, 4].length) (baseStart_6696073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696073 prefixEnd_6696073 := by exact prefixLift 6696073
  have htrace : WordTrace (prefixWord ++ tailWord_6696073) baseStart_6696073 baseEnd_6696073 := by
    simpa [prefixWord, tailWord_6696073, baseEnd_6696073] using wordTrace_append hprefix tailTrace_6696073
  have hstable : (prefixWord ++ tailWord_6696073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696073).length < 2 ^ (prefixWord ++ tailWord_6696073).sum := by decide
  have hdescent : baseEnd_6696073 < baseStart_6696073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696103 : List Nat := [1, 1, 6, 2, 1, 1, 4, 1, 6]
def baseStart_6696103 : Nat := 118140960795 + 6696103 * 2 ^ 59
def prefixEnd_6696103 : Nat := 4983230072969 + 3 ^ 40 * 6696103 * 2
def baseEnd_6696103 : Nat := 382035483445924466657521

theorem tailTrace_6696103 : CollatzResearch.WordTrace tailWord_6696103 prefixEnd_6696103 382035483445924466657521 := by
  unfold tailWord_6696103
  simp only [CollatzResearch.WordTrace]
  refine ⟨244226940460169909190596963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162817960306779939460397975 244226940460169909190596963)
  ·
    refine ⟨366340410690254863785895445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244226940460169909190596963 366340410690254863785895445)
    ·
      refine ⟨17172206751105696739963849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 366340410690254863785895445 17172206751105696739963849)
      ·
        refine ⟨12879155063329272554972887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17172206751105696739963849 12879155063329272554972887)
        ·
          refine ⟨19318732594993908832459331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12879155063329272554972887 19318732594993908832459331)
          ·
            refine ⟨28978098892490863248688997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19318732594993908832459331 28978098892490863248688997)
            ·
              refine ⟨5433393542342036859129187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28978098892490863248688997 5433393542342036859129187)
              ·
                refine ⟨8150090313513055288693781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5433393542342036859129187 8150090313513055288693781)
                ·
                  refine ⟨382035483445924466657521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8150090313513055288693781 382035483445924466657521)
                  ·
                    rfl

theorem cell23_6696103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 6].length) (baseStart_6696103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696103 prefixEnd_6696103 := by exact prefixLift 6696103
  have htrace : WordTrace (prefixWord ++ tailWord_6696103) baseStart_6696103 baseEnd_6696103 := by
    simpa [prefixWord, tailWord_6696103, baseEnd_6696103] using wordTrace_append hprefix tailTrace_6696103
  have hstable : (prefixWord ++ tailWord_6696103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696103).length < 2 ^ (prefixWord ++ tailWord_6696103).sum := by decide
  have hdescent : baseEnd_6696103 < baseStart_6696103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696136 : List Nat := [2, 1, 3, 1, 2, 1, 2, 5, 1, 1, 4]
def baseStart_6696136 : Nat := 118140960795 + 6696136 * 2 ^ 59
def prefixEnd_6696136 : Nat := 4983230072969 + 3 ^ 40 * 6696136 * 2
def baseEnd_6696136 : Nat := 3438336295874918570805037

theorem tailTrace_6696136 : CollatzResearch.WordTrace tailWord_6696136 prefixEnd_6696136 3438336295874918570805037 := by
  unfold tailWord_6696136
  simp only [CollatzResearch.WordTrace]
  refine ⟨122114072034525177913274131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162818762712700237217698841 122114072034525177913274131)
  ·
    refine ⟨183171108051787766869911197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122114072034525177913274131 183171108051787766869911197)
    ·
      refine ⟨68689165519420412576216699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183171108051787766869911197 68689165519420412576216699)
      ·
        refine ⟨103033748279130618864325049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68689165519420412576216699 103033748279130618864325049)
        ·
          refine ⟨77275311209347964148243787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103033748279130618864325049 77275311209347964148243787)
          ·
            refine ⟨115912966814021946222365681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77275311209347964148243787 115912966814021946222365681)
            ·
              refine ⟨86934725110516459666774261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115912966814021946222365681 86934725110516459666774261)
              ·
                refine ⟨8150130479110918093760087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86934725110516459666774261 8150130479110918093760087)
                ·
                  refine ⟨12225195718666377140640131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8150130479110918093760087 12225195718666377140640131)
                  ·
                    refine ⟨18337793577999565710960197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12225195718666377140640131 18337793577999565710960197)
                    ·
                      refine ⟨3438336295874918570805037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18337793577999565710960197 3438336295874918570805037)
                      ·
                        rfl

theorem cell23_6696136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_6696136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696136 prefixEnd_6696136 := by exact prefixLift 6696136
  have htrace : WordTrace (prefixWord ++ tailWord_6696136) baseStart_6696136 baseEnd_6696136 := by
    simpa [prefixWord, tailWord_6696136, baseEnd_6696136] using wordTrace_append hprefix tailTrace_6696136
  have hstable : (prefixWord ++ tailWord_6696136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696136).length < 2 ^ (prefixWord ++ tailWord_6696136).sum := by decide
  have hdescent : baseEnd_6696136 < baseStart_6696136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696139 : List Nat := [1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 5]
def baseStart_6696139 : Nat := 118140960795 + 6696139 * 2 ^ 59
def prefixEnd_6696139 : Nat := 4983230072969 + 3 ^ 40 * 6696139 * 2
def baseEnd_6696139 : Nat := 3438337836316882059067523

theorem tailTrace_6696139 : CollatzResearch.WordTrace tailWord_6696139 prefixEnd_6696139 3438337836316882059067523 := by
  unfold tailWord_6696139
  simp only [CollatzResearch.WordTrace]
  refine ⟨244228253488039487338907471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162818835658692991559271647 244228253488039487338907471)
  ·
    refine ⟨366342380232059231008361207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244228253488039487338907471 366342380232059231008361207)
    ·
      refine ⟨549513570348088846512541811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366342380232059231008361207 549513570348088846512541811)
      ·
        refine ⟨824270355522133269768812717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549513570348088846512541811 824270355522133269768812717)
        ·
          refine ⟨309101383320799976163304769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 824270355522133269768812717 309101383320799976163304769)
          ·
            refine ⟨231826037490599982122478577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309101383320799976163304769 231826037490599982122478577)
            ·
              refine ⟨173869528117949986591858933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231826037490599982122478577 173869528117949986591858933)
              ·
                refine ⟨16300268261057811242986775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173869528117949986591858933 16300268261057811242986775)
                ·
                  refine ⟨24450402391586716864480163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16300268261057811242986775 24450402391586716864480163)
                  ·
                    refine ⟨36675603587380075296720245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24450402391586716864480163 36675603587380075296720245)
                    ·
                      refine ⟨3438337836316882059067523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36675603587380075296720245 3438337836316882059067523)
                      ·
                        rfl

theorem cell23_6696139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 5].length) (baseStart_6696139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696139 prefixEnd_6696139 := by exact prefixLift 6696139
  have htrace : WordTrace (prefixWord ++ tailWord_6696139) baseStart_6696139 baseEnd_6696139 := by
    simpa [prefixWord, tailWord_6696139, baseEnd_6696139] using wordTrace_append hprefix tailTrace_6696139
  have hstable : (prefixWord ++ tailWord_6696139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696139).length < 2 ^ (prefixWord ++ tailWord_6696139).sum := by decide
  have hdescent : baseEnd_6696139 < baseStart_6696139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696141 : List Nat := [1, 6, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_6696141 : Nat := 118140960795 + 6696141 * 2 ^ 59
def prefixEnd_6696141 : Nat := 4983230072969 + 3 ^ 40 * 6696141 * 2
def baseEnd_6696141 : Nat := 1146112954426063683747505

theorem tailTrace_6696141 : CollatzResearch.WordTrace tailWord_6696141 prefixEnd_6696141 1146112954426063683747505 := by
  unfold tailWord_6696141
  simp only [CollatzResearch.WordTrace]
  refine ⟨244228326434032241680480277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162818884289354827786986851 244228326434032241680480277)
  ·
    refine ⟨11448202801595261328772513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 244228326434032241680480277 11448202801595261328772513)
    ·
      refine ⟨8586152101196445996579385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11448202801595261328772513 8586152101196445996579385)
      ·
        refine ⟨6439614075897334497434539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8586152101196445996579385 6439614075897334497434539)
        ·
          refine ⟨9659421113846001746151809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6439614075897334497434539 9659421113846001746151809)
          ·
            refine ⟨7244565835384501309613857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9659421113846001746151809 7244565835384501309613857)
            ·
              refine ⟨5433424376538375982210393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7244565835384501309613857 5433424376538375982210393)
              ·
                refine ⟨4075068282403781986657795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5433424376538375982210393 4075068282403781986657795)
                ·
                  refine ⟨6112602423605672979986693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4075068282403781986657795 6112602423605672979986693)
                  ·
                    refine ⟨1146112954426063683747505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6112602423605672979986693 1146112954426063683747505)
                    ·
                      rfl

theorem cell23_6696141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_6696141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696141 prefixEnd_6696141 := by exact prefixLift 6696141
  have htrace : WordTrace (prefixWord ++ tailWord_6696141) baseStart_6696141 baseEnd_6696141 := by
    simpa [prefixWord, tailWord_6696141, baseEnd_6696141] using wordTrace_append hprefix tailTrace_6696141
  have hstable : (prefixWord ++ tailWord_6696141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696141).length < 2 ^ (prefixWord ++ tailWord_6696141).sum := by decide
  have hdescent : baseEnd_6696141 < baseStart_6696141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696153 : List Nat := [1, 2, 1, 2, 3, 1, 1, 5, 3, 2, 2]
def baseStart_6696153 : Nat := 118140960795 + 6696153 * 2 ^ 59
def prefixEnd_6696153 : Nat := 4983230072969 + 3 ^ 40 * 6696153 * 2
def baseEnd_6696153 : Nat := 3438345025046045004292459

theorem tailTrace_6696153 : CollatzResearch.WordTrace tailWord_6696153 prefixEnd_6696153 3438345025046045004292459 := by
  unfold tailWord_6696153
  simp only [CollatzResearch.WordTrace]
  refine ⟨244228764109988767729917113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162819176073325845153278075 244228764109988767729917113)
  ·
    refine ⟨183171573082491575797437835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244228764109988767729917113 183171573082491575797437835)
    ·
      refine ⟨274757359623737363696156753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183171573082491575797437835 274757359623737363696156753)
      ·
        refine ⟨206068019717803022772117565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274757359623737363696156753 206068019717803022772117565)
        ·
          refine ⟨77275507394176133539544087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206068019717803022772117565 77275507394176133539544087)
          ·
            refine ⟨115913261091264200309316131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77275507394176133539544087 115913261091264200309316131)
            ·
              refine ⟨173869891636896300463974197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115913261091264200309316131 173869891636896300463974197)
              ·
                refine ⟨16300302340959028168497581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173869891636896300463974197 16300302340959028168497581)
                ·
                  refine ⟨6112613377859635563186593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16300302340959028168497581 6112613377859635563186593)
                  ·
                    refine ⟨4584460033394726672389945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6112613377859635563186593 4584460033394726672389945)
                    ·
                      refine ⟨3438345025046045004292459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4584460033394726672389945 3438345025046045004292459)
                      ·
                        rfl

theorem cell23_6696153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 2, 2].length) (baseStart_6696153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696153 prefixEnd_6696153 := by exact prefixLift 6696153
  have htrace : WordTrace (prefixWord ++ tailWord_6696153) baseStart_6696153 baseEnd_6696153 := by
    simpa [prefixWord, tailWord_6696153, baseEnd_6696153] using wordTrace_append hprefix tailTrace_6696153
  have hstable : (prefixWord ++ tailWord_6696153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696153).length < 2 ^ (prefixWord ++ tailWord_6696153).sum := by decide
  have hdescent : baseEnd_6696153 < baseStart_6696153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696159 : List Nat := [1, 1, 2, 3, 2, 1, 5, 8]
def baseStart_6696159 : Nat := 118140960795 + 6696159 * 2 ^ 59
def prefixEnd_6696159 : Nat := 4983230072969 + 3 ^ 40 * 6696159 * 2
def baseEnd_6696159 : Nat := 127346226145554517808053

theorem tailTrace_6696159 : CollatzResearch.WordTrace tailWord_6696159 prefixEnd_6696159 127346226145554517808053 := by
  unfold tailWord_6696159
  simp only [CollatzResearch.WordTrace]
  refine ⟨244228982947967030754635531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162819321965311353836423687 244228982947967030754635531)
  ·
    refine ⟨366343474421950546131953297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244228982947967030754635531 366343474421950546131953297)
    ·
      refine ⟨274757605816462909598964973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366343474421950546131953297 274757605816462909598964973)
      ·
        refine ⟨103034102181173591099611865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274757605816462909598964973 103034102181173591099611865)
        ·
          refine ⟨77275576635880193324708899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103034102181173591099611865 77275576635880193324708899)
          ·
            refine ⟨115913364953820289987063349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77275576635880193324708899 115913364953820289987063349)
            ·
              refine ⟨10866877964420652186287189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115913364953820289987063349 10866877964420652186287189)
              ·
                refine ⟨127346226145554517808053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10866877964420652186287189 127346226145554517808053)
                ·
                  rfl

theorem cell23_6696159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 8].length) (baseStart_6696159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696159 prefixEnd_6696159 := by exact prefixLift 6696159
  have htrace : WordTrace (prefixWord ++ tailWord_6696159) baseStart_6696159 baseEnd_6696159 := by
    simpa [prefixWord, tailWord_6696159, baseEnd_6696159] using wordTrace_append hprefix tailTrace_6696159
  have hstable : (prefixWord ++ tailWord_6696159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696159).length < 2 ^ (prefixWord ++ tailWord_6696159).sum := by decide
  have hdescent : baseEnd_6696159 < baseStart_6696159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696170 : List Nat := [3, 1, 3, 1, 1, 4, 1, 2, 3, 2, 2]
def baseStart_6696170 : Nat := 118140960795 + 6696170 * 2 ^ 59
def prefixEnd_6696170 : Nat := 4983230072969 + 3 ^ 40 * 6696170 * 2
def baseEnd_6696170 : Nat := 3438353754217171437779881

theorem tailTrace_6696170 : CollatzResearch.WordTrace tailWord_6696170 prefixEnd_6696170 3438353754217171437779881 := by
  unfold tailWord_6696170
  simp only [CollatzResearch.WordTrace]
  refine ⟨61057346037731794908321491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162819589433951453088857309 61057346037731794908321491)
  ·
    refine ⟨91586019056597692362482237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61057346037731794908321491 91586019056597692362482237)
    ·
      refine ⟨34344757146224134635930839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91586019056597692362482237 34344757146224134635930839)
      ·
        refine ⟨51517135719336201953896259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34344757146224134635930839 51517135719336201953896259)
        ·
          refine ⟨77275703579004302930844389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51517135719336201953896259 77275703579004302930844389)
          ·
            refine ⟨14489194421063306799533323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77275703579004302930844389 14489194421063306799533323)
            ·
              refine ⟨21733791631594960199299985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14489194421063306799533323 21733791631594960199299985)
              ·
                refine ⟨16300343723696220149474989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21733791631594960199299985 16300343723696220149474989)
                ·
                  refine ⟨6112628896386082556053121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16300343723696220149474989 6112628896386082556053121)
                  ·
                    refine ⟨4584471672289561917039841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6112628896386082556053121 4584471672289561917039841)
                    ·
                      refine ⟨3438353754217171437779881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4584471672289561917039841 3438353754217171437779881)
                      ·
                        rfl

theorem cell23_6696170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_6696170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696170 prefixEnd_6696170 := by exact prefixLift 6696170
  have htrace : WordTrace (prefixWord ++ tailWord_6696170) baseStart_6696170 baseEnd_6696170 := by
    simpa [prefixWord, tailWord_6696170, baseEnd_6696170] using wordTrace_append hprefix tailTrace_6696170
  have hstable : (prefixWord ++ tailWord_6696170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696170).length < 2 ^ (prefixWord ++ tailWord_6696170).sum := by decide
  have hdescent : baseEnd_6696170 < baseStart_6696170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696173 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_6696173 : Nat := 118140960795 + 6696173 * 2 ^ 59
def prefixEnd_6696173 : Nat := 4983230072969 + 3 ^ 40 * 6696173 * 2
def baseEnd_6696173 : Nat := 3438355294659134926042367

theorem tailTrace_6696173 : CollatzResearch.WordTrace tailWord_6696173 prefixEnd_6696173 3438355294659134926042367 := by
  unfold tailWord_6696173
  simp only [CollatzResearch.WordTrace]
  refine ⟨244229493569916311145645173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162819662379944207430430115 244229493569916311145645173)
  ·
    refine ⟨22896515022179654169904235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244229493569916311145645173 22896515022179654169904235)
    ·
      refine ⟨34344772533269481254856353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22896515022179654169904235 34344772533269481254856353)
      ·
        refine ⟨25758579399952110941142265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34344772533269481254856353 25758579399952110941142265)
        ·
          refine ⟨19318934549964083205856699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25758579399952110941142265 19318934549964083205856699)
          ·
            refine ⟨28978401824946124808785049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19318934549964083205856699 28978401824946124808785049)
            ·
              refine ⟨21733801368709593606588787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28978401824946124808785049 21733801368709593606588787)
              ·
                refine ⟨32600702053064390409883181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21733801368709593606588787 32600702053064390409883181)
                ·
                  refine ⟨12225263269899146403706193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32600702053064390409883181 12225263269899146403706193)
                  ·
                    refine ⟨9168947452424359802779645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12225263269899146403706193 9168947452424359802779645)
                    ·
                      refine ⟨3438355294659134926042367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9168947452424359802779645 3438355294659134926042367)
                      ·
                        rfl

theorem cell23_6696173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_6696173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696173 prefixEnd_6696173 := by exact prefixLift 6696173
  have htrace : WordTrace (prefixWord ++ tailWord_6696173) baseStart_6696173 baseEnd_6696173 := by
    simpa [prefixWord, tailWord_6696173, baseEnd_6696173] using wordTrace_append hprefix tailTrace_6696173
  have hstable : (prefixWord ++ tailWord_6696173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696173).length < 2 ^ (prefixWord ++ tailWord_6696173).sum := by decide
  have hdescent : baseEnd_6696173 < baseStart_6696173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696186 : List Nat := [3, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3]
def baseStart_6696186 : Nat := 118140960795 + 6696186 * 2 ^ 59
def prefixEnd_6696186 : Nat := 4983230072969 + 3 ^ 40 * 6696186 * 2
def baseEnd_6696186 : Nat := 3438361969907643375179807

theorem tailTrace_6696186 : CollatzResearch.WordTrace tailWord_6696186 prefixEnd_6696186 3438361969907643375179807 := by
  unfold tailWord_6696186
  simp only [CollatzResearch.WordTrace]
  refine ⟨61057491929717303591467103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162819978479246142910578941 61057491929717303591467103)
  ·
    refine ⟨91586237894575955387200655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61057491929717303591467103 91586237894575955387200655)
    ·
      refine ⟨137379356841863933080800983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91586237894575955387200655 137379356841863933080800983)
      ·
        refine ⟨206069035262795899621201475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137379356841863933080800983 206069035262795899621201475)
        ·
          refine ⟨309103552894193849431802213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206069035262795899621201475 309103552894193849431802213)
          ·
            refine ⟨57956916167661346768462915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 309103552894193849431802213 57956916167661346768462915)
            ·
              refine ⟨86935374251492020152694373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57956916167661346768462915 86935374251492020152694373)
              ·
                refine ⟨16300382672154753778630195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86935374251492020152694373 16300382672154753778630195)
                ·
                  refine ⟨24450574008232130667945293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16300382672154753778630195 24450574008232130667945293)
                  ·
                    refine ⟨9168965253087049000479485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24450574008232130667945293 9168965253087049000479485)
                    ·
                      refine ⟨3438361969907643375179807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9168965253087049000479485 3438361969907643375179807)
                      ·
                        rfl

theorem cell23_6696186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_6696186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696186 prefixEnd_6696186 := by exact prefixLift 6696186
  have htrace : WordTrace (prefixWord ++ tailWord_6696186) baseStart_6696186 baseEnd_6696186 := by
    simpa [prefixWord, tailWord_6696186, baseEnd_6696186] using wordTrace_append hprefix tailTrace_6696186
  have hstable : (prefixWord ++ tailWord_6696186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696186).length < 2 ^ (prefixWord ++ tailWord_6696186).sum := by decide
  have hdescent : baseEnd_6696186 < baseStart_6696186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696190 : List Nat := [4, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_6696190 : Nat := 118140960795 + 6696190 * 2 ^ 59
def prefixEnd_6696190 : Nat := 4983230072969 + 3 ^ 40 * 6696190 * 2
def baseEnd_6696190 : Nat := 3438364023830261359529789

theorem tailTrace_6696190 : CollatzResearch.WordTrace tailWord_6696190 prefixEnd_6696190 3438364023830261359529789 := by
  unfold tailWord_6696190
  simp only [CollatzResearch.WordTrace]
  refine ⟨30528764201356840381126753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162820075740569815366009349 30528764201356840381126753)
  ·
    refine ⟨22896573151017630285845065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30528764201356840381126753 22896573151017630285845065)
    ·
      refine ⟨17172429863263222714383799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22896573151017630285845065 17172429863263222714383799)
      ·
        refine ⟨25758644794894834071575699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17172429863263222714383799 25758644794894834071575699)
        ·
          refine ⟨38637967192342251107363549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25758644794894834071575699 38637967192342251107363549)
          ·
            refine ⟨14489237697128344165261331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38637967192342251107363549 14489237697128344165261331)
            ·
              refine ⟨21733856545692516247891997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14489237697128344165261331 21733856545692516247891997)
              ·
                refine ⟨8150196204634693592959499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21733856545692516247891997 8150196204634693592959499)
                ·
                  refine ⟨12225294306952040389439249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8150196204634693592959499 12225294306952040389439249)
                  ·
                    refine ⟨9168970730214030292079437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12225294306952040389439249 9168970730214030292079437)
                    ·
                      refine ⟨3438364023830261359529789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9168970730214030292079437 3438364023830261359529789)
                      ·
                        rfl

theorem cell23_6696190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_6696190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696190 prefixEnd_6696190 := by exact prefixLift 6696190
  have htrace : WordTrace (prefixWord ++ tailWord_6696190) baseStart_6696190 baseEnd_6696190 := by
    simpa [prefixWord, tailWord_6696190, baseEnd_6696190] using wordTrace_append hprefix tailTrace_6696190
  have hstable : (prefixWord ++ tailWord_6696190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696190).length < 2 ^ (prefixWord ++ tailWord_6696190).sum := by decide
  have hdescent : baseEnd_6696190 < baseStart_6696190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696203 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 4, 1, 3]
def baseStart_6696203 : Nat := 118140960795 + 6696203 * 2 ^ 59
def prefixEnd_6696203 : Nat := 4983230072969 + 3 ^ 40 * 6696203 * 2
def baseEnd_6696203 : Nat := 3438370699078769808667229

theorem tailTrace_6696203 : CollatzResearch.WordTrace tailWord_6696203 prefixEnd_6696203 3438370699078769808667229 := by
  unfold tailWord_6696203
  simp only [CollatzResearch.WordTrace]
  refine ⟨244230587759807626269237263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162820391839871750846158175 244230587759807626269237263)
  ·
    refine ⟨366345881639711439403855895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244230587759807626269237263 366345881639711439403855895)
    ·
      refine ⟨549518822459567159105783843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366345881639711439403855895 549518822459567159105783843)
      ·
        refine ⟨824278233689350738658675765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549518822459567159105783843 824278233689350738658675765)
        ·
          refine ⟨77276084408376631749250853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 824278233689350738658675765 77276084408376631749250853)
          ·
            refine ⟨14489265826570618452984535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77276084408376631749250853 14489265826570618452984535)
            ·
              refine ⟨21733898739855927679476803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14489265826570618452984535 21733898739855927679476803)
              ·
                refine ⟨32600848109783891519215205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21733898739855927679476803 32600848109783891519215205)
                ·
                  refine ⟨6112659020584479659852851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32600848109783891519215205 6112659020584479659852851)
                  ·
                    refine ⟨9168988530876719489779277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6112659020584479659852851 9168988530876719489779277)
                    ·
                      refine ⟨3438370699078769808667229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9168988530876719489779277 3438370699078769808667229)
                      ·
                        rfl

theorem cell23_6696203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 1, 3].length) (baseStart_6696203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696203 prefixEnd_6696203 := by exact prefixLift 6696203
  have htrace : WordTrace (prefixWord ++ tailWord_6696203) baseStart_6696203 baseEnd_6696203 := by
    simpa [prefixWord, tailWord_6696203, baseEnd_6696203] using wordTrace_append hprefix tailTrace_6696203
  have hstable : (prefixWord ++ tailWord_6696203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696203).length < 2 ^ (prefixWord ++ tailWord_6696203).sum := by decide
  have hdescent : baseEnd_6696203 < baseStart_6696203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696259 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 9]
def baseStart_6696259 : Nat := 118140960795 + 6696259 * 2 ^ 59
def prefixEnd_6696259 : Nat := 4983230072969 + 3 ^ 40 * 6696259 * 2
def baseEnd_6696259 : Nat := 3438399453995421589566971

theorem tailTrace_6696259 : CollatzResearch.WordTrace tailWord_6696259 prefixEnd_6696259 3438399453995421589566971 := by
  unfold tailWord_6696259
  simp only [CollatzResearch.WordTrace]
  refine ⟨244232630247604747833275831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162821753498403165222183887 244232630247604747833275831)
  ·
    refine ⟨366348945371407121749913747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244232630247604747833275831 366348945371407121749913747)
    ·
      refine ⟨549523418057110682624870621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366348945371407121749913747 549523418057110682624870621)
      ·
        refine ⟨206071281771416505984326483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 549523418057110682624870621 206071281771416505984326483)
        ·
          refine ⟨309106922657124758976489725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206071281771416505984326483 309106922657124758976489725)
          ·
            refine ⟨115915095996421784616183647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309106922657124758976489725 115915095996421784616183647)
            ·
              refine ⟨173872643994632676924275471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115915095996421784616183647 173872643994632676924275471)
              ·
                refine ⟨260808965991949015386413207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173872643994632676924275471 260808965991949015386413207)
                ·
                  refine ⟨391213448987923523079619811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260808965991949015386413207 391213448987923523079619811)
                  ·
                    refine ⟨586820173481885284619429717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 391213448987923523079619811 586820173481885284619429717)
                    ·
                      refine ⟨3438399453995421589566971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 586820173481885284619429717 3438399453995421589566971)
                      ·
                        rfl

theorem cell23_6696259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_6696259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696259 prefixEnd_6696259 := by exact prefixLift 6696259
  have htrace : WordTrace (prefixWord ++ tailWord_6696259) baseStart_6696259 baseEnd_6696259 := by
    simpa [prefixWord, tailWord_6696259, baseEnd_6696259] using wordTrace_append hprefix tailTrace_6696259
  have hstable : (prefixWord ++ tailWord_6696259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696259).length < 2 ^ (prefixWord ++ tailWord_6696259).sum := by decide
  have hdescent : baseEnd_6696259 < baseStart_6696259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696277 : List Nat := [1, 3, 2, 2, 3, 2, 1, 3, 2, 2, 2]
def baseStart_6696277 : Nat := 118140960795 + 6696277 * 2 ^ 59
def prefixEnd_6696277 : Nat := 4983230072969 + 3 ^ 40 * 6696277 * 2
def baseEnd_6696277 : Nat := 3438408696647202519141889

theorem tailTrace_6696277 : CollatzResearch.WordTrace tailWord_6696277 prefixEnd_6696277 3438408696647202519141889 := by
  unfold tailWord_6696277
  simp only [CollatzResearch.WordTrace]
  refine ⟨244233286761539536907431085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162822191174359691271620723 244233286761539536907431085)
  ·
    refine ⟨91587482535577326340286657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244233286761539536907431085 91587482535577326340286657)
    ·
      refine ⟨68690611901682994755214993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91587482535577326340286657 68690611901682994755214993)
      ·
        refine ⟨51517958926262246066411245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68690611901682994755214993 51517958926262246066411245)
        ·
          refine ⟨19319234597348342274904217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51517958926262246066411245 19319234597348342274904217)
          ·
            refine ⟨14489425948011256706178163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19319234597348342274904217 14489425948011256706178163)
            ·
              refine ⟨21734138922016885059267245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14489425948011256706178163 21734138922016885059267245)
              ·
                refine ⟨8150302095756331897225217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21734138922016885059267245 8150302095756331897225217)
                ·
                  refine ⟨6112726571817248922918913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8150302095756331897225217 6112726571817248922918913)
                  ·
                    refine ⟨4584544928862936692189185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6112726571817248922918913 4584544928862936692189185)
                    ·
                      refine ⟨3438408696647202519141889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4584544928862936692189185 3438408696647202519141889)
                      ·
                        rfl

theorem cell23_6696277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_6696277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696277 prefixEnd_6696277 := by exact prefixLift 6696277
  have htrace : WordTrace (prefixWord ++ tailWord_6696277) baseStart_6696277 baseEnd_6696277 := by
    simpa [prefixWord, tailWord_6696277, baseEnd_6696277] using wordTrace_append hprefix tailTrace_6696277
  have hstable : (prefixWord ++ tailWord_6696277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696277).length < 2 ^ (prefixWord ++ tailWord_6696277).sum := by decide
  have hdescent : baseEnd_6696277 < baseStart_6696277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696306 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_6696306 : Nat := 118140960795 + 6696306 * 2 ^ 59
def prefixEnd_6696306 : Nat := 4983230072969 + 3 ^ 40 * 6696306 * 2
def baseEnd_6696306 : Nat := 3438423587586182905679255

theorem tailTrace_6696306 : CollatzResearch.WordTrace tailWord_6696306 prefixEnd_6696306 3438423587586182905679255 := by
  unfold tailWord_6696306
  simp only [CollatzResearch.WordTrace]
  refine ⟨61058586119608618715059193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162822896318956316573491181 61058586119608618715059193)
  ·
    refine ⟨45793939589706464036294395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61058586119608618715059193 45793939589706464036294395)
    ·
      refine ⟨68690909384559696054441593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45793939589706464036294395 68690909384559696054441593)
      ·
        refine ⟨51518182038419772040831195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68690909384559696054441593 51518182038419772040831195)
        ·
          refine ⟨77277273057629658061246793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51518182038419772040831195 77277273057629658061246793)
          ·
            refine ⟨57957954793222243545935095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77277273057629658061246793 57957954793222243545935095)
            ·
              refine ⟨86936932189833365318902643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57957954793222243545935095 86936932189833365318902643)
              ·
                refine ⟨130405398284750047978353965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86936932189833365318902643 130405398284750047978353965)
                ·
                  refine ⟨48902024356781267991882737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130405398284750047978353965 48902024356781267991882737)
                  ·
                    refine ⟨36676518267585950993912053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48902024356781267991882737 36676518267585950993912053)
                    ·
                      refine ⟨3438423587586182905679255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36676518267585950993912053 3438423587586182905679255)
                      ·
                        rfl

theorem cell23_6696306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_6696306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696306 prefixEnd_6696306 := by exact prefixLift 6696306
  have htrace : WordTrace (prefixWord ++ tailWord_6696306) baseStart_6696306 baseEnd_6696306 := by
    simpa [prefixWord, tailWord_6696306, baseEnd_6696306] using wordTrace_append hprefix tailTrace_6696306
  have hstable : (prefixWord ++ tailWord_6696306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696306).length < 2 ^ (prefixWord ++ tailWord_6696306).sum := by decide
  have hdescent : baseEnd_6696306 < baseStart_6696306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696356 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 8]
def baseStart_6696356 : Nat := 118140960795 + 6696356 * 2 ^ 59
def prefixEnd_6696356 : Nat := 4983230072969 + 3 ^ 40 * 6696356 * 2
def baseEnd_6696356 : Nat := 382049917957656412228225

theorem tailTrace_6696356 : CollatzResearch.WordTrace tailWord_6696356 prefixEnd_6696356 382049917957656412228225 := by
  unfold tailWord_6696356
  simp only [CollatzResearch.WordTrace]
  refine ⟨122118084064126666699778461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162824112085502222266371281 122118084064126666699778461)
  ·
    refine ⟨45794281524047500012416923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122118084064126666699778461 45794281524047500012416923)
    ·
      refine ⟨68691422286071250018625385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45794281524047500012416923 68691422286071250018625385)
      ·
        refine ⟨51518566714553437513969039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68691422286071250018625385 51518566714553437513969039)
        ·
          refine ⟨77277850071830156270953559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51518566714553437513969039 77277850071830156270953559)
          ·
            refine ⟨115916775107745234406430339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77277850071830156270953559 115916775107745234406430339)
            ·
              refine ⟨173875162661617851609645509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115916775107745234406430339 173875162661617851609645509)
              ·
                refine ⟨32601592999053347176808533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173875162661617851609645509 32601592999053347176808533)
                ·
                  refine ⟨382049917957656412228225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32601592999053347176808533 382049917957656412228225)
                  ·
                    rfl

theorem cell23_6696356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_6696356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696356 prefixEnd_6696356 := by exact prefixLift 6696356
  have htrace : WordTrace (prefixWord ++ tailWord_6696356) baseStart_6696356 baseEnd_6696356 := by
    simpa [prefixWord, tailWord_6696356, baseEnd_6696356] using wordTrace_append hprefix tailTrace_6696356
  have hstable : (prefixWord ++ tailWord_6696356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696356).length < 2 ^ (prefixWord ++ tailWord_6696356).sum := by decide
  have hdescent : baseEnd_6696356 < baseStart_6696356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696373 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 8]
def baseStart_6696373 : Nat := 118140960795 + 6696373 * 2 ^ 59
def prefixEnd_6696373 : Nat := 4983230072969 + 3 ^ 40 * 6696373 * 2
def baseEnd_6696373 : Nat := 382050887865559349282383

theorem tailTrace_6696373 : CollatzResearch.WordTrace tailWord_6696373 prefixEnd_6696373 382050887865559349282383 := by
  unfold tailWord_6696373
  simp only [CollatzResearch.WordTrace]
  refine ⟨244236788169191745302925773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162824525446127830201950515 244236788169191745302925773)
  ·
    refine ⟨91588795563446904488597165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244236788169191745302925773 91588795563446904488597165)
    ·
      refine ⟨34345798336292589183223937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91588795563446904488597165 34345798336292589183223937)
      ·
        refine ⟨25759348752219441887417953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34345798336292589183223937 25759348752219441887417953)
        ·
          refine ⟨19319511564164581415563465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25759348752219441887417953 19319511564164581415563465)
          ·
            refine ⟨14489633673123436061672599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19319511564164581415563465 14489633673123436061672599)
            ·
              refine ⟨21734450509685154092508899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14489633673123436061672599 21734450509685154092508899)
              ·
                refine ⟨32601675764527731138763349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21734450509685154092508899 32601675764527731138763349)
                ·
                  refine ⟨382050887865559349282383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32601675764527731138763349 382050887865559349282383)
                  ·
                    rfl

theorem cell23_6696373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 8].length) (baseStart_6696373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696373 prefixEnd_6696373 := by exact prefixLift 6696373
  have htrace : WordTrace (prefixWord ++ tailWord_6696373) baseStart_6696373 baseEnd_6696373 := by
    simpa [prefixWord, tailWord_6696373, baseEnd_6696373] using wordTrace_append hprefix tailTrace_6696373
  have hstable : (prefixWord ++ tailWord_6696373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696373).length < 2 ^ (prefixWord ++ tailWord_6696373).sum := by decide
  have hdescent : baseEnd_6696373 < baseStart_6696373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696376 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 1, 2, 6]
def baseStart_6696376 : Nat := 118140960795 + 6696376 * 2 ^ 59
def prefixEnd_6696376 : Nat := 4983230072969 + 3 ^ 40 * 6696376 * 2
def baseEnd_6696376 : Nat := 3438459531231997631803933

theorem tailTrace_6696376 : CollatzResearch.WordTrace tailWord_6696376 prefixEnd_6696376 3438459531231997631803933 := by
  unfold tailWord_6696376
  simp only [CollatzResearch.WordTrace]
  refine ⟨122118448794090438407642491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162824598392120584543523321 122118448794090438407642491)
  ·
    refine ⟨183177673191135657611463737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122118448794090438407642491 183177673191135657611463737)
    ·
      refine ⟨137383254893351743208597803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183177673191135657611463737 137383254893351743208597803)
      ·
        refine ⟨206074882340027614812896705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137383254893351743208597803 206074882340027614812896705)
        ·
          refine ⟨154556161755020711109672529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206074882340027614812896705 154556161755020711109672529)
          ·
            refine ⟨115917121316265533332254397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154556161755020711109672529 115917121316265533332254397)
            ·
              refine ⟨43468920493599574999595399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115917121316265533332254397 43468920493599574999595399)
              ·
                refine ⟨65203380740399362499393099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43468920493599574999595399 65203380740399362499393099)
                ·
                  refine ⟨97805071110599043749089649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65203380740399362499393099 97805071110599043749089649)
                  ·
                    refine ⟨73353803332949282811817237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97805071110599043749089649 73353803332949282811817237)
                    ·
                      refine ⟨3438459531231997631803933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73353803332949282811817237 3438459531231997631803933)
                      ·
                        rfl

theorem cell23_6696376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_6696376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696376 prefixEnd_6696376 := by exact prefixLift 6696376
  have htrace : WordTrace (prefixWord ++ tailWord_6696376) baseStart_6696376 baseEnd_6696376 := by
    simpa [prefixWord, tailWord_6696376, baseEnd_6696376] using wordTrace_append hprefix tailTrace_6696376
  have hstable : (prefixWord ++ tailWord_6696376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696376).length < 2 ^ (prefixWord ++ tailWord_6696376).sum := by decide
  have hdescent : baseEnd_6696376 < baseStart_6696376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696410 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2]
def baseStart_6696410 : Nat := 118140960795 + 6696410 * 2 ^ 59
def prefixEnd_6696410 : Nat := 4983230072969 + 3 ^ 40 * 6696410 * 2
def baseEnd_6696410 : Nat := 3438476989574250498778777

theorem tailTrace_6696410 : CollatzResearch.WordTrace tailWord_6696410 prefixEnd_6696410 3438476989574250498778777 := by
  unfold tailWord_6696410
  simp only [CollatzResearch.WordTrace]
  refine ⟨61059534417514425155505671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162825425113371800414681789 61059534417514425155505671)
  ·
    refine ⟨91589301626271637733258507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61059534417514425155505671 91589301626271637733258507)
    ·
      refine ⟨137383952439407456599887761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91589301626271637733258507 137383952439407456599887761)
      ·
        refine ⟨103037964329555592449915821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137383952439407456599887761 103037964329555592449915821)
        ·
          refine ⟨38639236623583347168718433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103037964329555592449915821 38639236623583347168718433)
          ·
            refine ⟨28979427467687510376538825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38639236623583347168718433 28979427467687510376538825)
            ·
              refine ⟨21734570600765632782404119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28979427467687510376538825 21734570600765632782404119)
              ·
                refine ⟨32601855901148449173606179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21734570600765632782404119 32601855901148449173606179)
                ·
                  refine ⟨48902783851722673760409269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32601855901148449173606179 48902783851722673760409269)
                  ·
                    refine ⟨4584635986099000665038369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48902783851722673760409269 4584635986099000665038369)
                    ·
                      refine ⟨3438476989574250498778777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4584635986099000665038369 3438476989574250498778777)
                      ·
                        rfl

theorem cell23_6696410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_6696410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696410 prefixEnd_6696410 := by exact prefixLift 6696410
  have htrace : WordTrace (prefixWord ++ tailWord_6696410) baseStart_6696410 baseEnd_6696410 := by
    simpa [prefixWord, tailWord_6696410, baseEnd_6696410] using wordTrace_append hprefix tailTrace_6696410
  have hstable : (prefixWord ++ tailWord_6696410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696410).length < 2 ^ (prefixWord ++ tailWord_6696410).sum := by decide
  have hdescent : baseEnd_6696410 < baseStart_6696410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696434 : List Nat := [3, 2, 1, 4, 1, 3, 1, 1, 3, 1, 3]
def baseStart_6696434 : Nat := 118140960795 + 6696434 * 2 ^ 59
def prefixEnd_6696434 : Nat := 4983230072969 + 3 ^ 40 * 6696434 * 2
def baseEnd_6696434 : Nat := 3438489313109958404878667

theorem tailTrace_6696434 : CollatzResearch.WordTrace tailWord_6696434 prefixEnd_6696434 3438489313109958404878667 := by
  unfold tailWord_6696434
  simp only [CollatzResearch.WordTrace]
  refine ⟨61059753255492688180224089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162826008681313835147264237 61059753255492688180224089)
  ·
    refine ⟨45794814941619516135168067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61059753255492688180224089 45794814941619516135168067)
    ·
      refine ⟨68692222412429274202752101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45794814941619516135168067 68692222412429274202752101)
      ·
        refine ⟨12879791702330488913016019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68692222412429274202752101 12879791702330488913016019)
        ·
          refine ⟨19319687553495733369524029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12879791702330488913016019 19319687553495733369524029)
          ·
            refine ⟨7244882832560900013571511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19319687553495733369524029 7244882832560900013571511)
            ·
              refine ⟨10867324248841350020357267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7244882832560900013571511 10867324248841350020357267)
              ·
                refine ⟨16300986373262025030535901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10867324248841350020357267 16300986373262025030535901)
                ·
                  refine ⟨6112869889973259386450963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16300986373262025030535901 6112869889973259386450963)
                  ·
                    refine ⟨9169304834959889079676445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6112869889973259386450963 9169304834959889079676445)
                    ·
                      refine ⟨3438489313109958404878667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9169304834959889079676445 3438489313109958404878667)
                      ·
                        rfl

theorem cell23_6696434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_6696434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696434 prefixEnd_6696434 := by exact prefixLift 6696434
  have htrace : WordTrace (prefixWord ++ tailWord_6696434) baseStart_6696434 baseEnd_6696434 := by
    simpa [prefixWord, tailWord_6696434, baseEnd_6696434] using wordTrace_append hprefix tailTrace_6696434
  have hstable : (prefixWord ++ tailWord_6696434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696434).length < 2 ^ (prefixWord ++ tailWord_6696434).sum := by decide
  have hdescent : baseEnd_6696434 < baseStart_6696434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696443 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 3]
def baseStart_6696443 : Nat := 118140960795 + 6696443 * 2 ^ 59
def prefixEnd_6696443 : Nat := 4983230072969 + 3 ^ 40 * 6696443 * 2
def baseEnd_6696443 : Nat := 3438493934435848869666125

theorem tailTrace_6696443 : CollatzResearch.WordTrace tailWord_6696443 prefixEnd_6696443 3438493934435848869666125 := by
  unfold tailWord_6696443
  simp only [CollatzResearch.WordTrace]
  refine ⟨244239341278938147257973983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162826227519292098171982655 244239341278938147257973983)
  ·
    refine ⟨366359011918407220886960975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244239341278938147257973983 366359011918407220886960975)
    ·
      refine ⟨549538517877610831330441463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366359011918407220886960975 549538517877610831330441463)
      ·
        refine ⟨824307776816416246995662195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549538517877610831330441463 824307776816416246995662195)
        ·
          refine ⟨1236461665224624370493493293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824307776816416246995662195 1236461665224624370493493293)
          ·
            refine ⟨463673124459234138935059985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1236461665224624370493493293 463673124459234138935059985)
            ·
              refine ⟨347754843344425604201294989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463673124459234138935059985 347754843344425604201294989)
              ·
                refine ⟨130408066254159601575485621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347754843344425604201294989 130408066254159601575485621)
                ·
                  refine ⟨12225756211327462647701777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130408066254159601575485621 12225756211327462647701777)
                  ·
                    refine ⟨9169317158495596985776333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12225756211327462647701777 9169317158495596985776333)
                    ·
                      refine ⟨3438493934435848869666125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9169317158495596985776333 3438493934435848869666125)
                      ·
                        rfl

theorem cell23_6696443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 3].length) (baseStart_6696443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696443 prefixEnd_6696443 := by exact prefixLift 6696443
  have htrace : WordTrace (prefixWord ++ tailWord_6696443) baseStart_6696443 baseEnd_6696443 := by
    simpa [prefixWord, tailWord_6696443, baseEnd_6696443] using wordTrace_append hprefix tailTrace_6696443
  have hstable : (prefixWord ++ tailWord_6696443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696443).length < 2 ^ (prefixWord ++ tailWord_6696443).sum := by decide
  have hdescent : baseEnd_6696443 < baseStart_6696443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696453 : List Nat := [1, 3, 1, 1, 2, 2, 1, 5, 1, 2, 4]
def baseStart_6696453 : Nat := 118140960795 + 6696453 * 2 ^ 59
def prefixEnd_6696453 : Nat := 4983230072969 + 3 ^ 40 * 6696453 * 2
def baseEnd_6696453 : Nat := 3438499069242393830541079

theorem tailTrace_6696453 : CollatzResearch.WordTrace tailWord_6696453 prefixEnd_6696453 3438499069242393830541079 := by
  unfold tailWord_6696453
  simp only [CollatzResearch.WordTrace]
  refine ⟨244239706008901918965838013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162826470672601279310558675 244239706008901918965838013)
  ·
    refine ⟨91589889753338219612189255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244239706008901918965838013 91589889753338219612189255)
    ·
      refine ⟨137384834630007329418283883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91589889753338219612189255 137384834630007329418283883)
      ·
        refine ⟨206077251945010994127425825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137384834630007329418283883 206077251945010994127425825)
        ·
          refine ⟨154557938958758245595569369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206077251945010994127425825 154557938958758245595569369)
          ·
            refine ⟨115918454219068684196677027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154557938958758245595569369 115918454219068684196677027)
            ·
              refine ⟨173877681328603026295015541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115918454219068684196677027 173877681328603026295015541)
              ·
                refine ⟨16301032624556533715157707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173877681328603026295015541 16301032624556533715157707)
                ·
                  refine ⟨24451548936834800572736561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16301032624556533715157707 24451548936834800572736561)
                  ·
                    refine ⟨18338661702626100429552421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24451548936834800572736561 18338661702626100429552421)
                    ·
                      refine ⟨3438499069242393830541079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18338661702626100429552421 3438499069242393830541079)
                      ·
                        rfl

theorem cell23_6696453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_6696453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696453 prefixEnd_6696453 := by exact prefixLift 6696453
  have htrace : WordTrace (prefixWord ++ tailWord_6696453) baseStart_6696453 baseEnd_6696453 := by
    simpa [prefixWord, tailWord_6696453, baseEnd_6696453] using wordTrace_append hprefix tailTrace_6696453
  have hstable : (prefixWord ++ tailWord_6696453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696453).length < 2 ^ (prefixWord ++ tailWord_6696453).sum := by decide
  have hdescent : baseEnd_6696453 < baseStart_6696453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696474 : List Nat := [3, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2]
def baseStart_6696474 : Nat := 118140960795 + 6696474 * 2 ^ 59
def prefixEnd_6696474 : Nat := 4983230072969 + 3 ^ 40 * 6696474 * 2
def baseEnd_6696474 : Nat := 3438509852336138248378483

theorem tailTrace_6696474 : CollatzResearch.WordTrace tailWord_6696474 prefixEnd_6696474 3438509852336138248378483 := by
  unfold tailWord_6696474
  simp only [CollatzResearch.WordTrace]
  refine ⟨61060117985456459888088119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162826981294550559701568317 61060117985456459888088119)
  ·
    refine ⟨91590176978184689832132179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61060117985456459888088119 91590176978184689832132179)
    ·
      refine ⟨137385265467277034748198269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91590176978184689832132179 137385265467277034748198269)
      ·
        refine ⟨51519474550228888030574351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137385265467277034748198269 51519474550228888030574351)
        ·
          refine ⟨77279211825343332045861527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51519474550228888030574351 77279211825343332045861527)
          ·
            refine ⟨115918817738014998068792291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77279211825343332045861527 115918817738014998068792291)
            ·
              refine ⟨173878226607022497103188437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115918817738014998068792291 173878226607022497103188437)
              ·
                refine ⟨4075270936102089775855979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 173878226607022497103188437 4075270936102089775855979)
                ·
                  refine ⟨6112906404153134663783969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4075270936102089775855979 6112906404153134663783969)
                  ·
                    refine ⟨4584679803114850997837977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6112906404153134663783969 4584679803114850997837977)
                    ·
                      refine ⟨3438509852336138248378483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4584679803114850997837977 3438509852336138248378483)
                      ·
                        rfl

theorem cell23_6696474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_6696474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696474 prefixEnd_6696474 := by exact prefixLift 6696474
  have htrace : WordTrace (prefixWord ++ tailWord_6696474) baseStart_6696474 baseEnd_6696474 := by
    simpa [prefixWord, tailWord_6696474, baseEnd_6696474] using wordTrace_append hprefix tailTrace_6696474
  have hstable : (prefixWord ++ tailWord_6696474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696474).length < 2 ^ (prefixWord ++ tailWord_6696474).sum := by decide
  have hdescent : baseEnd_6696474 < baseStart_6696474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696490 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_6696490 : Nat := 118140960795 + 6696490 * 2 ^ 59
def prefixEnd_6696490 : Nat := 4983230072969 + 3 ^ 40 * 6696490 * 2
def baseEnd_6696490 : Nat := 3438518068026610185778409

theorem tailTrace_6696490 : CollatzResearch.WordTrace tailWord_6696490 prefixEnd_6696490 3438518068026610185778409 := by
  unfold tailWord_6696490
  simp only [CollatzResearch.WordTrace]
  refine ⟨61060263877441968571233731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162827370339845249523289949 61060263877441968571233731)
  ·
    refine ⟨91590395816162952856850597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61060263877441968571233731 91590395816162952856850597)
    ·
      refine ⟨17173199215530553660659487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91590395816162952856850597 17173199215530553660659487)
      ·
        refine ⟨25759798823295830490989231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17173199215530553660659487 25759798823295830490989231)
        ·
          refine ⟨38639698234943745736483847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25759798823295830490989231 38639698234943745736483847)
          ·
            refine ⟨57959547352415618604725771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38639698234943745736483847 57959547352415618604725771)
            ·
              refine ⟨86939321028623427907088657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57959547352415618604725771 86939321028623427907088657)
              ·
                refine ⟨65204490771467570930316493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86939321028623427907088657 65204490771467570930316493)
                ·
                  refine ⟨24451684039300339098868685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65204490771467570930316493 24451684039300339098868685)
                  ·
                    refine ⟨9169381514737627162075757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24451684039300339098868685 9169381514737627162075757)
                    ·
                      refine ⟨3438518068026610185778409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9169381514737627162075757 3438518068026610185778409)
                      ·
                        rfl

theorem cell23_6696490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_6696490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696490 prefixEnd_6696490 := by exact prefixLift 6696490
  have htrace : WordTrace (prefixWord ++ tailWord_6696490) baseStart_6696490 baseEnd_6696490 := by
    simpa [prefixWord, tailWord_6696490, baseEnd_6696490] using wordTrace_append hprefix tailTrace_6696490
  have hstable : (prefixWord ++ tailWord_6696490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696490).length < 2 ^ (prefixWord ++ tailWord_6696490).sum := by decide
  have hdescent : baseEnd_6696490 < baseStart_6696490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696517 : List Nat := [1, 3, 1, 1, 1, 4, 2, 4, 1, 3, 2]
def baseStart_6696517 : Nat := 118140960795 + 6696517 * 2 ^ 59
def prefixEnd_6696517 : Nat := 4983230072969 + 3 ^ 40 * 6696517 * 2
def baseEnd_6696517 : Nat := 3438531932004281580140785

theorem tailTrace_6696517 : CollatzResearch.WordTrace tailWord_6696517 prefixEnd_6696517 3438531932004281580140785 := by
  unfold tailWord_6696517
  simp only [CollatzResearch.WordTrace]
  refine ⟨244242040280670057896167805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162828026853780038597445203 244242040280670057896167805)
  ·
    refine ⟨91590765105251271711062927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244242040280670057896167805 91590765105251271711062927)
    ·
      refine ⟨137386147657876907566594391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91590765105251271711062927 137386147657876907566594391)
      ·
        refine ⟨206079221486815361349891587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137386147657876907566594391 206079221486815361349891587)
        ·
          refine ⟨309118832230223042024837381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206079221486815361349891587 309118832230223042024837381)
          ·
            refine ⟨57959781043166820379657009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 309118832230223042024837381 57959781043166820379657009)
            ·
              refine ⟨43469835782375115284742757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57959781043166820379657009 43469835782375115284742757)
              ·
                refine ⟨8150594209195334115889267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43469835782375115284742757 8150594209195334115889267)
                ·
                  refine ⟨12225891313793001173833901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8150594209195334115889267 12225891313793001173833901)
                  ·
                    refine ⟨4584709242672375440187713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12225891313793001173833901 4584709242672375440187713)
                    ·
                      refine ⟨3438531932004281580140785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4584709242672375440187713 3438531932004281580140785)
                      ·
                        rfl

theorem cell23_6696517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 3, 2].length) (baseStart_6696517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696517 prefixEnd_6696517 := by exact prefixLift 6696517
  have htrace : WordTrace (prefixWord ++ tailWord_6696517) baseStart_6696517 baseEnd_6696517 := by
    simpa [prefixWord, tailWord_6696517, baseEnd_6696517] using wordTrace_append hprefix tailTrace_6696517
  have hstable : (prefixWord ++ tailWord_6696517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696517).length < 2 ^ (prefixWord ++ tailWord_6696517).sum := by decide
  have hdescent : baseEnd_6696517 < baseStart_6696517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696533 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_6696533 : Nat := 118140960795 + 6696533 * 2 ^ 59
def prefixEnd_6696533 : Nat := 4983230072969 + 3 ^ 40 * 6696533 * 2
def baseEnd_6696533 : Nat := 3438540147694753517540711

theorem tailTrace_6696533 : CollatzResearch.WordTrace tailWord_6696533 prefixEnd_6696533 3438540147694753517540711 := by
  unfold tailWord_6696533
  simp only [CollatzResearch.WordTrace]
  refine ⟨244242623848612092628750253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162828415899074728419166835 244242623848612092628750253)
  ·
    refine ⟨91590983943229534735781345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244242623848612092628750253 91590983943229534735781345)
    ·
      refine ⟨68693237957422151051836009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91590983943229534735781345 68693237957422151051836009)
      ·
        refine ⟨51519928468066613288877007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68693237957422151051836009 51519928468066613288877007)
        ·
          refine ⟨77279892702099919933315511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51519928468066613288877007 77279892702099919933315511)
          ·
            refine ⟨115919839053149879899973267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77279892702099919933315511 115919839053149879899973267)
            ·
              refine ⟨173879758579724819849959901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115919839053149879899973267 173879758579724819849959901)
              ·
                refine ⟨65204909467396807443734963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173879758579724819849959901 65204909467396807443734963)
                ·
                  refine ⟨97807364201095211165602445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65204909467396807443734963 97807364201095211165602445)
                  ·
                    refine ⟨36677761575410704187100917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97807364201095211165602445 36677761575410704187100917)
                    ·
                      refine ⟨3438540147694753517540711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36677761575410704187100917 3438540147694753517540711)
                      ·
                        rfl

theorem cell23_6696533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_6696533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696533 prefixEnd_6696533 := by exact prefixLift 6696533
  have htrace : WordTrace (prefixWord ++ tailWord_6696533) baseStart_6696533 baseEnd_6696533 := by
    simpa [prefixWord, tailWord_6696533, baseEnd_6696533] using wordTrace_append hprefix tailTrace_6696533
  have hstable : (prefixWord ++ tailWord_6696533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696533).length < 2 ^ (prefixWord ++ tailWord_6696533).sum := by decide
  have hdescent : baseEnd_6696533 < baseStart_6696533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696540 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 2, 6]
def baseStart_6696540 : Nat := 118140960795 + 6696540 * 2 ^ 59
def prefixEnd_6696540 : Nat := 4983230072969 + 3 ^ 40 * 6696540 * 2
def baseEnd_6696540 : Nat := 1146181247353111663384393

theorem tailTrace_6696540 : CollatzResearch.WordTrace tailWord_6696540 prefixEnd_6696540 1146181247353111663384393 := by
  unfold tailWord_6696540
  simp only [CollatzResearch.WordTrace]
  refine ⟨122121439579793366412127537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162828586106391155216170049 122121439579793366412127537)
  ·
    refine ⟨91591079684845024809095653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122121439579793366412127537 91591079684845024809095653)
    ·
      refine ⟨17173327440908442151705435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91591079684845024809095653 17173327440908442151705435)
      ·
        refine ⟨25759991161362663227558153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17173327440908442151705435 25759991161362663227558153)
        ·
          refine ⟨19319993371021997420668615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25759991161362663227558153 19319993371021997420668615)
          ·
            refine ⟨28979990056532996131002923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19319993371021997420668615 28979990056532996131002923)
            ·
              refine ⟨43469985084799494196504385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28979990056532996131002923 43469985084799494196504385)
              ·
                refine ⟨32602488813599620647378289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43469985084799494196504385 32602488813599620647378289)
                ·
                  refine ⟨24451866610199715485533717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32602488813599620647378289 24451866610199715485533717)
                  ·
                    refine ⟨1146181247353111663384393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24451866610199715485533717 1146181247353111663384393)
                    ·
                      rfl

theorem cell23_6696540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_6696540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696540 prefixEnd_6696540 := by exact prefixLift 6696540
  have htrace : WordTrace (prefixWord ++ tailWord_6696540) baseStart_6696540 baseEnd_6696540 := by
    simpa [prefixWord, tailWord_6696540, baseEnd_6696540] using wordTrace_append hprefix tailTrace_6696540
  have hstable : (prefixWord ++ tailWord_6696540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696540).length < 2 ^ (prefixWord ++ tailWord_6696540).sum := by decide
  have hdescent : baseEnd_6696540 < baseStart_6696540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696541 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_6696541 : Nat := 118140960795 + 6696541 * 2 ^ 59
def prefixEnd_6696541 : Nat := 4983230072969 + 3 ^ 40 * 6696541 * 2
def baseEnd_6696541 : Nat := 3438544255539989486240675

theorem tailTrace_6696541 : CollatzResearch.WordTrace tailWord_6696541 prefixEnd_6696541 3438544255539989486240675 := by
  unfold tailWord_6696541
  simp only [CollatzResearch.WordTrace]
  refine ⟨244242915632583109995041477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162828610421722073330027651 244242915632583109995041477)
  ·
    refine ⟨45795546681109333124070277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244242915632583109995041477 45795546681109333124070277)
    ·
      refine ⟨8586665002707999960763177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45795546681109333124070277 8586665002707999960763177)
      ·
        refine ⟨6439998752030999970572383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8586665002707999960763177 6439998752030999970572383)
        ·
          refine ⟨9659998128046499955858575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6439998752030999970572383 9659998128046499955858575)
          ·
            refine ⟨14489997192069749933787863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9659998128046499955858575 14489997192069749933787863)
            ·
              refine ⟨21734995788104624900681795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14489997192069749933787863 21734995788104624900681795)
              ·
                refine ⟨32602493682156937351022693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21734995788104624900681795 32602493682156937351022693)
                ·
                  refine ⟨6112967565404425753316755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32602493682156937351022693 6112967565404425753316755)
                  ·
                    refine ⟨9169451348106638629975133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6112967565404425753316755 9169451348106638629975133)
                    ·
                      refine ⟨3438544255539989486240675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9169451348106638629975133 3438544255539989486240675)
                      ·
                        rfl

theorem cell23_6696541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_6696541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696541 prefixEnd_6696541 := by exact prefixLift 6696541
  have htrace : WordTrace (prefixWord ++ tailWord_6696541) baseStart_6696541 baseEnd_6696541 := by
    simpa [prefixWord, tailWord_6696541, baseEnd_6696541] using wordTrace_append hprefix tailTrace_6696541
  have hstable : (prefixWord ++ tailWord_6696541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696541).length < 2 ^ (prefixWord ++ tailWord_6696541).sum := by decide
  have hdescent : baseEnd_6696541 < baseStart_6696541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696553 : List Nat := [1, 2, 1, 1, 1, 4, 3, 3, 7]
def baseStart_6696553 : Nat := 118140960795 + 6696553 * 2 ^ 59
def prefixEnd_6696553 : Nat := 4983230072969 + 3 ^ 40 * 6696553 * 2
def baseEnd_6696553 : Nat := 382061157478649271032291

theorem tailTrace_6696553 : CollatzResearch.WordTrace tailWord_6696553 prefixEnd_6696553 382061157478649271032291 := by
  unfold tailWord_6696553
  simp only [CollatzResearch.WordTrace]
  refine ⟨244243353308539636044478313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162828902205693090696318875 244243353308539636044478313)
  ·
    refine ⟨183182514981404727033358735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244243353308539636044478313 183182514981404727033358735)
    ·
      refine ⟨274773772472107090550038103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183182514981404727033358735 274773772472107090550038103)
      ·
        refine ⟨412160658708160635825057155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274773772472107090550038103 412160658708160635825057155)
        ·
          refine ⟨618240988062240953737585733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412160658708160635825057155 618240988062240953737585733)
          ·
            refine ⟨115920185261670178825797325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 618240988062240953737585733 115920185261670178825797325)
            ·
              refine ⟨43470069473126317059673997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115920185261670178825797325 43470069473126317059673997)
              ·
                refine ⟨16301276052422368897377749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43470069473126317059673997 16301276052422368897377749)
                ·
                  refine ⟨382061157478649271032291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16301276052422368897377749 382061157478649271032291)
                  ·
                    rfl

theorem cell23_6696553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 7].length) (baseStart_6696553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696553 prefixEnd_6696553 := by exact prefixLift 6696553
  have htrace : WordTrace (prefixWord ++ tailWord_6696553) baseStart_6696553 baseEnd_6696553 := by
    simpa [prefixWord, tailWord_6696553, baseEnd_6696553] using wordTrace_append hprefix tailTrace_6696553
  have hstable : (prefixWord ++ tailWord_6696553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696553).length < 2 ^ (prefixWord ++ tailWord_6696553).sum := by decide
  have hdescent : baseEnd_6696553 < baseStart_6696553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696560 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 4]
def baseStart_6696560 : Nat := 118140960795 + 6696560 * 2 ^ 59
def prefixEnd_6696560 : Nat := 4983230072969 + 3 ^ 40 * 6696560 * 2
def baseEnd_6696560 : Nat := 3438554011672424911903087

theorem tailTrace_6696560 : CollatzResearch.WordTrace tailWord_6696560 prefixEnd_6696560 3438554011672424911903087 := by
  unfold tailWord_6696560
  simp only [CollatzResearch.WordTrace]
  refine ⟨122121804309757138119991567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162829072413009517493322089 122121804309757138119991567)
  ·
    refine ⟨183182706464635707179987351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122121804309757138119991567 183182706464635707179987351)
    ·
      refine ⟨274774059696953560769981027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183182706464635707179987351 274774059696953560769981027)
      ·
        refine ⟨412161089545430341154971541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274774059696953560769981027 412161089545430341154971541)
        ·
          refine ⟨19320051072442047241639291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 412161089545430341154971541 19320051072442047241639291)
          ·
            refine ⟨28980076608663070862458937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19320051072442047241639291 28980076608663070862458937)
            ·
              refine ⟨21735057456497303146844203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28980076608663070862458937 21735057456497303146844203)
              ·
                refine ⟨32602586184745954720266305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21735057456497303146844203 32602586184745954720266305)
                ·
                  refine ⟨24451939638559466040199729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32602586184745954720266305 24451939638559466040199729)
                  ·
                    refine ⟨18338954728919599530149797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24451939638559466040199729 18338954728919599530149797)
                    ·
                      refine ⟨3438554011672424911903087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18338954728919599530149797 3438554011672424911903087)
                      ·
                        rfl

theorem cell23_6696560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_6696560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696560 prefixEnd_6696560 := by exact prefixLift 6696560
  have htrace : WordTrace (prefixWord ++ tailWord_6696560) baseStart_6696560 baseEnd_6696560 := by
    simpa [prefixWord, tailWord_6696560, baseEnd_6696560] using wordTrace_append hprefix tailTrace_6696560
  have hstable : (prefixWord ++ tailWord_6696560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696560).length < 2 ^ (prefixWord ++ tailWord_6696560).sum := by decide
  have hdescent : baseEnd_6696560 < baseStart_6696560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696600 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 4, 5]
def baseStart_6696600 : Nat := 118140960795 + 6696600 * 2 ^ 59
def prefixEnd_6696600 : Nat := 4983230072969 + 3 ^ 40 * 6696600 * 2
def baseEnd_6696600 : Nat := 1146191516966201585134301

theorem tailTrace_6696600 : CollatzResearch.WordTrace tailWord_6696600 prefixEnd_6696600 1146191516966201585134301 := by
  unfold tailWord_6696600
  simp only [CollatzResearch.WordTrace]
  refine ⟨122122533769684681535719627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162830045026246242047626169 122122533769684681535719627)
  ·
    refine ⟨183183800654527022303579441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122122533769684681535719627 183183800654527022303579441)
    ·
      refine ⟨137387850490895266727684581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183183800654527022303579441 137387850490895266727684581)
      ·
        refine ⟨25760221967042862511440859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137387850490895266727684581 25760221967042862511440859)
        ·
          refine ⟨38640332950564293767161289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25760221967042862511440859 38640332950564293767161289)
          ·
            refine ⟨28980249712923220325370967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38640332950564293767161289 28980249712923220325370967)
            ·
              refine ⟨43470374569384830488056451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28980249712923220325370967 43470374569384830488056451)
              ·
                refine ⟨65205561854077245732084677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43470374569384830488056451 65205561854077245732084677)
                ·
                  refine ⟨12226042847639483574765877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65205561854077245732084677 12226042847639483574765877)
                  ·
                    refine ⟨1146191516966201585134301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12226042847639483574765877 1146191516966201585134301)
                    ·
                      rfl

theorem cell23_6696600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_6696600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696600 prefixEnd_6696600 := by exact prefixLift 6696600
  have htrace : WordTrace (prefixWord ++ tailWord_6696600) baseStart_6696600 baseEnd_6696600 := by
    simpa [prefixWord, tailWord_6696600, baseEnd_6696600] using wordTrace_append hprefix tailTrace_6696600
  have hstable : (prefixWord ++ tailWord_6696600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696600).length < 2 ^ (prefixWord ++ tailWord_6696600).sum := by decide
  have hdescent : baseEnd_6696600 < baseStart_6696600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696604 : List Nat := [2, 2, 3, 2, 4, 1, 1, 1, 7]
def baseStart_6696604 : Nat := 118140960795 + 6696604 * 2 ^ 59
def prefixEnd_6696604 : Nat := 4983230072969 + 3 ^ 40 * 6696604 * 2
def baseEnd_6696604 : Nat := 382064067202358082194765

theorem tailTrace_6696604 : CollatzResearch.WordTrace tailWord_6696604 prefixEnd_6696604 382064067202358082194765 := by
  unfold tailWord_6696604
  simp only [CollatzResearch.WordTrace]
  refine ⟨122122606715677435877292433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162830142287569914503056577 122122606715677435877292433)
  ·
    refine ⟨91591955036758076907969325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122122606715677435877292433 91591955036758076907969325)
    ·
      refine ⟨34346983138784278840488497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91591955036758076907969325 34346983138784278840488497)
      ·
        refine ⟨25760237354088209130366373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34346983138784278840488497 25760237354088209130366373)
        ·
          refine ⟨4830044503891539211943695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25760237354088209130366373 4830044503891539211943695)
          ·
            refine ⟨7245066755837308817915543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4830044503891539211943695 7245066755837308817915543)
            ·
              refine ⟨10867600133755963226873315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7245066755837308817915543 10867600133755963226873315)
              ·
                refine ⟨16301400200633944840309973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10867600133755963226873315 16301400200633944840309973)
                ·
                  refine ⟨382064067202358082194765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16301400200633944840309973 382064067202358082194765)
                  ·
                    rfl

theorem cell23_6696604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 7].length) (baseStart_6696604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696604 prefixEnd_6696604 := by exact prefixLift 6696604
  have htrace : WordTrace (prefixWord ++ tailWord_6696604) baseStart_6696604 baseEnd_6696604 := by
    simpa [prefixWord, tailWord_6696604, baseEnd_6696604] using wordTrace_append hprefix tailTrace_6696604
  have hstable : (prefixWord ++ tailWord_6696604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696604).length < 2 ^ (prefixWord ++ tailWord_6696604).sum := by decide
  have hdescent : baseEnd_6696604 < baseStart_6696604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696637 : List Nat := [1, 4, 1, 2, 1, 2, 4, 1, 2, 1, 4]
def baseStart_6696637 : Nat := 118140960795 + 6696637 * 2 ^ 59
def prefixEnd_6696637 : Nat := 4983230072969 + 3 ^ 40 * 6696637 * 2
def baseEnd_6696637 : Nat := 3438593549682821110640233

theorem tailTrace_6696637 : CollatzResearch.WordTrace tailWord_6696637 prefixEnd_6696637 3438593549682821110640233 := by
  unfold tailWord_6696637
  simp only [CollatzResearch.WordTrace]
  refine ⟨244246417040235318390536165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162830944693490212260357443 244246417040235318390536165)
  ·
    refine ⟨45796203195044122198225531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244246417040235318390536165 45796203195044122198225531)
    ·
      refine ⟨68694304792566183297338297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45796203195044122198225531 68694304792566183297338297)
      ·
        refine ⟨51520728594424637473003723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68694304792566183297338297 51520728594424637473003723)
        ·
          refine ⟨77281092891636956209505585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51520728594424637473003723 77281092891636956209505585)
          ·
            refine ⟨57960819668727717157129189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77281092891636956209505585 57960819668727717157129189)
            ·
              refine ⟨10867653687886446966961723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57960819668727717157129189 10867653687886446966961723)
              ·
                refine ⟨16301480531829670450442585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10867653687886446966961723 16301480531829670450442585)
                ·
                  refine ⟨12226110398872252837831939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16301480531829670450442585 12226110398872252837831939)
                  ·
                    refine ⟨18339165598308379256747909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12226110398872252837831939 18339165598308379256747909)
                    ·
                      refine ⟨3438593549682821110640233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18339165598308379256747909 3438593549682821110640233)
                      ·
                        rfl

theorem cell23_6696637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_6696637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696637 prefixEnd_6696637 := by exact prefixLift 6696637
  have htrace : WordTrace (prefixWord ++ tailWord_6696637) baseStart_6696637 baseEnd_6696637 := by
    simpa [prefixWord, tailWord_6696637, baseEnd_6696637] using wordTrace_append hprefix tailTrace_6696637
  have hstable : (prefixWord ++ tailWord_6696637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696637).length < 2 ^ (prefixWord ++ tailWord_6696637).sum := by decide
  have hdescent : baseEnd_6696637 < baseStart_6696637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696657 : List Nat := [1, 2, 2, 1, 2, 4, 2, 2, 2, 2, 3]
def baseStart_6696657 : Nat := 118140960795 + 6696657 * 2 ^ 59
def prefixEnd_6696657 : Nat := 4983230072969 + 3 ^ 40 * 6696657 * 2
def baseEnd_6696657 : Nat := 3438603819295911032390141

theorem tailTrace_6696657 : CollatzResearch.WordTrace tailWord_6696657 prefixEnd_6696657 3438603819295911032390141 := by
  unfold tailWord_6696657
  simp only [CollatzResearch.WordTrace]
  refine ⟨244247146500162861806264225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162831431000108574537509483 244247146500162861806264225)
  ·
    refine ⟨183185359875122146354698169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244247146500162861806264225 183185359875122146354698169)
    ·
      refine ⟨137389019906341609766023627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183185359875122146354698169 137389019906341609766023627)
      ·
        refine ⟨206083529859512414649035441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137389019906341609766023627 206083529859512414649035441)
        ·
          refine ⟨154562647394634310986776581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206083529859512414649035441 154562647394634310986776581)
          ·
            refine ⟨28980496386493933310020609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154562647394634310986776581 28980496386493933310020609)
            ·
              refine ⟨21735372289870449982515457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28980496386493933310020609 21735372289870449982515457)
              ·
                refine ⟨16301529217402837486886593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21735372289870449982515457 16301529217402837486886593)
                ·
                  refine ⟨12226146913052128115164945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16301529217402837486886593 12226146913052128115164945)
                  ·
                    refine ⟨9169610184789096086373709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12226146913052128115164945 9169610184789096086373709)
                    ·
                      refine ⟨3438603819295911032390141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9169610184789096086373709 3438603819295911032390141)
                      ·
                        rfl

theorem cell23_6696657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_6696657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696657 prefixEnd_6696657 := by exact prefixLift 6696657
  have htrace : WordTrace (prefixWord ++ tailWord_6696657) baseStart_6696657 baseEnd_6696657 := by
    simpa [prefixWord, tailWord_6696657, baseEnd_6696657] using wordTrace_append hprefix tailTrace_6696657
  have hstable : (prefixWord ++ tailWord_6696657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696657).length < 2 ^ (prefixWord ++ tailWord_6696657).sum := by decide
  have hdescent : baseEnd_6696657 < baseStart_6696657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696664 : List Nat := [2, 1, 2, 2, 3, 1, 3, 4, 1, 4]
def baseStart_6696664 : Nat := 118140960795 + 6696664 * 2 ^ 59
def prefixEnd_6696664 : Nat := 4983230072969 + 3 ^ 40 * 6696664 * 2
def baseEnd_6696664 : Nat := 1146202471220164168334203

theorem tailTrace_6696664 : CollatzResearch.WordTrace tailWord_6696664 prefixEnd_6696664 1146202471220164168334203 := by
  unfold tailWord_6696664
  simp only [CollatzResearch.WordTrace]
  refine ⟨122123700905568751000884523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162831601207425001334512697 122123700905568751000884523)
  ·
    refine ⟨183185551358353126501326785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122123700905568751000884523 183185551358353126501326785)
    ·
      refine ⟨137389163518764844875995089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183185551358353126501326785 137389163518764844875995089)
      ·
        refine ⟨103041872639073633656996317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137389163518764844875995089 103041872639073633656996317)
        ·
          refine ⟨38640702239652612621373619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103041872639073633656996317 38640702239652612621373619)
          ·
            refine ⟨57961053359478918932060429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38640702239652612621373619 57961053359478918932060429)
            ·
              refine ⟨21735395009804594599522661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57961053359478918932060429 21735395009804594599522661)
              ·
                refine ⟨4075386564338361487410499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21735395009804594599522661 4075386564338361487410499)
                ·
                  refine ⟨6113079846507542231115749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4075386564338361487410499 6113079846507542231115749)
                  ·
                    refine ⟨1146202471220164168334203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6113079846507542231115749 1146202471220164168334203)
                    ·
                      rfl

theorem cell23_6696664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 1, 4].length) (baseStart_6696664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696664 prefixEnd_6696664 := by exact prefixLift 6696664
  have htrace : WordTrace (prefixWord ++ tailWord_6696664) baseStart_6696664 baseEnd_6696664 := by
    simpa [prefixWord, tailWord_6696664, baseEnd_6696664] using wordTrace_append hprefix tailTrace_6696664
  have hstable : (prefixWord ++ tailWord_6696664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696664).length < 2 ^ (prefixWord ++ tailWord_6696664).sum := by decide
  have hdescent : baseEnd_6696664 < baseStart_6696664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696711 : List Nat := [1, 1, 4, 4, 3, 1, 1, 2, 6]
def baseStart_6696711 : Nat := 118140960795 + 6696711 * 2 ^ 59
def prefixEnd_6696711 : Nat := 4983230072969 + 3 ^ 40 * 6696711 * 2
def baseEnd_6696711 : Nat := 382070171916805980123877

theorem tailTrace_6696711 : CollatzResearch.WordTrace tailWord_6696711 prefixEnd_6696711 382070171916805980123877 := by
  unfold tailWord_6696711
  simp only [CollatzResearch.WordTrace]
  refine ⟨244249116041967229028729987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162832744027978152685819991 244249116041967229028729987)
  ·
    refine ⟨366373674062950843543094981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244249116041967229028729987 366373674062950843543094981)
    ·
      refine ⟨68695063886803283164330309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 366373674062950843543094981 68695063886803283164330309)
      ·
        refine ⟨12880324478775615593311933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68695063886803283164330309 12880324478775615593311933)
        ·
          refine ⟨4830121679540855847491975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12880324478775615593311933 4830121679540855847491975)
          ·
            refine ⟨7245182519311283771237963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4830121679540855847491975 7245182519311283771237963)
            ·
              refine ⟨10867773778966925656856945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7245182519311283771237963 10867773778966925656856945)
              ·
                refine ⟨8150830334225194242642709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10867773778966925656856945 8150830334225194242642709)
                ·
                  refine ⟨382070171916805980123877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8150830334225194242642709 382070171916805980123877)
                  ·
                    rfl

theorem cell23_6696711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 6].length) (baseStart_6696711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696711 prefixEnd_6696711 := by exact prefixLift 6696711
  have htrace : WordTrace (prefixWord ++ tailWord_6696711) baseStart_6696711 baseEnd_6696711 := by
    simpa [prefixWord, tailWord_6696711, baseEnd_6696711] using wordTrace_append hprefix tailTrace_6696711
  have hstable : (prefixWord ++ tailWord_6696711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696711).length < 2 ^ (prefixWord ++ tailWord_6696711).sum := by decide
  have hdescent : baseEnd_6696711 < baseStart_6696711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696737 : List Nat := [1, 2, 3, 2, 1, 3, 3, 1, 1, 6]
def baseStart_6696737 : Nat := 118140960795 + 6696737 * 2 ^ 59
def prefixEnd_6696737 : Nat := 4983230072969 + 3 ^ 40 * 6696737 * 2
def baseEnd_6696737 : Nat := 1146214965916090239796591

theorem tailTrace_6696737 : CollatzResearch.WordTrace tailWord_6696737 prefixEnd_6696737 1146214965916090239796591 := by
  unfold tailWord_6696737
  simp only [CollatzResearch.WordTrace]
  refine ⟨244250064339873035469176465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162833376226582023646117643 244250064339873035469176465)
  ·
    refine ⟨183187548254904776601882349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244250064339873035469176465 183187548254904776601882349)
    ·
      refine ⟨68695330595589291225705881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183187548254904776601882349 68695330595589291225705881)
      ·
        refine ⟨51521497946691968419279411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68695330595589291225705881 51521497946691968419279411)
        ·
          refine ⟨77282246920037952628919117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51521497946691968419279411 77282246920037952628919117)
          ·
            refine ⟨28980842595014232235844669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77282246920037952628919117 28980842595014232235844669)
            ·
              refine ⟨10867815973130337088441751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28980842595014232235844669 10867815973130337088441751)
              ·
                refine ⟨16301723959695505632662627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10867815973130337088441751 16301723959695505632662627)
                ·
                  refine ⟨24452585939543258448993941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16301723959695505632662627 24452585939543258448993941)
                  ·
                    refine ⟨1146214965916090239796591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24452585939543258448993941 1146214965916090239796591)
                    ·
                      rfl

theorem cell23_6696737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_6696737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696737 prefixEnd_6696737 := by exact prefixLift 6696737
  have htrace : WordTrace (prefixWord ++ tailWord_6696737) baseStart_6696737 baseEnd_6696737 := by
    simpa [prefixWord, tailWord_6696737, baseEnd_6696737] using wordTrace_append hprefix tailTrace_6696737
  have hstable : (prefixWord ++ tailWord_6696737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696737).length < 2 ^ (prefixWord ++ tailWord_6696737).sum := by decide
  have hdescent : baseEnd_6696737 < baseStart_6696737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696744 : List Nat := [2, 1, 5, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_6696744 : Nat := 118140960795 + 6696744 * 2 ^ 59
def prefixEnd_6696744 : Nat := 4983230072969 + 3 ^ 40 * 6696744 * 2
def baseEnd_6696744 : Nat := 3438648492112852192002241

theorem tailTrace_6696744 : CollatzResearch.WordTrace tailWord_6696744 prefixEnd_6696744 3438648492112852192002241 := by
  unfold tailWord_6696744
  simp only [CollatzResearch.WordTrace]
  refine ⟨122125159825423837832340643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162833546433898450443120857 122125159825423837832340643)
  ·
    refine ⟨183187739738135756748510965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122125159825423837832340643 183187739738135756748510965)
    ·
      refine ⟨17173850600450227195172903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183187739738135756748510965 17173850600450227195172903)
      ·
        refine ⟨25760775900675340792759355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17173850600450227195172903 25760775900675340792759355)
        ·
          refine ⟨38641163851013011189139033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25760775900675340792759355 38641163851013011189139033)
          ·
            refine ⟨28980872888259758391854275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38641163851013011189139033 28980872888259758391854275)
            ·
              refine ⟨43471309332389637587781413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28980872888259758391854275 43471309332389637587781413)
              ·
                refine ⟨8150870499823057047709015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43471309332389637587781413 8150870499823057047709015)
                ·
                  refine ⟨12226305749734585571563523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8150870499823057047709015 12226305749734585571563523)
                  ·
                    refine ⟨18339458624601878357345285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12226305749734585571563523 18339458624601878357345285)
                    ·
                      refine ⟨3438648492112852192002241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18339458624601878357345285 3438648492112852192002241)
                      ·
                        rfl

theorem cell23_6696744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_6696744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696744 prefixEnd_6696744 := by exact prefixLift 6696744
  have htrace : WordTrace (prefixWord ++ tailWord_6696744) baseStart_6696744 baseEnd_6696744 := by
    simpa [prefixWord, tailWord_6696744, baseEnd_6696744] using wordTrace_append hprefix tailTrace_6696744
  have hstable : (prefixWord ++ tailWord_6696744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696744).length < 2 ^ (prefixWord ++ tailWord_6696744).sum := by decide
  have hdescent : baseEnd_6696744 < baseStart_6696744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696755 : List Nat := [1, 1, 1, 2, 8, 1, 1, 3, 1, 1, 3]
def baseStart_6696755 : Nat := 118140960795 + 6696755 * 2 ^ 59
def prefixEnd_6696755 : Nat := 4983230072969 + 3 ^ 40 * 6696755 * 2
def baseEnd_6696755 : Nat := 3438654140400051648964691

theorem tailTrace_6696755 : CollatzResearch.WordTrace tailWord_6696755 prefixEnd_6696755 3438654140400051648964691 := by
  unfold tailWord_6696755
  simp only [CollatzResearch.WordTrace]
  refine ⟨244250720853807824543331719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162833813902538549695554479 244250720853807824543331719)
  ·
    refine ⟨366376081280711736814997579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244250720853807824543331719 366376081280711736814997579)
    ·
      refine ⟨549564121921067605222496369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366376081280711736814997579 549564121921067605222496369)
      ·
        refine ⟨412173091440800703916872277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 549564121921067605222496369 412173091440800703916872277)
        ·
          refine ⟨4830153415321883249025847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 412173091440800703916872277 4830153415321883249025847)
          ·
            refine ⟨7245230122982824873538771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4830153415321883249025847 7245230122982824873538771)
            ·
              refine ⟨10867845184474237310308157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7245230122982824873538771 10867845184474237310308157)
              ·
                refine ⟨4075441944177838991365559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10867845184474237310308157 4075441944177838991365559)
                ·
                  refine ⟨6113162916266758487048339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4075441944177838991365559 6113162916266758487048339)
                  ·
                    refine ⟨9169744374400137730572509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6113162916266758487048339 9169744374400137730572509)
                    ·
                      refine ⟨3438654140400051648964691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9169744374400137730572509 3438654140400051648964691)
                      ·
                        rfl

theorem cell23_6696755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 1, 1, 3].length) (baseStart_6696755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696755 prefixEnd_6696755 := by exact prefixLift 6696755
  have htrace : WordTrace (prefixWord ++ tailWord_6696755) baseStart_6696755 baseEnd_6696755 := by
    simpa [prefixWord, tailWord_6696755, baseEnd_6696755] using wordTrace_append hprefix tailTrace_6696755
  have hstable : (prefixWord ++ tailWord_6696755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696755).length < 2 ^ (prefixWord ++ tailWord_6696755).sum := by decide
  have hdescent : baseEnd_6696755 < baseStart_6696755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696764 : List Nat := [2, 2, 2, 2, 1, 1, 4, 3, 1, 2, 3]
def baseStart_6696764 : Nat := 118140960795 + 6696764 * 2 ^ 59
def prefixEnd_6696764 : Nat := 4983230072969 + 3 ^ 40 * 6696764 * 2
def baseEnd_6696764 : Nat := 3438658761725942113752149

theorem tailTrace_6696764 : CollatzResearch.WordTrace tailWord_6696764 prefixEnd_6696764 3438658761725942113752149 := by
  unfold tailWord_6696764
  simp only [CollatzResearch.WordTrace]
  refine ⟨122125524555387609540204673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162834032740516812720272897 122125524555387609540204673)
  ·
    refine ⟨91594143416540707155153505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122125524555387609540204673 91594143416540707155153505)
    ·
      refine ⟨68695607562405530366365129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91594143416540707155153505 68695607562405530366365129)
      ·
        refine ⟨51521705671804147774773847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68695607562405530366365129 51521705671804147774773847)
        ·
          refine ⟨77282558507706221662160771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51521705671804147774773847 77282558507706221662160771)
          ·
            refine ⟨115923837761559332493241157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77282558507706221662160771 115923837761559332493241157)
            ·
              refine ⟨21735719580292374842482717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115923837761559332493241157 21735719580292374842482717)
              ·
                refine ⟨8150894842609640565931019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21735719580292374842482717 8150894842609640565931019)
                ·
                  refine ⟨12226342263914460848896529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8150894842609640565931019 12226342263914460848896529)
                  ·
                    refine ⟨9169756697935845636672397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12226342263914460848896529 9169756697935845636672397)
                    ·
                      refine ⟨3438658761725942113752149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9169756697935845636672397 3438658761725942113752149)
                      ·
                        rfl

theorem cell23_6696764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_6696764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696764 prefixEnd_6696764 := by exact prefixLift 6696764
  have htrace : WordTrace (prefixWord ++ tailWord_6696764) baseStart_6696764 baseEnd_6696764 := by
    simpa [prefixWord, tailWord_6696764, baseEnd_6696764] using wordTrace_append hprefix tailTrace_6696764
  have hstable : (prefixWord ++ tailWord_6696764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696764).length < 2 ^ (prefixWord ++ tailWord_6696764).sum := by decide
  have hdescent : baseEnd_6696764 < baseStart_6696764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696767 : List Nat := [1, 1, 2, 2, 6, 2, 9]
def baseStart_6696767 : Nat := 118140960795 + 6696767 * 2 ^ 59
def prefixEnd_6696767 : Nat := 4983230072969 + 3 ^ 40 * 6696767 * 2
def baseEnd_6696767 : Nat := 42452596323060562987835

theorem tailTrace_6696767 : CollatzResearch.WordTrace tailWord_6696767 prefixEnd_6696767 42452596323060562987835 := by
  unfold tailWord_6696767
  simp only [CollatzResearch.WordTrace]
  refine ⟨244251158529764350592768555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162834105686509567061845703 244251158529764350592768555)
  ·
    refine ⟨366376737794646525889152833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244251158529764350592768555 366376737794646525889152833)
    ·
      refine ⟨274782553345984894416864625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366376737794646525889152833 274782553345984894416864625)
      ·
        refine ⟨206086915009488670812648469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274782553345984894416864625 206086915009488670812648469)
        ·
          refine ⟨9660324141069781444342897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 206086915009488670812648469 9660324141069781444342897)
          ·
            refine ⟨7245243105802336083257173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9660324141069781444342897 7245243105802336083257173)
            ·
              refine ⟨42452596323060562987835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7245243105802336083257173 42452596323060562987835)
              ·
                rfl

theorem cell23_6696767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 9].length) (baseStart_6696767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696767 prefixEnd_6696767 := by exact prefixLift 6696767
  have htrace : WordTrace (prefixWord ++ tailWord_6696767) baseStart_6696767 baseEnd_6696767 := by
    simpa [prefixWord, tailWord_6696767, baseEnd_6696767] using wordTrace_append hprefix tailTrace_6696767
  have hstable : (prefixWord ++ tailWord_6696767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696767).length < 2 ^ (prefixWord ++ tailWord_6696767).sum := by decide
  have hdescent : baseEnd_6696767 < baseStart_6696767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696787 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 1, 9, 2]
def baseStart_6696787 : Nat := 118140960795 + 6696787 * 2 ^ 59
def prefixEnd_6696787 : Nat := 4983230072969 + 3 ^ 40 * 6696787 * 2
def baseEnd_6696787 : Nat := 3438670571780995523764543

theorem tailTrace_6696787 : CollatzResearch.WordTrace tailWord_6696787 prefixEnd_6696787 3438670571780995523764543 := by
  unfold tailWord_6696787
  simp only [CollatzResearch.WordTrace]
  refine ⟨244251887989691894008496615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162834591993127929338997743 244251887989691894008496615)
  ·
    refine ⟨366377831984537841012744923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244251887989691894008496615 366377831984537841012744923)
    ·
      refine ⟨549566747976806761519117385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366377831984537841012744923 549566747976806761519117385)
      ·
        refine ⟨412175060982605071139338039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 549566747976806761519117385 412175060982605071139338039)
        ·
          refine ⟨618262591473907606709007059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412175060982605071139338039 618262591473907606709007059)
          ·
            refine ⟨927393887210861410063510589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618262591473907606709007059 927393887210861410063510589)
            ·
              refine ⟨347772707704073028773816471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 927393887210861410063510589 347772707704073028773816471)
              ·
                refine ⟨521659061556109543160724707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347772707704073028773816471 521659061556109543160724707)
                ·
                  refine ⟨782488592334164314741087061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521659061556109543160724707 782488592334164314741087061)
                  ·
                    refine ⟨4584894095707994031686057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 782488592334164314741087061 4584894095707994031686057)
                    ·
                      refine ⟨3438670571780995523764543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4584894095707994031686057 3438670571780995523764543)
                      ·
                        rfl

theorem cell23_6696787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 9, 2].length) (baseStart_6696787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696787 prefixEnd_6696787 := by exact prefixLift 6696787
  have htrace : WordTrace (prefixWord ++ tailWord_6696787) baseStart_6696787 baseEnd_6696787 := by
    simpa [prefixWord, tailWord_6696787, baseEnd_6696787] using wordTrace_append hprefix tailTrace_6696787
  have hstable : (prefixWord ++ tailWord_6696787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696787).length < 2 ^ (prefixWord ++ tailWord_6696787).sum := by decide
  have hdescent : baseEnd_6696787 < baseStart_6696787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696788 : List Nat := [2, 4, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_6696788 : Nat := 118140960795 + 6696788 * 2 ^ 59
def prefixEnd_6696788 : Nat := 4983230072969 + 3 ^ 40 * 6696788 * 2
def baseEnd_6696788 : Nat := 1146223695087216673284013

theorem tailTrace_6696788 : CollatzResearch.WordTrace tailWord_6696788 prefixEnd_6696788 1146223695087216673284013 := by
  unfold tailWord_6696788
  simp only [CollatzResearch.WordTrace]
  refine ⟨122125962231344135589641509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162834616308458847452855345 122125962231344135589641509)
  ·
    refine ⟨22898617918377025423057783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122125962231344135589641509 22898617918377025423057783)
    ·
      refine ⟨34347926877565538134586675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22898617918377025423057783 34347926877565538134586675)
      ·
        refine ⟨51521890316348307201880013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34347926877565538134586675 51521890316348307201880013)
        ·
          refine ⟨19320708868630615200705005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51521890316348307201880013 19320708868630615200705005)
          ·
            refine ⟨7245265825736480700264377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19320708868630615200705005 7245265825736480700264377)
            ·
              refine ⟨5433949369302360525198283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7245265825736480700264377 5433949369302360525198283)
              ·
                refine ⟨8150924053953540787797425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5433949369302360525198283 8150924053953540787797425)
                ·
                  refine ⟨6113193040465155590848069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8150924053953540787797425 6113193040465155590848069)
                  ·
                    refine ⟨1146223695087216673284013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6113193040465155590848069 1146223695087216673284013)
                    ·
                      rfl

theorem cell23_6696788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_6696788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696788 prefixEnd_6696788 := by exact prefixLift 6696788
  have htrace : WordTrace (prefixWord ++ tailWord_6696788) baseStart_6696788 baseEnd_6696788 := by
    simpa [prefixWord, tailWord_6696788, baseEnd_6696788] using wordTrace_append hprefix tailTrace_6696788
  have hstable : (prefixWord ++ tailWord_6696788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696788).length < 2 ^ (prefixWord ++ tailWord_6696788).sum := by decide
  have hdescent : baseEnd_6696788 < baseStart_6696788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696837 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 1, 6, 3]
def baseStart_6696837 : Nat := 118140960795 + 6696837 * 2 ^ 59
def prefixEnd_6696837 : Nat := 4983230072969 + 3 ^ 40 * 6696837 * 2
def baseEnd_6696837 : Nat := 3438696245813720328139313

theorem tailTrace_6696837 : CollatzResearch.WordTrace tailWord_6696837 prefixEnd_6696837 3438696245813720328139313 := by
  unfold tailWord_6696837
  simp only [CollatzResearch.WordTrace]
  refine ⟨244253711639510752547816765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162835807759673835031877843 244253711639510752547816765)
  ·
    refine ⟨91595141864816532205431287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244253711639510752547816765 91595141864816532205431287)
    ·
      refine ⟨137392712797224798308146931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91595141864816532205431287 137392712797224798308146931)
      ·
        refine ⟨206089069195837197462220397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137392712797224798308146931 206089069195837197462220397)
        ·
          refine ⟨77283400948438949048332649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206089069195837197462220397 77283400948438949048332649)
          ·
            refine ⟨57962550711329211786249487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77283400948438949048332649 57962550711329211786249487)
            ·
              refine ⟨86943826066993817679374231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57962550711329211786249487 86943826066993817679374231)
              ·
                refine ⟨130415739100490726519061347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86943826066993817679374231 130415739100490726519061347)
                ·
                  refine ⟨195623608650736089778592021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130415739100490726519061347 195623608650736089778592021)
                  ·
                    refine ⟨9169856655503254208371501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 195623608650736089778592021 9169856655503254208371501)
                    ·
                      refine ⟨3438696245813720328139313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9169856655503254208371501 3438696245813720328139313)
                      ·
                        rfl

theorem cell23_6696837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_6696837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696837 prefixEnd_6696837 := by exact prefixLift 6696837
  have htrace : WordTrace (prefixWord ++ tailWord_6696837) baseStart_6696837 baseEnd_6696837 := by
    simpa [prefixWord, tailWord_6696837, baseEnd_6696837] using wordTrace_append hprefix tailTrace_6696837
  have hstable : (prefixWord ++ tailWord_6696837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696837).length < 2 ^ (prefixWord ++ tailWord_6696837).sum := by decide
  have hdescent : baseEnd_6696837 < baseStart_6696837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696867 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 3]
def baseStart_6696867 : Nat := 118140960795 + 6696867 * 2 ^ 59
def prefixEnd_6696867 : Nat := 4983230072969 + 3 ^ 40 * 6696867 * 2
def baseEnd_6696867 : Nat := 3438711650233355210764175

theorem tailTrace_6696867 : CollatzResearch.WordTrace tailWord_6696867 prefixEnd_6696867 3438711650233355210764175 := by
  unfold tailWord_6696867
  simp only [CollatzResearch.WordTrace]
  refine ⟨244254805829402067671408855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162836537219601378447605903 244254805829402067671408855)
  ·
    refine ⟨366382208744103101507113283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244254805829402067671408855 366382208744103101507113283)
    ·
      refine ⟨549573313116154652260669925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366382208744103101507113283 549573313116154652260669925)
      ·
        refine ⟨103044996209278997298875611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 549573313116154652260669925 103044996209278997298875611)
        ·
          refine ⟨154567494313918495948313417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103044996209278997298875611 154567494313918495948313417)
          ·
            refine ⟨115925620735438871961235063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154567494313918495948313417 115925620735438871961235063)
            ·
              refine ⟨173888431103158307941852595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115925620735438871961235063 173888431103158307941852595)
              ·
                refine ⟨260832646654737461912778893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173888431103158307941852595 260832646654737461912778893)
                ·
                  refine ⟨97812242495526548217292085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260832646654737461912778893 97812242495526548217292085)
                  ·
                    refine ⟨9169897733955613895371133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97812242495526548217292085 9169897733955613895371133)
                    ·
                      refine ⟨3438711650233355210764175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9169897733955613895371133 3438711650233355210764175)
                      ·
                        rfl

theorem cell23_6696867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_6696867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696867 prefixEnd_6696867 := by exact prefixLift 6696867
  have htrace : WordTrace (prefixWord ++ tailWord_6696867) baseStart_6696867 baseEnd_6696867 := by
    simpa [prefixWord, tailWord_6696867, baseEnd_6696867] using wordTrace_append hprefix tailTrace_6696867
  have hstable : (prefixWord ++ tailWord_6696867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696867).length < 2 ^ (prefixWord ++ tailWord_6696867).sum := by decide
  have hdescent : baseEnd_6696867 < baseStart_6696867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696885 : List Nat := [1, 3, 3, 2, 1, 4, 1, 2, 2, 2, 2]
def baseStart_6696885 : Nat := 118140960795 + 6696885 * 2 ^ 59
def prefixEnd_6696885 : Nat := 4983230072969 + 3 ^ 40 * 6696885 * 2
def baseEnd_6696885 : Nat := 3438720892885136140339093

theorem tailTrace_6696885 : CollatzResearch.WordTrace tailWord_6696885 prefixEnd_6696885 3438720892885136140339093 := by
  unfold tailWord_6696885
  simp only [CollatzResearch.WordTrace]
  refine ⟨244255462343336856745564109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162836974895557904497042739 244255462343336856745564109)
  ·
    refine ⟨91595798378751321279586541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244255462343336856745564109 91595798378751321279586541)
    ·
      refine ⟨34348424392031745479844953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91595798378751321279586541 34348424392031745479844953)
      ·
        refine ⟨25761318294023809109883715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34348424392031745479844953 25761318294023809109883715)
        ·
          refine ⟨38641977441035713664825573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25761318294023809109883715 38641977441035713664825573)
          ·
            refine ⟨7245370770194196312154795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38641977441035713664825573 7245370770194196312154795)
            ·
              refine ⟨10868056155291294468232193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7245370770194196312154795 10868056155291294468232193)
              ·
                refine ⟨8151042116468470851174145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10868056155291294468232193 8151042116468470851174145)
                ·
                  refine ⟨6113281587351353138380609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8151042116468470851174145 6113281587351353138380609)
                  ·
                    refine ⟨4584961190513514853785457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6113281587351353138380609 4584961190513514853785457)
                    ·
                      refine ⟨3438720892885136140339093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4584961190513514853785457 3438720892885136140339093)
                      ·
                        rfl

theorem cell23_6696885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_6696885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696885 prefixEnd_6696885 := by exact prefixLift 6696885
  have htrace : WordTrace (prefixWord ++ tailWord_6696885) baseStart_6696885 baseEnd_6696885 := by
    simpa [prefixWord, tailWord_6696885, baseEnd_6696885] using wordTrace_append hprefix tailTrace_6696885
  have hstable : (prefixWord ++ tailWord_6696885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696885).length < 2 ^ (prefixWord ++ tailWord_6696885).sum := by decide
  have hdescent : baseEnd_6696885 < baseStart_6696885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696887 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 4, 5]
def baseStart_6696887 : Nat := 118140960795 + 6696887 * 2 ^ 59
def prefixEnd_6696887 : Nat := 4983230072969 + 3 ^ 40 * 6696887 * 2
def baseEnd_6696887 : Nat := 1146240639948815044171361

theorem tailTrace_6696887 : CollatzResearch.WordTrace tailWord_6696887 prefixEnd_6696887 1146240639948815044171361 := by
  unfold tailWord_6696887
  simp only [CollatzResearch.WordTrace]
  refine ⟨244255535289329611087136915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162837023526219740724757943 244255535289329611087136915)
  ·
    refine ⟨366383302933994416630705373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244255535289329611087136915 366383302933994416630705373)
    ·
      refine ⟨137393738600247906236514515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366383302933994416630705373 137393738600247906236514515)
      ·
        refine ⟨206090607900371859354771773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137393738600247906236514515 206090607900371859354771773)
        ·
          refine ⟨77283977962639447258039415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206090607900371859354771773 77283977962639447258039415)
          ·
            refine ⟨115925966943959170887059123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77283977962639447258039415 115925966943959170887059123)
            ·
              refine ⟨173888950415938756330588685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115925966943959170887059123 173888950415938756330588685)
              ·
                refine ⟨65208356405977033623970757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173888950415938756330588685 65208356405977033623970757)
                ·
                  refine ⟨12226566826120693804494517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65208356405977033623970757 12226566826120693804494517)
                  ·
                    refine ⟨1146240639948815044171361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12226566826120693804494517 1146240639948815044171361)
                    ·
                      rfl

theorem cell23_6696887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_6696887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696887 prefixEnd_6696887 := by exact prefixLift 6696887
  have htrace : WordTrace (prefixWord ++ tailWord_6696887) baseStart_6696887 baseEnd_6696887 := by
    simpa [prefixWord, tailWord_6696887, baseEnd_6696887] using wordTrace_append hprefix tailTrace_6696887
  have hstable : (prefixWord ++ tailWord_6696887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696887).length < 2 ^ (prefixWord ++ tailWord_6696887).sum := by decide
  have hdescent : baseEnd_6696887 < baseStart_6696887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696907 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 4]
def baseStart_6696907 : Nat := 118140960795 + 6696907 * 2 ^ 59
def prefixEnd_6696907 : Nat := 4983230072969 + 3 ^ 40 * 6696907 * 2
def baseEnd_6696907 : Nat := 3438732189459535054263991

theorem tailTrace_6696907 : CollatzResearch.WordTrace tailWord_6696907 prefixEnd_6696907 3438732189459535054263991 := by
  unfold tailWord_6696907
  simp only [CollatzResearch.WordTrace]
  refine ⟨244256264749257154502864975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162837509832838103001909983 244256264749257154502864975)
  ·
    refine ⟨366384397123885731754297463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244256264749257154502864975 366384397123885731754297463)
    ·
      refine ⟨549576595685828597631446195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366384397123885731754297463 549576595685828597631446195)
      ·
        refine ⟨824364893528742896447169293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549576595685828597631446195 824364893528742896447169293)
        ·
          refine ⟨309136835073278586167688485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 824364893528742896447169293 309136835073278586167688485)
          ·
            refine ⟨57963156576239734906441591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 309136835073278586167688485 57963156576239734906441591)
            ·
              refine ⟨86944734864359602359662387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57963156576239734906441591 86944734864359602359662387)
              ·
                refine ⟨130417102296539403539493581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86944734864359602359662387 130417102296539403539493581)
                ·
                  refine ⟨48906413361202276327310093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130417102296539403539493581 48906413361202276327310093)
                  ·
                    refine ⟨18339905010450853622741285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48906413361202276327310093 18339905010450853622741285)
                    ·
                      refine ⟨3438732189459535054263991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18339905010450853622741285 3438732189459535054263991)
                      ·
                        rfl

theorem cell23_6696907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 4].length) (baseStart_6696907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696907 prefixEnd_6696907 := by exact prefixLift 6696907
  have htrace : WordTrace (prefixWord ++ tailWord_6696907) baseStart_6696907 baseEnd_6696907 := by
    simpa [prefixWord, tailWord_6696907, baseEnd_6696907] using wordTrace_append hprefix tailTrace_6696907
  have hstable : (prefixWord ++ tailWord_6696907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696907).length < 2 ^ (prefixWord ++ tailWord_6696907).sum := by decide
  have hdescent : baseEnd_6696907 < baseStart_6696907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696925 : List Nat := [1, 4, 3, 1, 4, 1, 1, 3, 5]
def baseStart_6696925 : Nat := 118140960795 + 6696925 * 2 ^ 59
def prefixEnd_6696925 : Nat := 4983230072969 + 3 ^ 40 * 6696925 * 2
def baseEnd_6696925 : Nat := 382082381345701775982101

theorem tailTrace_6696925 : CollatzResearch.WordTrace tailWord_6696925 prefixEnd_6696925 382082381345701775982101 := by
  unfold tailWord_6696925
  simp only [CollatzResearch.WordTrace]
  refine ⟨244256921263191943577020229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162837947508794629051346819 244256921263191943577020229)
  ·
    refine ⟨45798172736848489420691293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244256921263191943577020229 45798172736848489420691293)
    ·
      refine ⟨17174314776318183532759235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45798172736848489420691293 17174314776318183532759235)
      ·
        refine ⟨25761472164477275299138853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17174314776318183532759235 25761472164477275299138853)
        ·
          refine ⟨4830276030839489118588535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25761472164477275299138853 4830276030839489118588535)
          ·
            refine ⟨7245414046259233677882803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4830276030839489118588535 7245414046259233677882803)
            ·
              refine ⟨10868121069388850516824205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7245414046259233677882803 10868121069388850516824205)
              ·
                refine ⟨4075545401020818943809077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10868121069388850516824205 4075545401020818943809077)
                ·
                  refine ⟨382082381345701775982101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4075545401020818943809077 382082381345701775982101)
                  ·
                    rfl

theorem cell23_6696925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_6696925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696925 prefixEnd_6696925 := by exact prefixLift 6696925
  have htrace : WordTrace (prefixWord ++ tailWord_6696925) baseStart_6696925 baseEnd_6696925 := by
    simpa [prefixWord, tailWord_6696925, baseEnd_6696925] using wordTrace_append hprefix tailTrace_6696925
  have hstable : (prefixWord ++ tailWord_6696925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696925).length < 2 ^ (prefixWord ++ tailWord_6696925).sum := by decide
  have hdescent : baseEnd_6696925 < baseStart_6696925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696944 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 3]
def baseStart_6696944 : Nat := 118140960795 + 6696944 * 2 ^ 59
def prefixEnd_6696944 : Nat := 4983230072969 + 3 ^ 40 * 6696944 * 2
def baseEnd_6696944 : Nat := 3438751188243751409501321

theorem tailTrace_6696944 : CollatzResearch.WordTrace tailWord_6696944 prefixEnd_6696944 3438751188243751409501321 := by
  unfold tailWord_6696944
  simp only [CollatzResearch.WordTrace]
  refine ⟨122128807125061554910980943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162838409500082073214641257 122128807125061554910980943)
  ·
    refine ⟨183193210687592332366471415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122128807125061554910980943 183193210687592332366471415)
    ·
      refine ⟨274789816031388498549707123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183193210687592332366471415 274789816031388498549707123)
      ·
        refine ⟨412184724047082747824560685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274789816031388498549707123 412184724047082747824560685)
        ·
          refine ⟨154569271517656030434210257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 412184724047082747824560685 154569271517656030434210257)
          ·
            refine ⟨115926953638242022825657693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154569271517656030434210257 115926953638242022825657693)
            ·
              refine ⟨43472607614340758559621635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115926953638242022825657693 43472607614340758559621635)
              ·
                refine ⟨65208911421511137839432453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43472607614340758559621635 65208911421511137839432453)
                ·
                  refine ⟨12226670891533338344893585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65208911421511137839432453 12226670891533338344893585)
                  ·
                    refine ⟨9170003168650003758670189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12226670891533338344893585 9170003168650003758670189)
                    ·
                      refine ⟨3438751188243751409501321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9170003168650003758670189 3438751188243751409501321)
                      ·
                        rfl

theorem cell23_6696944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 3].length) (baseStart_6696944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696944 prefixEnd_6696944 := by exact prefixLift 6696944
  have htrace : WordTrace (prefixWord ++ tailWord_6696944) baseStart_6696944 baseEnd_6696944 := by
    simpa [prefixWord, tailWord_6696944, baseEnd_6696944] using wordTrace_append hprefix tailTrace_6696944
  have hstable : (prefixWord ++ tailWord_6696944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696944).length < 2 ^ (prefixWord ++ tailWord_6696944).sum := by decide
  have hdescent : baseEnd_6696944 < baseStart_6696944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6696987 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 5]
def baseStart_6696987 : Nat := 118140960795 + 6696987 * 2 ^ 59
def prefixEnd_6696987 : Nat := 4983230072969 + 3 ^ 40 * 6696987 * 2
def baseEnd_6696987 : Nat := 3438773267911894741263623

theorem tailTrace_6696987 : CollatzResearch.WordTrace tailWord_6696987 prefixEnd_6696987 3438773267911894741263623 := by
  unfold tailWord_6696987
  simp only [CollatzResearch.WordTrace]
  refine ⟨244259182588967328165777215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162839455059311552110518143 244259182588967328165777215)
  ·
    refine ⟨366388773883450992248665823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244259182588967328165777215 366388773883450992248665823)
    ·
      refine ⟨549583160825176488372998735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366388773883450992248665823 549583160825176488372998735)
      ·
        refine ⟨824374741237764732559498103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549583160825176488372998735 824374741237764732559498103)
        ·
          refine ⟨1236562111856647098839247155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824374741237764732559498103 1236562111856647098839247155)
          ·
            refine ⟨1854843167784970648258870733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1236562111856647098839247155 1854843167784970648258870733)
            ·
              refine ⟨695566187919363993097076525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1854843167784970648258870733 695566187919363993097076525)
              ·
                refine ⟨260837320469761497411403697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 695566187919363993097076525 260837320469761497411403697)
                ·
                  refine ⟨195627990352321123058552773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260837320469761497411403697 195627990352321123058552773)
                  ·
                    refine ⟨36680248191060210573478645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 195627990352321123058552773 36680248191060210573478645)
                    ·
                      refine ⟨3438773267911894741263623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36680248191060210573478645 3438773267911894741263623)
                      ·
                        rfl

theorem cell23_6696987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 5].length) (baseStart_6696987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6696987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6696987 prefixEnd_6696987 := by exact prefixLift 6696987
  have htrace : WordTrace (prefixWord ++ tailWord_6696987) baseStart_6696987 baseEnd_6696987 := by
    simpa [prefixWord, tailWord_6696987, baseEnd_6696987] using wordTrace_append hprefix tailTrace_6696987
  have hstable : (prefixWord ++ tailWord_6696987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6696987).length < 2 ^ (prefixWord ++ tailWord_6696987).sum := by decide
  have hdescent : baseEnd_6696987 < baseStart_6696987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6696987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697002 : List Nat := [3, 1, 4, 1, 2, 3, 2, 2, 1, 4]
def baseStart_6697002 : Nat := 118140960795 + 6697002 * 2 ^ 59
def prefixEnd_6697002 : Nat := 4983230072969 + 3 ^ 40 * 6697002 * 2
def baseEnd_6697002 : Nat := 1146260323373904060858685

theorem tailTrace_6697002 : CollatzResearch.WordTrace tailWord_6697002 prefixEnd_6697002 1146260323373904060858685 := by
  unfold tailWord_6697002
  simp only [CollatzResearch.WordTrace]
  refine ⟨61064932420978246431893315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162839819789275323818382173 61064932420978246431893315)
  ·
    refine ⟨91597398631467369647839973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61064932420978246431893315 91597398631467369647839973)
    ·
      refine ⟨17174512243400131808969995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91597398631467369647839973 17174512243400131808969995)
      ·
        refine ⟨25761768365100197713454993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17174512243400131808969995 25761768365100197713454993)
        ·
          refine ⟨19321326273825148285091245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25761768365100197713454993 19321326273825148285091245)
          ·
            refine ⟨7245497352684430606909217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19321326273825148285091245 7245497352684430606909217)
            ·
              refine ⟨5434123014513322955181913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7245497352684430606909217 5434123014513322955181913)
              ·
                refine ⟨4075592260884992216386435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5434123014513322955181913 4075592260884992216386435)
                ·
                  refine ⟨6113388391327488324579653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4075592260884992216386435 6113388391327488324579653)
                  ·
                    refine ⟨1146260323373904060858685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6113388391327488324579653 1146260323373904060858685)
                    ·
                      rfl

theorem cell23_6697002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_6697002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697002 prefixEnd_6697002 := by exact prefixLift 6697002
  have htrace : WordTrace (prefixWord ++ tailWord_6697002) baseStart_6697002 baseEnd_6697002 := by
    simpa [prefixWord, tailWord_6697002, baseEnd_6697002] using wordTrace_append hprefix tailTrace_6697002
  have hstable : (prefixWord ++ tailWord_6697002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697002).length < 2 ^ (prefixWord ++ tailWord_6697002).sum := by decide
  have hdescent : baseEnd_6697002 < baseStart_6697002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697024 : List Nat := [2, 1, 1, 2, 2, 4, 1, 3, 1, 6]
def baseStart_6697024 : Nat := 118140960795 + 6697024 * 2 ^ 59
def prefixEnd_6697024 : Nat := 4983230072969 + 3 ^ 40 * 6697024 * 2
def baseEnd_6697024 : Nat := 1146264088898703698833651

theorem tailTrace_6697024 : CollatzResearch.WordTrace tailWord_6697024 prefixEnd_6697024 1146264088898703698833651 := by
  unfold tailWord_6697024
  simp only [CollatzResearch.WordTrace]
  refine ⟨122130266044916641742437063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162840354726555522323249417 122130266044916641742437063)
  ·
    refine ⟨183195399067374962613655595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122130266044916641742437063 183195399067374962613655595)
    ·
      refine ⟨274793098601062443920483393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183195399067374962613655595 274793098601062443920483393)
      ·
        refine ⟨206094823950796832940362545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274793098601062443920483393 206094823950796832940362545)
        ·
          refine ⟨154571117963097624705271909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206094823950796832940362545 154571117963097624705271909)
          ·
            refine ⟨28982084618080804632238483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154571117963097624705271909 28982084618080804632238483)
            ·
              refine ⟨43473126927121206948357725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28982084618080804632238483 43473126927121206948357725)
              ·
                refine ⟨16302422597670452605634147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43473126927121206948357725 16302422597670452605634147)
                ·
                  refine ⟨24453633896505678908451221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16302422597670452605634147 24453633896505678908451221)
                  ·
                    refine ⟨1146264088898703698833651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24453633896505678908451221 1146264088898703698833651)
                    ·
                      rfl

theorem cell23_6697024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 1, 6].length) (baseStart_6697024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697024 prefixEnd_6697024 := by exact prefixLift 6697024
  have htrace : WordTrace (prefixWord ++ tailWord_6697024) baseStart_6697024 baseEnd_6697024 := by
    simpa [prefixWord, tailWord_6697024, baseEnd_6697024] using wordTrace_append hprefix tailTrace_6697024
  have hstable : (prefixWord ++ tailWord_6697024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697024).length < 2 ^ (prefixWord ++ tailWord_6697024).sum := by decide
  have hdescent : baseEnd_6697024 < baseStart_6697024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697031 : List Nat := [1, 1, 4, 1, 3, 1, 2, 4, 1, 1, 4]
def baseStart_6697031 : Nat := 118140960795 + 6697031 * 2 ^ 59
def prefixEnd_6697031 : Nat := 4983230072969 + 3 ^ 40 * 6697031 * 2
def baseEnd_6697031 : Nat := 3438795861060692569113421

theorem tailTrace_6697031 : CollatzResearch.WordTrace tailWord_6697031 prefixEnd_6697031 3438795861060692569113421 := by
  unfold tailWord_6697031
  simp only [CollatzResearch.WordTrace]
  refine ⟨244260787400807923680378947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162840524933871949120252631 244260787400807923680378947)
  ·
    refine ⟨366391181101211885520568421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244260787400807923680378947 366391181101211885520568421)
    ·
      refine ⟨68698346456477228535106579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 366391181101211885520568421 68698346456477228535106579)
      ·
        refine ⟨103047519684715842802659869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68698346456477228535106579 103047519684715842802659869)
        ·
          refine ⟨38642819881768441050997451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103047519684715842802659869 38642819881768441050997451)
          ·
            refine ⟨57964229822652661576496177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38642819881768441050997451 57964229822652661576496177)
            ·
              refine ⟨43473172366989496182372133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57964229822652661576496177 43473172366989496182372133)
              ·
                refine ⟨8151219818810530534194775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43473172366989496182372133 8151219818810530534194775)
                ·
                  refine ⟨12226829728215795801292163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8151219818810530534194775 12226829728215795801292163)
                  ·
                    refine ⟨18340244592323693701938245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12226829728215795801292163 18340244592323693701938245)
                    ·
                      refine ⟨3438795861060692569113421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18340244592323693701938245 3438795861060692569113421)
                      ·
                        rfl

theorem cell23_6697031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_6697031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697031 prefixEnd_6697031 := by exact prefixLift 6697031
  have htrace : WordTrace (prefixWord ++ tailWord_6697031) baseStart_6697031 baseEnd_6697031 := by
    simpa [prefixWord, tailWord_6697031, baseEnd_6697031] using wordTrace_append hprefix tailTrace_6697031
  have hstable : (prefixWord ++ tailWord_6697031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697031).length < 2 ^ (prefixWord ++ tailWord_6697031).sum := by decide
  have hdescent : baseEnd_6697031 < baseStart_6697031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697042 : List Nat := [3, 2, 2, 1, 4, 1, 2, 3, 1, 1, 3]
def baseStart_6697042 : Nat := 118140960795 + 6697042 * 2 ^ 59
def prefixEnd_6697042 : Nat := 4983230072969 + 3 ^ 40 * 6697042 * 2
def baseEnd_6697042 : Nat := 3438801509347892026075871

theorem tailTrace_6697042 : CollatzResearch.WordTrace tailWord_6697042 prefixEnd_6697042 3438801509347892026075871 := by
  unfold tailWord_6697042
  simp only [CollatzResearch.WordTrace]
  refine ⟨61065297150942018139757345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162840792402512048372686253 61065297150942018139757345)
  ·
    refine ⟨45798972863206513604818009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61065297150942018139757345 45798972863206513604818009)
    ·
      refine ⟨34349229647404885203613507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45798972863206513604818009 34349229647404885203613507)
      ·
        refine ⟨51523844471107327805420261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34349229647404885203613507 51523844471107327805420261)
        ·
          refine ⟨9660720838332623963516299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51523844471107327805420261 9660720838332623963516299)
          ·
            refine ⟨14491081257498935945274449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9660720838332623963516299 14491081257498935945274449)
            ·
              refine ⟨10868310943124201958955837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14491081257498935945274449 10868310943124201958955837)
              ·
                refine ⟨4075616603671575734608439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10868310943124201958955837 4075616603671575734608439)
                ·
                  refine ⟨6113424905507363601912659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4075616603671575734608439 6113424905507363601912659)
                  ·
                    refine ⟨9170137358261045402868989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6113424905507363601912659 9170137358261045402868989)
                    ·
                      refine ⟨3438801509347892026075871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9170137358261045402868989 3438801509347892026075871)
                      ·
                        rfl

theorem cell23_6697042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_6697042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697042 prefixEnd_6697042 := by exact prefixLift 6697042
  have htrace : WordTrace (prefixWord ++ tailWord_6697042) baseStart_6697042 baseEnd_6697042 := by
    simpa [prefixWord, tailWord_6697042, baseEnd_6697042] using wordTrace_append hprefix tailTrace_6697042
  have hstable : (prefixWord ++ tailWord_6697042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697042).length < 2 ^ (prefixWord ++ tailWord_6697042).sum := by decide
  have hdescent : baseEnd_6697042 < baseStart_6697042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697044 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_6697044 : Nat := 118140960795 + 6697044 * 2 ^ 59
def prefixEnd_6697044 : Nat := 4983230072969 + 3 ^ 40 * 6697044 * 2
def baseEnd_6697044 : Nat := 3438802536309201018250861

theorem tailTrace_6697044 : CollatzResearch.WordTrace tailWord_6697044 prefixEnd_6697044 3438802536309201018250861 := by
  unfold tailWord_6697044
  simp only [CollatzResearch.WordTrace]
  refine ⟨122130630774880413450301093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162840841033173884600401457 122130630774880413450301093)
  ·
    refine ⟨22899493270290077521931455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122130630774880413450301093 22899493270290077521931455)
    ·
      refine ⟨34349239905435116282897183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22899493270290077521931455 34349239905435116282897183)
      ·
        refine ⟨51523859858152674424345775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34349239905435116282897183 51523859858152674424345775)
        ·
          refine ⟨77285789787229011636518663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51523859858152674424345775 77285789787229011636518663)
          ·
            refine ⟨115928684680843517454777995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77285789787229011636518663 115928684680843517454777995)
            ·
              refine ⟨173893027021265276182166993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115928684680843517454777995 173893027021265276182166993)
              ·
                refine ⟨130419770265948957136625245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173893027021265276182166993 130419770265948957136625245)
                ·
                  refine ⟨48907413849730858926234467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130419770265948957136625245 48907413849730858926234467)
                  ·
                    refine ⟨73361120774596288389351701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48907413849730858926234467 73361120774596288389351701)
                    ·
                      refine ⟨3438802536309201018250861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73361120774596288389351701 3438802536309201018250861)
                      ·
                        rfl

theorem cell23_6697044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_6697044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697044 prefixEnd_6697044 := by exact prefixLift 6697044
  have htrace : WordTrace (prefixWord ++ tailWord_6697044) baseStart_6697044 baseEnd_6697044 := by
    simpa [prefixWord, tailWord_6697044, baseEnd_6697044] using wordTrace_append hprefix tailTrace_6697044
  have hstable : (prefixWord ++ tailWord_6697044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697044).length < 2 ^ (prefixWord ++ tailWord_6697044).sum := by decide
  have hdescent : baseEnd_6697044 < baseStart_6697044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697048 : List Nat := [2, 1, 2, 2, 1, 4, 4, 1, 1, 1, 4]
def baseStart_6697048 : Nat := 118140960795 + 6697048 * 2 ^ 59
def prefixEnd_6697048 : Nat := 4983230072969 + 3 ^ 40 * 6697048 * 2
def baseEnd_6697048 : Nat := 3438804590231819002600843

theorem tailTrace_6697048 : CollatzResearch.WordTrace tailWord_6697048 prefixEnd_6697048 3438804590231819002600843 := by
  unfold tailWord_6697048
  simp only [CollatzResearch.WordTrace]
  refine ⟨122130703720873167791873899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162840938294497557055831865 122130703720873167791873899)
  ·
    refine ⟨183196055581309751687810849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122130703720873167791873899 183196055581309751687810849)
    ·
      refine ⟨137397041685982313765858137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183196055581309751687810849 137397041685982313765858137)
      ·
        refine ⟨103047781264486735324393603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137397041685982313765858137 103047781264486735324393603)
        ·
          refine ⟨154571671896730102986590405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103047781264486735324393603 154571671896730102986590405)
          ·
            refine ⟨28982188480636894309985701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154571671896730102986590405 28982188480636894309985701)
            ·
              refine ⟨5434160340119417683122319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28982188480636894309985701 5434160340119417683122319)
              ·
                refine ⟨8151240510179126524683479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5434160340119417683122319 8151240510179126524683479)
                ·
                  refine ⟨12226860765268689787025219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8151240510179126524683479 12226860765268689787025219)
                  ·
                    refine ⟨18340291147903034680537829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12226860765268689787025219 18340291147903034680537829)
                    ·
                      refine ⟨3438804590231819002600843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18340291147903034680537829 3438804590231819002600843)
                      ·
                        rfl

theorem cell23_6697048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_6697048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697048 prefixEnd_6697048 := by exact prefixLift 6697048
  have htrace : WordTrace (prefixWord ++ tailWord_6697048) baseStart_6697048 baseEnd_6697048 := by
    simpa [prefixWord, tailWord_6697048, baseEnd_6697048] using wordTrace_append hprefix tailTrace_6697048
  have hstable : (prefixWord ++ tailWord_6697048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697048).length < 2 ^ (prefixWord ++ tailWord_6697048).sum := by decide
  have hdescent : baseEnd_6697048 < baseStart_6697048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697065 : List Nat := [1, 2, 1, 1, 1, 5, 1, 6, 1, 2, 2]
def baseStart_6697065 : Nat := 118140960795 + 6697065 * 2 ^ 59
def prefixEnd_6697065 : Nat := 4983230072969 + 3 ^ 40 * 6697065 * 2
def baseEnd_6697065 : Nat := 3438813319402945436088265

theorem tailTrace_6697065 : CollatzResearch.WordTrace tailWord_6697065 prefixEnd_6697065 3438813319402945436088265 := by
  unfold tailWord_6697065
  simp only [CollatzResearch.WordTrace]
  refine ⟨244262027482684747487116649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162841351655123164991411099 244262027482684747487116649)
  ·
    refine ⟨183196520612013560615337487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244262027482684747487116649 183196520612013560615337487)
    ·
      refine ⟨274794780918020340923006231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183196520612013560615337487 274794780918020340923006231)
      ·
        refine ⟨412192171377030511384509347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274794780918020340923006231 412192171377030511384509347)
        ·
          refine ⟨618288257065545767076764021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412192171377030511384509347 618288257065545767076764021)
          ·
            refine ⟨57964524099894915663446627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 618288257065545767076764021 57964524099894915663446627)
            ·
              refine ⟨86946786149842373495169941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57964524099894915663446627 86946786149842373495169941)
              ·
                refine ⟨4075630600773861257586091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86946786149842373495169941 4075630600773861257586091)
                ·
                  refine ⟨6113445901160791886379137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4075630600773861257586091 6113445901160791886379137)
                  ·
                    refine ⟨4585084425870593914784353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6113445901160791886379137 4585084425870593914784353)
                    ·
                      refine ⟨3438813319402945436088265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4585084425870593914784353 3438813319402945436088265)
                      ·
                        rfl

theorem cell23_6697065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 1, 2, 2].length) (baseStart_6697065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697065 prefixEnd_6697065 := by exact prefixLift 6697065
  have htrace : WordTrace (prefixWord ++ tailWord_6697065) baseStart_6697065 baseEnd_6697065 := by
    simpa [prefixWord, tailWord_6697065, baseEnd_6697065] using wordTrace_append hprefix tailTrace_6697065
  have hstable : (prefixWord ++ tailWord_6697065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697065).length < 2 ^ (prefixWord ++ tailWord_6697065).sum := by decide
  have hdescent : baseEnd_6697065 < baseStart_6697065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697078 : List Nat := [5, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_6697078 : Nat := 118140960795 + 6697078 * 2 ^ 59
def prefixEnd_6697078 : Nat := 4983230072969 + 3 ^ 40 * 6697078 * 2
def baseEnd_6697078 : Nat := 3438819994651453885225705

theorem tailTrace_6697078 : CollatzResearch.WordTrace tailWord_6697078 prefixEnd_6697078 3438819994651453885225705 := by
  unfold tailWord_6697078
  simp only [CollatzResearch.WordTrace]
  refine ⟨15266406351977353169208743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162841667754425100471559925 15266406351977353169208743)
  ·
    refine ⟨22899609527966029753813115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15266406351977353169208743 22899609527966029753813115)
    ·
      refine ⟨34349414291949044630719673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22899609527966029753813115 34349414291949044630719673)
      ·
        refine ⟨25762060718961783473039755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34349414291949044630719673 25762060718961783473039755)
        ·
          refine ⟨38643091078442675209559633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25762060718961783473039755 38643091078442675209559633)
          ·
            refine ⟨28982318308832006407169725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38643091078442675209559633 28982318308832006407169725)
            ·
              refine ⟨10868369365812002402688647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28982318308832006407169725 10868369365812002402688647)
              ·
                refine ⟨16302554048718003604032971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10868369365812002402688647 16302554048718003604032971)
                ·
                  refine ⟨24453831073077005406049457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16302554048718003604032971 24453831073077005406049457)
                  ·
                    refine ⟨18340373304807754054537093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24453831073077005406049457 18340373304807754054537093)
                    ·
                      refine ⟨3438819994651453885225705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18340373304807754054537093 3438819994651453885225705)
                      ·
                        rfl

theorem cell23_6697078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_6697078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697078 prefixEnd_6697078 := by exact prefixLift 6697078
  have htrace : WordTrace (prefixWord ++ tailWord_6697078) baseStart_6697078 baseEnd_6697078 := by
    simpa [prefixWord, tailWord_6697078, baseEnd_6697078] using wordTrace_append hprefix tailTrace_6697078
  have hstable : (prefixWord ++ tailWord_6697078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697078).length < 2 ^ (prefixWord ++ tailWord_6697078).sum := by decide
  have hdescent : baseEnd_6697078 < baseStart_6697078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697098 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 4, 1, 3]
def baseStart_6697098 : Nat := 118140960795 + 6697098 * 2 ^ 59
def prefixEnd_6697098 : Nat := 4983230072969 + 3 ^ 40 * 6697098 * 2
def baseEnd_6697098 : Nat := 3438830264264543806975613

theorem tailTrace_6697098 : CollatzResearch.WordTrace tailWord_6697098 prefixEnd_6697098 3438830264264543806975613 := by
  unfold tailWord_6697098
  simp only [CollatzResearch.WordTrace]
  refine ⟨61065807772891298530766987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162842154061043462748711965 61065807772891298530766987)
  ·
    refine ⟨91598711659336947796150481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61065807772891298530766987 91598711659336947796150481)
    ·
      refine ⟨68699033744502710847112861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91598711659336947796150481 68699033744502710847112861)
      ·
        refine ⟨25762137654188516567667323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68699033744502710847112861 25762137654188516567667323)
        ·
          refine ⟨38643206481282774851500985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25762137654188516567667323 38643206481282774851500985)
          ·
            refine ⟨28982404860962081138625739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38643206481282774851500985 28982404860962081138625739)
            ·
              refine ⟨43473607291443121707938609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28982404860962081138625739 43473607291443121707938609)
              ·
                refine ⟨32605205468582341280953957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43473607291443121707938609 32605205468582341280953957)
                ·
                  refine ⟨6113476025359188990178867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32605205468582341280953957 6113476025359188990178867)
                  ·
                    refine ⟨9170214038038783485268301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6113476025359188990178867 9170214038038783485268301)
                    ·
                      refine ⟨3438830264264543806975613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9170214038038783485268301 3438830264264543806975613)
                      ·
                        rfl

theorem cell23_6697098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_6697098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697098 prefixEnd_6697098 := by exact prefixLift 6697098
  have htrace : WordTrace (prefixWord ++ tailWord_6697098) baseStart_6697098 baseEnd_6697098 := by
    simpa [prefixWord, tailWord_6697098, baseEnd_6697098] using wordTrace_append hprefix tailTrace_6697098
  have hstable : (prefixWord ++ tailWord_6697098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697098).length < 2 ^ (prefixWord ++ tailWord_6697098).sum := by decide
  have hdescent : baseEnd_6697098 < baseStart_6697098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697110 : List Nat := [5, 3, 2, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_6697110 : Nat := 118140960795 + 6697110 * 2 ^ 59
def prefixEnd_6697110 : Nat := 4983230072969 + 3 ^ 40 * 6697110 * 2
def baseEnd_6697110 : Nat := 3438836426032397760025559

theorem tailTrace_6697110 : CollatzResearch.WordTrace tailWord_6697110 prefixEnd_6697110 3438836426032397760025559 := by
  unfold tailWord_6697110
  simp only [CollatzResearch.WordTrace]
  refine ⟨15266479297970107510781549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162842445845014480115003189 15266479297970107510781549)
  ·
    refine ⟨5724929736738790316543081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15266479297970107510781549 5724929736738790316543081)
    ·
      refine ⟨4293697302554092737407311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5724929736738790316543081 4293697302554092737407311)
      ·
        refine ⟨6440545953831139106110967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4293697302554092737407311 6440545953831139106110967)
        ·
          refine ⟨9660818930746708659166451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6440545953831139106110967 9660818930746708659166451)
          ·
            refine ⟨14491228396120062988749677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9660818930746708659166451 14491228396120062988749677)
            ·
              refine ⟨5434210648545023620781129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14491228396120062988749677 5434210648545023620781129)
              ·
                refine ⟨4075657986408767715585847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5434210648545023620781129 4075657986408767715585847)
                ·
                  refine ⟨6113486979613151573378771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4075657986408767715585847 6113486979613151573378771)
                  ·
                    refine ⟨9170230469419727360068157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6113486979613151573378771 9170230469419727360068157)
                    ·
                      refine ⟨3438836426032397760025559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9170230469419727360068157 3438836426032397760025559)
                      ·
                        rfl

theorem cell23_6697110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_6697110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697110 prefixEnd_6697110 := by exact prefixLift 6697110
  have htrace : WordTrace (prefixWord ++ tailWord_6697110) baseStart_6697110 baseEnd_6697110 := by
    simpa [prefixWord, tailWord_6697110, baseEnd_6697110] using wordTrace_append hprefix tailTrace_6697110
  have hstable : (prefixWord ++ tailWord_6697110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697110).length < 2 ^ (prefixWord ++ tailWord_6697110).sum := by decide
  have hdescent : baseEnd_6697110 < baseStart_6697110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697138 : List Nat := [3, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2]
def baseStart_6697138 : Nat := 118140960795 + 6697138 * 2 ^ 59
def prefixEnd_6697138 : Nat := 4983230072969 + 3 ^ 40 * 6697138 * 2
def baseEnd_6697138 : Nat := 3438850803490723650475429

theorem tailTrace_6697138 : CollatzResearch.WordTrace tailWord_6697138 prefixEnd_6697138 3438850803490723650475429 := by
  unfold tailWord_6697138
  simp only [CollatzResearch.WordTrace]
  refine ⟨61066172502855070238631017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162843126674280187303016045 61066172502855070238631017)
  ·
    refine ⟨45799629377141302678973263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61066172502855070238631017 45799629377141302678973263)
    ·
      refine ⟨68699444065711954018459895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45799629377141302678973263 68699444065711954018459895)
      ·
        refine ⟨103049166098567931027689843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68699444065711954018459895 103049166098567931027689843)
        ·
          refine ⟨154573749147851896541534765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103049166098567931027689843 154573749147851896541534765)
          ·
            refine ⟨57965155930444461203075537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154573749147851896541534765 57965155930444461203075537)
            ·
              refine ⟨43473866947833345902306653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57965155930444461203075537 43473866947833345902306653)
              ·
                refine ⟨16302700105437504713364995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43473866947833345902306653 16302700105437504713364995)
                ·
                  refine ⟨24454050158156257070047493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16302700105437504713364995 24454050158156257070047493)
                  ·
                    refine ⟨4585134404654298200633905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24454050158156257070047493 4585134404654298200633905)
                    ·
                      refine ⟨3438850803490723650475429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4585134404654298200633905 3438850803490723650475429)
                      ·
                        rfl

theorem cell23_6697138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_6697138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697138 prefixEnd_6697138 := by exact prefixLift 6697138
  have htrace : WordTrace (prefixWord ++ tailWord_6697138) baseStart_6697138 baseEnd_6697138 := by
    simpa [prefixWord, tailWord_6697138, baseEnd_6697138] using wordTrace_append hprefix tailTrace_6697138
  have hstable : (prefixWord ++ tailWord_6697138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697138).length < 2 ^ (prefixWord ++ tailWord_6697138).sum := by decide
  have hdescent : baseEnd_6697138 < baseStart_6697138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697144 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 9]
def baseStart_6697144 : Nat := 118140960795 + 6697144 * 2 ^ 59
def prefixEnd_6697144 : Nat := 4983230072969 + 3 ^ 40 * 6697144 * 2
def baseEnd_6697144 : Nat := 382094876041627847444489

theorem tailTrace_6697144 : CollatzResearch.WordTrace tailWord_6697144 prefixEnd_6697144 382094876041627847444489 := by
  unfold tailWord_6697144
  simp only [CollatzResearch.WordTrace]
  refine ⟨122132454424699271989621243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162843272566265695986161657 122132454424699271989621243)
  ·
    refine ⟨183198681637048907984431865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122132454424699271989621243 183198681637048907984431865)
    ·
      refine ⟨137399011227786680988323899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183198681637048907984431865 137399011227786680988323899)
      ·
        refine ⟨206098516841680021482485849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137399011227786680988323899 206098516841680021482485849)
        ·
          refine ⟨154573887631260016111864387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206098516841680021482485849 154573887631260016111864387)
          ·
            refine ⟨231860831446890024167796581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154573887631260016111864387 231860831446890024167796581)
            ·
              refine ⟨43473905896291879531461859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231860831446890024167796581 43473905896291879531461859)
              ·
                refine ⟨65210858844437819297192789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43473905896291879531461859 65210858844437819297192789)
                ·
                  refine ⟨382094876041627847444489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65210858844437819297192789 382094876041627847444489)
                  ·
                    rfl

theorem cell23_6697144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 9].length) (baseStart_6697144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697144 prefixEnd_6697144 := by exact prefixLift 6697144
  have htrace : WordTrace (prefixWord ++ tailWord_6697144) baseStart_6697144 baseEnd_6697144 := by
    simpa [prefixWord, tailWord_6697144, baseEnd_6697144] using wordTrace_append hprefix tailTrace_6697144
  have hstable : (prefixWord ++ tailWord_6697144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697144).length < 2 ^ (prefixWord ++ tailWord_6697144).sum := by decide
  have hdescent : baseEnd_6697144 < baseStart_6697144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697198 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 4, 5, 2]
def baseStart_6697198 : Nat := 118140960795 + 6697198 * 2 ^ 59
def prefixEnd_6697198 : Nat := 4983230072969 + 3 ^ 40 * 6697198 * 2
def baseEnd_6697198 : Nat := 3438881612329993415725153

theorem tailTrace_6697198 : CollatzResearch.WordTrace tailWord_6697198 prefixEnd_6697198 3438881612329993415725153 := by
  unfold tailWord_6697198
  simp only [CollatzResearch.WordTrace]
  refine ⟨30533359798900363900213531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162844585594135274134472165 30533359798900363900213531)
  ·
    refine ⟨45800039698350545850320297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30533359798900363900213531 45800039698350545850320297)
    ·
      refine ⟨34350029773762909387740223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45800039698350545850320297 34350029773762909387740223)
      ·
        refine ⟨51525044660644364081610335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34350029773762909387740223 51525044660644364081610335)
        ·
          refine ⟨77287566990966546122415503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51525044660644364081610335 77287566990966546122415503)
          ·
            refine ⟨115931350486449819183623255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77287566990966546122415503 115931350486449819183623255)
            ·
              refine ⟨173897025729674728775434883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115931350486449819183623255 173897025729674728775434883)
              ·
                refine ⟨260845538594512093163152325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173897025729674728775434883 260845538594512093163152325)
                ·
                  refine ⟨48908538486471017468091061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 260845538594512093163152325 48908538486471017468091061)
                  ·
                    refine ⟨4585175483106657887633537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48908538486471017468091061 4585175483106657887633537)
                    ·
                      refine ⟨3438881612329993415725153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4585175483106657887633537 3438881612329993415725153)
                      ·
                        rfl

theorem cell23_6697198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_6697198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697198 prefixEnd_6697198 := by exact prefixLift 6697198
  have htrace : WordTrace (prefixWord ++ tailWord_6697198) baseStart_6697198 baseEnd_6697198 := by
    simpa [prefixWord, tailWord_6697198, baseEnd_6697198] using wordTrace_append hprefix tailTrace_6697198
  have hstable : (prefixWord ++ tailWord_6697198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697198).length < 2 ^ (prefixWord ++ tailWord_6697198).sum := by decide
  have hdescent : baseEnd_6697198 < baseStart_6697198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697228 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 4, 4, 2]
def baseStart_6697228 : Nat := 118140960795 + 6697228 * 2 ^ 59
def prefixEnd_6697228 : Nat := 4983230072969 + 3 ^ 40 * 6697228 * 2
def baseEnd_6697228 : Nat := 3438897016749628298350015

theorem tailTrace_6697228 : CollatzResearch.WordTrace tailWord_6697228 prefixEnd_6697228 3438897016749628298350015 := by
  unfold tailWord_6697228
  simp only [CollatzResearch.WordTrace]
  refine ⟨122133986290547113162650169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162845315054062817550200225 122133986290547113162650169)
  ·
    refine ⟨91600489717910334871987627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122133986290547113162650169 91600489717910334871987627)
    ·
      refine ⟨137400734576865502307981441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91600489717910334871987627 137400734576865502307981441)
      ·
        refine ⟨103050550932649126730986081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137400734576865502307981441 103050550932649126730986081)
        ·
          refine ⟨77287913199486845048239561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103050550932649126730986081 77287913199486845048239561)
          ·
            refine ⟨57965934899615133786179671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77287913199486845048239561 57965934899615133786179671)
            ·
              refine ⟨86948902349422700679269507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57965934899615133786179671 86948902349422700679269507)
              ·
                refine ⟨130423353524134051018904261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86948902349422700679269507 130423353524134051018904261)
                ·
                  refine ⟨24454378785775134566044549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130423353524134051018904261 24454378785775134566044549)
                  ·
                    refine ⟨4585196022332837731133353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24454378785775134566044549 4585196022332837731133353)
                    ·
                      refine ⟨3438897016749628298350015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4585196022332837731133353 3438897016749628298350015)
                      ·
                        rfl

theorem cell23_6697228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_6697228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697228 prefixEnd_6697228 := by exact prefixLift 6697228
  have htrace : WordTrace (prefixWord ++ tailWord_6697228) baseStart_6697228 baseEnd_6697228 := by
    simpa [prefixWord, tailWord_6697228, baseEnd_6697228] using wordTrace_append hprefix tailTrace_6697228
  have hstable : (prefixWord ++ tailWord_6697228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697228).length < 2 ^ (prefixWord ++ tailWord_6697228).sum := by decide
  have hdescent : baseEnd_6697228 < baseStart_6697228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697248 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 3]
def baseStart_6697248 : Nat := 118140960795 + 6697248 * 2 ^ 59
def prefixEnd_6697248 : Nat := 4983230072969 + 3 ^ 40 * 6697248 * 2
def baseEnd_6697248 : Nat := 3438907286362718220099923

theorem tailTrace_6697248 : CollatzResearch.WordTrace tailWord_6697248 prefixEnd_6697248 3438907286362718220099923 := by
  unfold tailWord_6697248
  simp only [CollatzResearch.WordTrace]
  refine ⟨122134351020510884870514199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162845801360681179827352265 122134351020510884870514199)
  ·
    refine ⟨183201526530766327305771299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122134351020510884870514199 183201526530766327305771299)
    ·
      refine ⟨274802289796149490958656949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183201526530766327305771299 274802289796149490958656949)
      ·
        refine ⟨25762714668389014777374089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 274802289796149490958656949 25762714668389014777374089)
        ·
          refine ⟨19322036001291761083030567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25762714668389014777374089 19322036001291761083030567)
          ·
            refine ⟨28983054001937641624545851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19322036001291761083030567 28983054001937641624545851)
            ·
              refine ⟨43474581002906462436818777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28983054001937641624545851 43474581002906462436818777)
              ·
                refine ⟨32605935752179846827614083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43474581002906462436818777 32605935752179846827614083)
                ·
                  refine ⟨48908903628269770241421125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32605935752179846827614083 48908903628269770241421125)
                  ·
                    refine ⟨9170419430300581920266461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48908903628269770241421125 9170419430300581920266461)
                    ·
                      refine ⟨3438907286362718220099923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9170419430300581920266461 3438907286362718220099923)
                      ·
                        rfl

theorem cell23_6697248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_6697248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697248 prefixEnd_6697248 := by exact prefixLift 6697248
  have htrace : WordTrace (prefixWord ++ tailWord_6697248) baseStart_6697248 baseEnd_6697248 := by
    simpa [prefixWord, tailWord_6697248, baseEnd_6697248] using wordTrace_append hprefix tailTrace_6697248
  have hstable : (prefixWord ++ tailWord_6697248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697248).length < 2 ^ (prefixWord ++ tailWord_6697248).sum := by decide
  have hdescent : baseEnd_6697248 < baseStart_6697248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697268 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 8]
def baseStart_6697268 : Nat := 118140960795 + 6697268 * 2 ^ 59
def prefixEnd_6697268 : Nat := 4983230072969 + 3 ^ 40 * 6697268 * 2
def baseEnd_6697268 : Nat := 382101950663978682427759

theorem tailTrace_6697268 : CollatzResearch.WordTrace tailWord_6697268 prefixEnd_6697268 382101950663978682427759 := by
  unfold tailWord_6697268
  simp only [CollatzResearch.WordTrace]
  refine ⟨122134715750474656578378229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162846287667299542104504305 122134715750474656578378229)
  ·
    refine ⟨11450129601606999054222959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122134715750474656578378229 11450129601606999054222959)
    ·
      refine ⟨17175194402410498581334439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11450129601606999054222959 17175194402410498581334439)
      ·
        refine ⟨25762791603615747872001659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17175194402410498581334439 25762791603615747872001659)
        ·
          refine ⟨38644187405423621808002489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25762791603615747872001659 38644187405423621808002489)
          ·
            refine ⟨28983140554067716356001867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38644187405423621808002489 28983140554067716356001867)
            ·
              refine ⟨43474710831101574534002801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28983140554067716356001867 43474710831101574534002801)
              ·
                refine ⟨32606033123326180900502101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43474710831101574534002801 32606033123326180900502101)
                ·
                  refine ⟨382101950663978682427759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32606033123326180900502101 382101950663978682427759)
                  ·
                    rfl

theorem cell23_6697268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_6697268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697268 prefixEnd_6697268 := by exact prefixLift 6697268
  have htrace : WordTrace (prefixWord ++ tailWord_6697268) baseStart_6697268 baseEnd_6697268 := by
    simpa [prefixWord, tailWord_6697268, baseEnd_6697268] using wordTrace_append hprefix tailTrace_6697268
  have hstable : (prefixWord ++ tailWord_6697268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697268).length < 2 ^ (prefixWord ++ tailWord_6697268).sum := by decide
  have hdescent : baseEnd_6697268 < baseStart_6697268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697322 : List Nat := [3, 1, 3, 3, 1, 1, 1, 3, 2, 3, 2]
def baseStart_6697322 : Nat := 118140960795 + 6697322 * 2 ^ 59
def prefixEnd_6697322 : Nat := 4983230072969 + 3 ^ 40 * 6697322 * 2
def baseEnd_6697322 : Nat := 3438945283931150930574583

theorem tailTrace_6697322 : CollatzResearch.WordTrace tailWord_6697322 prefixEnd_6697322 3438945283931150930574583 := by
  unfold tailWord_6697322
  simp only [CollatzResearch.WordTrace]
  refine ⟨61067850260688420094805555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162847600695169120252814813 61067850260688420094805555)
  ·
    refine ⟨91601775391032630142208333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61067850260688420094805555 91601775391032630142208333)
    ·
      refine ⟨34350665771637236303328125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91601775391032630142208333 34350665771637236303328125)
      ·
        refine ⟨12881499664363963613748047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34350665771637236303328125 12881499664363963613748047)
        ·
          refine ⟨19322249496545945420622071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12881499664363963613748047 19322249496545945420622071)
          ·
            refine ⟨28983374244818918130933107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19322249496545945420622071 28983374244818918130933107)
            ·
              refine ⟨43475061367228377196399661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28983374244818918130933107 43475061367228377196399661)
              ·
                refine ⟨16303148012710641448649873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43475061367228377196399661 16303148012710641448649873)
                ·
                  refine ⟨12227361009532981086487405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16303148012710641448649873 12227361009532981086487405)
                  ·
                    refine ⟨4585260378574867907432777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12227361009532981086487405 4585260378574867907432777)
                    ·
                      refine ⟨3438945283931150930574583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4585260378574867907432777 3438945283931150930574583)
                      ·
                        rfl

theorem cell23_6697322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_6697322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697322 prefixEnd_6697322 := by exact prefixLift 6697322
  have htrace : WordTrace (prefixWord ++ tailWord_6697322) baseStart_6697322 baseEnd_6697322 := by
    simpa [prefixWord, tailWord_6697322, baseEnd_6697322] using wordTrace_append hprefix tailTrace_6697322
  have hstable : (prefixWord ++ tailWord_6697322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697322).length < 2 ^ (prefixWord ++ tailWord_6697322).sum := by decide
  have hdescent : baseEnd_6697322 < baseStart_6697322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697328 : List Nat := [2, 1, 1, 1, 4, 4, 1, 2, 1, 6]
def baseStart_6697328 : Nat := 118140960795 + 6697328 * 2 ^ 59
def prefixEnd_6697328 : Nat := 4983230072969 + 3 ^ 40 * 6697328 * 2
def baseEnd_6697328 : Nat := 1146316121605025969033185

theorem tailTrace_6697328 : CollatzResearch.WordTrace tailWord_6697328 prefixEnd_6697328 1146316121605025969033185 := by
  unfold tailWord_6697328
  simp only [CollatzResearch.WordTrace]
  refine ⟨122135809940365971701970319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162847746587154628935960425 122135809940365971701970319)
  ·
    refine ⟨183203714910548957552955479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122135809940365971701970319 183203714910548957552955479)
    ·
      refine ⟨274805572365823436329433219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183203714910548957552955479 274805572365823436329433219)
      ·
        refine ⟨412208358548735154494149829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274805572365823436329433219 412208358548735154494149829)
        ·
          refine ⟨77289067227887841467653093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 412208358548735154494149829 77289067227887841467653093)
          ·
            refine ⟨14491700105228970275184955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77289067227887841467653093 14491700105228970275184955)
            ·
              refine ⟨21737550157843455412777433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14491700105228970275184955 21737550157843455412777433)
              ·
                refine ⟨16303162618382591559583075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21737550157843455412777433 16303162618382591559583075)
                ·
                  refine ⟨24454743927573887339374613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16303162618382591559583075 24454743927573887339374613)
                  ·
                    refine ⟨1146316121605025969033185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24454743927573887339374613 1146316121605025969033185)
                    ·
                      rfl

theorem cell23_6697328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 1, 6].length) (baseStart_6697328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697328 prefixEnd_6697328 := by exact prefixLift 6697328
  have htrace : WordTrace (prefixWord ++ tailWord_6697328) baseStart_6697328 baseEnd_6697328 := by
    simpa [prefixWord, tailWord_6697328, baseEnd_6697328] using wordTrace_append hprefix tailTrace_6697328
  have hstable : (prefixWord ++ tailWord_6697328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697328).length < 2 ^ (prefixWord ++ tailWord_6697328).sum := by decide
  have hdescent : baseEnd_6697328 < baseStart_6697328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697335 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 7, 2, 2]
def baseStart_6697335 : Nat := 118140960795 + 6697335 * 2 ^ 59
def prefixEnd_6697335 : Nat := 4983230072969 + 3 ^ 40 * 6697335 * 2
def baseEnd_6697335 : Nat := 3438951959179659379712023

theorem tailTrace_6697335 : CollatzResearch.WordTrace tailWord_6697335 prefixEnd_6697335 3438951959179659379712023 := by
  unfold tailWord_6697335
  simp only [CollatzResearch.WordTrace]
  refine ⟨244271875191706583599445459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162847916794471055732963639 244271875191706583599445459)
  ·
    refine ⟨366407812787559875399168189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244271875191706583599445459 366407812787559875399168189)
    ·
      refine ⟨137402929795334953274688071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366407812787559875399168189 137402929795334953274688071)
      ·
        refine ⟨206104394693002429912032107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137402929795334953274688071 206104394693002429912032107)
        ·
          refine ⟨309156592039503644868048161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206104394693002429912032107 309156592039503644868048161)
          ·
            refine ⟨231867444029627733651036121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309156592039503644868048161 231867444029627733651036121)
            ·
              refine ⟨173900583022220800238277091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231867444029627733651036121 173900583022220800238277091)
              ·
                refine ⟨260850874533331200357415637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173900583022220800238277091 260850874533331200357415637)
                ·
                  refine ⟨6113692371874950008376929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 260850874533331200357415637 6113692371874950008376929)
                  ·
                    refine ⟨4585269278906212506282697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6113692371874950008376929 4585269278906212506282697)
                    ·
                      refine ⟨3438951959179659379712023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4585269278906212506282697 3438951959179659379712023)
                      ·
                        rfl

theorem cell23_6697335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 2, 2].length) (baseStart_6697335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697335 prefixEnd_6697335 := by exact prefixLift 6697335
  have htrace : WordTrace (prefixWord ++ tailWord_6697335) baseStart_6697335 baseEnd_6697335 := by
    simpa [prefixWord, tailWord_6697335, baseEnd_6697335] using wordTrace_append hprefix tailTrace_6697335
  have hstable : (prefixWord ++ tailWord_6697335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697335).length < 2 ^ (prefixWord ++ tailWord_6697335).sum := by decide
  have hdescent : baseEnd_6697335 < baseStart_6697335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697338 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3]
def baseStart_6697338 : Nat := 118140960795 + 6697338 * 2 ^ 59
def prefixEnd_6697338 : Nat := 4983230072969 + 3 ^ 40 * 6697338 * 2
def baseEnd_6697338 : Nat := 3438953499621622867974509

theorem tailTrace_6697338 : CollatzResearch.WordTrace tailWord_6697338 prefixEnd_6697338 3438953499621622867974509 := by
  unfold tailWord_6697338
  simp only [CollatzResearch.WordTrace]
  refine ⟨61067996152673928777951167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162847989740463810074536445 61067996152673928777951167)
  ·
    refine ⟨91601994229010893166926751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61067996152673928777951167 91601994229010893166926751)
    ·
      refine ⟨137402991343516339750390127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91601994229010893166926751 137402991343516339750390127)
      ·
        refine ⟨206104487015274509625585191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137402991343516339750390127 206104487015274509625585191)
        ·
          refine ⟨309156730522911764438377787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206104487015274509625585191 309156730522911764438377787)
          ·
            refine ⟨463735095784367646657566681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309156730522911764438377787 463735095784367646657566681)
            ·
              refine ⟨347801321838275734993175011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463735095784367646657566681 347801321838275734993175011)
              ·
                refine ⟨521701982757413602489762517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347801321838275734993175011 521701982757413602489762517)
                ·
                  refine ⟨12227390220876881308353809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 521701982757413602489762517 12227390220876881308353809)
                  ·
                    refine ⟨9170542665657660981265357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12227390220876881308353809 9170542665657660981265357)
                    ·
                      refine ⟨3438953499621622867974509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9170542665657660981265357 3438953499621622867974509)
                      ·
                        rfl

theorem cell23_6697338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_6697338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697338 prefixEnd_6697338 := by exact prefixLift 6697338
  have htrace : WordTrace (prefixWord ++ tailWord_6697338) baseStart_6697338 baseEnd_6697338 := by
    simpa [prefixWord, tailWord_6697338, baseEnd_6697338] using wordTrace_append hprefix tailTrace_6697338
  have hstable : (prefixWord ++ tailWord_6697338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697338).length < 2 ^ (prefixWord ++ tailWord_6697338).sum := by decide
  have hdescent : baseEnd_6697338 < baseStart_6697338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697341 : List Nat := [1, 4, 1, 1, 2, 14]
def baseStart_6697341 : Nat := 118140960795 + 6697341 * 2 ^ 59
def prefixEnd_6697341 : Nat := 4983230072969 + 3 ^ 40 * 6697341 * 2
def baseEnd_6697341 : Nat := 14152078354171137268465

theorem tailTrace_6697341 : CollatzResearch.WordTrace tailWord_6697341 prefixEnd_6697341 14152078354171137268465 := by
  unfold tailWord_6697341
  simp only [CollatzResearch.WordTrace]
  refine ⟨244272094029684846624163877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162848062686456564416109251 244272094029684846624163877)
  ·
    refine ⟨45801017630565908742030727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244272094029684846624163877 45801017630565908742030727)
    ·
      refine ⟨68701526445848863113046091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45801017630565908742030727 68701526445848863113046091)
      ·
        refine ⟨103052289668773294669569137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68701526445848863113046091 103052289668773294669569137)
        ·
          refine ⟨77289217251579971002176853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103052289668773294669569137 77289217251579971002176853)
          ·
            refine ⟨14152078354171137268465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 77289217251579971002176853 14152078354171137268465)
            ·
              rfl

theorem cell23_6697341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 14].length) (baseStart_6697341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697341 prefixEnd_6697341 := by exact prefixLift 6697341
  have htrace : WordTrace (prefixWord ++ tailWord_6697341) baseStart_6697341 baseEnd_6697341 := by
    simpa [prefixWord, tailWord_6697341, baseEnd_6697341] using wordTrace_append hprefix tailTrace_6697341
  have hstable : (prefixWord ++ tailWord_6697341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697341).length < 2 ^ (prefixWord ++ tailWord_6697341).sum := by decide
  have hdescent : baseEnd_6697341 < baseStart_6697341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697348 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_6697348 : Nat := 118140960795 + 6697348 * 2 ^ 59
def prefixEnd_6697348 : Nat := 4983230072969 + 3 ^ 40 * 6697348 * 2
def baseEnd_6697348 : Nat := 3438958634428167828849463

theorem tailTrace_6697348 : CollatzResearch.WordTrace tailWord_6697348 prefixEnd_6697348 3438958634428167828849463 := by
  unfold tailWord_6697348
  simp only [CollatzResearch.WordTrace]
  refine ⟨122136174670329743409834349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162848232893772991213112465 122136174670329743409834349)
  ·
    refine ⟨45801065501373653778687881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122136174670329743409834349 45801065501373653778687881)
    ·
      refine ⟨34350799126030240334015911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45801065501373653778687881 34350799126030240334015911)
      ·
        refine ⟨51526198689045360501023867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34350799126030240334015911 51526198689045360501023867)
        ·
          refine ⟨77289298033568040751535801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51526198689045360501023867 77289298033568040751535801)
          ·
            refine ⟨57966973525176030563651851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77289298033568040751535801 57966973525176030563651851)
            ·
              refine ⟨86950460287764045845477777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57966973525176030563651851 86950460287764045845477777)
              ·
                refine ⟨65212845215823034384108333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86950460287764045845477777 65212845215823034384108333)
                ·
                  refine ⟨24454816955933637894040625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65212845215823034384108333 24454816955933637894040625)
                  ·
                    refine ⟨18341112716950228420530469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24454816955933637894040625 18341112716950228420530469)
                    ·
                      refine ⟨3438958634428167828849463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18341112716950228420530469 3438958634428167828849463)
                      ·
                        rfl

theorem cell23_6697348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_6697348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697348 prefixEnd_6697348 := by exact prefixLift 6697348
  have htrace : WordTrace (prefixWord ++ tailWord_6697348) baseStart_6697348 baseEnd_6697348 := by
    simpa [prefixWord, tailWord_6697348, baseEnd_6697348] using wordTrace_append hprefix tailTrace_6697348
  have hstable : (prefixWord ++ tailWord_6697348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697348).length < 2 ^ (prefixWord ++ tailWord_6697348).sum := by decide
  have hdescent : baseEnd_6697348 < baseStart_6697348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697352 : List Nat := [2, 1, 3, 3, 1, 1, 2, 3, 3, 2, 2]
def baseStart_6697352 : Nat := 118140960795 + 6697352 * 2 ^ 59
def prefixEnd_6697352 : Nat := 4983230072969 + 3 ^ 40 * 6697352 * 2
def baseEnd_6697352 : Nat := 3438960688350785813199445

theorem tailTrace_6697352 : CollatzResearch.WordTrace tailWord_6697352 prefixEnd_6697352 3438960688350785813199445 := by
  unfold tailWord_6697352
  simp only [CollatzResearch.WordTrace]
  refine ⟨122136247616322497751407155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162848330155096663668542873 122136247616322497751407155)
  ·
    refine ⟨183204371424483746627110733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122136247616322497751407155 183204371424483746627110733)
    ·
      refine ⟨68701639284181404985166525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183204371424483746627110733 68701639284181404985166525)
      ·
        refine ⟨25763114731568026869437447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68701639284181404985166525 25763114731568026869437447)
        ·
          refine ⟨38644672097352040304156171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25763114731568026869437447 38644672097352040304156171)
          ·
            refine ⟨57967008146028060456234257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38644672097352040304156171 57967008146028060456234257)
            ·
              refine ⟨43475256109521045342175693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57967008146028060456234257 43475256109521045342175693)
              ·
                refine ⟨16303221041070392003315885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43475256109521045342175693 16303221041070392003315885)
                ·
                  refine ⟨6113707890401397001243457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16303221041070392003315885 6113707890401397001243457)
                  ·
                    refine ⟨4585280917801047750932593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6113707890401397001243457 4585280917801047750932593)
                    ·
                      refine ⟨3438960688350785813199445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4585280917801047750932593 3438960688350785813199445)
                      ·
                        rfl

theorem cell23_6697352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_6697352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697352 prefixEnd_6697352 := by exact prefixLift 6697352
  have htrace : WordTrace (prefixWord ++ tailWord_6697352) baseStart_6697352 baseEnd_6697352 := by
    simpa [prefixWord, tailWord_6697352, baseEnd_6697352] using wordTrace_append hprefix tailTrace_6697352
  have hstable : (prefixWord ++ tailWord_6697352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697352).length < 2 ^ (prefixWord ++ tailWord_6697352).sum := by decide
  have hdescent : baseEnd_6697352 < baseStart_6697352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697386 : List Nat := [3, 1, 6, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_6697386 : Nat := 118140960795 + 6697386 * 2 ^ 59
def prefixEnd_6697386 : Nat := 4983230072969 + 3 ^ 40 * 6697386 * 2
def baseEnd_6697386 : Nat := 3438978146693038680174289

theorem tailTrace_6697386 : CollatzResearch.WordTrace tailWord_6697386 prefixEnd_6697386 3438978146693038680174289 := by
  unfold tailWord_6697386
  simp only [CollatzResearch.WordTrace]
  refine ⟨61068433828630454827388003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162849156876347879539701341 61068433828630454827388003)
  ·
    refine ⟨91602650742945682241082005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61068433828630454827388003 91602650742945682241082005)
    ·
      refine ⟨4293874253575578855050719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91602650742945682241082005 4293874253575578855050719)
      ·
        refine ⟨6440811380363368282576079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4293874253575578855050719 6440811380363368282576079)
        ·
          refine ⟨9661217070545052423864119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6440811380363368282576079 9661217070545052423864119)
          ·
            refine ⟨14491825605817578635796179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9661217070545052423864119 14491825605817578635796179)
            ·
              refine ⟨21737738408726367953694269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14491825605817578635796179 21737738408726367953694269)
              ·
                refine ⟨8151651903272387982635351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21737738408726367953694269 8151651903272387982635351)
                ·
                  refine ⟨12227477854908581973953027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8151651903272387982635351 12227477854908581973953027)
                  ·
                    refine ⟨18341216782362872960929541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12227477854908581973953027 18341216782362872960929541)
                    ·
                      refine ⟨3438978146693038680174289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18341216782362872960929541 3438978146693038680174289)
                      ·
                        rfl

theorem cell23_6697386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_6697386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697386 prefixEnd_6697386 := by exact prefixLift 6697386
  have htrace : WordTrace (prefixWord ++ tailWord_6697386) baseStart_6697386 baseEnd_6697386 := by
    simpa [prefixWord, tailWord_6697386, baseEnd_6697386] using wordTrace_append hprefix tailTrace_6697386
  have hstable : (prefixWord ++ tailWord_6697386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697386).length < 2 ^ (prefixWord ++ tailWord_6697386).sum := by decide
  have hdescent : baseEnd_6697386 < baseStart_6697386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697389 : List Nat := [1, 5, 2, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_6697389 : Nat := 118140960795 + 6697389 * 2 ^ 59
def prefixEnd_6697389 : Nat := 4983230072969 + 3 ^ 40 * 6697389 * 2
def baseEnd_6697389 : Nat := 3438979687135002168436775

theorem tailTrace_6697389 : CollatzResearch.WordTrace tailWord_6697389 prefixEnd_6697389 3438979687135002168436775 := by
  unfold tailWord_6697389
  simp only [CollatzResearch.WordTrace]
  refine ⟨244273844733510950821911221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162849229822340633881274147 244273844733510950821911221)
  ·
    refine ⟨22900672943766651639554177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244273844733510950821911221 22900672943766651639554177)
    ·
      refine ⟨17175504707824988729665633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22900672943766651639554177 17175504707824988729665633)
      ·
        refine ⟨12881628530868741547249225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17175504707824988729665633 12881628530868741547249225)
        ·
          refine ⟨9661221398151556160436919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12881628530868741547249225 9661221398151556160436919)
          ·
            refine ⟨14491832097227334240655379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9661221398151556160436919 14491832097227334240655379)
            ·
              refine ⟨21737748145841001360983069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14491832097227334240655379 21737748145841001360983069)
              ·
                refine ⟨8151655554690375510368651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21737748145841001360983069 8151655554690375510368651)
                ·
                  refine ⟨12227483332035563265552977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8151655554690375510368651 12227483332035563265552977)
                  ·
                    refine ⟨9170612499026672449164733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12227483332035563265552977 9170612499026672449164733)
                    ·
                      refine ⟨3438979687135002168436775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9170612499026672449164733 3438979687135002168436775)
                      ·
                        rfl

theorem cell23_6697389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_6697389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697389 prefixEnd_6697389 := by exact prefixLift 6697389
  have htrace : WordTrace (prefixWord ++ tailWord_6697389) baseStart_6697389 baseEnd_6697389 := by
    simpa [prefixWord, tailWord_6697389, baseEnd_6697389] using wordTrace_append hprefix tailTrace_6697389
  have hstable : (prefixWord ++ tailWord_6697389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697389).length < 2 ^ (prefixWord ++ tailWord_6697389).sum := by decide
  have hdescent : baseEnd_6697389 < baseStart_6697389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697418 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 2, 6]
def baseStart_6697418 : Nat := 118140960795 + 6697418 * 2 ^ 59
def prefixEnd_6697418 : Nat := 4983230072969 + 3 ^ 40 * 6697418 * 2
def baseEnd_6697418 : Nat := 1146331526024660851658047

theorem tailTrace_6697418 : CollatzResearch.WordTrace tailWord_6697418 prefixEnd_6697418 1146331526024660851658047 := by
  unfold tailWord_6697418
  simp only [CollatzResearch.WordTrace]
  refine ⟨61068725612601472193679227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162849934966937259183144605 61068725612601472193679227)
  ·
    refine ⟨91603088418902208290518841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61068725612601472193679227 91603088418902208290518841)
    ·
      refine ⟨68702316314176656217889131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91603088418902208290518841 68702316314176656217889131)
      ·
        refine ⟨103053474471264984326833697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68702316314176656217889131 103053474471264984326833697)
        ·
          refine ⟨77290105853448738245125273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103053474471264984326833697 77290105853448738245125273)
          ·
            refine ⟨57967579390086553683843955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77290105853448738245125273 57967579390086553683843955)
            ·
              refine ⟨86951369085129830525765933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57967579390086553683843955 86951369085129830525765933)
              ·
                refine ⟨32606763406923686447162225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86951369085129830525765933 32606763406923686447162225)
                ·
                  refine ⟨24455072555192764835371669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32606763406923686447162225 24455072555192764835371669)
                  ·
                    refine ⟨1146331526024660851658047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24455072555192764835371669 1146331526024660851658047)
                    ·
                      rfl

theorem cell23_6697418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_6697418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697418 prefixEnd_6697418 := by exact prefixLift 6697418
  have htrace : WordTrace (prefixWord ++ tailWord_6697418) baseStart_6697418 baseEnd_6697418 := by
    simpa [prefixWord, tailWord_6697418, baseEnd_6697418] using wordTrace_append hprefix tailTrace_6697418
  have hstable : (prefixWord ++ tailWord_6697418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697418).length < 2 ^ (prefixWord ++ tailWord_6697418).sum := by decide
  have hdescent : baseEnd_6697418 < baseStart_6697418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697429 : List Nat := [1, 3, 2, 3, 1, 3, 2, 2, 1, 3, 2]
def baseStart_6697429 : Nat := 118140960795 + 6697429 * 2 ^ 59
def prefixEnd_6697429 : Nat := 4983230072969 + 3 ^ 40 * 6697429 * 2
def baseEnd_6697429 : Nat := 3439000226361182011936591

theorem tailTrace_6697429 : CollatzResearch.WordTrace tailWord_6697429 prefixEnd_6697429 3439000226361182011936591 := by
  unfold tailWord_6697429
  simp only [CollatzResearch.WordTrace]
  refine ⟨244275303653366037653367341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162850202435577358435578227 244275303653366037653367341)
  ·
    refine ⟨91603238870012264120012753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244275303653366037653367341 91603238870012264120012753)
    ·
      refine ⟨68702429152509198090009565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91603238870012264120012753 68702429152509198090009565)
      ·
        refine ⟨25763410932190949283753587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68702429152509198090009565 25763410932190949283753587)
        ·
          refine ⟨38645116398286423925630381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25763410932190949283753587 38645116398286423925630381)
          ·
            refine ⟨14491918649357408972111393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38645116398286423925630381 14491918649357408972111393)
            ·
              refine ⟨10868938987018056729083545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14491918649357408972111393 10868938987018056729083545)
              ·
                refine ⟨8151704240263542546812659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10868938987018056729083545 8151704240263542546812659)
                ·
                  refine ⟨12227556360395313820218989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8151704240263542546812659 12227556360395313820218989)
                  ·
                    refine ⟨4585333635148242682582121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12227556360395313820218989 4585333635148242682582121)
                    ·
                      refine ⟨3439000226361182011936591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4585333635148242682582121 3439000226361182011936591)
                      ·
                        rfl

theorem cell23_6697429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_6697429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697429 prefixEnd_6697429 := by exact prefixLift 6697429
  have htrace : WordTrace (prefixWord ++ tailWord_6697429) baseStart_6697429 baseEnd_6697429 := by
    simpa [prefixWord, tailWord_6697429, baseEnd_6697429] using wordTrace_append hprefix tailTrace_6697429
  have hstable : (prefixWord ++ tailWord_6697429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697429).length < 2 ^ (prefixWord ++ tailWord_6697429).sum := by decide
  have hdescent : baseEnd_6697429 < baseStart_6697429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697465 : List Nat := [1, 2, 1, 3, 1, 2, 2, 6, 5]
def baseStart_6697465 : Nat := 118140960795 + 6697465 * 2 ^ 59
def prefixEnd_6697465 : Nat := 4983230072969 + 3 ^ 40 * 6697465 * 2
def baseEnd_6697465 : Nat := 382113190184971541231825

theorem tailTrace_6697465 : CollatzResearch.WordTrace tailWord_6697465 prefixEnd_6697465 382113190184971541231825 := by
  unfold tailWord_6697465
  simp only [CollatzResearch.WordTrace]
  refine ⟨244276616681235615801677849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162851077787490410534451899 244276616681235615801677849)
  ·
    refine ⟨183207462510926711851258387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244276616681235615801677849 183207462510926711851258387)
    ·
      refine ⟨274811193766390067776887581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183207462510926711851258387 274811193766390067776887581)
      ·
        refine ⟨103054197662396275416332843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274811193766390067776887581 103054197662396275416332843)
        ·
          refine ⟨154581296493594413124499265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103054197662396275416332843 154581296493594413124499265)
          ·
            refine ⟨115935972370195809843374449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154581296493594413124499265 115935972370195809843374449)
            ·
              refine ⟨86951979277646857382530837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115935972370195809843374449 86951979277646857382530837)
              ·
                refine ⟨4075874028639696439806133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86951979277646857382530837 4075874028639696439806133)
                ·
                  refine ⟨382113190184971541231825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4075874028639696439806133 382113190184971541231825)
                  ·
                    rfl

theorem cell23_6697465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 5].length) (baseStart_6697465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697465 prefixEnd_6697465 := by exact prefixLift 6697465
  have htrace : WordTrace (prefixWord ++ tailWord_6697465) baseStart_6697465 baseEnd_6697465 := by
    simpa [prefixWord, tailWord_6697465, baseEnd_6697465] using wordTrace_append hprefix tailTrace_6697465
  have hstable : (prefixWord ++ tailWord_6697465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697465).length < 2 ^ (prefixWord ++ tailWord_6697465).sum := by decide
  have hdescent : baseEnd_6697465 < baseStart_6697465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697476 : List Nat := [2, 3, 2, 3, 1, 2, 1, 3, 2, 2, 2]
def baseStart_6697476 : Nat := 118140960795 + 6697476 * 2 ^ 59
def prefixEnd_6697476 : Nat := 4983230072969 + 3 ^ 40 * 6697476 * 2
def baseEnd_6697476 : Nat := 3439024359951943328048875

theorem tailTrace_6697476 : CollatzResearch.WordTrace tailWord_6697476 prefixEnd_6697476 3439024359951943328048875 := by
  unfold tailWord_6697476
  simp only [CollatzResearch.WordTrace]
  refine ⟨122138508942097882340164141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162851345256130509786885521 122138508942097882340164141)
  ·
    refine ⟨45801940853286705877561553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122138508942097882340164141 45801940853286705877561553)
    ·
      refine ⟨34351455639965029408171165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45801940853286705877561553 34351455639965029408171165)
      ·
        refine ⟨12881795864986886028064187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34351455639965029408171165 12881795864986886028064187)
        ·
          refine ⟨19322693797480329042096281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12881795864986886028064187 19322693797480329042096281)
          ·
            refine ⟨14492020348110246781572211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19322693797480329042096281 14492020348110246781572211)
            ·
              refine ⟨21738030522165370172358317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14492020348110246781572211 21738030522165370172358317)
              ·
                refine ⟨8151761445812013814634369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21738030522165370172358317 8151761445812013814634369)
                ·
                  refine ⟨6113821084359010360975777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8151761445812013814634369 6113821084359010360975777)
                  ·
                    refine ⟨4585365813269257770731833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6113821084359010360975777 4585365813269257770731833)
                    ·
                      refine ⟨3439024359951943328048875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4585365813269257770731833 3439024359951943328048875)
                      ·
                        rfl

theorem cell23_6697476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_6697476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697476 prefixEnd_6697476 := by exact prefixLift 6697476
  have htrace : WordTrace (prefixWord ++ tailWord_6697476) baseStart_6697476 baseEnd_6697476 := by
    simpa [prefixWord, tailWord_6697476, baseEnd_6697476] using wordTrace_append hprefix tailTrace_6697476
  have hstable : (prefixWord ++ tailWord_6697476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697476).length < 2 ^ (prefixWord ++ tailWord_6697476).sum := by decide
  have hdescent : baseEnd_6697476 < baseStart_6697476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697512 : List Nat := [2, 1, 5, 2, 1, 1, 2, 2, 2, 5]
def baseStart_6697512 : Nat := 118140960795 + 6697512 * 2 ^ 59
def prefixEnd_6697512 : Nat := 4983230072969 + 3 ^ 40 * 6697512 * 2
def baseEnd_6697512 : Nat := 1146347615085168395732903

theorem tailTrace_6697512 : CollatzResearch.WordTrace tailWord_6697512 prefixEnd_6697512 1146347615085168395732903 := by
  unfold tailWord_6697512
  simp only [CollatzResearch.WordTrace]
  refine ⟨122139165456032671414319395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162852220608043561885759193 122139165456032671414319395)
  ·
    refine ⟨183208748184049007121479093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122139165456032671414319395 183208748184049007121479093)
    ·
      refine ⟨17175820142254594417638665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183208748184049007121479093 17175820142254594417638665)
      ·
        refine ⟨12881865106690945813228999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17175820142254594417638665 12881865106690945813228999)
        ·
          refine ⟨19322797660036418719843499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12881865106690945813228999 19322797660036418719843499)
          ·
            refine ⟨28984196490054628079765249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19322797660036418719843499 28984196490054628079765249)
            ·
              refine ⟨21738147367540971059823937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28984196490054628079765249 21738147367540971059823937)
              ·
                refine ⟨16303610525655728294867953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21738147367540971059823937 16303610525655728294867953)
                ·
                  refine ⟨12227707894241796221150965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16303610525655728294867953 12227707894241796221150965)
                  ·
                    refine ⟨1146347615085168395732903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12227707894241796221150965 1146347615085168395732903)
                    ·
                      rfl

theorem cell23_6697512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_6697512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697512 prefixEnd_6697512 := by exact prefixLift 6697512
  have htrace : WordTrace (prefixWord ++ tailWord_6697512) baseStart_6697512 baseEnd_6697512 := by
    simpa [prefixWord, tailWord_6697512, baseEnd_6697512] using wordTrace_append hprefix tailTrace_6697512
  have hstable : (prefixWord ++ tailWord_6697512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697512).length < 2 ^ (prefixWord ++ tailWord_6697512).sum := by decide
  have hdescent : baseEnd_6697512 < baseStart_6697512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697515 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 3, 6, 2]
def baseStart_6697515 : Nat := 118140960795 + 6697515 * 2 ^ 59
def prefixEnd_6697515 : Nat := 4983230072969 + 3 ^ 40 * 6697515 * 2
def baseEnd_6697515 : Nat := 3439044385697468675461195

theorem tailTrace_6697515 : CollatzResearch.WordTrace tailWord_6697515 prefixEnd_6697515 3439044385697468675461195 := by
  unfold tailWord_6697515
  simp only [CollatzResearch.WordTrace]
  refine ⟨244278440331054474340997999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162852293554036316227331999 244278440331054474340997999)
  ·
    refine ⟨366417660496581711511496999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244278440331054474340997999 366417660496581711511496999)
    ·
      refine ⟨549626490744872567267245499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366417660496581711511496999 549626490744872567267245499)
      ·
        refine ⟨824439736117308850900868249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549626490744872567267245499 824439736117308850900868249)
        ·
          refine ⟨618329802087981638175651187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 824439736117308850900868249 618329802087981638175651187)
          ·
            refine ⟨927494703131972457263476781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618329802087981638175651187 927494703131972457263476781)
            ·
              refine ⟨347810513674489671473803793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 927494703131972457263476781 347810513674489671473803793)
              ·
                refine ⟨260857885255867253605352845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347810513674489671473803793 260857885255867253605352845)
                ·
                  refine ⟨97821706970950220102007317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260857885255867253605352845 97821706970950220102007317)
                  ·
                    refine ⟨4585392514263291567281593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97821706970950220102007317 4585392514263291567281593)
                    ·
                      refine ⟨3439044385697468675461195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4585392514263291567281593 3439044385697468675461195)
                      ·
                        rfl

theorem cell23_6697515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 6, 2].length) (baseStart_6697515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697515 prefixEnd_6697515 := by exact prefixLift 6697515
  have htrace : WordTrace (prefixWord ++ tailWord_6697515) baseStart_6697515 baseEnd_6697515 := by
    simpa [prefixWord, tailWord_6697515, baseEnd_6697515] using wordTrace_append hprefix tailTrace_6697515
  have hstable : (prefixWord ++ tailWord_6697515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697515).length < 2 ^ (prefixWord ++ tailWord_6697515).sum := by decide
  have hdescent : baseEnd_6697515 < baseStart_6697515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697532 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 1, 6, 2]
def baseStart_6697532 : Nat := 118140960795 + 6697532 * 2 ^ 59
def prefixEnd_6697532 : Nat := 4983230072969 + 3 ^ 40 * 6697532 * 2
def baseEnd_6697532 : Nat := 3439053114868595108948617

theorem tailTrace_6697532 : CollatzResearch.WordTrace tailWord_6697532 prefixEnd_6697532 3439053114868595108948617 := by
  unfold tailWord_6697532
  simp only [CollatzResearch.WordTrace]
  refine ⟨122139530185996443122183425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162852706914661924162911233 122139530185996443122183425)
  ·
    refine ⟨91604647639497332341637569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122139530185996443122183425 91604647639497332341637569)
    ·
      refine ⟨68703485729622999256228177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91604647639497332341637569 68703485729622999256228177)
      ·
        refine ⟨51527614297217249442171133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68703485729622999256228177 51527614297217249442171133)
        ·
          refine ⟨19322855361456468540814175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51527614297217249442171133 19322855361456468540814175)
          ·
            refine ⟨28984283042184702811221263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19322855361456468540814175 28984283042184702811221263)
            ·
              refine ⟨43476424563277054216831895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28984283042184702811221263 43476424563277054216831895)
              ·
                refine ⟨65214636844915581325247843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43476424563277054216831895 65214636844915581325247843)
                ·
                  refine ⟨97821955267373371987871765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65214636844915581325247843 97821955267373371987871765)
                  ·
                    refine ⟨4585404153158126811931489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97821955267373371987871765 4585404153158126811931489)
                    ·
                      refine ⟨3439053114868595108948617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4585404153158126811931489 3439053114868595108948617)
                      ·
                        rfl

theorem cell23_6697532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_6697532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697532 prefixEnd_6697532 := by exact prefixLift 6697532
  have htrace : WordTrace (prefixWord ++ tailWord_6697532) baseStart_6697532 baseEnd_6697532 := by
    simpa [prefixWord, tailWord_6697532, baseEnd_6697532] using wordTrace_append hprefix tailTrace_6697532
  have hstable : (prefixWord ++ tailWord_6697532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697532).length < 2 ^ (prefixWord ++ tailWord_6697532).sum := by decide
  have hdescent : baseEnd_6697532 < baseStart_6697532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697535 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 3]
def baseStart_6697535 : Nat := 118140960795 + 6697535 * 2 ^ 59
def prefixEnd_6697535 : Nat := 4983230072969 + 3 ^ 40 * 6697535 * 2
def baseEnd_6697535 : Nat := 3439054655310558597211103

theorem tailTrace_6697535 : CollatzResearch.WordTrace tailWord_6697535 prefixEnd_6697535 3439054655310558597211103 := by
  unfold tailWord_6697535
  simp only [CollatzResearch.WordTrace]
  refine ⟨244279169790982017756726059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162852779860654678504484039 244279169790982017756726059)
  ·
    refine ⟨366418754686473026635089089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244279169790982017756726059 366418754686473026635089089)
    ·
      refine ⟨274814066014854769976316817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366418754686473026635089089 274814066014854769976316817)
      ·
        refine ⟨206110549511141077482237613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274814066014854769976316817 206110549511141077482237613)
        ·
          refine ⟨77291456066677904055839105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206110549511141077482237613 77291456066677904055839105)
          ·
            refine ⟨57968592050008428041879329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77291456066677904055839105 57968592050008428041879329)
            ·
              refine ⟨43476444037506321031409497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57968592050008428041879329 43476444037506321031409497)
              ·
                refine ⟨32607333028129740773557123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43476444037506321031409497 32607333028129740773557123)
                ·
                  refine ⟨48910999542194611160335685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32607333028129740773557123 48910999542194611160335685)
                  ·
                    refine ⟨9170812414161489592562941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48910999542194611160335685 9170812414161489592562941)
                    ·
                      refine ⟨3439054655310558597211103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9170812414161489592562941 3439054655310558597211103)
                      ·
                        rfl

theorem cell23_6697535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_6697535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697535 prefixEnd_6697535 := by exact prefixLift 6697535
  have htrace : WordTrace (prefixWord ++ tailWord_6697535) baseStart_6697535 baseEnd_6697535 := by
    simpa [prefixWord, tailWord_6697535, baseEnd_6697535] using wordTrace_append hprefix tailTrace_6697535
  have hstable : (prefixWord ++ tailWord_6697535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697535).length < 2 ^ (prefixWord ++ tailWord_6697535).sum := by decide
  have hdescent : baseEnd_6697535 < baseStart_6697535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697549 : List Nat := [1, 6, 1, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_6697549 : Nat := 118140960795 + 6697549 * 2 ^ 59
def prefixEnd_6697549 : Nat := 4983230072969 + 3 ^ 40 * 6697549 * 2
def baseEnd_6697549 : Nat := 3439061844039721542436039

theorem tailTrace_6697549 : CollatzResearch.WordTrace tailWord_6697549 prefixEnd_6697549 3439061844039721542436039 := by
  unfold tailWord_6697549
  simp only [CollatzResearch.WordTrace]
  refine ⟨244279680412931298147735701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162853120275287532098490467 244279680412931298147735701)
  ·
    refine ⟨11450610019356154600675111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 244279680412931298147735701 11450610019356154600675111)
    ·
      refine ⟨17175915029034231901012667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11450610019356154600675111 17175915029034231901012667)
      ·
        refine ⟨25763872543551347851519001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17175915029034231901012667 25763872543551347851519001)
        ·
          refine ⟨19322904407663510888639251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25763872543551347851519001 19322904407663510888639251)
          ·
            refine ⟨28984356611495266332958877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19322904407663510888639251 28984356611495266332958877)
            ·
              refine ⟨10869133729310724874859579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28984356611495266332958877 10869133729310724874859579)
              ·
                refine ⟨16303700593966087312289369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10869133729310724874859579 16303700593966087312289369)
                ·
                  refine ⟨12227775445474565484217027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16303700593966087312289369 12227775445474565484217027)
                  ·
                    refine ⟨18341663168211848226325541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12227775445474565484217027 18341663168211848226325541)
                    ·
                      refine ⟨3439061844039721542436039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18341663168211848226325541 3439061844039721542436039)
                      ·
                        rfl

theorem cell23_6697549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_6697549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697549 prefixEnd_6697549 := by exact prefixLift 6697549
  have htrace : WordTrace (prefixWord ++ tailWord_6697549) baseStart_6697549 baseEnd_6697549 := by
    simpa [prefixWord, tailWord_6697549, baseEnd_6697549] using wordTrace_append hprefix tailTrace_6697549
  have hstable : (prefixWord ++ tailWord_6697549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697549).length < 2 ^ (prefixWord ++ tailWord_6697549).sum := by decide
  have hdescent : baseEnd_6697549 < baseStart_6697549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697559 : List Nat := [1, 1, 3, 2, 2, 2, 4, 3, 1, 4]
def baseStart_6697559 : Nat := 118140960795 + 6697559 * 2 ^ 59
def prefixEnd_6697559 : Nat := 4983230072969 + 3 ^ 40 * 6697559 * 2
def baseEnd_6697559 : Nat := 1146355659615422167770331

theorem tailTrace_6697559 : CollatzResearch.WordTrace tailWord_6697559 prefixEnd_6697559 1146355659615422167770331 := by
  unfold tailWord_6697559
  simp only [CollatzResearch.WordTrace]
  refine ⟨244280045142895069855599731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162853363428596713237066487 244280045142895069855599731)
  ·
    refine ⟨366420067714342604783399597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244280045142895069855599731 366420067714342604783399597)
    ·
      refine ⟨137407525392878476793774849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366420067714342604783399597 137407525392878476793774849)
      ·
        refine ⟨103055644044658857595331137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137407525392878476793774849 103055644044658857595331137)
        ·
          refine ⟨77291733033494143196498353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103055644044658857595331137 77291733033494143196498353)
          ·
            refine ⟨57968799775120607397373765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77291733033494143196498353 57968799775120607397373765)
            ·
              refine ⟨10869149957835113887007581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57968799775120607397373765 10869149957835113887007581)
              ·
                refine ⟨4075931234188167707627843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10869149957835113887007581 4075931234188167707627843)
                ·
                  refine ⟨6113896851282251561441765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4075931234188167707627843 6113896851282251561441765)
                  ·
                    refine ⟨1146355659615422167770331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6113896851282251561441765 1146355659615422167770331)
                    ·
                      rfl

theorem cell23_6697559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 1, 4].length) (baseStart_6697559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697559 prefixEnd_6697559 := by exact prefixLift 6697559
  have htrace : WordTrace (prefixWord ++ tailWord_6697559) baseStart_6697559 baseEnd_6697559 := by
    simpa [prefixWord, tailWord_6697559, baseEnd_6697559] using wordTrace_append hprefix tailTrace_6697559
  have hstable : (prefixWord ++ tailWord_6697559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697559).length < 2 ^ (prefixWord ++ tailWord_6697559).sum := by decide
  have hdescent : baseEnd_6697559 < baseStart_6697559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697592 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 4, 3, 2]
def baseStart_6697592 : Nat := 118140960795 + 6697592 * 2 ^ 59
def prefixEnd_6697592 : Nat := 4983230072969 + 3 ^ 40 * 6697592 * 2
def baseEnd_6697592 : Nat := 3439083923707864874198341

theorem tailTrace_6697592 : CollatzResearch.WordTrace tailWord_6697592 prefixEnd_6697592 3439083923707864874198341 := by
  unfold tailWord_6697592
  simp only [CollatzResearch.WordTrace]
  refine ⟨122140624375887758245775515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162854165834517010994367353 122140624375887758245775515)
  ·
    refine ⟨183210936563831637368663273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122140624375887758245775515 183210936563831637368663273)
    ·
      refine ⟨137408202422873728026497455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183210936563831637368663273 137408202422873728026497455)
      ·
        refine ⟨206112303634310592039746183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137408202422873728026497455 206112303634310592039746183)
        ·
          refine ⟨309168455451465888059619275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206112303634310592039746183 309168455451465888059619275)
          ·
            refine ⟨463752683177198832089428913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309168455451465888059619275 463752683177198832089428913)
            ·
              refine ⟨347814512382899124067071685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463752683177198832089428913 347814512382899124067071685)
              ·
                refine ⟨65215221071793585762575941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 347814512382899124067071685 65215221071793585762575941)
                ·
                  refine ⟨12227853950961297330482989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65215221071793585762575941 12227853950961297330482989)
                  ·
                    refine ⟨4585445231610486498931121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12227853950961297330482989 4585445231610486498931121)
                    ·
                      refine ⟨3439083923707864874198341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4585445231610486498931121 3439083923707864874198341)
                      ·
                        rfl

theorem cell23_6697592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 4, 3, 2].length) (baseStart_6697592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697592 prefixEnd_6697592 := by exact prefixLift 6697592
  have htrace : WordTrace (prefixWord ++ tailWord_6697592) baseStart_6697592 baseEnd_6697592 := by
    simpa [prefixWord, tailWord_6697592, baseEnd_6697592] using wordTrace_append hprefix tailTrace_6697592
  have hstable : (prefixWord ++ tailWord_6697592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697592).length < 2 ^ (prefixWord ++ tailWord_6697592).sum := by decide
  have hdescent : baseEnd_6697592 < baseStart_6697592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697633 : List Nat := [1, 2, 3, 3, 4, 1, 1, 1, 3, 1, 3]
def baseStart_6697633 : Nat := 118140960795 + 6697633 * 2 ^ 59
def prefixEnd_6697633 : Nat := 4983230072969 + 3 ^ 40 * 6697633 * 2
def baseEnd_6697633 : Nat := 3439104976414699213785653

theorem tailTrace_6697633 : CollatzResearch.WordTrace tailWord_6697633 prefixEnd_6697633 3439104976414699213785653 := by
  unfold tailWord_6697633
  simp only [CollatzResearch.WordTrace]
  refine ⟨244282744144626980493793553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162855162763084653662529035 244282744144626980493793553)
  ·
    refine ⟨183212058108470235370345165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244282744144626980493793553 183212058108470235370345165)
    ·
      refine ⟨68704521790676338263879437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183212058108470235370345165 68704521790676338263879437)
      ·
        refine ⟨25764195671503626848954789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68704521790676338263879437 25764195671503626848954789)
        ·
          refine ⟨4830786688406930034179023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25764195671503626848954789 4830786688406930034179023)
          ·
            refine ⟨7246180032610395051268535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4830786688406930034179023 7246180032610395051268535)
            ·
              refine ⟨10869270048915592576902803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7246180032610395051268535 10869270048915592576902803)
              ·
                refine ⟨16303905073373388865354205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10869270048915592576902803 16303905073373388865354205)
                ·
                  refine ⟨6113964402515020824507827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16303905073373388865354205 6113964402515020824507827)
                  ·
                    refine ⟨9170946603772531236761741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6113964402515020824507827 9170946603772531236761741)
                    ·
                      refine ⟨3439104976414699213785653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9170946603772531236761741 3439104976414699213785653)
                      ·
                        rfl

theorem cell23_6697633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_6697633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697633 prefixEnd_6697633 := by exact prefixLift 6697633
  have htrace : WordTrace (prefixWord ++ tailWord_6697633) baseStart_6697633 baseEnd_6697633 := by
    simpa [prefixWord, tailWord_6697633, baseEnd_6697633] using wordTrace_append hprefix tailTrace_6697633
  have hstable : (prefixWord ++ tailWord_6697633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697633).length < 2 ^ (prefixWord ++ tailWord_6697633).sum := by decide
  have hdescent : baseEnd_6697633 < baseStart_6697633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697635 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 4]
def baseStart_6697635 : Nat := 118140960795 + 6697635 * 2 ^ 59
def prefixEnd_6697635 : Nat := 4983230072969 + 3 ^ 40 * 6697635 * 2
def baseEnd_6697635 : Nat := 3439106003376008205960643

theorem tailTrace_6697635 : CollatzResearch.WordTrace tailWord_6697635 prefixEnd_6697635 3439106003376008205960643 := by
  unfold tailWord_6697635
  simp only [CollatzResearch.WordTrace]
  refine ⟨244282817090619734835366359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162855211393746489890244239 244282817090619734835366359)
  ·
    refine ⟨366424225635929602253049539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244282817090619734835366359 366424225635929602253049539)
    ·
      refine ⟨549636338453894403379574309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366424225635929602253049539 549636338453894403379574309)
      ·
        refine ⟨103056813460105200633670183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 549636338453894403379574309 103056813460105200633670183)
        ·
          refine ⟨154585220190157800950505275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103056813460105200633670183 154585220190157800950505275)
          ·
            refine ⟨231877830285236701425757913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154585220190157800950505275 231877830285236701425757913)
            ·
              refine ⟨173908372713927526069318435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231877830285236701425757913 173908372713927526069318435)
              ·
                refine ⟨260862559070891289103977653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173908372713927526069318435 260862559070891289103977653)
                ·
                  refine ⟨24455864912896058353497905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 260862559070891289103977653 24455864912896058353497905)
                  ·
                    refine ⟨18341898684672043765123429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24455864912896058353497905 18341898684672043765123429)
                    ·
                      refine ⟨3439106003376008205960643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18341898684672043765123429 3439106003376008205960643)
                      ·
                        rfl

theorem cell23_6697635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_6697635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697635 prefixEnd_6697635 := by exact prefixLift 6697635
  have htrace : WordTrace (prefixWord ++ tailWord_6697635) baseStart_6697635 baseEnd_6697635 := by
    simpa [prefixWord, tailWord_6697635, baseEnd_6697635] using wordTrace_append hprefix tailTrace_6697635
  have hstable : (prefixWord ++ tailWord_6697635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697635).length < 2 ^ (prefixWord ++ tailWord_6697635).sum := by decide
  have hdescent : baseEnd_6697635 < baseStart_6697635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697670 : List Nat := [6, 1, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_6697670 : Nat := 118140960795 + 6697670 * 2 ^ 59
def prefixEnd_6697670 : Nat := 4983230072969 + 3 ^ 40 * 6697670 * 2
def baseEnd_6697670 : Nat := 1146374658399638523007661

theorem tailTrace_6697670 : CollatzResearch.WordTrace tailWord_6697670 prefixEnd_6697670 1146374658399638523007661 := by
  unfold tailWord_6697670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7633877926421654244152827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 162856062430328623875260309 7633877926421654244152827)
  ·
    refine ⟨11450816889632481366229241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7633877926421654244152827 11450816889632481366229241)
    ·
      refine ⟨8588112667224361024671931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11450816889632481366229241 8588112667224361024671931)
      ·
        refine ⟨12882169000836541537007897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8588112667224361024671931 12882169000836541537007897)
        ·
          refine ⟨9661626750627406152755923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12882169000836541537007897 9661626750627406152755923)
          ·
            refine ⟨14492440125941109229133885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9661626750627406152755923 14492440125941109229133885)
            ·
              refine ⟨5434665047227915960925207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14492440125941109229133885 5434665047227915960925207)
              ·
                refine ⟨8151997570841873941387811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5434665047227915960925207 8151997570841873941387811)
                ·
                  refine ⟨12227996356262810912081717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8151997570841873941387811 12227996356262810912081717)
                  ·
                    refine ⟨1146374658399638523007661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12227996356262810912081717 1146374658399638523007661)
                    ·
                      rfl

theorem cell23_6697670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_6697670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697670 prefixEnd_6697670 := by exact prefixLift 6697670
  have htrace : WordTrace (prefixWord ++ tailWord_6697670) baseStart_6697670 baseEnd_6697670 := by
    simpa [prefixWord, tailWord_6697670, baseEnd_6697670] using wordTrace_append hprefix tailTrace_6697670
  have hstable : (prefixWord ++ tailWord_6697670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697670).length < 2 ^ (prefixWord ++ tailWord_6697670).sum := by decide
  have hdescent : baseEnd_6697670 < baseStart_6697670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697672 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 3, 3, 3]
def baseStart_6697672 : Nat := 118140960795 + 6697672 * 2 ^ 59
def prefixEnd_6697672 : Nat := 4983230072969 + 3 ^ 40 * 6697672 * 2
def baseEnd_6697672 : Nat := 3439125002160224561197973

theorem tailTrace_6697672 : CollatzResearch.WordTrace tailWord_6697672 prefixEnd_6697672 3439125002160224561197973 := by
  unfold tailWord_6697672
  simp only [CollatzResearch.WordTrace]
  refine ⟨122142083295742845077231635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162856111060990460102975513 122142083295742845077231635)
  ·
    refine ⟨183213124943614267615847453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122142083295742845077231635 183213124943614267615847453)
    ·
      refine ⟨68704921853855350355942795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183213124943614267615847453 68704921853855350355942795)
      ·
        refine ⟨103057382780783025533914193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68704921853855350355942795 103057382780783025533914193)
        ·
          refine ⟨77293037085587269150435645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103057382780783025533914193 77293037085587269150435645)
          ·
            refine ⟨28984888907095225931413367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77293037085587269150435645 28984888907095225931413367)
            ·
              refine ⟨43477333360642838897120051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28984888907095225931413367 43477333360642838897120051)
              ·
                refine ⟨65216000040964258345680077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43477333360642838897120051 65216000040964258345680077)
                ·
                  refine ⟨24456000015361596879630029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65216000040964258345680077 24456000015361596879630029)
                  ·
                    refine ⟨9171000005760598829861261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24456000015361596879630029 9171000005760598829861261)
                    ·
                      refine ⟨3439125002160224561197973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9171000005760598829861261 3439125002160224561197973)
                      ·
                        rfl

theorem cell23_6697672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_6697672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697672 prefixEnd_6697672 := by exact prefixLift 6697672
  have htrace : WordTrace (prefixWord ++ tailWord_6697672) baseStart_6697672 baseEnd_6697672 := by
    simpa [prefixWord, tailWord_6697672, baseEnd_6697672] using wordTrace_append hprefix tailTrace_6697672
  have hstable : (prefixWord ++ tailWord_6697672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697672).length < 2 ^ (prefixWord ++ tailWord_6697672).sum := by decide
  have hdescent : baseEnd_6697672 < baseStart_6697672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697705 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 1, 8]
def baseStart_6697705 : Nat := 118140960795 + 6697705 * 2 ^ 59
def prefixEnd_6697705 : Nat := 4983230072969 + 3 ^ 40 * 6697705 * 2
def baseEnd_6697705 : Nat := 1146380649007274310695107

theorem tailTrace_6697705 : CollatzResearch.WordTrace tailWord_6697705 prefixEnd_6697705 1146380649007274310695107 := by
  unfold tailWord_6697705
  simp only [CollatzResearch.WordTrace]
  refine ⟨244285370200366136790414569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162856913466910757860276379 244285370200366136790414569)
  ·
    refine ⟨183214027650274602592810927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244285370200366136790414569 183214027650274602592810927)
    ·
      refine ⟨274821041475411903889216391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183214027650274602592810927 274821041475411903889216391)
      ·
        refine ⟨412231562213117855833824587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274821041475411903889216391 412231562213117855833824587)
        ·
          refine ⟨618347343319676783750736881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412231562213117855833824587 618347343319676783750736881)
          ·
            refine ⟨463760507489757587813052661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 618347343319676783750736881 463760507489757587813052661)
            ·
              refine ⟨43477547577164773857473687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 463760507489757587813052661 43477547577164773857473687)
              ·
                refine ⟨65216321365747160786210531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43477547577164773857473687 65216321365747160786210531)
                ·
                  refine ⟨97824482048620741179315797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65216321365747160786210531 97824482048620741179315797)
                  ·
                    refine ⟨1146380649007274310695107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97824482048620741179315797 1146380649007274310695107)
                    ·
                      rfl

theorem cell23_6697705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 8].length) (baseStart_6697705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697705 prefixEnd_6697705 := by exact prefixLift 6697705
  have htrace : WordTrace (prefixWord ++ tailWord_6697705) baseStart_6697705 baseEnd_6697705 := by
    simpa [prefixWord, tailWord_6697705, baseEnd_6697705] using wordTrace_append hprefix tailTrace_6697705
  have hstable : (prefixWord ++ tailWord_6697705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697705).length < 2 ^ (prefixWord ++ tailWord_6697705).sum := by decide
  have hdescent : baseEnd_6697705 < baseStart_6697705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697732 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_6697732 : Nat := 118140960795 + 6697732 * 2 ^ 59
def prefixEnd_6697732 : Nat := 4983230072969 + 3 ^ 40 * 6697732 * 2
def baseEnd_6697732 : Nat := 3439155810999494326447697

theorem tailTrace_6697732 : CollatzResearch.WordTrace tailWord_6697732 prefixEnd_6697732 3439155810999494326447697 := by
  unfold tailWord_6697732
  simp only [CollatzResearch.WordTrace]
  refine ⟨122143177485634160200823725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162857569980845546934431633 122143177485634160200823725)
  ·
    refine ⟨45803691557112810075308897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122143177485634160200823725 45803691557112810075308897)
    ·
      refine ⟨34352768667834607556481673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45803691557112810075308897 34352768667834607556481673)
      ·
        refine ⟨25764576500875955667361255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34352768667834607556481673 25764576500875955667361255)
        ·
          refine ⟨38646864751313933501041883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25764576500875955667361255 38646864751313933501041883)
          ·
            refine ⟨57970297126970900251562825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38646864751313933501041883 57970297126970900251562825)
            ·
              refine ⟨43477722845228175188672119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57970297126970900251562825 43477722845228175188672119)
              ·
                refine ⟨65216584267842262783008179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43477722845228175188672119 65216584267842262783008179)
                ·
                  refine ⟨97824876401763394174512269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65216584267842262783008179 97824876401763394174512269)
                  ·
                    refine ⟨36684328650661272815442101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97824876401763394174512269 36684328650661272815442101)
                    ·
                      refine ⟨3439155810999494326447697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36684328650661272815442101 3439155810999494326447697)
                      ·
                        rfl

theorem cell23_6697732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_6697732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697732 prefixEnd_6697732 := by exact prefixLift 6697732
  have htrace : WordTrace (prefixWord ++ tailWord_6697732) baseStart_6697732 baseEnd_6697732 := by
    simpa [prefixWord, tailWord_6697732, baseEnd_6697732] using wordTrace_append hprefix tailTrace_6697732
  have hstable : (prefixWord ++ tailWord_6697732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697732).length < 2 ^ (prefixWord ++ tailWord_6697732).sum := by decide
  have hdescent : baseEnd_6697732 < baseStart_6697732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697755 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 8]
def baseStart_6697755 : Nat := 118140960795 + 6697755 * 2 ^ 59
def prefixEnd_6697755 : Nat := 4983230072969 + 3 ^ 40 * 6697755 * 2
def baseEnd_6697755 : Nat := 3439167621054547736460091

theorem tailTrace_6697755 : CollatzResearch.WordTrace tailWord_6697755 prefixEnd_6697755 3439167621054547736460091 := by
  unfold tailWord_6697755
  simp only [CollatzResearch.WordTrace]
  refine ⟨244287193850184995329734719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162858129233456663553156479 244287193850184995329734719)
  ·
    refine ⟨366430790775277492994602079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244287193850184995329734719 366430790775277492994602079)
    ·
      refine ⟨549646186162916239491903119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366430790775277492994602079 549646186162916239491903119)
      ·
        refine ⟨824469279244374359237854679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549646186162916239491903119 824469279244374359237854679)
        ·
          refine ⟨1236703918866561538856782019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824469279244374359237854679 1236703918866561538856782019)
          ·
            refine ⟨1855055878299842308285173029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1236703918866561538856782019 1855055878299842308285173029)
            ·
              refine ⟨347822977181220432803469943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1855055878299842308285173029 347822977181220432803469943)
              ·
                refine ⟨521734465771830649205204915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347822977181220432803469943 521734465771830649205204915)
                ·
                  refine ⟨782601698657745973807807373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521734465771830649205204915 782601698657745973807807373)
                  ·
                    refine ⟨293475636996654740177927765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 782601698657745973807807373 293475636996654740177927765)
                    ·
                      refine ⟨3439167621054547736460091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 293475636996654740177927765 3439167621054547736460091)
                      ·
                        rfl

theorem cell23_6697755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 8].length) (baseStart_6697755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697755 prefixEnd_6697755 := by exact prefixLift 6697755
  have htrace : WordTrace (prefixWord ++ tailWord_6697755) baseStart_6697755 baseEnd_6697755 := by
    simpa [prefixWord, tailWord_6697755, baseEnd_6697755] using wordTrace_append hprefix tailTrace_6697755
  have hstable : (prefixWord ++ tailWord_6697755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697755).length < 2 ^ (prefixWord ++ tailWord_6697755).sum := by decide
  have hdescent : baseEnd_6697755 < baseStart_6697755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697802 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_6697802 : Nat := 118140960795 + 6697802 * 2 ^ 59
def prefixEnd_6697802 : Nat := 4983230072969 + 3 ^ 40 * 6697802 * 2
def baseEnd_6697802 : Nat := 3439191754645309052572375

theorem tailTrace_6697802 : CollatzResearch.WordTrace tailWord_6697802 prefixEnd_6697802 3439191754645309052572375 := by
  unfold tailWord_6697802
  simp only [CollatzResearch.WordTrace]
  refine ⟨61072227020253680589173915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162859272054009814904463773 61072227020253680589173915)
  ·
    refine ⟨91608340530380520883760873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61072227020253680589173915 91608340530380520883760873)
    ·
      refine ⟨68706255397785390662820655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91608340530380520883760873 68706255397785390662820655)
      ·
        refine ⟨103059383096678085994230983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68706255397785390662820655 103059383096678085994230983)
        ·
          refine ⟨154589074645017128991346475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103059383096678085994230983 154589074645017128991346475)
          ·
            refine ⟨231883611967525693487019713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154589074645017128991346475 231883611967525693487019713)
            ·
              refine ⟨173912708975644270115264785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231883611967525693487019713 173912708975644270115264785)
              ·
                refine ⟨130434531731733202586448589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173912708975644270115264785 130434531731733202586448589)
                ·
                  refine ⟨48912949399399950969918221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130434531731733202586448589 48912949399399950969918221)
                  ·
                    refine ⟨18342356024774981613719333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48912949399399950969918221 18342356024774981613719333)
                    ·
                      refine ⟨3439191754645309052572375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18342356024774981613719333 3439191754645309052572375)
                      ·
                        rfl

theorem cell23_6697802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_6697802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697802 prefixEnd_6697802 := by exact prefixLift 6697802
  have htrace : WordTrace (prefixWord ++ tailWord_6697802) baseStart_6697802 baseEnd_6697802 := by
    simpa [prefixWord, tailWord_6697802, baseEnd_6697802] using wordTrace_append hprefix tailTrace_6697802
  have hstable : (prefixWord ++ tailWord_6697802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697802).length < 2 ^ (prefixWord ++ tailWord_6697802).sum := by decide
  have hdescent : baseEnd_6697802 < baseStart_6697802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697809 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 1, 2, 5]
def baseStart_6697809 : Nat := 118140960795 + 6697809 * 2 ^ 59
def prefixEnd_6697809 : Nat := 4983230072969 + 3 ^ 40 * 6697809 * 2
def baseEnd_6697809 : Nat := 3439195349009890525184843

theorem tailTrace_6697809 : CollatzResearch.WordTrace tailWord_6697809 prefixEnd_6697809 3439195349009890525184843 := by
  unfold tailWord_6697809
  simp only [CollatzResearch.WordTrace]
  refine ⟨244289163391989362552200481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162859442261326241701466987 244289163391989362552200481)
  ·
    refine ⟨183216872543992021914150361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244289163391989362552200481 183216872543992021914150361)
    ·
      refine ⟨137412654407994016435612771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183216872543992021914150361 137412654407994016435612771)
      ·
        refine ⟨206118981611991024653419157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137412654407994016435612771 206118981611991024653419157)
        ·
          refine ⟨9661827263062079280629023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 206118981611991024653419157 9661827263062079280629023)
          ·
            refine ⟨14492740894593118920943535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9661827263062079280629023 14492740894593118920943535)
            ·
              refine ⟨21739111341889678381415303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14492740894593118920943535 21739111341889678381415303)
              ·
                refine ⟨32608667012834517572122955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21739111341889678381415303 32608667012834517572122955)
                ·
                  refine ⟨48913000519251776358184433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32608667012834517572122955 48913000519251776358184433)
                  ·
                    refine ⟨36684750389438832268638325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48913000519251776358184433 36684750389438832268638325)
                    ·
                      refine ⟨3439195349009890525184843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36684750389438832268638325 3439195349009890525184843)
                      ·
                        rfl

theorem cell23_6697809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_6697809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697809 prefixEnd_6697809 := by exact prefixLift 6697809
  have htrace : WordTrace (prefixWord ++ tailWord_6697809) baseStart_6697809 baseEnd_6697809 := by
    simpa [prefixWord, tailWord_6697809, baseEnd_6697809] using wordTrace_append hprefix tailTrace_6697809
  have hstable : (prefixWord ++ tailWord_6697809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697809).length < 2 ^ (prefixWord ++ tailWord_6697809).sum := by decide
  have hdescent : baseEnd_6697809 < baseStart_6697809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697829 : List Nat := [1, 3, 1, 3, 1, 1, 2, 4, 3, 4]
def baseStart_6697829 : Nat := 118140960795 + 6697829 * 2 ^ 59
def prefixEnd_6697829 : Nat := 4983230072969 + 3 ^ 40 * 6697829 * 2
def baseEnd_6697829 : Nat := 1146401872874326815644917

theorem tailTrace_6697829 : CollatzResearch.WordTrace tailWord_6697829 prefixEnd_6697829 1146401872874326815644917 := by
  unfold tailWord_6697829
  simp only [CollatzResearch.WordTrace]
  refine ⟨244289892851916905967928541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162859928567944603978619027 244289892851916905967928541)
  ·
    refine ⟨91608709819468839737973203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244289892851916905967928541 91608709819468839737973203)
    ·
      refine ⟨137413064729203259606959805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91608709819468839737973203 137413064729203259606959805)
      ·
        refine ⟨51529899273451222352609927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137413064729203259606959805 51529899273451222352609927)
        ·
          refine ⟨77294848910176833528914891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51529899273451222352609927 77294848910176833528914891)
          ·
            refine ⟨115942273365265250293372337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77294848910176833528914891 115942273365265250293372337)
            ·
              refine ⟨86956705023948937720029253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115942273365265250293372337 86956705023948937720029253)
              ·
                refine ⟨16304382191990425822505485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86956705023948937720029253 16304382191990425822505485)
                ·
                  refine ⟨6114143321996409683439557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16304382191990425822505485 6114143321996409683439557)
                  ·
                    refine ⟨1146401872874326815644917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6114143321996409683439557 1146401872874326815644917)
                    ·
                      rfl

theorem cell23_6697829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_6697829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697829 prefixEnd_6697829 := by exact prefixLift 6697829
  have htrace : WordTrace (prefixWord ++ tailWord_6697829) baseStart_6697829 baseEnd_6697829 := by
    simpa [prefixWord, tailWord_6697829, baseEnd_6697829] using wordTrace_append hprefix tailTrace_6697829
  have hstable : (prefixWord ++ tailWord_6697829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697829).length < 2 ^ (prefixWord ++ tailWord_6697829).sum := by decide
  have hdescent : baseEnd_6697829 < baseStart_6697829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697842 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 10]
def baseStart_6697842 : Nat := 118140960795 + 6697842 * 2 ^ 59
def prefixEnd_6697842 : Nat := 4983230072969 + 3 ^ 40 * 6697842 * 2
def baseEnd_6697842 : Nat := 382134699319054321785799

theorem tailTrace_6697842 : CollatzResearch.WordTrace tailWord_6697842 prefixEnd_6697842 382134699319054321785799 := by
  unfold tailWord_6697842
  simp only [CollatzResearch.WordTrace]
  refine ⟨61072591750217452297037945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162860244667246539458767853 61072591750217452297037945)
  ·
    refine ⟨45804443812663089222778459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61072591750217452297037945 45804443812663089222778459)
    ·
      refine ⟨68706665718994633834167689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45804443812663089222778459 68706665718994633834167689)
      ·
        refine ⟨51529999289245975375625767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68706665718994633834167689 51529999289245975375625767)
        ·
          refine ⟨77294998933868963063438651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51529999289245975375625767 77294998933868963063438651)
          ·
            refine ⟨115942498400803444595157977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77294998933868963063438651 115942498400803444595157977)
            ·
              refine ⟨86956873800602583446368483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115942498400803444595157977 86956873800602583446368483)
              ·
                refine ⟨130435310700903875169552725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86956873800602583446368483 130435310700903875169552725)
                ·
                  refine ⟨382134699319054321785799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 130435310700903875169552725 382134699319054321785799)
                  ·
                    rfl

theorem cell23_6697842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_6697842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697842 prefixEnd_6697842 := by exact prefixLift 6697842
  have htrace : WordTrace (prefixWord ++ tailWord_6697842) baseStart_6697842 baseEnd_6697842 := by
    simpa [prefixWord, tailWord_6697842, baseEnd_6697842] using wordTrace_append hprefix tailTrace_6697842
  have hstable : (prefixWord ++ tailWord_6697842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697842).length < 2 ^ (prefixWord ++ tailWord_6697842).sum := by decide
  have hdescent : baseEnd_6697842 < baseStart_6697842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697859 : List Nat := [1, 1, 1, 3, 4, 1, 4, 2, 6]
def baseStart_6697859 : Nat := 118140960795 + 6697859 * 2 ^ 59
def prefixEnd_6697859 : Nat := 4983230072969 + 3 ^ 40 * 6697859 * 2
def baseEnd_6697859 : Nat := 382135669226957258839957

theorem tailTrace_6697859 : CollatzResearch.WordTrace tailWord_6697859 prefixEnd_6697859 382135669226957258839957 := by
  unfold tailWord_6697859
  simp only [CollatzResearch.WordTrace]
  refine ⟨244290987041808221091520631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162860658027872147394347087 244290987041808221091520631)
  ·
    refine ⟨366436480562712331637280947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244290987041808221091520631 366436480562712331637280947)
    ·
      refine ⟨549654720844068497455921421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366436480562712331637280947 549654720844068497455921421)
      ·
        refine ⟨206120520316525686545970533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 549654720844068497455921421 206120520316525686545970533)
        ·
          refine ⟨38647597559348566227369475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206120520316525686545970533 38647597559348566227369475)
          ·
            refine ⟨57971396339022849341054213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38647597559348566227369475 57971396339022849341054213)
            ·
              refine ⟨10869636813566784251447665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57971396339022849341054213 10869636813566784251447665)
              ·
                refine ⟨8152227610175088188585749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10869636813566784251447665 8152227610175088188585749)
                ·
                  refine ⟨382135669226957258839957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8152227610175088188585749 382135669226957258839957)
                  ·
                    rfl

theorem cell23_6697859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 6].length) (baseStart_6697859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697859 prefixEnd_6697859 := by exact prefixLift 6697859
  have htrace : WordTrace (prefixWord ++ tailWord_6697859) baseStart_6697859 baseEnd_6697859 := by
    simpa [prefixWord, tailWord_6697859, baseEnd_6697859] using wordTrace_append hprefix tailTrace_6697859
  have hstable : (prefixWord ++ tailWord_6697859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697859).length < 2 ^ (prefixWord ++ tailWord_6697859).sum := by decide
  have hdescent : baseEnd_6697859 < baseStart_6697859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697863 : List Nat := [1, 1, 4, 2, 3, 2, 1, 4, 1, 4]
def baseStart_6697863 : Nat := 118140960795 + 6697863 * 2 ^ 59
def prefixEnd_6697863 : Nat := 4983230072969 + 3 ^ 40 * 6697863 * 2
def baseEnd_6697863 : Nat := 1146407692321744437969865

theorem tailTrace_6697863 : CollatzResearch.WordTrace tailWord_6697863 prefixEnd_6697863 1146407692321744437969865 := by
  unfold tailWord_6697863
  simp only [CollatzResearch.WordTrace]
  refine ⟨244291132933793729774666243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162860755289195819849777495 244291132933793729774666243)
  ·
    refine ⟨366436699400690594661999365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244291132933793729774666243 366436699400690594661999365)
    ·
      refine ⟨68706881137629486499124881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 366436699400690594661999365 68706881137629486499124881)
      ·
        refine ⟨51530160853222114874343661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68706881137629486499124881 51530160853222114874343661)
        ·
          refine ⟨19323810319958293077878873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51530160853222114874343661 19323810319958293077878873)
          ·
            refine ⟨14492857739968719808409155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19323810319958293077878873 14492857739968719808409155)
            ·
              refine ⟨21739286609953079712613733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14492857739968719808409155 21739286609953079712613733)
              ·
                refine ⟨4076116239366202446115075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21739286609953079712613733 4076116239366202446115075)
                ·
                  refine ⟨6114174359049303669172613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4076116239366202446115075 6114174359049303669172613)
                  ·
                    refine ⟨1146407692321744437969865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6114174359049303669172613 1146407692321744437969865)
                    ·
                      rfl

theorem cell23_6697863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_6697863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697863 prefixEnd_6697863 := by exact prefixLift 6697863
  have htrace : WordTrace (prefixWord ++ tailWord_6697863) baseStart_6697863 baseEnd_6697863 := by
    simpa [prefixWord, tailWord_6697863, baseEnd_6697863] using wordTrace_append hprefix tailTrace_6697863
  have hstable : (prefixWord ++ tailWord_6697863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697863).length < 2 ^ (prefixWord ++ tailWord_6697863).sum := by decide
  have hdescent : baseEnd_6697863 < baseStart_6697863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697910 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 8]
def baseStart_6697910 : Nat := 118140960795 + 6697910 * 2 ^ 59
def prefixEnd_6697910 : Nat := 4983230072969 + 3 ^ 40 * 6697910 * 2
def baseEnd_6697910 : Nat := 382138578950666070002431

theorem tailTrace_6697910 : CollatzResearch.WordTrace tailWord_6697910 prefixEnd_6697910 382138578950666070002431 := by
  unfold tailWord_6697910
  simp only [CollatzResearch.WordTrace]
  refine ⟨15268302947788966050101699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162861898109748971201084789 15268302947788966050101699)
  ·
    refine ⟨22902454421683449075152549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15268302947788966050101699 22902454421683449075152549)
    ·
      refine ⟨4294210204065646701591103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22902454421683449075152549 4294210204065646701591103)
      ·
        refine ⟨6441315306098470052386655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4294210204065646701591103 6441315306098470052386655)
        ·
          refine ⟨9661972959147705078579983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6441315306098470052386655 9661972959147705078579983)
          ·
            refine ⟨14492959438721557617869975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9661972959147705078579983 14492959438721557617869975)
            ·
              refine ⟨21739439158082336426804963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14492959438721557617869975 21739439158082336426804963)
              ·
                refine ⟨32609158737123504640207445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21739439158082336426804963 32609158737123504640207445)
                ·
                  refine ⟨382138578950666070002431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32609158737123504640207445 382138578950666070002431)
                  ·
                    rfl

theorem cell23_6697910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_6697910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697910 prefixEnd_6697910 := by exact prefixLift 6697910
  have htrace : WordTrace (prefixWord ++ tailWord_6697910) baseStart_6697910 baseEnd_6697910 := by
    simpa [prefixWord, tailWord_6697910, baseEnd_6697910] using wordTrace_append hprefix tailTrace_6697910
  have hstable : (prefixWord ++ tailWord_6697910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697910).length < 2 ^ (prefixWord ++ tailWord_6697910).sum := by decide
  have hdescent : baseEnd_6697910 < baseStart_6697910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697954 : List Nat := [3, 3, 3, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_6697954 : Nat := 118140960795 + 6697954 * 2 ^ 59
def prefixEnd_6697954 : Nat := 4983230072969 + 3 ^ 40 * 6697954 * 2
def baseEnd_6697954 : Nat := 3439269803704792457871677

theorem tailTrace_6697954 : CollatzResearch.WordTrace tailWord_6697954 prefixEnd_6697954 3439269803704792457871677 := by
  unfold tailWord_6697954
  simp only [CollatzResearch.WordTrace]
  refine ⟨61073612994116013079057229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162862967984309368210819277 61073612994116013079057229)
  ·
    refine ⟨22902604872793504904646461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61073612994116013079057229 22902604872793504904646461)
    ·
      refine ⟨8588476827297564339242423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22902604872793504904646461 8588476827297564339242423)
      ·
        refine ⟨12882715240946346508863635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8588476827297564339242423 12882715240946346508863635)
        ·
          refine ⟨19324072861419519763295453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12882715240946346508863635 19324072861419519763295453)
          ·
            refine ⟨7246527323032319911235795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19324072861419519763295453 7246527323032319911235795)
            ·
              refine ⟨10869790984548479866853693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7246527323032319911235795 10869790984548479866853693)
              ·
                refine ⟨4076171619205679950070135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10869790984548479866853693 4076171619205679950070135)
                ·
                  refine ⟨6114257428808519925105203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4076171619205679950070135 6114257428808519925105203)
                  ·
                    refine ⟨9171386143212779887657805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6114257428808519925105203 9171386143212779887657805)
                    ·
                      refine ⟨3439269803704792457871677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9171386143212779887657805 3439269803704792457871677)
                      ·
                        rfl

theorem cell23_6697954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_6697954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697954 prefixEnd_6697954 := by exact prefixLift 6697954
  have htrace : WordTrace (prefixWord ++ tailWord_6697954) baseStart_6697954 baseEnd_6697954 := by
    simpa [prefixWord, tailWord_6697954, baseEnd_6697954] using wordTrace_append hprefix tailTrace_6697954
  have hstable : (prefixWord ++ tailWord_6697954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697954).length < 2 ^ (prefixWord ++ tailWord_6697954).sum := by decide
  have hdescent : baseEnd_6697954 < baseStart_6697954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697966 : List Nat := [4, 1, 2, 1, 4, 2, 9]
def baseStart_6697966 : Nat := 118140960795 + 6697966 * 2 ^ 59
def prefixEnd_6697966 : Nat := 4983230072969 + 3 ^ 40 * 6697966 * 2
def baseEnd_6697966 : Nat := 42460197104600572974341

theorem tailTrace_6697966 : CollatzResearch.WordTrace tailWord_6697966 prefixEnd_6697966 42460197104600572974341 := by
  unfold tailWord_6697966
  simp only [CollatzResearch.WordTrace]
  refine ⟨30536861206552572295708219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162863259768280385577110501 30536861206552572295708219)
  ·
    refine ⟨45805291809828858443562329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30536861206552572295708219 45805291809828858443562329)
    ·
      refine ⟨34353968857371643832671747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45805291809828858443562329 34353968857371643832671747)
      ·
        refine ⟨51530953286057465749007621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34353968857371643832671747 51530953286057465749007621)
        ·
          refine ⟨9662053741135774827938929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51530953286057465749007621 9662053741135774827938929)
          ·
            refine ⟨7246540305851831120954197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9662053741135774827938929 7246540305851831120954197)
            ·
              refine ⟨42460197104600572974341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7246540305851831120954197 42460197104600572974341)
              ·
                rfl

theorem cell23_6697966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 9].length) (baseStart_6697966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697966 prefixEnd_6697966 := by exact prefixLift 6697966
  have htrace : WordTrace (prefixWord ++ tailWord_6697966) baseStart_6697966 baseEnd_6697966 := by
    simpa [prefixWord, tailWord_6697966, baseEnd_6697966] using wordTrace_append hprefix tailTrace_6697966
  have hstable : (prefixWord ++ tailWord_6697966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697966).length < 2 ^ (prefixWord ++ tailWord_6697966).sum := by decide
  have hdescent : baseEnd_6697966 < baseStart_6697966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6697977 : List Nat := [1, 2, 1, 3, 1, 3, 5, 2, 1, 2, 2]
def baseStart_6697977 : Nat := 118140960795 + 6697977 * 2 ^ 59
def prefixEnd_6697977 : Nat := 4983230072969 + 3 ^ 40 * 6697977 * 2
def baseEnd_6697977 : Nat := 3439281613759845867884071

theorem tailTrace_6697977 : CollatzResearch.WordTrace tailWord_6697977 prefixEnd_6697977 3439281613759845867884071 := by
  unfold tailWord_6697977
  simp only [CollatzResearch.WordTrace]
  refine ⟨244295290855380727244316185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162863527236920484829544123 244295290855380727244316185)
  ·
    refine ⟨183221468141535545433237139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244295290855380727244316185 183221468141535545433237139)
    ·
      refine ⟨274832202212303318149855709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183221468141535545433237139 274832202212303318149855709)
      ·
        refine ⟨103062075829613744306195891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274832202212303318149855709 103062075829613744306195891)
        ·
          refine ⟨154593113744420616459293837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103062075829613744306195891 154593113744420616459293837)
          ·
            refine ⟨57972417654157731172235189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154593113744420616459293837 57972417654157731172235189)
            ·
              refine ⟨5434914155077287297397049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57972417654157731172235189 5434914155077287297397049)
              ·
                refine ⟨4076185616307965473047787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5434914155077287297397049 4076185616307965473047787)
                ·
                  refine ⟨6114278424461948209571681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4076185616307965473047787 6114278424461948209571681)
                  ·
                    refine ⟨4585708818346461157178761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6114278424461948209571681 4585708818346461157178761)
                    ·
                      refine ⟨3439281613759845867884071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4585708818346461157178761 3439281613759845867884071)
                      ·
                        rfl

theorem cell23_6697977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 1, 2, 2].length) (baseStart_6697977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6697977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6697977 prefixEnd_6697977 := by exact prefixLift 6697977
  have htrace : WordTrace (prefixWord ++ tailWord_6697977) baseStart_6697977 baseEnd_6697977 := by
    simpa [prefixWord, tailWord_6697977, baseEnd_6697977] using wordTrace_append hprefix tailTrace_6697977
  have hstable : (prefixWord ++ tailWord_6697977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6697977).length < 2 ^ (prefixWord ++ tailWord_6697977).sum := by decide
  have hdescent : baseEnd_6697977 < baseStart_6697977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6697977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698039 : List Nat := [1, 1, 3, 1, 2, 2, 1, 5, 7]
def baseStart_6698039 : Nat := 118140960795 + 6698039 * 2 ^ 59
def prefixEnd_6698039 : Nat := 4983230072969 + 3 ^ 40 * 6698039 * 2
def baseEnd_6698039 : Nat := 382145938840047180589865

theorem tailTrace_6698039 : CollatzResearch.WordTrace tailWord_6698039 prefixEnd_6698039 382145938840047180589865 := by
  unfold tailWord_6698039
  simp only [CollatzResearch.WordTrace]
  refine ⟨244297552181156111833073171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162865034787437407888715447 244297552181156111833073171)
  ·
    refine ⟨366446328271734167749609757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244297552181156111833073171 366446328271734167749609757)
    ·
      refine ⟨137417373101900312906103659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366446328271734167749609757 137417373101900312906103659)
      ·
        refine ⟨206126059652850469359155489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137417373101900312906103659 206126059652850469359155489)
        ·
          refine ⟨154594544739637852019366617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206126059652850469359155489 154594544739637852019366617)
          ·
            refine ⟨115945908554728389014524963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154594544739637852019366617 115945908554728389014524963)
            ·
              refine ⟨173918862832092583521787445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115945908554728389014524963 173918862832092583521787445)
              ·
                refine ⟨16304893390508679705167573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173918862832092583521787445 16304893390508679705167573)
                ·
                  refine ⟨382145938840047180589865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16304893390508679705167573 382145938840047180589865)
                  ·
                    rfl

theorem cell23_6698039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 7].length) (baseStart_6698039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698039 prefixEnd_6698039 := by exact prefixLift 6698039
  have htrace : WordTrace (prefixWord ++ tailWord_6698039) baseStart_6698039 baseEnd_6698039 := by
    simpa [prefixWord, tailWord_6698039, baseEnd_6698039] using wordTrace_append hprefix tailTrace_6698039
  have hstable : (prefixWord ++ tailWord_6698039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698039).length < 2 ^ (prefixWord ++ tailWord_6698039).sum := by decide
  have hdescent : baseEnd_6698039 < baseStart_6698039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698101 : List Nat := [1, 3, 4, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_6698101 : Nat := 118140960795 + 6698101 * 2 ^ 59
def prefixEnd_6698101 : Nat := 4983230072969 + 3 ^ 40 * 6698101 * 2
def baseEnd_6698101 : Nat := 3439345285361003382733501

theorem tailTrace_6698101 : CollatzResearch.WordTrace tailWord_6698101 prefixEnd_6698101 3439345285361003382733501 := by
  unfold tailWord_6698101
  simp only [CollatzResearch.WordTrace]
  refine ⟨244299813506931496421830157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162866542337954330947886771 244299813506931496421830157)
  ·
    refine ⟨91612430065099311158186309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244299813506931496421830157 91612430065099311158186309)
    ·
      refine ⟨17177330637206120842159933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91612430065099311158186309 17177330637206120842159933)
      ·
        refine ⟨6441498988952295315809975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17177330637206120842159933 6441498988952295315809975)
        ·
          refine ⟨9662248483428442973714963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6441498988952295315809975 9662248483428442973714963)
          ·
            refine ⟨14493372725142664460572445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9662248483428442973714963 14493372725142664460572445)
            ·
              refine ⟨5435014771928499172714667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14493372725142664460572445 5435014771928499172714667)
              ·
                refine ⟨8152522157892748759072001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5435014771928499172714667 8152522157892748759072001)
                ·
                  refine ⟨6114391618419561569304001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8152522157892748759072001 6114391618419561569304001)
                  ·
                    refine ⟨4585793713814671176978001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6114391618419561569304001 4585793713814671176978001)
                    ·
                      refine ⟨3439345285361003382733501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4585793713814671176978001 3439345285361003382733501)
                      ·
                        rfl

theorem cell23_6698101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_6698101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698101 prefixEnd_6698101 := by exact prefixLift 6698101
  have htrace : WordTrace (prefixWord ++ tailWord_6698101) baseStart_6698101 baseEnd_6698101 := by
    simpa [prefixWord, tailWord_6698101, baseEnd_6698101] using wordTrace_append hprefix tailTrace_6698101
  have hstable : (prefixWord ++ tailWord_6698101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698101).length < 2 ^ (prefixWord ++ tailWord_6698101).sum := by decide
  have hdescent : baseEnd_6698101 < baseStart_6698101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698156 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 3]
def baseStart_6698156 : Nat := 118140960795 + 6698156 * 2 ^ 59
def prefixEnd_6698156 : Nat := 4983230072969 + 3 ^ 40 * 6698156 * 2
def baseEnd_6698156 : Nat := 3439373526797000667545747

theorem tailTrace_6698156 : CollatzResearch.WordTrace tailWord_6698156 prefixEnd_6698156 3439373526797000667545747 := by
  unfold tailWord_6698156
  simp only [CollatzResearch.WordTrace]
  refine ⟨122150909760866120407541161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162867879681154827210054881 122150909760866120407541161)
  ·
    refine ⟨91613182320649590305655871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122150909760866120407541161 91613182320649590305655871)
    ·
      refine ⟨137419773480974385458483807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91613182320649590305655871 137419773480974385458483807)
      ·
        refine ⟨206129660221461578187725711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137419773480974385458483807 206129660221461578187725711)
        ·
          refine ⟨309194490332192367281588567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206129660221461578187725711 309194490332192367281588567)
          ·
            refine ⟨463791735498288550922382851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309194490332192367281588567 463791735498288550922382851)
            ·
              refine ⟨695687603247432826383574277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463791735498288550922382851 695687603247432826383574277)
              ·
                refine ⟨130441425608893654946920177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 695687603247432826383574277 130441425608893654946920177)
                ·
                  refine ⟨97831069206670241210190133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130441425608893654946920177 97831069206670241210190133)
                  ·
                    refine ⟨9171662738125335113455325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97831069206670241210190133 9171662738125335113455325)
                    ·
                      refine ⟨3439373526797000667545747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9171662738125335113455325 3439373526797000667545747)
                      ·
                        rfl

theorem cell23_6698156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_6698156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698156 prefixEnd_6698156 := by exact prefixLift 6698156
  have htrace : WordTrace (prefixWord ++ tailWord_6698156) baseStart_6698156 baseEnd_6698156 := by
    simpa [prefixWord, tailWord_6698156, baseEnd_6698156] using wordTrace_append hprefix tailTrace_6698156
  have hstable : (prefixWord ++ tailWord_6698156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698156).length < 2 ^ (prefixWord ++ tailWord_6698156).sum := by decide
  have hdescent : baseEnd_6698156 < baseStart_6698156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698163 : List Nat := [1, 1, 1, 2, 3, 2, 6, 1, 6]
def baseStart_6698163 : Nat := 118140960795 + 6698163 * 2 ^ 59
def prefixEnd_6698163 : Nat := 4983230072969 + 3 ^ 40 * 6698163 * 2
def baseEnd_6698163 : Nat := 382153013462398015573135

theorem tailTrace_6698163 : CollatzResearch.WordTrace tailWord_6698163 prefixEnd_6698163 382153013462398015573135 := by
  unfold tailWord_6698163
  simp only [CollatzResearch.WordTrace]
  refine ⟨244302074832706881010587143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162868049888471254007058095 244302074832706881010587143)
  ·
    refine ⟨366453112249060321515880715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244302074832706881010587143 366453112249060321515880715)
    ·
      refine ⟨549679668373590482273821073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366453112249060321515880715 549679668373590482273821073)
      ·
        refine ⟨412259751280192861705365805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 549679668373590482273821073 412259751280192861705365805)
        ·
          refine ⟨154597406730072323139512177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 412259751280192861705365805 154597406730072323139512177)
          ·
            refine ⟨115948055047554242354634133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154597406730072323139512177 115948055047554242354634133)
            ·
              refine ⟨5435065080354105110373475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115948055047554242354634133 5435065080354105110373475)
              ·
                refine ⟨8152597620531157665560213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5435065080354105110373475 8152597620531157665560213)
                ·
                  refine ⟨382153013462398015573135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8152597620531157665560213 382153013462398015573135)
                  ·
                    rfl

theorem cell23_6698163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 6].length) (baseStart_6698163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698163 prefixEnd_6698163 := by exact prefixLift 6698163
  have htrace : WordTrace (prefixWord ++ tailWord_6698163) baseStart_6698163 baseEnd_6698163 := by
    simpa [prefixWord, tailWord_6698163, baseEnd_6698163] using wordTrace_append hprefix tailTrace_6698163
  have hstable : (prefixWord ++ tailWord_6698163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698163).length < 2 ^ (prefixWord ++ tailWord_6698163).sum := by decide
  have hdescent : baseEnd_6698163 < baseStart_6698163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698177 : List Nat := [1, 2, 6, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_6698177 : Nat := 118140960795 + 6698177 * 2 ^ 59
def prefixEnd_6698177 : Nat := 4983230072969 + 3 ^ 40 * 6698177 * 2
def baseEnd_6698177 : Nat := 3439384309890745085383151

theorem tailTrace_6698177 : CollatzResearch.WordTrace tailWord_6698177 prefixEnd_6698177 3439384309890745085383151 := by
  unfold tailWord_6698177
  simp only [CollatzResearch.WordTrace]
  refine ⟨244302585454656161401596785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162868390303104107601064523 244302585454656161401596785)
  ·
    refine ⟨183226939090992121051197589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244302585454656161401596785 183226939090992121051197589)
    ·
      refine ⟨8588762769890255674274887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 183226939090992121051197589 8588762769890255674274887)
      ·
        refine ⟨12883144154835383511412331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8588762769890255674274887 12883144154835383511412331)
        ·
          refine ⟨19324716232253075267118497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12883144154835383511412331 19324716232253075267118497)
          ·
            refine ⟨14493537174189806450338873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19324716232253075267118497 14493537174189806450338873)
            ·
              refine ⟨10870152880642354837754155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14493537174189806450338873 10870152880642354837754155)
              ·
                refine ⟨16305229320963532256631233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10870152880642354837754155 16305229320963532256631233)
                ·
                  refine ⟨12228921990722649192473425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16305229320963532256631233 12228921990722649192473425)
                  ·
                    refine ⟨9171691493041986894355069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12228921990722649192473425 9171691493041986894355069)
                    ·
                      refine ⟨3439384309890745085383151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9171691493041986894355069 3439384309890745085383151)
                      ·
                        rfl

theorem cell23_6698177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_6698177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698177 prefixEnd_6698177 := by exact prefixLift 6698177
  have htrace : WordTrace (prefixWord ++ tailWord_6698177) baseStart_6698177 baseEnd_6698177 := by
    simpa [prefixWord, tailWord_6698177, baseEnd_6698177] using wordTrace_append hprefix tailTrace_6698177
  have hstable : (prefixWord ++ tailWord_6698177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698177).length < 2 ^ (prefixWord ++ tailWord_6698177).sum := by decide
  have hdescent : baseEnd_6698177 < baseStart_6698177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698183 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 1, 5, 2]
def baseStart_6698183 : Nat := 118140960795 + 6698183 * 2 ^ 59
def prefixEnd_6698183 : Nat := 4983230072969 + 3 ^ 40 * 6698183 * 2
def baseEnd_6698183 : Nat := 3439387390774672061908123

theorem tailTrace_6698183 : CollatzResearch.WordTrace tailWord_6698183 prefixEnd_6698183 3439387390774672061908123 := by
  unfold tailWord_6698183
  simp only [CollatzResearch.WordTrace]
  refine ⟨244302804292634424426315203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162868536195089616284210135 244302804292634424426315203)
  ·
    refine ⟨366454206438951636639472805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244302804292634424426315203 366454206438951636639472805)
    ·
      refine ⟨68710163707303431869901151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 366454206438951636639472805 68710163707303431869901151)
      ·
        refine ⟨103065245560955147804851727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68710163707303431869901151 103065245560955147804851727)
        ·
          refine ⟨154597868341432721707277591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103065245560955147804851727 154597868341432721707277591)
          ·
            refine ⟨231896802512149082560916387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154597868341432721707277591 231896802512149082560916387)
            ·
              refine ⟨347845203768223623841374581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231896802512149082560916387 347845203768223623841374581)
              ·
                refine ⟨32610487853270964735128867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 347845203768223623841374581 32610487853270964735128867)
                ·
                  refine ⟨48915731779906447102693301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32610487853270964735128867 48915731779906447102693301)
                  ·
                    refine ⟨4585849854366229415877497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48915731779906447102693301 4585849854366229415877497)
                    ·
                      refine ⟨3439387390774672061908123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4585849854366229415877497 3439387390774672061908123)
                      ·
                        rfl

theorem cell23_6698183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_6698183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698183 prefixEnd_6698183 := by exact prefixLift 6698183
  have htrace : WordTrace (prefixWord ++ tailWord_6698183) baseStart_6698183 baseEnd_6698183 := by
    simpa [prefixWord, tailWord_6698183, baseEnd_6698183] using wordTrace_append hprefix tailTrace_6698183
  have hstable : (prefixWord ++ tailWord_6698183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698183).length < 2 ^ (prefixWord ++ tailWord_6698183).sum := by decide
  have hdescent : baseEnd_6698183 < baseStart_6698183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698228 : List Nat := [2, 6, 1, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_6698228 : Nat := 118140960795 + 6698228 * 2 ^ 59
def prefixEnd_6698228 : Nat := 4983230072969 + 3 ^ 40 * 6698228 * 2
def baseEnd_6698228 : Nat := 3439410497404124385845417

theorem tailTrace_6698228 : CollatzResearch.WordTrace tailWord_6698228 prefixEnd_6698228 3439410497404124385845417 := by
  unfold tailWord_6698228
  simp only [CollatzResearch.WordTrace]
  refine ⟨122152222788735698555851669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162869630384980931407802225 122152222788735698555851669)
  ·
    refine ⟨5725885443221985869805547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122152222788735698555851669 5725885443221985869805547)
    ·
      refine ⟨8588828164832978804708321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5725885443221985869805547 8588828164832978804708321)
      ·
        refine ⟨6441621123624734103531241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8588828164832978804708321 6441621123624734103531241)
        ·
          refine ⟨4831215842718550577648431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6441621123624734103531241 4831215842718550577648431)
          ·
            refine ⟨7246823764077825866472647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4831215842718550577648431 7246823764077825866472647)
            ·
              refine ⟨10870235646116738799708971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7246823764077825866472647 10870235646116738799708971)
              ·
                refine ⟨16305353469175108199563457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10870235646116738799708971 16305353469175108199563457)
                ·
                  refine ⟨12229015101881331149672593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16305353469175108199563457 12229015101881331149672593)
                  ·
                    refine ⟨9171761326410998362254445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12229015101881331149672593 9171761326410998362254445)
                    ·
                      refine ⟨3439410497404124385845417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9171761326410998362254445 3439410497404124385845417)
                      ·
                        rfl

theorem cell23_6698228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_6698228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698228 prefixEnd_6698228 := by exact prefixLift 6698228
  have htrace : WordTrace (prefixWord ++ tailWord_6698228) baseStart_6698228 baseEnd_6698228 := by
    simpa [prefixWord, tailWord_6698228, baseEnd_6698228] using wordTrace_append hprefix tailTrace_6698228
  have hstable : (prefixWord ++ tailWord_6698228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698228).length < 2 ^ (prefixWord ++ tailWord_6698228).sum := by decide
  have hdescent : baseEnd_6698228 < baseStart_6698228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698230 : List Nat := [5, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_6698230 : Nat := 118140960795 + 6698230 * 2 ^ 59
def prefixEnd_6698230 : Nat := 4983230072969 + 3 ^ 40 * 6698230 * 2
def baseEnd_6698230 : Nat := 3439411524365433378020407

theorem tailTrace_6698230 : CollatzResearch.WordTrace tailWord_6698230 prefixEnd_6698230 3439411524365433378020407 := by
  unfold tailWord_6698230
  simp only [CollatzResearch.WordTrace]
  refine ⟨15269032407716509465829759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162869679015642767635517429 15269032407716509465829759)
  ·
    refine ⟨22903548611574764198744639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15269032407716509465829759 22903548611574764198744639)
    ·
      refine ⟨34355322917362146298116959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22903548611574764198744639 34355322917362146298116959)
      ·
        refine ⟨51532984376043219447175439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34355322917362146298116959 51532984376043219447175439)
        ·
          refine ⟨77299476564064829170763159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51532984376043219447175439 77299476564064829170763159)
          ·
            refine ⟨115949214846097243756144739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77299476564064829170763159 115949214846097243756144739)
            ·
              refine ⟨173923822269145865634217109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115949214846097243756144739 173923822269145865634217109)
              ·
                refine ⟨8152679168866212451603927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173923822269145865634217109 8152679168866212451603927)
                ·
                  refine ⟨12229018753299318677405891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8152679168866212451603927 12229018753299318677405891)
                  ·
                    refine ⟨18343528129948978016108837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12229018753299318677405891 18343528129948978016108837)
                    ·
                      refine ⟨3439411524365433378020407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18343528129948978016108837 3439411524365433378020407)
                      ·
                        rfl

theorem cell23_6698230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_6698230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698230 prefixEnd_6698230 := by exact prefixLift 6698230
  have htrace : WordTrace (prefixWord ++ tailWord_6698230) baseStart_6698230 baseEnd_6698230 := by
    simpa [prefixWord, tailWord_6698230, baseEnd_6698230] using wordTrace_append hprefix tailTrace_6698230
  have hstable : (prefixWord ++ tailWord_6698230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698230).length < 2 ^ (prefixWord ++ tailWord_6698230).sum := by decide
  have hdescent : baseEnd_6698230 < baseStart_6698230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698233 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 3, 2, 3]
def baseStart_6698233 : Nat := 118140960795 + 6698233 * 2 ^ 59
def prefixEnd_6698233 : Nat := 4983230072969 + 3 ^ 40 * 6698233 * 2
def baseEnd_6698233 : Nat := 3439413064807396866282893

theorem tailTrace_6698233 : CollatzResearch.WordTrace tailWord_6698233 prefixEnd_6698233 3439413064807396866282893 := by
  unfold tailWord_6698233
  simp only [CollatzResearch.WordTrace]
  refine ⟨244304627942453282965635353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162869751961635521977090235 244304627942453282965635353)
  ·
    refine ⟨183228470956839962224226515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244304627942453282965635353 183228470956839962224226515)
    ·
      refine ⟨274842706435259943336339773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183228470956839962224226515 274842706435259943336339773)
      ·
        refine ⟨103066014913222478751127415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274842706435259943336339773 103066014913222478751127415)
        ·
          refine ⟨154599022369833718126691123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103066014913222478751127415 154599022369833718126691123)
          ·
            refine ⟨231898533554750577190036685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154599022369833718126691123 231898533554750577190036685)
            ·
              refine ⟨86961950083031466446263757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231898533554750577190036685 86961950083031466446263757)
              ·
                refine ⟨32610731281136799917348909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86961950083031466446263757 32610731281136799917348909)
                ·
                  refine ⟨12229024230426299969005841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32610731281136799917348909 12229024230426299969005841)
                  ·
                    refine ⟨9171768172819724976754381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12229024230426299969005841 9171768172819724976754381)
                    ·
                      refine ⟨3439413064807396866282893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9171768172819724976754381 3439413064807396866282893)
                      ·
                        rfl

theorem cell23_6698233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_6698233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698233 prefixEnd_6698233 := by exact prefixLift 6698233
  have htrace : WordTrace (prefixWord ++ tailWord_6698233) baseStart_6698233 baseEnd_6698233 := by
    simpa [prefixWord, tailWord_6698233, baseEnd_6698233] using wordTrace_append hprefix tailTrace_6698233
  have hstable : (prefixWord ++ tailWord_6698233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698233).length < 2 ^ (prefixWord ++ tailWord_6698233).sum := by decide
  have hdescent : baseEnd_6698233 < baseStart_6698233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698243 : List Nat := [1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 4]
def baseStart_6698243 : Nat := 118140960795 + 6698243 * 2 ^ 59
def prefixEnd_6698243 : Nat := 4983230072969 + 3 ^ 40 * 6698243 * 2
def baseEnd_6698243 : Nat := 3439418199613941827157847

theorem tailTrace_6698243 : CollatzResearch.WordTrace tailWord_6698243 prefixEnd_6698243 3439418199613941827157847 := by
  unfold tailWord_6698243
  simp only [CollatzResearch.WordTrace]
  refine ⟨244304992672417054673499383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162869995114944703115666255 244304992672417054673499383)
  ·
    refine ⟨366457489008625582010249075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244304992672417054673499383 366457489008625582010249075)
    ·
      refine ⟨549686233512938373015373613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366457489008625582010249075 549686233512938373015373613)
      ·
        refine ⟨206132337567351889880765105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 549686233512938373015373613 206132337567351889880765105)
        ·
          refine ⟨154599253175513917410573829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206132337567351889880765105 154599253175513917410573829)
          ·
            refine ⟨28987359970408859514482593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154599253175513917410573829 28987359970408859514482593)
            ·
              refine ⟨21740519977806644635861945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28987359970408859514482593 21740519977806644635861945)
              ·
                refine ⟨16305389983354983476896459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21740519977806644635861945 16305389983354983476896459)
                ·
                  refine ⟨24458084975032475215344689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16305389983354983476896459 24458084975032475215344689)
                  ·
                    refine ⟨18343563731274356411508517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24458084975032475215344689 18343563731274356411508517)
                    ·
                      refine ⟨3439418199613941827157847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18343563731274356411508517 3439418199613941827157847)
                      ·
                        rfl

theorem cell23_6698243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_6698243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698243 prefixEnd_6698243 := by exact prefixLift 6698243
  have htrace : WordTrace (prefixWord ++ tailWord_6698243) baseStart_6698243 baseEnd_6698243 := by
    simpa [prefixWord, tailWord_6698243, baseEnd_6698243] using wordTrace_append hprefix tailTrace_6698243
  have hstable : (prefixWord ++ tailWord_6698243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698243).length < 2 ^ (prefixWord ++ tailWord_6698243).sum := by decide
  have hdescent : baseEnd_6698243 < baseStart_6698243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698264 : List Nat := [2, 1, 2, 3, 1, 3, 2, 4, 1, 2, 2]
def baseStart_6698264 : Nat := 118140960795 + 6698264 * 2 ^ 59
def prefixEnd_6698264 : Nat := 4983230072969 + 3 ^ 40 * 6698264 * 2
def baseEnd_6698264 : Nat := 3439428982707686244995251

theorem tailTrace_6698264 : CollatzResearch.WordTrace tailWord_6698264 prefixEnd_6698264 3439428982707686244995251 := by
  unfold tailWord_6698264
  simp only [CollatzResearch.WordTrace]
  refine ⟨122152879302670487630006923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162870505736893983506675897 122152879302670487630006923)
  ·
    refine ⟨183229318954005731445010385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122152879302670487630006923 183229318954005731445010385)
    ·
      refine ⟨137421989215504298583757789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183229318954005731445010385 137421989215504298583757789)
      ·
        refine ⟨51533245955814111968909171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137421989215504298583757789 51533245955814111968909171)
        ·
          refine ⟨77299868933721167953363757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51533245955814111968909171 77299868933721167953363757)
          ·
            refine ⟨28987450850145437982511409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77299868933721167953363757 28987450850145437982511409)
            ·
              refine ⟨21740588137609078486883557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28987450850145437982511409 21740588137609078486883557)
              ·
                refine ⟨4076360275801702216290667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21740588137609078486883557 4076360275801702216290667)
                ·
                  refine ⟨6114540413702553324436001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4076360275801702216290667 6114540413702553324436001)
                  ·
                    refine ⟨4585905310276914993327001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6114540413702553324436001 4585905310276914993327001)
                    ·
                      refine ⟨3439428982707686244995251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4585905310276914993327001 3439428982707686244995251)
                      ·
                        rfl

theorem cell23_6698264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_6698264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698264 prefixEnd_6698264 := by exact prefixLift 6698264
  have htrace : WordTrace (prefixWord ++ tailWord_6698264) baseStart_6698264 baseEnd_6698264 := by
    simpa [prefixWord, tailWord_6698264, baseEnd_6698264] using wordTrace_append hprefix tailTrace_6698264
  have hstable : (prefixWord ++ tailWord_6698264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698264).length < 2 ^ (prefixWord ++ tailWord_6698264).sum := by decide
  have hdescent : baseEnd_6698264 < baseStart_6698264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698274 : List Nat := [3, 3, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_6698274 : Nat := 118140960795 + 6698274 * 2 ^ 59
def prefixEnd_6698274 : Nat := 4983230072969 + 3 ^ 40 * 6698274 * 2
def baseEnd_6698274 : Nat := 1146478039171410401956735

theorem tailTrace_6698274 : CollatzResearch.WordTrace tailWord_6698274 prefixEnd_6698274 1146478039171410401956735 := by
  unfold tailWord_6698274
  simp only [CollatzResearch.WordTrace]
  refine ⟨61076530833826186741969469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162870748890203164645251917 61076530833826186741969469)
  ·
    refine ⟨22903699062684820028238551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61076530833826186741969469 22903699062684820028238551)
    ·
      refine ⟨34355548594027230042357827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22903699062684820028238551 34355548594027230042357827)
      ·
        refine ⟨51533322891040845063536741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34355548594027230042357827 51533322891040845063536741)
        ·
          refine ⟨9662498042070158449413139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51533322891040845063536741 9662498042070158449413139)
          ·
            refine ⟨14493747063105237674119709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9662498042070158449413139 14493747063105237674119709)
            ·
              refine ⟨5435155148664464127794891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14493747063105237674119709 5435155148664464127794891)
              ·
                refine ⟨8152732722996696191692337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5435155148664464127794891 8152732722996696191692337)
                ·
                  refine ⟨6114549542247522143769253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8152732722996696191692337 6114549542247522143769253)
                  ·
                    refine ⟨1146478039171410401956735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6114549542247522143769253 1146478039171410401956735)
                    ·
                      rfl

theorem cell23_6698274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_6698274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698274 prefixEnd_6698274 := by exact prefixLift 6698274
  have htrace : WordTrace (prefixWord ++ tailWord_6698274) baseStart_6698274 baseEnd_6698274 := by
    simpa [prefixWord, tailWord_6698274, baseEnd_6698274] using wordTrace_append hprefix tailTrace_6698274
  have hstable : (prefixWord ++ tailWord_6698274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698274).length < 2 ^ (prefixWord ++ tailWord_6698274).sum := by decide
  have hdescent : baseEnd_6698274 < baseStart_6698274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698293 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_6698293 : Nat := 118140960795 + 6698293 * 2 ^ 59
def prefixEnd_6698293 : Nat := 4983230072969 + 3 ^ 40 * 6698293 * 2
def baseEnd_6698293 : Nat := 3439443873646666631532617

theorem tailTrace_6698293 : CollatzResearch.WordTrace tailWord_6698293 prefixEnd_6698293 3439443873646666631532617 := by
  unfold tailWord_6698293
  simp only [CollatzResearch.WordTrace]
  refine ⟨244306816322235913212819533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162871210881490608808546355 244306816322235913212819533)
  ·
    refine ⟨91615056120838467454807325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244306816322235913212819533 91615056120838467454807325)
    ·
      refine ⟨34355646045314425295552747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91615056120838467454807325 34355646045314425295552747)
      ·
        refine ⟨51533469067971637943329121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34355646045314425295552747 51533469067971637943329121)
        ·
          refine ⟨38650101800978728457496841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51533469067971637943329121 38650101800978728457496841)
          ·
            refine ⟨28987576350734046343122631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38650101800978728457496841 28987576350734046343122631)
            ·
              refine ⟨43481364526101069514683947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28987576350734046343122631 43481364526101069514683947)
              ·
                refine ⟨65222046789151604272025921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43481364526101069514683947 65222046789151604272025921)
                ·
                  refine ⟨48916535091863703204019441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65222046789151604272025921 48916535091863703204019441)
                  ·
                    refine ⟨36687401318897777403014581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48916535091863703204019441 36687401318897777403014581)
                    ·
                      refine ⟨3439443873646666631532617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36687401318897777403014581 3439443873646666631532617)
                      ·
                        rfl

theorem cell23_6698293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_6698293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698293 prefixEnd_6698293 := by exact prefixLift 6698293
  have htrace : WordTrace (prefixWord ++ tailWord_6698293) baseStart_6698293 baseEnd_6698293 := by
    simpa [prefixWord, tailWord_6698293, baseEnd_6698293] using wordTrace_append hprefix tailTrace_6698293
  have hstable : (prefixWord ++ tailWord_6698293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698293).length < 2 ^ (prefixWord ++ tailWord_6698293).sum := by decide
  have hdescent : baseEnd_6698293 < baseStart_6698293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698323 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 3]
def baseStart_6698323 : Nat := 118140960795 + 6698323 * 2 ^ 59
def prefixEnd_6698323 : Nat := 4983230072969 + 3 ^ 40 * 6698323 * 2
def baseEnd_6698323 : Nat := 3439459278066301514157479

theorem tailTrace_6698323 : CollatzResearch.WordTrace tailWord_6698323 prefixEnd_6698323 3439459278066301514157479 := by
  unfold tailWord_6698323
  simp only [CollatzResearch.WordTrace]
  refine ⟨244307910512127228336411623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162871940341418152224274415 244307910512127228336411623)
  ·
    refine ⟨366461865768190842504617435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244307910512127228336411623 366461865768190842504617435)
    ·
      refine ⟨549692798652286263756926153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366461865768190842504617435 549692798652286263756926153)
      ·
        refine ⟨412269598989214697817694615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 549692798652286263756926153 412269598989214697817694615)
        ·
          refine ⟨618404398483822046726541923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412269598989214697817694615 618404398483822046726541923)
          ·
            refine ⟨927606597725733070089812885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618404398483822046726541923 927606597725733070089812885)
            ·
              refine ⟨43481559268393737660459979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 927606597725733070089812885 43481559268393737660459979)
              ·
                refine ⟨65222338902590606490689969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43481559268393737660459979 65222338902590606490689969)
                ·
                  refine ⟨48916754176942954868017477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65222338902590606490689969 48916754176942954868017477)
                  ·
                    refine ⟨9171891408176804037753277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48916754176942954868017477 9171891408176804037753277)
                    ·
                      refine ⟨3439459278066301514157479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9171891408176804037753277 3439459278066301514157479)
                      ·
                        rfl

theorem cell23_6698323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 3].length) (baseStart_6698323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698323 prefixEnd_6698323 := by exact prefixLift 6698323
  have htrace : WordTrace (prefixWord ++ tailWord_6698323) baseStart_6698323 baseEnd_6698323 := by
    simpa [prefixWord, tailWord_6698323, baseEnd_6698323] using wordTrace_append hprefix tailTrace_6698323
  have hstable : (prefixWord ++ tailWord_6698323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698323).length < 2 ^ (prefixWord ++ tailWord_6698323).sum := by decide
  have hdescent : baseEnd_6698323 < baseStart_6698323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698377 : List Nat := [1, 2, 1, 1, 7, 1, 1, 4, 5]
def baseStart_6698377 : Nat := 118140960795 + 6698377 * 2 ^ 59
def prefixEnd_6698377 : Nat := 4983230072969 + 3 ^ 40 * 6698377 * 2
def baseEnd_6698377 : Nat := 382165222891293811431359

theorem tailTrace_6698377 : CollatzResearch.WordTrace tailWord_6698377 prefixEnd_6698377 382165222891293811431359 := by
  unfold tailWord_6698377
  simp only [CollatzResearch.WordTrace]
  refine ⟨244309880053931595558877385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162873253369287730372584923 244309880053931595558877385)
  ·
    refine ⟨183232410040448696669158039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244309880053931595558877385 183232410040448696669158039)
    ·
      refine ⟨274848615060673045003737059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183232410040448696669158039 274848615060673045003737059)
      ·
        refine ⟨412272922591009567505605589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274848615060673045003737059 412272922591009567505605589)
        ·
          refine ⟨9662646623226786738412631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 412272922591009567505605589 9662646623226786738412631)
          ·
            refine ⟨14493969934840180107618947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9662646623226786738412631 14493969934840180107618947)
            ·
              refine ⟨21740954902260270161428421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14493969934840180107618947 21740954902260270161428421)
              ·
                refine ⟨4076429044173800655267829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21740954902260270161428421 4076429044173800655267829)
                ·
                  refine ⟨382165222891293811431359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4076429044173800655267829 382165222891293811431359)
                  ·
                    rfl

theorem cell23_6698377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 5].length) (baseStart_6698377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698377 prefixEnd_6698377 := by exact prefixLift 6698377
  have htrace : WordTrace (prefixWord ++ tailWord_6698377) baseStart_6698377 baseEnd_6698377 := by
    simpa [prefixWord, tailWord_6698377, baseEnd_6698377] using wordTrace_append hprefix tailTrace_6698377
  have hstable : (prefixWord ++ tailWord_6698377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698377).length < 2 ^ (prefixWord ++ tailWord_6698377).sum := by decide
  have hdescent : baseEnd_6698377 < baseStart_6698377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698380 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 1, 7, 2]
def baseStart_6698380 : Nat := 118140960795 + 6698380 * 2 ^ 59
def prefixEnd_6698380 : Nat := 4983230072969 + 3 ^ 40 * 6698380 * 2
def baseEnd_6698380 : Nat := 3439488546463607791144717

theorem tailTrace_6698380 : CollatzResearch.WordTrace tailWord_6698380 prefixEnd_6698380 3439488546463607791144717 := by
  unfold tailWord_6698380
  simp only [CollatzResearch.WordTrace]
  refine ⟨122154994736460363535618297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162873326315280484714157729 122154994736460363535618297)
  ·
    refine ⟨91616246052345272651713723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122154994736460363535618297 91616246052345272651713723)
    ·
      refine ⟨137424369078517908977570585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91616246052345272651713723 137424369078517908977570585)
      ·
        refine ⟨103068276808888431733177939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137424369078517908977570585 103068276808888431733177939)
        ·
          refine ⟨154602415213332647599766909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103068276808888431733177939 154602415213332647599766909)
          ·
            refine ⟨57975905704999742849912591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154602415213332647599766909 57975905704999742849912591)
            ·
              refine ⟨86963858557499614274868887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57975905704999742849912591 86963858557499614274868887)
              ·
                refine ⟨130445787836249421412303331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86963858557499614274868887 130445787836249421412303331)
                ·
                  refine ⟨195668681754374132118454997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130445787836249421412303331 195668681754374132118454997)
                  ·
                    refine ⟨4585984728618143721526289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 195668681754374132118454997 4585984728618143721526289)
                    ·
                      refine ⟨3439488546463607791144717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4585984728618143721526289 3439488546463607791144717)
                      ·
                        rfl

theorem cell23_6698380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_6698380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698380 prefixEnd_6698380 := by exact prefixLift 6698380
  have htrace : WordTrace (prefixWord ++ tailWord_6698380) baseStart_6698380 baseEnd_6698380 := by
    simpa [prefixWord, tailWord_6698380, baseEnd_6698380] using wordTrace_append hprefix tailTrace_6698380
  have hstable : (prefixWord ++ tailWord_6698380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698380).length < 2 ^ (prefixWord ++ tailWord_6698380).sum := by decide
  have hdescent : baseEnd_6698380 < baseStart_6698380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698423 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 6]
def baseStart_6698423 : Nat := 118140960795 + 6698423 * 2 ^ 59
def prefixEnd_6698423 : Nat := 4983230072969 + 3 ^ 40 * 6698423 * 2
def baseEnd_6698423 : Nat := 3439510626131751122907019

theorem tailTrace_6698423 : CollatzResearch.WordTrace tailWord_6698423 prefixEnd_6698423 3439510626131751122907019 := by
  unfold tailWord_6698423
  simp only [CollatzResearch.WordTrace]
  refine ⟨244311557811764945415051923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162874371874509963610034615 244311557811764945415051923)
  ·
    refine ⟨366467336717647418122577885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244311557811764945415051923 366467336717647418122577885)
    ·
      refine ⟨137425251269117781795966707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366467336717647418122577885 137425251269117781795966707)
      ·
        refine ⟨206137876903676672693950061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137425251269117781795966707 206137876903676672693950061)
        ·
          refine ⟨77301703838878752260231273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206137876903676672693950061 77301703838878752260231273)
          ·
            refine ⟨57976277879159064195173455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77301703838878752260231273 57976277879159064195173455)
            ·
              refine ⟨86964416818738596292760183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57976277879159064195173455 86964416818738596292760183)
              ·
                refine ⟨130446625228107894439140275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86964416818738596292760183 130446625228107894439140275)
                ·
                  refine ⟨195669937842161841658710413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130446625228107894439140275 195669937842161841658710413)
                  ·
                    refine ⟨73376226690810690622016405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195669937842161841658710413 73376226690810690622016405)
                    ·
                      refine ⟨3439510626131751122907019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73376226690810690622016405 3439510626131751122907019)
                      ·
                        rfl

theorem cell23_6698423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_6698423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698423 prefixEnd_6698423 := by exact prefixLift 6698423
  have htrace : WordTrace (prefixWord ++ tailWord_6698423) baseStart_6698423 baseEnd_6698423 := by
    simpa [prefixWord, tailWord_6698423, baseEnd_6698423] using wordTrace_append hprefix tailTrace_6698423
  have hstable : (prefixWord ++ tailWord_6698423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698423).length < 2 ^ (prefixWord ++ tailWord_6698423).sum := by decide
  have hdescent : baseEnd_6698423 < baseStart_6698423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698454 : List Nat := [5, 2, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_6698454 : Nat := 118140960795 + 6698454 * 2 ^ 59
def prefixEnd_6698454 : Nat := 4983230072969 + 3 ^ 40 * 6698454 * 2
def baseEnd_6698454 : Nat := 1146508848010680167206459

theorem tailTrace_6698454 : CollatzResearch.WordTrace tailWord_6698454 prefixEnd_6698454 1146508848010680167206459 := by
  unfold tailWord_6698454
  simp only [CollatzResearch.WordTrace]
  refine ⟨15269543029665789856839401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162875125649768425139620277 15269543029665789856839401)
  ·
    refine ⟨11452157272249342392629551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15269543029665789856839401 11452157272249342392629551)
    ·
      refine ⟨17178235908374013588944327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11452157272249342392629551 17178235908374013588944327)
      ·
        refine ⟨25767353862561020383416491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17178235908374013588944327 25767353862561020383416491)
        ·
          refine ⟨38651030793841530575124737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25767353862561020383416491 38651030793841530575124737)
          ·
            refine ⟨28988273095381147931343553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38651030793841530575124737 28988273095381147931343553)
            ·
              refine ⟨21741204821535860948507665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28988273095381147931343553 21741204821535860948507665)
              ·
                refine ⟨16305903616151895711380749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21741204821535860948507665 16305903616151895711380749)
                ·
                  refine ⟨6114713856056960891767781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16305903616151895711380749 6114713856056960891767781)
                  ·
                    refine ⟨1146508848010680167206459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6114713856056960891767781 1146508848010680167206459)
                    ·
                      rfl

theorem cell23_6698454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_6698454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698454 prefixEnd_6698454 := by exact prefixLift 6698454
  have htrace : WordTrace (prefixWord ++ tailWord_6698454) baseStart_6698454 baseEnd_6698454 := by
    simpa [prefixWord, tailWord_6698454, baseEnd_6698454] using wordTrace_append hprefix tailTrace_6698454
  have hstable : (prefixWord ++ tailWord_6698454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698454).length < 2 ^ (prefixWord ++ tailWord_6698454).sum := by decide
  have hdescent : baseEnd_6698454 < baseStart_6698454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698471 : List Nat := [1, 1, 5, 2, 1, 4, 1, 3, 1, 4]
def baseStart_6698471 : Nat := 118140960795 + 6698471 * 2 ^ 59
def prefixEnd_6698471 : Nat := 4983230072969 + 3 ^ 40 * 6698471 * 2
def baseEnd_6698471 : Nat := 1146511757734388978368933

theorem tailTrace_6698471 : CollatzResearch.WordTrace tailWord_6698471 prefixEnd_6698471 1146511757734388978368933 := by
  unfold tailWord_6698471
  simp only [CollatzResearch.WordTrace]
  refine ⟨244313308515591049612799267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162875539010394033075199511 244313308515591049612799267)
  ·
    refine ⟨366469962773386574419198901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244313308515591049612799267 366469962773386574419198901)
    ·
      refine ⟨34356559010004991351799897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 366469962773386574419198901 34356559010004991351799897)
      ·
        refine ⟨25767419257503743513849923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34356559010004991351799897 25767419257503743513849923)
        ·
          refine ⟨38651128886255615270774885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25767419257503743513849923 38651128886255615270774885)
          ·
            refine ⟨7247086666172927863270291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38651128886255615270774885 7247086666172927863270291)
            ·
              refine ⟨10870629999259391794905437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7247086666172927863270291 10870629999259391794905437)
              ·
                refine ⟨4076486249722271923089539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10870629999259391794905437 4076486249722271923089539)
                ·
                  refine ⟨6114729374583407884634309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4076486249722271923089539 6114729374583407884634309)
                  ·
                    refine ⟨1146511757734388978368933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6114729374583407884634309 1146511757734388978368933)
                    ·
                      rfl

theorem cell23_6698471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_6698471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698471 prefixEnd_6698471 := by exact prefixLift 6698471
  have htrace : WordTrace (prefixWord ++ tailWord_6698471) baseStart_6698471 baseEnd_6698471 := by
    simpa [prefixWord, tailWord_6698471, baseEnd_6698471] using wordTrace_append hprefix tailTrace_6698471
  have hstable : (prefixWord ++ tailWord_6698471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698471).length < 2 ^ (prefixWord ++ tailWord_6698471).sum := by decide
  have hdescent : baseEnd_6698471 < baseStart_6698471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698473 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 4, 1, 7]
def baseStart_6698473 : Nat := 118140960795 + 6698473 * 2 ^ 59
def prefixEnd_6698473 : Nat := 4983230072969 + 3 ^ 40 * 6698473 * 2
def baseEnd_6698473 : Nat := 3439536300164475927281789

theorem tailTrace_6698473 : CollatzResearch.WordTrace tailWord_6698473 prefixEnd_6698473 3439536300164475927281789 := by
  unfold tailWord_6698473
  simp only [CollatzResearch.WordTrace]
  refine ⟨244313381461583803954372073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162875587641055869302914715 244313381461583803954372073)
  ·
    refine ⟨183235036096187852965779055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244313381461583803954372073 183235036096187852965779055)
    ·
      refine ⟨274852554144281779448668583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183235036096187852965779055 274852554144281779448668583)
      ·
        refine ⟨412278831216422669173002875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274852554144281779448668583 412278831216422669173002875)
        ·
          refine ⟨618418246824634003759504313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412278831216422669173002875 618418246824634003759504313)
          ·
            refine ⟨463813685118475502819628235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 618418246824634003759504313 463813685118475502819628235)
            ·
              refine ⟨695720527677713254229442353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463813685118475502819628235 695720527677713254229442353)
              ·
                refine ⟨521790395758284940672081765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 695720527677713254229442353 521790395758284940672081765)
                ·
                  refine ⟨97835699204678426376015331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 521790395758284940672081765 97835699204678426376015331)
                  ·
                    refine ⟨146753548807017639564022997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97835699204678426376015331 146753548807017639564022997)
                    ·
                      refine ⟨3439536300164475927281789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 146753548807017639564022997 3439536300164475927281789)
                      ·
                        rfl

theorem cell23_6698473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_6698473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698473 prefixEnd_6698473 := by exact prefixLift 6698473
  have htrace : WordTrace (prefixWord ++ tailWord_6698473) baseStart_6698473 baseEnd_6698473 := by
    simpa [prefixWord, tailWord_6698473, baseEnd_6698473] using wordTrace_append hprefix tailTrace_6698473
  have hstable : (prefixWord ++ tailWord_6698473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698473).length < 2 ^ (prefixWord ++ tailWord_6698473).sum := by decide
  have hdescent : baseEnd_6698473 < baseStart_6698473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698517 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_6698517 : Nat := 118140960795 + 6698517 * 2 ^ 59
def prefixEnd_6698517 : Nat := 4983230072969 + 3 ^ 40 * 6698517 * 2
def baseEnd_6698517 : Nat := 3439558893313273755131587

theorem tailTrace_6698517 : CollatzResearch.WordTrace tailWord_6698517 prefixEnd_6698517 3439558893313273755131587 := by
  unfold tailWord_6698517
  simp only [CollatzResearch.WordTrace]
  refine ⟨244314986273424399468973805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162876657515616266312649203 244314986273424399468973805)
  ·
    refine ⟨91618119852534149800865177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244314986273424399468973805 91618119852534149800865177)
    ·
      refine ⟨68713589889400612350648883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91618119852534149800865177 68713589889400612350648883)
      ·
        refine ⟨103070384834100918525973325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68713589889400612350648883 103070384834100918525973325)
        ·
          refine ⟨38651394312787844447239997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103070384834100918525973325 38651394312787844447239997)
          ·
            refine ⟨14494272867295441667714999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38651394312787844447239997 14494272867295441667714999)
            ·
              refine ⟨21741409300943162501572499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14494272867295441667714999 21741409300943162501572499)
              ·
                refine ⟨32612113951414743752358749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21741409300943162501572499 32612113951414743752358749)
                ·
                  refine ⟨12229542731780528907134531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32612113951414743752358749 12229542731780528907134531)
                  ·
                    refine ⟨18344314097670793360701797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12229542731780528907134531 18344314097670793360701797)
                    ·
                      refine ⟨3439558893313273755131587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18344314097670793360701797 3439558893313273755131587)
                      ·
                        rfl

theorem cell23_6698517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_6698517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698517 prefixEnd_6698517 := by exact prefixLift 6698517
  have htrace : WordTrace (prefixWord ++ tailWord_6698517) baseStart_6698517 baseEnd_6698517 := by
    simpa [prefixWord, tailWord_6698517, baseEnd_6698517] using wordTrace_append hprefix tailTrace_6698517
  have hstable : (prefixWord ++ tailWord_6698517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698517).length < 2 ^ (prefixWord ++ tailWord_6698517).sum := by decide
  have hdescent : baseEnd_6698517 < baseStart_6698517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698570 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 2, 7]
def baseStart_6698570 : Nat := 118140960795 + 6698570 * 2 ^ 59
def prefixEnd_6698570 : Nat := 4983230072969 + 3 ^ 40 * 6698570 * 2
def baseEnd_6698570 : Nat := 1146528702595987349256281

theorem tailTrace_6698570 : CollatzResearch.WordTrace tailWord_6698570 prefixEnd_6698570 1146528702595987349256281 := by
  unfold tailWord_6698570
  simp only [CollatzResearch.WordTrace]
  refine ⟨61079229835558097380163291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162877946228154926347102109 61079229835558097380163291)
  ·
    refine ⟨91618844753337146070244937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61079229835558097380163291 91618844753337146070244937)
    ·
      refine ⟨68714133565002859552683703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91618844753337146070244937 68714133565002859552683703)
      ·
        refine ⟨103071200347504289329025555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68714133565002859552683703 103071200347504289329025555)
        ·
          refine ⟨154606800521256433993538333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103071200347504289329025555 154606800521256433993538333)
          ·
            refine ⟨57977550195471162747576875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154606800521256433993538333 57977550195471162747576875)
            ·
              refine ⟨86966325293206744121365313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57977550195471162747576875 86966325293206744121365313)
              ·
                refine ⟨65224743969905058091023985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86966325293206744121365313 65224743969905058091023985)
                ·
                  refine ⟨48918557977428793568267989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65224743969905058091023985 48918557977428793568267989)
                  ·
                    refine ⟨1146528702595987349256281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48918557977428793568267989 1146528702595987349256281)
                    ·
                      rfl

theorem cell23_6698570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_6698570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698570 prefixEnd_6698570 := by exact prefixLift 6698570
  have htrace : WordTrace (prefixWord ++ tailWord_6698570) baseStart_6698570 baseEnd_6698570 := by
    simpa [prefixWord, tailWord_6698570, baseEnd_6698570] using wordTrace_append hprefix tailTrace_6698570
  have hstable : (prefixWord ++ tailWord_6698570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698570).length < 2 ^ (prefixWord ++ tailWord_6698570).sum := by decide
  have hdescent : baseEnd_6698570 < baseStart_6698570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698582 : List Nat := [5, 2, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_6698582 : Nat := 118140960795 + 6698582 * 2 ^ 59
def prefixEnd_6698582 : Nat := 4983230072969 + 3 ^ 40 * 6698582 * 2
def baseEnd_6698582 : Nat := 1146530756518605333606263

theorem tailTrace_6698582 : CollatzResearch.WordTrace tailWord_6698582 prefixEnd_6698582 1146530756518605333606263 := by
  unfold tailWord_6698582
  simp only [CollatzResearch.WordTrace]
  refine ⟨15269834813636807223130625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162878238012125943713393333 15269834813636807223130625)
  ·
    refine ⟨11452376110227605417347969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15269834813636807223130625 11452376110227605417347969)
    ·
      refine ⟨8589282082670704063010977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11452376110227605417347969 8589282082670704063010977)
      ·
        refine ⟨6441961562003028047258233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8589282082670704063010977 6441961562003028047258233)
        ·
          refine ⟨4831471171502271035443675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6441961562003028047258233 4831471171502271035443675)
          ·
            refine ⟨7247206757253406553165513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4831471171502271035443675 7247206757253406553165513)
            ·
              refine ⟨5435405067940054914874135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7247206757253406553165513 5435405067940054914874135)
              ·
                refine ⟨8153107601910082372311203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5435405067940054914874135 8153107601910082372311203)
                ·
                  refine ⟨12229661402865123558466805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8153107601910082372311203 12229661402865123558466805)
                  ·
                    refine ⟨1146530756518605333606263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12229661402865123558466805 1146530756518605333606263)
                    ·
                      rfl

theorem cell23_6698582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_6698582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698582 prefixEnd_6698582 := by exact prefixLift 6698582
  have htrace : WordTrace (prefixWord ++ tailWord_6698582) baseStart_6698582 baseEnd_6698582 := by
    simpa [prefixWord, tailWord_6698582, baseEnd_6698582] using wordTrace_append hprefix tailTrace_6698582
  have hstable : (prefixWord ++ tailWord_6698582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698582).length < 2 ^ (prefixWord ++ tailWord_6698582).sum := by decide
  have hdescent : baseEnd_6698582 < baseStart_6698582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698588 : List Nat := [2, 2, 4, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_6698588 : Nat := 118140960795 + 6698588 * 2 ^ 59
def prefixEnd_6698588 : Nat := 4983230072969 + 3 ^ 40 * 6698588 * 2
def baseEnd_6698588 : Nat := 3439595350439742977343761

theorem tailTrace_6698588 : CollatzResearch.WordTrace tailWord_6698588 prefixEnd_6698588 3439595350439742977343761 := by
  unfold tailWord_6698588
  simp only [CollatzResearch.WordTrace]
  refine ⟨122158787928083589297404209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162878383904111452396538945 122158787928083589297404209)
  ·
    refine ⟨91619090946062691973053157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122158787928083589297404209 91619090946062691973053157)
    ·
      refine ⟨17178579552386754744947467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91619090946062691973053157 17178579552386754744947467)
      ·
        refine ⟨25767869328580132117421201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17178579552386754744947467 25767869328580132117421201)
        ·
          refine ⟨19325901996435099088065901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25767869328580132117421201 19325901996435099088065901)
          ·
            refine ⟨7247213248663162158024713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19325901996435099088065901 7247213248663162158024713)
            ·
              refine ⟨5435409936497371618518535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7247213248663162158024713 5435409936497371618518535)
              ·
                refine ⟨8153114904746057427777803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5435409936497371618518535 8153114904746057427777803)
                ·
                  refine ⟨12229672357119086141666705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8153114904746057427777803 12229672357119086141666705)
                  ·
                    refine ⟨9172254267839314606250029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12229672357119086141666705 9172254267839314606250029)
                    ·
                      refine ⟨3439595350439742977343761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9172254267839314606250029 3439595350439742977343761)
                      ·
                        rfl

theorem cell23_6698588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_6698588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698588 prefixEnd_6698588 := by exact prefixLift 6698588
  have htrace : WordTrace (prefixWord ++ tailWord_6698588) baseStart_6698588 baseEnd_6698588 := by
    simpa [prefixWord, tailWord_6698588, baseEnd_6698588] using wordTrace_append hprefix tailTrace_6698588
  have hstable : (prefixWord ++ tailWord_6698588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698588).length < 2 ^ (prefixWord ++ tailWord_6698588).sum := by decide
  have hdescent : baseEnd_6698588 < baseStart_6698588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698628 : List Nat := [2, 3, 2, 1, 4, 1, 2, 2, 1, 3, 2]
def baseStart_6698628 : Nat := 118140960795 + 6698628 * 2 ^ 59
def prefixEnd_6698628 : Nat := 4983230072969 + 3 ^ 40 * 6698628 * 2
def baseEnd_6698628 : Nat := 3439615889665922820843577

theorem tailTrace_6698628 : CollatzResearch.WordTrace tailWord_6698628 prefixEnd_6698628 3439615889665922820843577 := by
  unfold tailWord_6698628
  simp only [CollatzResearch.WordTrace]
  refine ⟨122159517388011132713132269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162879356517348176950843025 122159517388011132713132269)
  ·
    refine ⟨45809819020504174767424601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122159517388011132713132269 45809819020504174767424601)
    ·
      refine ⟨34357364265378131075568451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45809819020504174767424601 34357364265378131075568451)
      ·
        refine ⟨51536046398067196613352677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34357364265378131075568451 51536046398067196613352677)
        ·
          refine ⟨9663008699637599365003627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51536046398067196613352677 9663008699637599365003627)
          ·
            refine ⟨14494513049456399047505441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9663008699637599365003627 14494513049456399047505441)
            ·
              refine ⟨10870884787092299285629081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14494513049456399047505441 10870884787092299285629081)
              ·
                refine ⟨8153163590319224464221811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10870884787092299285629081 8153163590319224464221811)
                ·
                  refine ⟨12229745385478836696332717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8153163590319224464221811 12229745385478836696332717)
                  ·
                    refine ⟨4586154519554563761124769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12229745385478836696332717 4586154519554563761124769)
                    ·
                      refine ⟨3439615889665922820843577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4586154519554563761124769 3439615889665922820843577)
                      ·
                        rfl

theorem cell23_6698628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_6698628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698628 prefixEnd_6698628 := by exact prefixLift 6698628
  have htrace : WordTrace (prefixWord ++ tailWord_6698628) baseStart_6698628 baseEnd_6698628 := by
    simpa [prefixWord, tailWord_6698628, baseEnd_6698628] using wordTrace_append hprefix tailTrace_6698628
  have hstable : (prefixWord ++ tailWord_6698628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698628).length < 2 ^ (prefixWord ++ tailWord_6698628).sum := by decide
  have hdescent : baseEnd_6698628 < baseStart_6698628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6698714 : List Nat := [3, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4]
def baseStart_6698714 : Nat := 118140960795 + 6698714 * 2 ^ 59
def prefixEnd_6698714 : Nat := 4983230072969 + 3 ^ 40 * 6698714 * 2
def baseEnd_6698714 : Nat := 3439660049002209484368181

theorem tailTrace_6698714 : CollatzResearch.WordTrace tailWord_6698714 prefixEnd_6698714 3439660049002209484368181 := by
  unfold tailWord_6698714
  simp only [CollatzResearch.WordTrace]
  refine ⟨61080542863427675528473799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162881447635807134742596797 61080542863427675528473799)
  ·
    refine ⟨91620814295141513292710699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61080542863427675528473799 91620814295141513292710699)
    ·
      refine ⟨137431221442712269939066049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91620814295141513292710699 137431221442712269939066049)
      ·
        refine ⟨103073416082034202454299537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137431221442712269939066049 103073416082034202454299537)
        ·
          refine ⟨77305062061525651840724653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103073416082034202454299537 77305062061525651840724653)
          ·
            refine ⟨28989398273072119440271745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77305062061525651840724653 28989398273072119440271745)
            ·
              refine ⟨21742048704804089580203809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28989398273072119440271745 21742048704804089580203809)
              ·
                refine ⟨16306536528603067185152857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21742048704804089580203809 16306536528603067185152857)
                ·
                  refine ⟨12229902396452300388864643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16306536528603067185152857 12229902396452300388864643)
                  ·
                    refine ⟨18344853594678450583296965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12229902396452300388864643 18344853594678450583296965)
                    ·
                      refine ⟨3439660049002209484368181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18344853594678450583296965 3439660049002209484368181)
                      ·
                        rfl

theorem cell23_6698714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_6698714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6698714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6698714 prefixEnd_6698714 := by exact prefixLift 6698714
  have htrace : WordTrace (prefixWord ++ tailWord_6698714) baseStart_6698714 baseEnd_6698714 := by
    simpa [prefixWord, tailWord_6698714, baseEnd_6698714] using wordTrace_append hprefix tailTrace_6698714
  have hstable : (prefixWord ++ tailWord_6698714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6698714).length < 2 ^ (prefixWord ++ tailWord_6698714).sum := by decide
  have hdescent : baseEnd_6698714 < baseStart_6698714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6698714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
