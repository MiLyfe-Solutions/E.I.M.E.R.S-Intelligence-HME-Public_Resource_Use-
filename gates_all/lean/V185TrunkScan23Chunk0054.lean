import V185TrunkScan23Chunk0053

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_319255 : List Nat := [1, 1, 3, 4, 2, 3, 1, 1, 7]
def baseStart_319255 : Nat := 118140960795 + 319255 * 2 ^ 59
def prefixEnd_319255 : Nat := 4983230072969 + 3 ^ 40 * 319255 * 2
def baseEnd_319255 : Nat := 18214585150139294116031

theorem tailTrace_319255 : CollatzResearch.WordTrace tailWord_319255 prefixEnd_319255 18214585150139294116031 := by
  unfold tailWord_319255
  simp only [CollatzResearch.WordTrace]
  refine ⟨11644186458401134258199219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7762790972267422838799479 11644186458401134258199219)
  ·
    refine ⟨17466279687601701387298829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11644186458401134258199219 17466279687601701387298829)
    ·
      refine ⟨6549854882850638020237061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17466279687601701387298829 6549854882850638020237061)
      ·
        refine ⟨1228097790534494628794449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6549854882850638020237061 1228097790534494628794449)
        ·
          refine ⟨921073342900870971595837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1228097790534494628794449 921073342900870971595837)
          ·
            refine ⟨345402503587826614348439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 921073342900870971595837 345402503587826614348439)
            ·
              refine ⟨518103755381739921522659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345402503587826614348439 518103755381739921522659)
              ·
                refine ⟨777155633072609882283989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518103755381739921522659 777155633072609882283989)
                ·
                  refine ⟨18214585150139294116031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 777155633072609882283989 18214585150139294116031)
                  ·
                    rfl

theorem cell23_319255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 7].length) (baseStart_319255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319255 prefixEnd_319255 := by exact prefixLift 319255
  have htrace : WordTrace (prefixWord ++ tailWord_319255) baseStart_319255 baseEnd_319255 := by
    simpa [prefixWord, tailWord_319255, baseEnd_319255] using wordTrace_append hprefix tailTrace_319255
  have hstable : (prefixWord ++ tailWord_319255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319255).length < 2 ^ (prefixWord ++ tailWord_319255).sum := by decide
  have hdescent : baseEnd_319255 < baseStart_319255 := by decide
  rcases family_descends (prefixWord ++ tailWord_319255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319305 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 2, 4, 2]
def baseStart_319305 : Nat := 118140960795 + 319305 * 2 ^ 59
def prefixEnd_319305 : Nat := 4983230072969 + 3 ^ 40 * 319305 * 2
def baseEnd_319305 : Nat := 163956940383978451419049

theorem tailTrace_319305 : CollatzResearch.WordTrace tailWord_319305 prefixEnd_319305 163956940383978451419049 := by
  unfold tailWord_319305
  simp only [CollatzResearch.WordTrace]
  refine ⟨11646010108219992797519369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7764006738813328531679579 11646010108219992797519369)
  ·
    refine ⟨8734507581164994598139527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11646010108219992797519369 8734507581164994598139527)
    ·
      refine ⟨13101761371747491897209291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8734507581164994598139527 13101761371747491897209291)
      ·
        refine ⟨19652642057621237845813937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13101761371747491897209291 19652642057621237845813937)
        ·
          refine ⟨14739481543215928384360453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19652642057621237845813937 14739481543215928384360453)
          ·
            refine ⟨2763652789352986572067585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14739481543215928384360453 2763652789352986572067585)
            ·
              refine ⟨2072739592014739929050689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2763652789352986572067585 2072739592014739929050689)
              ·
                refine ⟨1554554694011054946788017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2072739592014739929050689 1554554694011054946788017)
                ·
                  refine ⟨1165916020508291210091013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1554554694011054946788017 1165916020508291210091013)
                  ·
                    refine ⟨218609253845304601892065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1165916020508291210091013 218609253845304601892065)
                    ·
                      refine ⟨163956940383978451419049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 218609253845304601892065 163956940383978451419049)
                      ·
                        rfl

theorem cell23_319305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 4, 2].length) (baseStart_319305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319305 prefixEnd_319305 := by exact prefixLift 319305
  have htrace : WordTrace (prefixWord ++ tailWord_319305) baseStart_319305 baseEnd_319305 := by
    simpa [prefixWord, tailWord_319305, baseEnd_319305] using wordTrace_append hprefix tailTrace_319305
  have hstable : (prefixWord ++ tailWord_319305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319305).length < 2 ^ (prefixWord ++ tailWord_319305).sum := by decide
  have hdescent : baseEnd_319305 < baseStart_319305 := by decide
  rcases family_descends (prefixWord ++ tailWord_319305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319332 : List Nat := [2, 3, 1, 1, 5, 1, 1, 2, 3, 4]
def baseStart_319332 : Nat := 118140960795 + 319332 * 2 ^ 59
def prefixEnd_319332 : Nat := 4983230072969 + 3 ^ 40 * 319332 * 2
def baseEnd_319332 : Nat := 54656934787216615260475

theorem tailTrace_319332 : CollatzResearch.WordTrace tailWord_319332 prefixEnd_319332 54656934787216615260475 := by
  unfold tailWord_319332
  simp only [CollatzResearch.WordTrace]
  refine ⟨5823497439561088204376125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7764663252748117605834833 5823497439561088204376125)
  ·
    refine ⟨2183811539835408076641047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5823497439561088204376125 2183811539835408076641047)
    ·
      refine ⟨3275717309753112114961571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2183811539835408076641047 3275717309753112114961571)
      ·
        refine ⟨4913575964629668172442357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3275717309753112114961571 4913575964629668172442357)
        ·
          refine ⟨460647746684031391166471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4913575964629668172442357 460647746684031391166471)
          ·
            refine ⟨690971620026047086749707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460647746684031391166471 690971620026047086749707)
            ·
              refine ⟨1036457430039070630124561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 690971620026047086749707 1036457430039070630124561)
              ·
                refine ⟨777343072529302972593421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1036457430039070630124561 777343072529302972593421)
                ·
                  refine ⟨291503652198488614722533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 777343072529302972593421 291503652198488614722533)
                  ·
                    refine ⟨54656934787216615260475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 291503652198488614722533 54656934787216615260475)
                    ·
                      rfl

theorem cell23_319332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_319332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319332 prefixEnd_319332 := by exact prefixLift 319332
  have htrace : WordTrace (prefixWord ++ tailWord_319332) baseStart_319332 baseEnd_319332 := by
    simpa [prefixWord, tailWord_319332, baseEnd_319332] using wordTrace_append hprefix tailTrace_319332
  have hstable : (prefixWord ++ tailWord_319332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319332).length < 2 ^ (prefixWord ++ tailWord_319332).sum := by decide
  have hdescent : baseEnd_319332 < baseStart_319332 := by decide
  rcases family_descends (prefixWord ++ tailWord_319332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319342 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_319342 : Nat := 118140960795 + 319342 * 2 ^ 59
def prefixEnd_319342 : Nat := 4983230072969 + 3 ^ 40 * 319342 * 2
def baseEnd_319342 : Nat := 163975939168194806656379

theorem tailTrace_319342 : CollatzResearch.WordTrace tailWord_319342 prefixEnd_319342 163975939168194806656379 := by
  unfold tailWord_319342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1455919951135743514577035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7764906406057298744410853 1455919951135743514577035)
  ·
    refine ⟨2183879926703615271865553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1455919951135743514577035 2183879926703615271865553)
    ·
      refine ⟨1637909945027711453899165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2183879926703615271865553 1637909945027711453899165)
      ·
        refine ⟨614216229385391795212187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1637909945027711453899165 614216229385391795212187)
        ·
          refine ⟨921324344078087692818281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614216229385391795212187 921324344078087692818281)
          ·
            refine ⟨690993258058565769613711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 921324344078087692818281 690993258058565769613711)
            ·
              refine ⟨1036489887087848654420567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 690993258058565769613711 1036489887087848654420567)
              ·
                refine ⟨1554734830631772981630851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1036489887087848654420567 1554734830631772981630851)
                ·
                  refine ⟨2332102245947659472446277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554734830631772981630851 2332102245947659472446277)
                  ·
                    refine ⟨437269171115186151083677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2332102245947659472446277 437269171115186151083677)
                    ·
                      refine ⟨163975939168194806656379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 437269171115186151083677 163975939168194806656379)
                      ·
                        rfl

theorem cell23_319342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_319342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319342 prefixEnd_319342 := by exact prefixLift 319342
  have htrace : WordTrace (prefixWord ++ tailWord_319342) baseStart_319342 baseEnd_319342 := by
    simpa [prefixWord, tailWord_319342, baseEnd_319342] using wordTrace_append hprefix tailTrace_319342
  have hstable : (prefixWord ++ tailWord_319342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319342).length < 2 ^ (prefixWord ++ tailWord_319342).sum := by decide
  have hdescent : baseEnd_319342 < baseStart_319342 := by decide
  rcases family_descends (prefixWord ++ tailWord_319342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319349 : List Nat := [1, 3, 4, 1, 1, 1, 4, 3, 1, 4]
def baseStart_319349 : Nat := 118140960795 + 319349 * 2 ^ 59
def prefixEnd_319349 : Nat := 4983230072969 + 3 ^ 40 * 319349 * 2
def baseEnd_319349 : Nat := 54659844510925426422949

theorem tailTrace_319349 : CollatzResearch.WordTrace tailWord_319349 prefixEnd_319349 54659844510925426422949 := by
  unfold tailWord_319349
  simp only [CollatzResearch.WordTrace]
  refine ⟨11647614920060588312121101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7765076613373725541414067 11647614920060588312121101)
  ·
    refine ⟨4367855595022720617045413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11647614920060588312121101 4367855595022720617045413)
    ·
      refine ⟨818972924066760115696015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4367855595022720617045413 818972924066760115696015)
      ·
        refine ⟨1228459386100140173544023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 818972924066760115696015 1228459386100140173544023)
        ·
          refine ⟨1842689079150210260316035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1228459386100140173544023 1842689079150210260316035)
          ·
            refine ⟨2764033618725315390474053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1842689079150210260316035 2764033618725315390474053)
            ·
              refine ⟨518256303510996635713885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2764033618725315390474053 518256303510996635713885)
              ·
                refine ⟨194346113816623738392707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 518256303510996635713885 194346113816623738392707)
                ·
                  refine ⟨291519170724935607589061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194346113816623738392707 291519170724935607589061)
                  ·
                    refine ⟨54659844510925426422949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 291519170724935607589061 54659844510925426422949)
                    ·
                      rfl

theorem cell23_319349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_319349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319349 prefixEnd_319349 := by exact prefixLift 319349
  have htrace : WordTrace (prefixWord ++ tailWord_319349) baseStart_319349 baseEnd_319349 := by
    simpa [prefixWord, tailWord_319349, baseEnd_319349] using wordTrace_append hprefix tailTrace_319349
  have hstable : (prefixWord ++ tailWord_319349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319349).length < 2 ^ (prefixWord ++ tailWord_319349).sum := by decide
  have hdescent : baseEnd_319349 < baseStart_319349 := by decide
  rcases family_descends (prefixWord ++ tailWord_319349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319355 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 7, 1, 3]
def baseStart_319355 : Nat := 118140960795 + 319355 * 2 ^ 59
def prefixEnd_319355 : Nat := 4983230072969 + 3 ^ 40 * 319355 * 2
def baseEnd_319355 : Nat := 163982614416703255793819

theorem tailTrace_319355 : CollatzResearch.WordTrace tailWord_319355 prefixEnd_319355 163982614416703255793819 := by
  unfold tailWord_319355
  simp only [CollatzResearch.WordTrace]
  refine ⟨11647833758038851336839519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7765222505359234224559679 11647833758038851336839519)
  ·
    refine ⟨17471750637058277005259279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11647833758038851336839519 17471750637058277005259279)
    ·
      refine ⟨26207625955587415507888919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17471750637058277005259279 26207625955587415507888919)
      ·
        refine ⟨39311438933381123261833379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26207625955587415507888919 39311438933381123261833379)
        ·
          refine ⟨58967158400071684892750069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39311438933381123261833379 58967158400071684892750069)
          ·
            refine ⟨5528171100006720458695319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58967158400071684892750069 5528171100006720458695319)
            ·
              refine ⟨8292256650010080688042979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5528171100006720458695319 8292256650010080688042979)
              ·
                refine ⟨12438384975015121032064469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8292256650010080688042979 12438384975015121032064469)
                ·
                  refine ⟨291524647851916899189011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12438384975015121032064469 291524647851916899189011)
                  ·
                    refine ⟨437286971777875348783517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 291524647851916899189011 437286971777875348783517)
                    ·
                      refine ⟨163982614416703255793819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 437286971777875348783517 163982614416703255793819)
                      ·
                        rfl

theorem cell23_319355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 1, 3].length) (baseStart_319355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319355 prefixEnd_319355 := by exact prefixLift 319355
  have htrace : WordTrace (prefixWord ++ tailWord_319355) baseStart_319355 baseEnd_319355 := by
    simpa [prefixWord, tailWord_319355, baseEnd_319355] using wordTrace_append hprefix tailTrace_319355
  have hstable : (prefixWord ++ tailWord_319355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319355).length < 2 ^ (prefixWord ++ tailWord_319355).sum := by decide
  have hdescent : baseEnd_319355 < baseStart_319355 := by decide
  rcases family_descends (prefixWord ++ tailWord_319355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319395 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 1, 8, 2]
def baseStart_319395 : Nat := 118140960795 + 319395 * 2 ^ 59
def prefixEnd_319395 : Nat := 4983230072969 + 3 ^ 40 * 319395 * 2
def baseEnd_319395 : Nat := 164003153642883099293635

theorem tailTrace_319395 : CollatzResearch.WordTrace tailWord_319395 prefixEnd_319395 164003153642883099293635 := by
  unfold tailWord_319395
  simp only [CollatzResearch.WordTrace]
  refine ⟨11649292677893938168295639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7766195118595958778863759 11649292677893938168295639)
  ·
    refine ⟨17473939016840907252443459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11649292677893938168295639 17473939016840907252443459)
    ·
      refine ⟨26210908525261360878665189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17473939016840907252443459 26210908525261360878665189)
      ·
        refine ⟨4914545348486505164749723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26210908525261360878665189 4914545348486505164749723)
        ·
          refine ⟨7371818022729757747124585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4914545348486505164749723 7371818022729757747124585)
          ·
            refine ⟨5528863517047318310343439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7371818022729757747124585 5528863517047318310343439)
            ·
              refine ⟨8293295275570977465515159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5528863517047318310343439 8293295275570977465515159)
              ·
                refine ⟨12439942913356466198272739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8293295275570977465515159 12439942913356466198272739)
                ·
                  refine ⟨18659914370034699297409109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12439942913356466198272739 18659914370034699297409109)
                  ·
                    refine ⟨218670871523844132391513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18659914370034699297409109 218670871523844132391513)
                    ·
                      refine ⟨164003153642883099293635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 218670871523844132391513 164003153642883099293635)
                      ·
                        rfl

theorem cell23_319395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_319395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319395 prefixEnd_319395 := by exact prefixLift 319395
  have htrace : WordTrace (prefixWord ++ tailWord_319395) baseStart_319395 baseEnd_319395 := by
    simpa [prefixWord, tailWord_319395, baseEnd_319395] using wordTrace_append hprefix tailTrace_319395
  have hstable : (prefixWord ++ tailWord_319395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319395).length < 2 ^ (prefixWord ++ tailWord_319395).sum := by decide
  have hdescent : baseEnd_319395 < baseStart_319395 := by decide
  rcases family_descends (prefixWord ++ tailWord_319395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319400 : List Nat := [2, 1, 6, 2, 2, 1, 1, 3, 1, 4]
def baseStart_319400 : Nat := 118140960795 + 319400 * 2 ^ 59
def prefixEnd_319400 : Nat := 4983230072969 + 3 ^ 40 * 319400 * 2
def baseEnd_319400 : Nat := 54668573682051859910371

theorem tailTrace_319400 : CollatzResearch.WordTrace tailWord_319400 prefixEnd_319400 54668573682051859910371 := by
  unfold tailWord_319400
  simp only [CollatzResearch.WordTrace]
  refine ⟨5824737521437912011113827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7766316695250549348151769 5824737521437912011113827)
  ·
    refine ⟨8737106282156868016670741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5824737521437912011113827 8737106282156868016670741)
    ·
      refine ⟨409551856976103188281441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8737106282156868016670741 409551856976103188281441)
      ·
        refine ⟨307163892732077391211081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 409551856976103188281441 307163892732077391211081)
        ·
          refine ⟨230372919549058043408311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307163892732077391211081 230372919549058043408311)
          ·
            refine ⟨345559379323587065112467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230372919549058043408311 345559379323587065112467)
            ·
              refine ⟨518339068985380597668701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345559379323587065112467 518339068985380597668701)
              ·
                refine ⟨194377150869517724125763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 518339068985380597668701 194377150869517724125763)
                ·
                  refine ⟨291565726304276586188645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194377150869517724125763 291565726304276586188645)
                  ·
                    refine ⟨54668573682051859910371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 291565726304276586188645 54668573682051859910371)
                    ·
                      rfl

theorem cell23_319400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_319400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319400 prefixEnd_319400 := by exact prefixLift 319400
  have htrace : WordTrace (prefixWord ++ tailWord_319400) baseStart_319400 baseEnd_319400 := by
    simpa [prefixWord, tailWord_319400, baseEnd_319400] using wordTrace_append hprefix tailTrace_319400
  have hstable : (prefixWord ++ tailWord_319400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319400).length < 2 ^ (prefixWord ++ tailWord_319400).sum := by decide
  have hdescent : baseEnd_319400 < baseStart_319400 := by decide
  rcases family_descends (prefixWord ++ tailWord_319400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319415 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 3]
def baseStart_319415 : Nat := 118140960795 + 319415 * 2 ^ 59
def prefixEnd_319415 : Nat := 4983230072969 + 3 ^ 40 * 319415 * 2
def baseEnd_319415 : Nat := 164013423255973021043543

theorem tailTrace_319415 : CollatzResearch.WordTrace tailWord_319415 prefixEnd_319415 164013423255973021043543 := by
  unfold tailWord_319415
  simp only [CollatzResearch.WordTrace]
  refine ⟨11650022137821481584023699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7766681425214321056015799 11650022137821481584023699)
  ·
    refine ⟨17475033206732222376035549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11650022137821481584023699 17475033206732222376035549)
    ·
      refine ⟨6553137452524583391013331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17475033206732222376035549 6553137452524583391013331)
      ·
        refine ⟨9829706178786875086519997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6553137452524583391013331 9829706178786875086519997)
        ·
          refine ⟨3686139817045078157444999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9829706178786875086519997 3686139817045078157444999)
          ·
            refine ⟨5529209725567617236167499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3686139817045078157444999 5529209725567617236167499)
            ·
              refine ⟨8293814588351425854251249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5529209725567617236167499 8293814588351425854251249)
              ·
                refine ⟨6220360941263569390688437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8293814588351425854251249 6220360941263569390688437)
                ·
                  refine ⟨583158838243459630377041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6220360941263569390688437 583158838243459630377041)
                  ·
                    refine ⟨437369128682594722782781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 583158838243459630377041 437369128682594722782781)
                    ·
                      refine ⟨164013423255973021043543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 437369128682594722782781 164013423255973021043543)
                      ·
                        rfl

theorem cell23_319415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_319415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319415 prefixEnd_319415 := by exact prefixLift 319415
  have htrace : WordTrace (prefixWord ++ tailWord_319415) baseStart_319415 baseEnd_319415 := by
    simpa [prefixWord, tailWord_319415, baseEnd_319415] using wordTrace_append hprefix tailTrace_319415
  have hstable : (prefixWord ++ tailWord_319415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319415).length < 2 ^ (prefixWord ++ tailWord_319415).sum := by decide
  have hdescent : baseEnd_319415 < baseStart_319415 := by decide
  rcases family_descends (prefixWord ++ tailWord_319415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319422 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_319422 : Nat := 118140960795 + 319422 * 2 ^ 59
def prefixEnd_319422 : Nat := 4983230072969 + 3 ^ 40 * 319422 * 2
def baseEnd_319422 : Nat := 54672339206851497885337

theorem tailTrace_319422 : CollatzResearch.WordTrace tailWord_319422 prefixEnd_319422 54672339206851497885337 := by
  unfold tailWord_319422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1456284681099515222441065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7766851632530747853019013 1456284681099515222441065)
  ·
    refine ⟨1092213510824636416830799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1456284681099515222441065 1092213510824636416830799)
    ·
      refine ⟨1638320266236954625246199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1092213510824636416830799 1638320266236954625246199)
      ·
        refine ⟨2457480399355431937869299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1638320266236954625246199 2457480399355431937869299)
        ·
          refine ⟨3686220599033147906803949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2457480399355431937869299 3686220599033147906803949)
          ·
            refine ⟨1382332724637430465051481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3686220599033147906803949 1382332724637430465051481)
            ·
              refine ⟨1036749543478072848788611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1382332724637430465051481 1036749543478072848788611)
              ·
                refine ⟨1555124315217109273182917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1036749543478072848788611 1555124315217109273182917)
                ·
                  refine ⟨291585809103207988721797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1555124315217109273182917 291585809103207988721797)
                  ·
                    refine ⟨54672339206851497885337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 291585809103207988721797 54672339206851497885337)
                    ·
                      rfl

theorem cell23_319422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_319422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319422 prefixEnd_319422 := by exact prefixLift 319422
  have htrace : WordTrace (prefixWord ++ tailWord_319422) baseStart_319422 baseEnd_319422 := by
    simpa [prefixWord, tailWord_319422, baseEnd_319422] using wordTrace_append hprefix tailTrace_319422
  have hstable : (prefixWord ++ tailWord_319422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319422).length < 2 ^ (prefixWord ++ tailWord_319422).sum := by decide
  have hdescent : baseEnd_319422 < baseStart_319422 := by decide
  rcases family_descends (prefixWord ++ tailWord_319422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319485 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_319485 : Nat := 118140960795 + 319485 * 2 ^ 59
def prefixEnd_319485 : Nat := 4983230072969 + 3 ^ 40 * 319485 * 2
def baseEnd_319485 : Nat := 164049366901787747168221

theorem tailTrace_319485 : CollatzResearch.WordTrace tailWord_319485 prefixEnd_319485 164049366901787747168221 := by
  unfold tailWord_319485
  simp only [CollatzResearch.WordTrace]
  refine ⟨11652575247567883539071909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7768383498378589026047939 11652575247567883539071909)
  ·
    refine ⟨2184857858918978163575983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11652575247567883539071909 2184857858918978163575983)
    ·
      refine ⟨3277286788378467245363975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2184857858918978163575983 3277286788378467245363975)
      ·
        refine ⟨4915930182567700868045963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3277286788378467245363975 4915930182567700868045963)
        ·
          refine ⟨7373895273851551302068945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4915930182567700868045963 7373895273851551302068945)
          ·
            refine ⟨5530421455388663476551709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7373895273851551302068945 5530421455388663476551709)
            ·
              refine ⟨2073908045770748803706891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5530421455388663476551709 2073908045770748803706891)
              ·
                refine ⟨3110862068656123205560337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2073908045770748803706891 3110862068656123205560337)
                ·
                  refine ⟨2333146551492092404170253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3110862068656123205560337 2333146551492092404170253)
                  ·
                    refine ⟨874929956809534651563845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2333146551492092404170253 874929956809534651563845)
                    ·
                      refine ⟨164049366901787747168221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 874929956809534651563845 164049366901787747168221)
                      ·
                        rfl

theorem cell23_319485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_319485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319485 prefixEnd_319485 := by exact prefixLift 319485
  have htrace : WordTrace (prefixWord ++ tailWord_319485) baseStart_319485 baseEnd_319485 := by
    simpa [prefixWord, tailWord_319485, baseEnd_319485] using wordTrace_append hprefix tailTrace_319485
  have hstable : (prefixWord ++ tailWord_319485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319485).length < 2 ^ (prefixWord ++ tailWord_319485).sum := by decide
  have hdescent : baseEnd_319485 < baseStart_319485 := by decide
  rcases family_descends (prefixWord ++ tailWord_319485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319495 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 1, 8]
def baseStart_319495 : Nat := 118140960795 + 319495 * 2 ^ 59
def prefixEnd_319495 : Nat := 4983230072969 + 3 ^ 40 * 319495 * 2
def baseEnd_319495 : Nat := 54684833902777569347725

theorem tailTrace_319495 : CollatzResearch.WordTrace tailWord_319495 prefixEnd_319495 54684833902777569347725 := by
  unfold tailWord_319495
  simp only [CollatzResearch.WordTrace]
  refine ⟨11652939977531655246935939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7768626651687770164623959 11652939977531655246935939)
  ·
    refine ⟨17479409966297482870403909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11652939977531655246935939 17479409966297482870403909)
    ·
      refine ⟨3277389368680778038200733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17479409966297482870403909 3277389368680778038200733)
      ·
        refine ⟨1229021013255291764325275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3277389368680778038200733 1229021013255291764325275)
        ·
          refine ⟨1843531519882937646487913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229021013255291764325275 1843531519882937646487913)
          ·
            refine ⟨1382648639912203234865935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1843531519882937646487913 1382648639912203234865935)
            ·
              refine ⟨2073972959868304852298903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1382648639912203234865935 2073972959868304852298903)
              ·
                refine ⟨3110959439802457278448355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2073972959868304852298903 3110959439802457278448355)
                ·
                  refine ⟨4666439159703685917672533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3110959439802457278448355 4666439159703685917672533)
                  ·
                    refine ⟨54684833902777569347725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4666439159703685917672533 54684833902777569347725)
                    ·
                      rfl

theorem cell23_319495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_319495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319495 prefixEnd_319495 := by exact prefixLift 319495
  have htrace : WordTrace (prefixWord ++ tailWord_319495) baseStart_319495 baseEnd_319495 := by
    simpa [prefixWord, tailWord_319495, baseEnd_319495] using wordTrace_append hprefix tailTrace_319495
  have hstable : (prefixWord ++ tailWord_319495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319495).length < 2 ^ (prefixWord ++ tailWord_319495).sum := by decide
  have hdescent : baseEnd_319495 < baseStart_319495 := by decide
  rcases family_descends (prefixWord ++ tailWord_319495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319519 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 4, 2, 2]
def baseStart_319519 : Nat := 118140960795 + 319519 * 2 ^ 59
def prefixEnd_319519 : Nat := 4983230072969 + 3 ^ 40 * 319519 * 2
def baseEnd_319519 : Nat := 164066825244040614143065

theorem tailTrace_319519 : CollatzResearch.WordTrace tailWord_319519 prefixEnd_319519 164066825244040614143065 := by
  unfold tailWord_319519
  simp only [CollatzResearch.WordTrace]
  refine ⟨11653815329444707345809611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7769210219629804897206407 11653815329444707345809611)
  ·
    refine ⟨17480722994167061018714417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11653815329444707345809611 17480722994167061018714417)
    ·
      refine ⟨13110542245625295764035813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17480722994167061018714417 13110542245625295764035813)
      ·
        refine ⟨2458226671054742955756715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13110542245625295764035813 2458226671054742955756715)
        ·
          refine ⟨3687340006582114433635073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2458226671054742955756715 3687340006582114433635073)
          ·
            refine ⟨2765505004936585825226305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3687340006582114433635073 2765505004936585825226305)
            ·
              refine ⟨2074128753702439368919729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2765505004936585825226305 2074128753702439368919729)
              ·
                refine ⟨1555596565276829526689797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2074128753702439368919729 1555596565276829526689797)
                ·
                  refine ⟨291674355989405536254337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1555596565276829526689797 291674355989405536254337)
                  ·
                    refine ⟨218755766992054152190753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 291674355989405536254337 218755766992054152190753)
                    ·
                      refine ⟨164066825244040614143065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 218755766992054152190753 164066825244040614143065)
                      ·
                        rfl

theorem cell23_319519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_319519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319519 prefixEnd_319519 := by exact prefixLift 319519
  have htrace : WordTrace (prefixWord ++ tailWord_319519) baseStart_319519 baseEnd_319519 := by
    simpa [prefixWord, tailWord_319519, baseEnd_319519] using wordTrace_append hprefix tailTrace_319519
  have hstable : (prefixWord ++ tailWord_319519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319519).length < 2 ^ (prefixWord ++ tailWord_319519).sum := by decide
  have hdescent : baseEnd_319519 < baseStart_319519 := by decide
  rcases family_descends (prefixWord ++ tailWord_319519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319536 : List Nat := [2, 1, 1, 1, 2, 5, 3, 2, 2, 2, 2]
def baseStart_319536 : Nat := 118140960795 + 319536 * 2 ^ 59
def prefixEnd_319536 : Nat := 4983230072969 + 3 ^ 40 * 319536 * 2
def baseEnd_319536 : Nat := 164075554415167047630487

theorem tailTrace_319536 : CollatzResearch.WordTrace tailWord_319536 prefixEnd_319536 164075554415167047630487 := by
  unfold tailWord_319536
  simp only [CollatzResearch.WordTrace]
  refine ⟨5827217685191559624589231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7769623580255412832785641 5827217685191559624589231)
  ·
    refine ⟨8740826527787339436883847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5827217685191559624589231 8740826527787339436883847)
    ·
      refine ⟨13111239791681009155325771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8740826527787339436883847 13111239791681009155325771)
      ·
        refine ⟨19666859687521513732988657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13111239791681009155325771 19666859687521513732988657)
        ·
          refine ⟨14750144765641135299741493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19666859687521513732988657 14750144765641135299741493)
          ·
            refine ⟨1382826071778856434350765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14750144765641135299741493 1382826071778856434350765)
            ·
              refine ⟨518559776917071162881537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1382826071778856434350765 518559776917071162881537)
              ·
                refine ⟨388919832687803372161153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518559776917071162881537 388919832687803372161153)
                ·
                  refine ⟨291689874515852529120865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388919832687803372161153 291689874515852529120865)
                  ·
                    refine ⟨218767405886889396840649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 291689874515852529120865 218767405886889396840649)
                    ·
                      refine ⟨164075554415167047630487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 218767405886889396840649 164075554415167047630487)
                      ·
                        rfl

theorem cell23_319536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 2, 2, 2].length) (baseStart_319536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319536 prefixEnd_319536 := by exact prefixLift 319536
  have htrace : WordTrace (prefixWord ++ tailWord_319536) baseStart_319536 baseEnd_319536 := by
    simpa [prefixWord, tailWord_319536, baseEnd_319536] using wordTrace_append hprefix tailTrace_319536
  have hstable : (prefixWord ++ tailWord_319536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319536).length < 2 ^ (prefixWord ++ tailWord_319536).sum := by decide
  have hdescent : baseEnd_319536 < baseStart_319536 := by decide
  rcases family_descends (prefixWord ++ tailWord_319536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319552 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 3]
def baseStart_319552 : Nat := 118140960795 + 319552 * 2 ^ 59
def prefixEnd_319552 : Nat := 4983230072969 + 3 ^ 40 * 319552 * 2
def baseEnd_319552 : Nat := 164083770105638985030413

theorem tailTrace_319552 : CollatzResearch.WordTrace tailWord_319552 prefixEnd_319552 164083770105638985030413 := by
  unfold tailWord_319552
  simp only [CollatzResearch.WordTrace]
  refine ⟨5827509469162576990880455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7770012625550102654507273 5827509469162576990880455)
  ·
    refine ⟨8741264203743865486320683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5827509469162576990880455 8741264203743865486320683)
    ·
      refine ⟨13111896305615798229481025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8741264203743865486320683 13111896305615798229481025)
      ·
        refine ⟨9833922229211848672110769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13111896305615798229481025 9833922229211848672110769)
        ·
          refine ⟨7375441671908886504083077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9833922229211848672110769 7375441671908886504083077)
          ·
            refine ⟨1382895313482916219515577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7375441671908886504083077 1382895313482916219515577)
            ·
              refine ⟨1037171485112187164636683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1382895313482916219515577 1037171485112187164636683)
              ·
                refine ⟨1555757227668280746955025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1037171485112187164636683 1555757227668280746955025)
                ·
                  refine ⟨1166817920751210560216269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1555757227668280746955025 1166817920751210560216269)
                  ·
                    refine ⟨437556720281703960081101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1166817920751210560216269 437556720281703960081101)
                    ·
                      refine ⟨164083770105638985030413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 437556720281703960081101 164083770105638985030413)
                      ·
                        rfl

theorem cell23_319552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_319552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319552 prefixEnd_319552 := by exact prefixLift 319552
  have htrace : WordTrace (prefixWord ++ tailWord_319552) baseStart_319552 baseEnd_319552 := by
    simpa [prefixWord, tailWord_319552, baseEnd_319552] using wordTrace_append hprefix tailTrace_319552
  have hstable : (prefixWord ++ tailWord_319552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319552).length < 2 ^ (prefixWord ++ tailWord_319552).sum := by decide
  have hdescent : baseEnd_319552 < baseStart_319552 := by decide
  rcases family_descends (prefixWord ++ tailWord_319552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319555 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 6, 5]
def baseStart_319555 : Nat := 118140960795 + 319555 * 2 ^ 59
def prefixEnd_319555 : Nat := 4983230072969 + 3 ^ 40 * 319555 * 2
def baseEnd_319555 : Nat := 54695103515867491097633

theorem tailTrace_319555 : CollatzResearch.WordTrace tailWord_319555 prefixEnd_319555 54695103515867491097633 := by
  unfold tailWord_319555
  simp only [CollatzResearch.WordTrace]
  refine ⟨11655128357314285494120119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7770085571542856996080079 11655128357314285494120119)
  ·
    refine ⟨17482692535971428241180179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11655128357314285494120119 17482692535971428241180179)
    ·
      refine ⟨26224038803957142361770269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17482692535971428241180179 26224038803957142361770269)
      ·
        refine ⟨9834014551483928385663851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26224038803957142361770269 9834014551483928385663851)
        ·
          refine ⟨14751021827225892578495777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9834014551483928385663851 14751021827225892578495777)
          ·
            refine ⟨11063266370419419433871833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14751021827225892578495777 11063266370419419433871833)
            ·
              refine ⟨8297449777814564575403875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11063266370419419433871833 8297449777814564575403875)
              ·
                refine ⟨12446174666721846863105813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8297449777814564575403875 12446174666721846863105813)
                ·
                  refine ⟨583414437502586571708085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12446174666721846863105813 583414437502586571708085)
                  ·
                    refine ⟨54695103515867491097633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 583414437502586571708085 54695103515867491097633)
                    ·
                      rfl

theorem cell23_319555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 5].length) (baseStart_319555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319555 prefixEnd_319555 := by exact prefixLift 319555
  have htrace : WordTrace (prefixWord ++ tailWord_319555) baseStart_319555 baseEnd_319555 := by
    simpa [prefixWord, tailWord_319555, baseEnd_319555] using wordTrace_append hprefix tailTrace_319555
  have hstable : (prefixWord ++ tailWord_319555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319555).length < 2 ^ (prefixWord ++ tailWord_319555).sum := by decide
  have hdescent : baseEnd_319555 < baseStart_319555 := by decide
  rcases family_descends (prefixWord ++ tailWord_319555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319572 : List Nat := [2, 4, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_319572 : Nat := 118140960795 + 319572 * 2 ^ 59
def prefixEnd_319572 : Nat := 4983230072969 + 3 ^ 40 * 319572 * 2
def baseEnd_319572 : Nat := 54698013239576302260107

theorem tailTrace_319572 : CollatzResearch.WordTrace tailWord_319572 prefixEnd_319572 54698013239576302260107 := by
  unfold tailWord_319572
  simp only [CollatzResearch.WordTrace]
  refine ⟨5827874199126348698744485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7770498932168464931659313 5827874199126348698744485)
  ·
    refine ⟨1092726412336190381014591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5827874199126348698744485 1092726412336190381014591)
    ·
      refine ⟨1639089618504285571521887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1092726412336190381014591 1639089618504285571521887)
      ·
        refine ⟨2458634427756428357282831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1639089618504285571521887 2458634427756428357282831)
        ·
          refine ⟨3687951641634642535924247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2458634427756428357282831 3687951641634642535924247)
          ·
            refine ⟨5531927462451963803886371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3687951641634642535924247 5531927462451963803886371)
            ·
              refine ⟨8297891193677945705829557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5531927462451963803886371 8297891193677945705829557)
              ·
                refine ⟨777927299407307409921521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8297891193677945705829557 777927299407307409921521)
                ·
                  refine ⟨583445474555480557441141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 777927299407307409921521 583445474555480557441141)
                  ·
                    refine ⟨54698013239576302260107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 583445474555480557441141 54698013239576302260107)
                    ·
                      rfl

theorem cell23_319572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_319572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319572 prefixEnd_319572 := by exact prefixLift 319572
  have htrace : WordTrace (prefixWord ++ tailWord_319572) baseStart_319572 baseEnd_319572 := by
    simpa [prefixWord, tailWord_319572, baseEnd_319572] using wordTrace_append hprefix tailTrace_319572
  have hstable : (prefixWord ++ tailWord_319572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319572).length < 2 ^ (prefixWord ++ tailWord_319572).sum := by decide
  have hdescent : baseEnd_319572 < baseStart_319572 := by decide
  rcases family_descends (prefixWord ++ tailWord_319572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319635 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 8]
def baseStart_319635 : Nat := 118140960795 + 319635 * 2 ^ 59
def prefixEnd_319635 : Nat := 4983230072969 + 3 ^ 40 * 319635 * 2
def baseEnd_319635 : Nat := 164126388999962160292531

theorem tailTrace_319635 : CollatzResearch.WordTrace tailWord_319635 prefixEnd_319635 164126388999962160292531 := by
  unfold tailWord_319635
  simp only [CollatzResearch.WordTrace]
  refine ⟨11658046197024459157032359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7772030798016306104688239 11658046197024459157032359)
  ·
    refine ⟨17487069295536688735548539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11658046197024459157032359 17487069295536688735548539)
    ·
      refine ⟨26230603943305033103322809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17487069295536688735548539 26230603943305033103322809)
      ·
        refine ⟨19672952957478774827492107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26230603943305033103322809 19672952957478774827492107)
        ·
          refine ⟨29509429436218162241238161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19672952957478774827492107 29509429436218162241238161)
          ·
            refine ⟨22132072077163621680928621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29509429436218162241238161 22132072077163621680928621)
            ·
              refine ⟨8299527028936358130348233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22132072077163621680928621 8299527028936358130348233)
              ·
                refine ⟨6224645271702268597761175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8299527028936358130348233 6224645271702268597761175)
                ·
                  refine ⟨9336967907553402896641763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6224645271702268597761175 9336967907553402896641763)
                  ·
                    refine ⟨14005451861330104344962645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9336967907553402896641763 14005451861330104344962645)
                    ·
                      refine ⟨164126388999962160292531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 14005451861330104344962645 164126388999962160292531)
                      ·
                        rfl

theorem cell23_319635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_319635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319635 prefixEnd_319635 := by exact prefixLift 319635
  have htrace : WordTrace (prefixWord ++ tailWord_319635) baseStart_319635 baseEnd_319635 := by
    simpa [prefixWord, tailWord_319635, baseEnd_319635] using wordTrace_append hprefix tailTrace_319635
  have hstable : (prefixWord ++ tailWord_319635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319635).length < 2 ^ (prefixWord ++ tailWord_319635).sum := by decide
  have hdescent : baseEnd_319635 < baseStart_319635 := by decide
  rcases family_descends (prefixWord ++ tailWord_319635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319649 : List Nat := [1, 2, 3, 3, 1, 3, 2, 2, 6]
def baseStart_319649 : Nat := 118140960795 + 319649 * 2 ^ 59
def prefixEnd_319649 : Nat := 4983230072969 + 3 ^ 40 * 319649 * 2
def baseEnd_319649 : Nat := 18237064192125011724163

theorem tailTrace_319649 : CollatzResearch.WordTrace tailWord_319649 prefixEnd_319649 18237064192125011724163 := by
  unfold tailWord_319649
  simp only [CollatzResearch.WordTrace]
  refine ⟨11658556818973739548042001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7772371212649159698694667 11658556818973739548042001)
  ·
    refine ⟨8743917614230304661031501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11658556818973739548042001 8743917614230304661031501)
    ·
      refine ⟨3278969105336364247886813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8743917614230304661031501 3278969105336364247886813)
      ·
        refine ⟨1229613414501136592957555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3278969105336364247886813 1229613414501136592957555)
        ·
          refine ⟨1844420121751704889436333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229613414501136592957555 1844420121751704889436333)
          ·
            refine ⟨691657545656889333538625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1844420121751704889436333 691657545656889333538625)
            ·
              refine ⟨518743159242667000153969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 691657545656889333538625 518743159242667000153969)
              ·
                refine ⟨389057369432000250115477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518743159242667000153969 389057369432000250115477)
                ·
                  refine ⟨18237064192125011724163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 389057369432000250115477 18237064192125011724163)
                  ·
                    rfl

theorem cell23_319649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 6].length) (baseStart_319649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319649 prefixEnd_319649 := by exact prefixLift 319649
  have htrace : WordTrace (prefixWord ++ tailWord_319649) baseStart_319649 baseEnd_319649 := by
    simpa [prefixWord, tailWord_319649, baseEnd_319649] using wordTrace_append hprefix tailTrace_319649
  have hstable : (prefixWord ++ tailWord_319649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319649).length < 2 ^ (prefixWord ++ tailWord_319649).sum := by decide
  have hdescent : baseEnd_319649 < baseStart_319649 := by decide
  rcases family_descends (prefixWord ++ tailWord_319649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319712 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 6]
def baseStart_319712 : Nat := 118140960795 + 319712 * 2 ^ 59
def prefixEnd_319712 : Nat := 4983230072969 + 3 ^ 40 * 319712 * 2
def baseEnd_319712 : Nat := 164165927010358359029677

theorem tailTrace_319712 : CollatzResearch.WordTrace tailWord_319712 prefixEnd_319712 164165927010358359029677 := by
  unfold tailWord_319712
  simp only [CollatzResearch.WordTrace]
  refine ⟨5830427308872750653792695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7773903078497000871723593 5830427308872750653792695)
  ·
    refine ⟨8745640963309125980689043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5830427308872750653792695 8745640963309125980689043)
    ·
      refine ⟨13118461444963688971033565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8745640963309125980689043 13118461444963688971033565)
      ·
        refine ⟨4919423041861383364137587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13118461444963688971033565 4919423041861383364137587)
        ·
          refine ⟨7379134562792075046206381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4919423041861383364137587 7379134562792075046206381)
          ·
            refine ⟨2767175461047028142327393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7379134562792075046206381 2767175461047028142327393)
            ·
              refine ⟨2075381595785271106745545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2767175461047028142327393 2075381595785271106745545)
              ·
                refine ⟨1556536196838953330059159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2075381595785271106745545 1556536196838953330059159)
                ·
                  refine ⟨2334804295258429995088739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1556536196838953330059159 2334804295258429995088739)
                  ·
                    refine ⟨3502206442887644992633109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2334804295258429995088739 3502206442887644992633109)
                    ·
                      refine ⟨164165927010358359029677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3502206442887644992633109 164165927010358359029677)
                      ·
                        rfl

theorem cell23_319712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_319712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319712 prefixEnd_319712 := by exact prefixLift 319712
  have htrace : WordTrace (prefixWord ++ tailWord_319712) baseStart_319712 baseEnd_319712 := by
    simpa [prefixWord, tailWord_319712, baseEnd_319712] using wordTrace_append hprefix tailTrace_319712
  have hstable : (prefixWord ++ tailWord_319712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319712).length < 2 ^ (prefixWord ++ tailWord_319712).sum := by decide
  have hdescent : baseEnd_319712 < baseStart_319712 := by decide
  rcases family_descends (prefixWord ++ tailWord_319712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319719 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_319719 : Nat := 118140960795 + 319719 * 2 ^ 59
def prefixEnd_319719 : Nat := 4983230072969 + 3 ^ 40 * 319719 * 2
def baseEnd_319719 : Nat := 164169521374939831642145

theorem tailTrace_319719 : CollatzResearch.WordTrace tailWord_319719 prefixEnd_319719 164169521374939831642145 := by
  unfold tailWord_319719
  simp only [CollatzResearch.WordTrace]
  refine ⟨11661109928720141503090211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7774073285813427668726807 11661109928720141503090211)
  ·
    refine ⟨17491664893080212254635317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11661109928720141503090211 17491664893080212254635317)
    ·
      refine ⟨1639843583726269898872061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17491664893080212254635317 1639843583726269898872061)
      ·
        refine ⟨614941343897351212077023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1639843583726269898872061 614941343897351212077023)
        ·
          refine ⟨922412015846026818115535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614941343897351212077023 922412015846026818115535)
          ·
            refine ⟨1383618023769040227173303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 922412015846026818115535 1383618023769040227173303)
            ·
              refine ⟨2075427035653560340759955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383618023769040227173303 2075427035653560340759955)
              ·
                refine ⟨3113140553480340511139933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2075427035653560340759955 3113140553480340511139933)
                ·
                  refine ⟨1167427707555127691677475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3113140553480340511139933 1167427707555127691677475)
                  ·
                    refine ⟨1751141561332691537516213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1167427707555127691677475 1751141561332691537516213)
                    ·
                      refine ⟨164169521374939831642145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1751141561332691537516213 164169521374939831642145)
                      ·
                        rfl

theorem cell23_319719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_319719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319719 prefixEnd_319719 := by exact prefixLift 319719
  have htrace : WordTrace (prefixWord ++ tailWord_319719) baseStart_319719 baseEnd_319719 := by
    simpa [prefixWord, tailWord_319719, baseEnd_319719] using wordTrace_append hprefix tailTrace_319719
  have hstable : (prefixWord ++ tailWord_319719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319719).length < 2 ^ (prefixWord ++ tailWord_319719).sum := by decide
  have hdescent : baseEnd_319719 < baseStart_319719 := by decide
  rcases family_descends (prefixWord ++ tailWord_319719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319722 : List Nat := [3, 1, 3, 1, 1, 2, 2, 10]
def baseStart_319722 : Nat := 118140960795 + 319722 * 2 ^ 59
def prefixEnd_319722 : Nat := 4983230072969 + 3 ^ 40 * 319722 * 2
def baseEnd_319722 : Nat := 6080409696922345181653

theorem tailTrace_319722 : CollatzResearch.WordTrace tailWord_319722 prefixEnd_319722 6080409696922345181653 := by
  unfold tailWord_319722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2915304836927318253862355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7774146231806182010299613 2915304836927318253862355)
  ·
    refine ⟨4372957255390977380793533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2915304836927318253862355 4372957255390977380793533)
    ·
      refine ⟨1639858970771616517797575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4372957255390977380793533 1639858970771616517797575)
      ·
        refine ⟨2459788456157424776696363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1639858970771616517797575 2459788456157424776696363)
        ·
          refine ⟨3689682684236137165044545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2459788456157424776696363 3689682684236137165044545)
          ·
            refine ⟨2767262013177102873783409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3689682684236137165044545 2767262013177102873783409)
            ·
              refine ⟨2075446509882827155337557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2767262013177102873783409 2075446509882827155337557)
              ·
                refine ⟨6080409696922345181653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2075446509882827155337557 6080409696922345181653)
                ·
                  rfl

theorem cell23_319722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 10].length) (baseStart_319722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319722 prefixEnd_319722 := by exact prefixLift 319722
  have htrace : WordTrace (prefixWord ++ tailWord_319722) baseStart_319722 baseEnd_319722 := by
    simpa [prefixWord, tailWord_319722, baseEnd_319722] using wordTrace_append hprefix tailTrace_319722
  have hstable : (prefixWord ++ tailWord_319722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319722).length < 2 ^ (prefixWord ++ tailWord_319722).sum := by decide
  have hdescent : baseEnd_319722 < baseStart_319722 := by decide
  rcases family_descends (prefixWord ++ tailWord_319722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319729 : List Nat := [1, 2, 2, 2, 2, 1, 5, 1, 1, 2, 4]
def baseStart_319729 : Nat := 118140960795 + 319729 * 2 ^ 59
def prefixEnd_319729 : Nat := 4983230072969 + 3 ^ 40 * 319729 * 2
def baseEnd_319729 : Nat := 164174656181484792517099

theorem tailTrace_319729 : CollatzResearch.WordTrace tailWord_319729 prefixEnd_319729 164174656181484792517099 := by
  unfold tailWord_319729
  simp only [CollatzResearch.WordTrace]
  refine ⟨11661474658683913210954241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7774316439122608807302827 11661474658683913210954241)
  ·
    refine ⟨8746105994012934908215681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11661474658683913210954241 8746105994012934908215681)
    ·
      refine ⟨6559579495509701181161761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8746105994012934908215681 6559579495509701181161761)
      ·
        refine ⟨4919684621632275885871321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6559579495509701181161761 4919684621632275885871321)
        ·
          refine ⟨3689763466224206914403491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4919684621632275885871321 3689763466224206914403491)
          ·
            refine ⟨5534645199336310371605237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3689763466224206914403491 5534645199336310371605237)
            ·
              refine ⟨518872987437779097337991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5534645199336310371605237 518872987437779097337991)
              ·
                refine ⟨778309481156668646006987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518872987437779097337991 778309481156668646006987)
                ·
                  refine ⟨1167464221735002969010481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 778309481156668646006987 1167464221735002969010481)
                  ·
                    refine ⟨875598166301252226757861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1167464221735002969010481 875598166301252226757861)
                    ·
                      refine ⟨164174656181484792517099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 875598166301252226757861 164174656181484792517099)
                      ·
                        rfl

theorem cell23_319729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_319729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319729 prefixEnd_319729 := by exact prefixLift 319729
  have htrace : WordTrace (prefixWord ++ tailWord_319729) baseStart_319729 baseEnd_319729 := by
    simpa [prefixWord, tailWord_319729, baseEnd_319729] using wordTrace_append hprefix tailTrace_319729
  have hstable : (prefixWord ++ tailWord_319729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319729).length < 2 ^ (prefixWord ++ tailWord_319729).sum := by decide
  have hdescent : baseEnd_319729 < baseStart_319729 := by decide
  rcases family_descends (prefixWord ++ tailWord_319729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319767 : List Nat := [1, 1, 3, 4, 1, 3, 3, 2, 1, 2, 2]
def baseStart_319767 : Nat := 118140960795 + 319767 * 2 ^ 59
def prefixEnd_319767 : Nat := 4983230072969 + 3 ^ 40 * 319767 * 2
def baseEnd_319767 : Nat := 164194168446355643841925

theorem tailTrace_319767 : CollatzResearch.WordTrace tailWord_319767 prefixEnd_319767 164194168446355643841925 := by
  unfold tailWord_319767
  simp only [CollatzResearch.WordTrace]
  refine ⟨11662860632546245700837555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7775240421697497133891703 11662860632546245700837555)
  ·
    refine ⟨17494290948819368551256333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11662860632546245700837555 17494290948819368551256333)
    ·
      refine ⟨6560359105807263206721125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17494290948819368551256333 6560359105807263206721125)
      ·
        refine ⟨1230067332338861851260211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6560359105807263206721125 1230067332338861851260211)
        ·
          refine ⟨1845100998508292776890317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1230067332338861851260211 1845100998508292776890317)
          ·
            refine ⟨691912874440609791333869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1845100998508292776890317 691912874440609791333869)
            ·
              refine ⟨259467327915228671750201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 691912874440609791333869 259467327915228671750201)
              ·
                refine ⟨194600495936421503812651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259467327915228671750201 194600495936421503812651)
                ·
                  refine ⟨291900743904632255718977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194600495936421503812651 291900743904632255718977)
                  ·
                    refine ⟨218925557928474191789233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 291900743904632255718977 218925557928474191789233)
                    ·
                      refine ⟨164194168446355643841925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 218925557928474191789233 164194168446355643841925)
                      ·
                        rfl

theorem cell23_319767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_319767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319767 prefixEnd_319767 := by exact prefixLift 319767
  have htrace : WordTrace (prefixWord ++ tailWord_319767) baseStart_319767 baseEnd_319767 := by
    simpa [prefixWord, tailWord_319767, baseEnd_319767] using wordTrace_append hprefix tailTrace_319767
  have hstable : (prefixWord ++ tailWord_319767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319767).length < 2 ^ (prefixWord ++ tailWord_319767).sum := by decide
  have hdescent : baseEnd_319767 < baseStart_319767 := by decide
  rcases family_descends (prefixWord ++ tailWord_319767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319793 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 3, 3, 2]
def baseStart_319793 : Nat := 118140960795 + 319793 * 2 ^ 59
def prefixEnd_319793 : Nat := 4983230072969 + 3 ^ 40 * 319793 * 2
def baseEnd_319793 : Nat := 164207518943372542116805

theorem tailTrace_319793 : CollatzResearch.WordTrace tailWord_319793 prefixEnd_319793 164207518943372542116805 := by
  unfold tailWord_319793
  simp only [CollatzResearch.WordTrace]
  refine ⟨11663808930452052141284033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7775872620301368094189355 11663808930452052141284033)
  ·
    refine ⟨8747856697839039105963025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11663808930452052141284033 8747856697839039105963025)
    ·
      refine ⟨6560892523379279329472269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8747856697839039105963025 6560892523379279329472269)
      ·
        refine ⟨2460334696267229748552101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6560892523379279329472269 2460334696267229748552101)
        ·
          refine ⟨461312755550105577853519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2460334696267229748552101 461312755550105577853519)
          ·
            refine ⟨691969133325158366780279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461312755550105577853519 691969133325158366780279)
            ·
              refine ⟨1037953699987737550170419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 691969133325158366780279 1037953699987737550170419)
              ·
                refine ⟨1556930549981606325255629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1037953699987737550170419 1556930549981606325255629)
                ·
                  refine ⟨583848956243102371970861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1556930549981606325255629 583848956243102371970861)
                  ·
                    refine ⟨218943358591163389489073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 583848956243102371970861 218943358591163389489073)
                    ·
                      refine ⟨164207518943372542116805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 218943358591163389489073 164207518943372542116805)
                      ·
                        rfl

theorem cell23_319793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_319793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319793 prefixEnd_319793 := by exact prefixLift 319793
  have htrace : WordTrace (prefixWord ++ tailWord_319793) baseStart_319793 baseEnd_319793 := by
    simpa [prefixWord, tailWord_319793, baseEnd_319793] using wordTrace_append hprefix tailTrace_319793
  have hstable : (prefixWord ++ tailWord_319793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319793).length < 2 ^ (prefixWord ++ tailWord_319793).sum := by decide
  have hdescent : baseEnd_319793 < baseStart_319793 := by decide
  rcases family_descends (prefixWord ++ tailWord_319793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319839 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 3]
def baseStart_319839 : Nat := 118140960795 + 319839 * 2 ^ 59
def prefixEnd_319839 : Nat := 4983230072969 + 3 ^ 40 * 319839 * 2
def baseEnd_319839 : Nat := 164231139053479362141593

theorem tailTrace_319839 : CollatzResearch.WordTrace tailWord_319839 prefixEnd_319839 164231139053479362141593 := by
  unfold tailWord_319839
  simp only [CollatzResearch.WordTrace]
  refine ⟨11665486688285401997458571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7776991125523601331639047 11665486688285401997458571)
  ·
    refine ⟨17498230032428102996187857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11665486688285401997458571 17498230032428102996187857)
    ·
      refine ⟨13123672524321077247140893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17498230032428102996187857 13123672524321077247140893)
      ·
        refine ⟨4921377196620403967677835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13123672524321077247140893 4921377196620403967677835)
        ·
          refine ⟨7382065794930605951516753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4921377196620403967677835 7382065794930605951516753)
          ·
            refine ⟨5536549346197954463637565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7382065794930605951516753 5536549346197954463637565)
            ·
              refine ⟨2076206004824232923864087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5536549346197954463637565 2076206004824232923864087)
              ·
                refine ⟨3114309007236349385796131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076206004824232923864087 3114309007236349385796131)
                ·
                  refine ⟨4671463510854524078694197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114309007236349385796131 4671463510854524078694197)
                  ·
                    refine ⟨437949704142611632377581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4671463510854524078694197 437949704142611632377581)
                    ·
                      refine ⟨164231139053479362141593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 437949704142611632377581 164231139053479362141593)
                      ·
                        rfl

theorem cell23_319839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_319839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319839 prefixEnd_319839 := by exact prefixLift 319839
  have htrace : WordTrace (prefixWord ++ tailWord_319839) baseStart_319839 baseEnd_319839 := by
    simpa [prefixWord, tailWord_319839, baseEnd_319839] using wordTrace_append hprefix tailTrace_319839
  have hstable : (prefixWord ++ tailWord_319839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319839).length < 2 ^ (prefixWord ++ tailWord_319839).sum := by decide
  have hdescent : baseEnd_319839 < baseStart_319839 := by decide
  rcases family_descends (prefixWord ++ tailWord_319839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319896 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 1, 3, 4]
def baseStart_319896 : Nat := 118140960795 + 319896 * 2 ^ 59
def prefixEnd_319896 : Nat := 4983230072969 + 3 ^ 40 * 319896 * 2
def baseEnd_319896 : Nat := 164260407450785639128831

theorem tailTrace_319896 : CollatzResearch.WordTrace tailWord_319896 prefixEnd_319896 164260407450785639128831 := by
  unfold tailWord_319896
  simp only [CollatzResearch.WordTrace]
  refine ⟨5833782824539450366141771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7778377099385933821522361 5833782824539450366141771)
  ·
    refine ⟨8750674236809175549212657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5833782824539450366141771 8750674236809175549212657)
    ·
      refine ⟨6563005677606881661909493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8750674236809175549212657 6563005677606881661909493)
      ·
        refine ⟨615281782275645155804015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6563005677606881661909493 615281782275645155804015)
        ·
          refine ⟨922922673413467733706023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615281782275645155804015 922922673413467733706023)
          ·
            refine ⟨1384384010120201600559035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 922922673413467733706023 1384384010120201600559035)
            ·
              refine ⟨2076576015180302400838553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1384384010120201600559035 2076576015180302400838553)
              ·
                refine ⟨1557432011385226800628915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2076576015180302400838553 1557432011385226800628915)
                ·
                  refine ⟨2336148017077840200943373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1557432011385226800628915 2336148017077840200943373)
                  ·
                    refine ⟨876055506404190075353765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2336148017077840200943373 876055506404190075353765)
                    ·
                      refine ⟨164260407450785639128831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 876055506404190075353765 164260407450785639128831)
                      ·
                        rfl

theorem cell23_319896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_319896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319896 prefixEnd_319896 := by exact prefixLift 319896
  have htrace : WordTrace (prefixWord ++ tailWord_319896) baseStart_319896 baseEnd_319896 := by
    simpa [prefixWord, tailWord_319896, baseEnd_319896] using wordTrace_append hprefix tailTrace_319896
  have hstable : (prefixWord ++ tailWord_319896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319896).length < 2 ^ (prefixWord ++ tailWord_319896).sum := by decide
  have hdescent : baseEnd_319896 < baseStart_319896 := by decide
  rcases family_descends (prefixWord ++ tailWord_319896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319909 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 2, 4, 4]
def baseStart_319909 : Nat := 118140960795 + 319909 * 2 ^ 59
def prefixEnd_319909 : Nat := 4983230072969 + 3 ^ 40 * 319909 * 2
def baseEnd_319909 : Nat := 164267082699294088266271

theorem tailTrace_319909 : CollatzResearch.WordTrace tailWord_319909 prefixEnd_319909 164267082699294088266271 := by
  unfold tailWord_319909
  simp only [CollatzResearch.WordTrace]
  refine ⟨11668039798031803952506781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7778693198687869301671187 11668039798031803952506781)
  ·
    refine ⟨4375514924261926482190043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11668039798031803952506781 4375514924261926482190043)
    ·
      refine ⟨6563272386392889723285065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4375514924261926482190043 6563272386392889723285065)
      ·
        refine ⟨4922454289794667292463799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6563272386392889723285065 4922454289794667292463799)
        ·
          refine ⟨7383681434692000938695699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4922454289794667292463799 7383681434692000938695699)
          ·
            refine ⟨11075522152038001408043549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7383681434692000938695699 11075522152038001408043549)
            ·
              refine ⟨4153320807014250528016331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11075522152038001408043549 4153320807014250528016331)
              ·
                refine ⟨6229981210521375792024497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4153320807014250528016331 6229981210521375792024497)
                ·
                  refine ⟨4672485907891031844018373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6229981210521375792024497 4672485907891031844018373)
                  ·
                    refine ⟨876091107729568470753445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4672485907891031844018373 876091107729568470753445)
                    ·
                      refine ⟨164267082699294088266271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 876091107729568470753445 164267082699294088266271)
                      ·
                        rfl

theorem cell23_319909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_319909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319909 prefixEnd_319909 := by exact prefixLift 319909
  have htrace : WordTrace (prefixWord ++ tailWord_319909) baseStart_319909 baseEnd_319909 := by
    simpa [prefixWord, tailWord_319909, baseEnd_319909] using wordTrace_append hprefix tailTrace_319909
  have hstable : (prefixWord ++ tailWord_319909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319909).length < 2 ^ (prefixWord ++ tailWord_319909).sum := by decide
  have hdescent : baseEnd_319909 < baseStart_319909 := by decide
  rcases family_descends (prefixWord ++ tailWord_319909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319914 : List Nat := [3, 1, 6, 1, 1, 2, 1, 3, 5]
def baseStart_319914 : Nat := 118140960795 + 319914 * 2 ^ 59
def prefixEnd_319914 : Nat := 4983230072969 + 3 ^ 40 * 319914 * 2
def baseEnd_319914 : Nat := 18252183344729618744861

theorem tailTrace_319914 : CollatzResearch.WordTrace tailWord_319914 prefixEnd_319914 18252183344729618744861 := by
  unfold tailWord_319914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2917055540753422451609699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7778814775342459870959197 2917055540753422451609699)
  ·
    refine ⟨4375583311130133677414549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2917055540753422451609699 4375583311130133677414549)
    ·
      refine ⟨205105467709225016128807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4375583311130133677414549 205105467709225016128807)
      ·
        refine ⟨307658201563837524193211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205105467709225016128807 307658201563837524193211)
        ·
          refine ⟨461487302345756286289817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307658201563837524193211 461487302345756286289817)
          ·
            refine ⟨346115476759317214717363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 461487302345756286289817 346115476759317214717363)
            ·
              refine ⟨519173215138975822076045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346115476759317214717363 519173215138975822076045)
              ·
                refine ⟨194689955677115933278517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 519173215138975822076045 194689955677115933278517)
                ·
                  refine ⟨18252183344729618744861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 194689955677115933278517 18252183344729618744861)
                  ·
                    rfl

theorem cell23_319914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 5].length) (baseStart_319914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319914 prefixEnd_319914 := by exact prefixLift 319914
  have htrace : WordTrace (prefixWord ++ tailWord_319914) baseStart_319914 baseEnd_319914 := by
    simpa [prefixWord, tailWord_319914, baseEnd_319914] using wordTrace_append hprefix tailTrace_319914
  have hstable : (prefixWord ++ tailWord_319914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319914).length < 2 ^ (prefixWord ++ tailWord_319914).sum := by decide
  have hdescent : baseEnd_319914 < baseStart_319914 := by decide
  rcases family_descends (prefixWord ++ tailWord_319914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319916 : List Nat := [2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 3]
def baseStart_319916 : Nat := 118140960795 + 319916 * 2 ^ 59
def prefixEnd_319916 : Nat := 4983230072969 + 3 ^ 40 * 319916 * 2
def baseEnd_319916 : Nat := 164270677063875560878739

theorem tailTrace_319916 : CollatzResearch.WordTrace tailWord_319916 prefixEnd_319916 164270677063875560878739 := by
  unfold tailWord_319916
  simp only [CollatzResearch.WordTrace]
  refine ⟨5834147554503222074005801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7778863406004296098674401 5834147554503222074005801)
  ·
    refine ⟨4375610665877416555504351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5834147554503222074005801 4375610665877416555504351)
    ·
      refine ⟨6563415998816124833256527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4375610665877416555504351 6563415998816124833256527)
      ·
        refine ⟨9845123998224187249884791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6563415998816124833256527 9845123998224187249884791)
        ·
          refine ⟨14767685997336280874827187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9845123998224187249884791 14767685997336280874827187)
          ·
            refine ⟨22151528996004421312240781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14767685997336280874827187 22151528996004421312240781)
            ·
              refine ⟨8306823373501657992090293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22151528996004421312240781 8306823373501657992090293)
              ·
                refine ⟨778764691265780436758465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8306823373501657992090293 778764691265780436758465)
                ·
                  refine ⟨584073518449335327568849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 778764691265780436758465 584073518449335327568849)
                  ·
                    refine ⟨438055138837001495676637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 584073518449335327568849 438055138837001495676637)
                    ·
                      refine ⟨164270677063875560878739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 438055138837001495676637 164270677063875560878739)
                      ·
                        rfl

theorem cell23_319916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_319916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319916 prefixEnd_319916 := by exact prefixLift 319916
  have htrace : WordTrace (prefixWord ++ tailWord_319916) baseStart_319916 baseEnd_319916 := by
    simpa [prefixWord, tailWord_319916, baseEnd_319916] using wordTrace_append hprefix tailTrace_319916
  have hstable : (prefixWord ++ tailWord_319916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319916).length < 2 ^ (prefixWord ++ tailWord_319916).sum := by decide
  have hdescent : baseEnd_319916 < baseStart_319916 := by decide
  rcases family_descends (prefixWord ++ tailWord_319916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319933 : List Nat := [1, 4, 1, 2, 2, 3, 1, 2, 2, 2, 3]
def baseStart_319933 : Nat := 118140960795 + 319933 * 2 ^ 59
def prefixEnd_319933 : Nat := 4983230072969 + 3 ^ 40 * 319933 * 2
def baseEnd_319933 : Nat := 164279406235001994366161

theorem tailTrace_319933 : CollatzResearch.WordTrace tailWord_319933 prefixEnd_319933 164279406235001994366161 := by
  unfold tailWord_319933
  simp only [CollatzResearch.WordTrace]
  refine ⟨11668915149944856051380453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7779276766629904034253635 11668915149944856051380453)
  ·
    refine ⟨2187921590614660509633835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11668915149944856051380453 2187921590614660509633835)
    ·
      refine ⟨3281882385921990764450753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2187921590614660509633835 3281882385921990764450753)
      ·
        refine ⟨2461411789441493073338065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3281882385921990764450753 2461411789441493073338065)
        ·
          refine ⟨1846058842081119805003549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2461411789441493073338065 1846058842081119805003549)
          ·
            refine ⟨692272065780419926876331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1846058842081119805003549 692272065780419926876331)
            ·
              refine ⟨1038408098670629890314497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692272065780419926876331 1038408098670629890314497)
              ·
                refine ⟨778806074002972417735873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1038408098670629890314497 778806074002972417735873)
                ·
                  refine ⟨584104555502229313301905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 778806074002972417735873 584104555502229313301905)
                  ·
                    refine ⟨438078416626671984976429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 584104555502229313301905 438078416626671984976429)
                    ·
                      refine ⟨164279406235001994366161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 438078416626671984976429 164279406235001994366161)
                      ·
                        rfl

theorem cell23_319933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_319933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319933 prefixEnd_319933 := by exact prefixLift 319933
  have htrace : WordTrace (prefixWord ++ tailWord_319933) baseStart_319933 baseEnd_319933 := by
    simpa [prefixWord, tailWord_319933, baseEnd_319933] using wordTrace_append hprefix tailTrace_319933
  have hstable : (prefixWord ++ tailWord_319933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319933).length < 2 ^ (prefixWord ++ tailWord_319933).sum := by decide
  have hdescent : baseEnd_319933 < baseStart_319933 := by decide
  rcases family_descends (prefixWord ++ tailWord_319933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319980 : List Nat := [2, 2, 1, 1, 2, 1, 4, 5, 1, 1, 3]
def baseStart_319980 : Nat := 118140960795 + 319980 * 2 ^ 59
def prefixEnd_319980 : Nat := 4983230072969 + 3 ^ 40 * 319980 * 2
def baseEnd_319980 : Nat := 164303539825763310478445

theorem tailTrace_319980 : CollatzResearch.WordTrace tailWord_319980 prefixEnd_319980 164303539825763310478445 := by
  unfold tailWord_319980
  simp only [CollatzResearch.WordTrace]
  refine ⟨5835314690387291539170697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7780419587183055385560929 5835314690387291539170697)
  ·
    refine ⟨4376486017790468654378023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5835314690387291539170697 4376486017790468654378023)
    ·
      refine ⟨6564729026685702981567035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4376486017790468654378023 6564729026685702981567035)
      ·
        refine ⟨9847093540028554472350553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6564729026685702981567035 9847093540028554472350553)
        ·
          refine ⟨7385320155021415854262915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9847093540028554472350553 7385320155021415854262915)
          ·
            refine ⟨11077980232532123781394373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7385320155021415854262915 11077980232532123781394373)
            ·
              refine ⟨2077121293599773209011445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11077980232532123781394373 2077121293599773209011445)
              ·
                refine ⟨194730121274978738344823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2077121293599773209011445 194730121274978738344823)
                ·
                  refine ⟨292095181912468107517235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194730121274978738344823 292095181912468107517235)
                  ·
                    refine ⟨438142772868702161275853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 292095181912468107517235 438142772868702161275853)
                    ·
                      refine ⟨164303539825763310478445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 438142772868702161275853 164303539825763310478445)
                      ·
                        rfl

theorem cell23_319980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 1, 1, 3].length) (baseStart_319980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319980 prefixEnd_319980 := by exact prefixLift 319980
  have htrace : WordTrace (prefixWord ++ tailWord_319980) baseStart_319980 baseEnd_319980 := by
    simpa [prefixWord, tailWord_319980, baseEnd_319980] using wordTrace_append hprefix tailTrace_319980
  have hstable : (prefixWord ++ tailWord_319980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319980).length < 2 ^ (prefixWord ++ tailWord_319980).sum := by decide
  have hdescent : baseEnd_319980 < baseStart_319980 := by decide
  rcases family_descends (prefixWord ++ tailWord_319980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319990 : List Nat := [5, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2]
def baseStart_319990 : Nat := 118140960795 + 319990 * 2 ^ 59
def prefixEnd_319990 : Nat := 4983230072969 + 3 ^ 40 * 319990 * 2
def baseEnd_319990 : Nat := 164308674632308271353399

theorem tailTrace_319990 : CollatzResearch.WordTrace tailWord_319990 prefixEnd_319990 164308674632308271353399 := by
  unfold tailWord_319990
  simp only [CollatzResearch.WordTrace]
  refine ⟨729437131921147174137839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7780662740492236524136949 729437131921147174137839)
  ·
    refine ⟨1094155697881720761206759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 729437131921147174137839 1094155697881720761206759)
    ·
      refine ⟨1641233546822581141810139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1094155697881720761206759 1641233546822581141810139)
      ·
        refine ⟨2461850320233871712715209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1641233546822581141810139 2461850320233871712715209)
        ·
          refine ⟨1846387740175403784536407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2461850320233871712715209 1846387740175403784536407)
          ·
            refine ⟨2769581610263105676804611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1846387740175403784536407 2769581610263105676804611)
            ·
              refine ⟨4154372415394658515206917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2769581610263105676804611 4154372415394658515206917)
              ·
                refine ⟨778944827886498471601297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4154372415394658515206917 778944827886498471601297)
                ·
                  refine ⟨584208620914873853700973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 778944827886498471601297 584208620914873853700973)
                  ·
                    refine ⟨219078232843077695137865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 584208620914873853700973 219078232843077695137865)
                    ·
                      refine ⟨164308674632308271353399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 219078232843077695137865 164308674632308271353399)
                      ·
                        rfl

theorem cell23_319990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_319990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319990 prefixEnd_319990 := by exact prefixLift 319990
  have htrace : WordTrace (prefixWord ++ tailWord_319990) baseStart_319990 baseEnd_319990 := by
    simpa [prefixWord, tailWord_319990, baseEnd_319990] using wordTrace_append hprefix tailTrace_319990
  have hstable : (prefixWord ++ tailWord_319990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319990).length < 2 ^ (prefixWord ++ tailWord_319990).sum := by decide
  have hdescent : baseEnd_319990 < baseStart_319990 := by decide
  rcases family_descends (prefixWord ++ tailWord_319990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320009 : List Nat := [1, 2, 1, 1, 3, 1, 2, 12]
def baseStart_320009 : Nat := 118140960795 + 320009 * 2 ^ 59
def prefixEnd_320009 : Nat := 4983230072969 + 3 ^ 40 * 320009 * 2
def baseEnd_320009 : Nat := 6085867806101618407993

theorem tailTrace_320009 : CollatzResearch.WordTrace tailWord_320009 prefixEnd_320009 6085867806101618407993 := by
  unfold tailWord_320009
  simp only [CollatzResearch.WordTrace]
  refine ⟨11671687097669521031147081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7781124731779680687431387 11671687097669521031147081)
  ·
    refine ⟨8753765323252140773360311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11671687097669521031147081 8753765323252140773360311)
    ·
      refine ⟨13130647984878211160040467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8753765323252140773360311 13130647984878211160040467)
      ·
        refine ⟨19695971977317316740060701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13130647984878211160040467 19695971977317316740060701)
        ·
          refine ⟨7385989491493993777522763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19695971977317316740060701 7385989491493993777522763)
          ·
            refine ⟨11078984237240990666284145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7385989491493993777522763 11078984237240990666284145)
            ·
              refine ⟨8309238177930742999713109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11078984237240990666284145 8309238177930742999713109)
              ·
                refine ⟨6085867806101618407993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 8309238177930742999713109 6085867806101618407993)
                ·
                  rfl

theorem cell23_320009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 12].length) (baseStart_320009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320009 prefixEnd_320009 := by exact prefixLift 320009
  have htrace : WordTrace (prefixWord ++ tailWord_320009) baseStart_320009 baseEnd_320009 := by
    simpa [prefixWord, tailWord_320009, baseEnd_320009] using wordTrace_append hprefix tailTrace_320009
  have hstable : (prefixWord ++ tailWord_320009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320009).length < 2 ^ (prefixWord ++ tailWord_320009).sum := by decide
  have hdescent : baseEnd_320009 < baseStart_320009 := by decide
  rcases family_descends (prefixWord ++ tailWord_320009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320020 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_320020 : Nat := 118140960795 + 320020 * 2 ^ 59
def prefixEnd_320020 : Nat := 4983230072969 + 3 ^ 40 * 320020 * 2
def baseEnd_320020 : Nat := 164324079051943153978261

theorem tailTrace_320020 : CollatzResearch.WordTrace tailWord_320020 prefixEnd_320020 164324079051943153978261 := by
  unfold tailWord_320020
  simp only [CollatzResearch.WordTrace]
  refine ⟨5836044150314834954898757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7781392200419779939865009 5836044150314834954898757)
  ·
    refine ⟨1094258278184031554043517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5836044150314834954898757 1094258278184031554043517)
    ·
      refine ⟨410346854319011832766319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1094258278184031554043517 410346854319011832766319)
      ·
        refine ⟨615520281478517749149479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410346854319011832766319 615520281478517749149479)
        ·
          refine ⟨923280422217776623724219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615520281478517749149479 923280422217776623724219)
          ·
            refine ⟨1384920633326664935586329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923280422217776623724219 1384920633326664935586329)
            ·
              refine ⟨1038690474994998701689747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1384920633326664935586329 1038690474994998701689747)
              ·
                refine ⟨1558035712492498052534621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038690474994998701689747 1558035712492498052534621)
                ·
                  refine ⟨584263392184686769700483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1558035712492498052534621 584263392184686769700483)
                  ·
                    refine ⟨876395088277030154550725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 584263392184686769700483 876395088277030154550725)
                    ·
                      refine ⟨164324079051943153978261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 876395088277030154550725 164324079051943153978261)
                      ·
                        rfl

theorem cell23_320020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_320020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320020 prefixEnd_320020 := by exact prefixLift 320020
  have htrace : WordTrace (prefixWord ++ tailWord_320020) baseStart_320020 baseEnd_320020 := by
    simpa [prefixWord, tailWord_320020, baseEnd_320020] using wordTrace_append hprefix tailTrace_320020
  have hstable : (prefixWord ++ tailWord_320020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320020).length < 2 ^ (prefixWord ++ tailWord_320020).sum := by decide
  have hdescent : baseEnd_320020 < baseStart_320020 := by decide
  rcases family_descends (prefixWord ++ tailWord_320020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320037 : List Nat := [1, 3, 1, 2, 2, 1, 3, 5, 1, 2, 2]
def baseStart_320037 : Nat := 118140960795 + 320037 * 2 ^ 59
def prefixEnd_320037 : Nat := 4983230072969 + 3 ^ 40 * 320037 * 2
def baseEnd_320037 : Nat := 164332808223069587465683

theorem tailTrace_320037 : CollatzResearch.WordTrace tailWord_320037 prefixEnd_320037 164332808223069587465683 := by
  unfold tailWord_320037
  simp only [CollatzResearch.WordTrace]
  refine ⟨11672708341568081813166365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7781805561045387875444243 11672708341568081813166365)
  ·
    refine ⟨4377265628088030679937387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11672708341568081813166365 4377265628088030679937387)
    ·
      refine ⟨6565898442132046019906081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4377265628088030679937387 6565898442132046019906081)
      ·
        refine ⟨4924423831599034514929561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6565898442132046019906081 4924423831599034514929561)
        ·
          refine ⟨3693317873699275886197171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4924423831599034514929561 3693317873699275886197171)
          ·
            refine ⟨5539976810548913829295757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3693317873699275886197171 5539976810548913829295757)
            ·
              refine ⟨2077491303955842685985909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5539976810548913829295757 2077491303955842685985909)
              ·
                refine ⟨194764809745860251811179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2077491303955842685985909 194764809745860251811179)
                ·
                  refine ⟨292147214618790377716769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194764809745860251811179 292147214618790377716769)
                  ·
                    refine ⟨219110410964092783287577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 292147214618790377716769 219110410964092783287577)
                    ·
                      refine ⟨164332808223069587465683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 219110410964092783287577 164332808223069587465683)
                      ·
                        rfl

theorem cell23_320037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 1, 2, 2].length) (baseStart_320037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320037 prefixEnd_320037 := by exact prefixLift 320037
  have htrace : WordTrace (prefixWord ++ tailWord_320037) baseStart_320037 baseEnd_320037 := by
    simpa [prefixWord, tailWord_320037, baseEnd_320037] using wordTrace_append hprefix tailTrace_320037
  have hstable : (prefixWord ++ tailWord_320037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320037).length < 2 ^ (prefixWord ++ tailWord_320037).sum := by decide
  have hdescent : baseEnd_320037 < baseStart_320037 := by decide
  rcases family_descends (prefixWord ++ tailWord_320037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320054 : List Nat := [5, 1, 2, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_320054 : Nat := 118140960795 + 320054 * 2 ^ 59
def prefixEnd_320054 : Nat := 4983230072969 + 3 ^ 40 * 320054 * 2
def baseEnd_320054 : Nat := 164341537394196020953105

theorem tailTrace_320054 : CollatzResearch.WordTrace tailWord_320054 prefixEnd_320054 164341537394196020953105 := by
  unfold tailWord_320054
  simp only [CollatzResearch.WordTrace]
  refine ⟨729583023906655857283451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7782218921670995811023477 729583023906655857283451)
  ·
    refine ⟨1094374535859983785925177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 729583023906655857283451 1094374535859983785925177)
    ·
      refine ⟨820780901894987839443883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1094374535859983785925177 820780901894987839443883)
      ·
        refine ⟨1231171352842481759165825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 820780901894987839443883 1231171352842481759165825)
        ·
          refine ⟨923378514631861319374369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1231171352842481759165825 923378514631861319374369)
          ·
            refine ⟨692533885973895989530777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 923378514631861319374369 692533885973895989530777)
            ·
              refine ⟨519400414480421992148083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692533885973895989530777 519400414480421992148083)
              ·
                refine ⟨779100621720632988222125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519400414480421992148083 779100621720632988222125)
                ·
                  refine ⟨292162733145237370583297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 779100621720632988222125 292162733145237370583297)
                  ·
                    refine ⟨219122049858928027937473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 292162733145237370583297 219122049858928027937473)
                    ·
                      refine ⟨164341537394196020953105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 219122049858928027937473 164341537394196020953105)
                      ·
                        rfl

theorem cell23_320054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_320054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320054 prefixEnd_320054 := by exact prefixLift 320054
  have htrace : WordTrace (prefixWord ++ tailWord_320054) baseStart_320054 baseEnd_320054 := by
    simpa [prefixWord, tailWord_320054, baseEnd_320054] using wordTrace_append hprefix tailTrace_320054
  have hstable : (prefixWord ++ tailWord_320054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320054).length < 2 ^ (prefixWord ++ tailWord_320054).sum := by decide
  have hdescent : baseEnd_320054 < baseStart_320054 := by decide
  rcases family_descends (prefixWord ++ tailWord_320054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320094 : List Nat := [4, 4, 1, 2, 2, 1, 9]
def baseStart_320094 : Nat := 118140960795 + 320094 * 2 ^ 59
def prefixEnd_320094 : Nat := 4983230072969 + 3 ^ 40 * 320094 * 2
def baseEnd_320094 : Nat := 2029161439757726721641

theorem tailTrace_320094 : CollatzResearch.WordTrace tailWord_320094 prefixEnd_320094 2029161439757726721641 := by
  unfold tailWord_320094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1459348412795197568498917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7783191534907720365327557 1459348412795197568498917)
  ·
    refine ⟨273627827399099544093547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1459348412795197568498917 273627827399099544093547)
    ·
      refine ⟨410441741098649316140321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273627827399099544093547 410441741098649316140321)
      ·
        refine ⟨307831305823986987105241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410441741098649316140321 307831305823986987105241)
        ·
          refine ⟨230873479367990240328931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307831305823986987105241 230873479367990240328931)
          ·
            refine ⟨346310219051985360493397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230873479367990240328931 346310219051985360493397)
            ·
              refine ⟨2029161439757726721641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 346310219051985360493397 2029161439757726721641)
              ·
                rfl

theorem cell23_320094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 9].length) (baseStart_320094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320094 prefixEnd_320094 := by exact prefixLift 320094
  have htrace : WordTrace (prefixWord ++ tailWord_320094) baseStart_320094 baseEnd_320094 := by
    simpa [prefixWord, tailWord_320094, baseEnd_320094] using wordTrace_append hprefix tailTrace_320094
  have hstable : (prefixWord ++ tailWord_320094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320094).length < 2 ^ (prefixWord ++ tailWord_320094).sum := by decide
  have hdescent : baseEnd_320094 < baseStart_320094 := by decide
  rcases family_descends (prefixWord ++ tailWord_320094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320096 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 5]
def baseStart_320096 : Nat := 118140960795 + 320096 * 2 ^ 59
def prefixEnd_320096 : Nat := 4983230072969 + 3 ^ 40 * 320096 * 2
def baseEnd_320096 : Nat := 164363103581684856627911

theorem tailTrace_320096 : CollatzResearch.WordTrace tailWord_320096 prefixEnd_320096 164363103581684856627911 := by
  unfold tailWord_320096
  simp only [CollatzResearch.WordTrace]
  refine ⟨5837430124177167444782071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7783240165569556593042761 5837430124177167444782071)
  ·
    refine ⟨8756145186265751167173107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5837430124177167444782071 8756145186265751167173107)
    ·
      refine ⟨13134217779398626750759661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8756145186265751167173107 13134217779398626750759661)
      ·
        refine ⟨4925331667274485031534873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13134217779398626750759661 4925331667274485031534873)
        ·
          refine ⟨3693998750455863773651155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4925331667274485031534873 3693998750455863773651155)
          ·
            refine ⟨5540998125683795660476733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3693998750455863773651155 5540998125683795660476733)
            ·
              refine ⟨2077874297131423372678775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5540998125683795660476733 2077874297131423372678775)
              ·
                refine ⟨3116811445697135059018163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2077874297131423372678775 3116811445697135059018163)
                ·
                  refine ⟨4675217168545702588527245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3116811445697135059018163 4675217168545702588527245)
                  ·
                    refine ⟨1753206438204638470697717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4675217168545702588527245 1753206438204638470697717)
                    ·
                      refine ⟨164363103581684856627911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1753206438204638470697717 164363103581684856627911)
                      ·
                        rfl

theorem cell23_320096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_320096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320096 prefixEnd_320096 := by exact prefixLift 320096
  have htrace : WordTrace (prefixWord ++ tailWord_320096) baseStart_320096 baseEnd_320096 := by
    simpa [prefixWord, tailWord_320096, baseEnd_320096] using wordTrace_append hprefix tailTrace_320096
  have hstable : (prefixWord ++ tailWord_320096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320096).length < 2 ^ (prefixWord ++ tailWord_320096).sum := by decide
  have hdescent : baseEnd_320096 < baseStart_320096 := by decide
  rcases family_descends (prefixWord ++ tailWord_320096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320176 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 2, 8]
def baseStart_320176 : Nat := 118140960795 + 320176 * 2 ^ 59
def prefixEnd_320176 : Nat := 4983230072969 + 3 ^ 40 * 320176 * 2
def baseEnd_320176 : Nat := 54801394011348181209181

theorem tailTrace_320176 : CollatzResearch.WordTrace tailWord_320176 prefixEnd_320176 54801394011348181209181 := by
  unfold tailWord_320176
  simp only [CollatzResearch.WordTrace]
  refine ⟨5838889044032254276238191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7785185392043005701650921 5838889044032254276238191)
  ·
    refine ⟨8758333566048381414357287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5838889044032254276238191 8758333566048381414357287)
    ·
      refine ⟨13137500349072572121535931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8758333566048381414357287 13137500349072572121535931)
      ·
        refine ⟨19706250523608858182303897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13137500349072572121535931 19706250523608858182303897)
        ·
          refine ⟨14779687892706643636727923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19706250523608858182303897 14779687892706643636727923)
          ·
            refine ⟨22169531839059965455091885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14779687892706643636727923 22169531839059965455091885)
            ·
              refine ⟨8313574439647487045659457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22169531839059965455091885 8313574439647487045659457)
              ·
                refine ⟨6235180829735615284244593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8313574439647487045659457 6235180829735615284244593)
                ·
                  refine ⟨4676385622301711463183445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6235180829735615284244593 4676385622301711463183445)
                  ·
                    refine ⟨54801394011348181209181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4676385622301711463183445 54801394011348181209181)
                    ·
                      rfl

theorem cell23_320176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 8].length) (baseStart_320176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320176 prefixEnd_320176 := by exact prefixLift 320176
  have htrace : WordTrace (prefixWord ++ tailWord_320176) baseStart_320176 baseEnd_320176 := by
    simpa [prefixWord, tailWord_320176, baseEnd_320176] using wordTrace_append hprefix tailTrace_320176
  have hstable : (prefixWord ++ tailWord_320176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320176).length < 2 ^ (prefixWord ++ tailWord_320176).sum := by decide
  have hdescent : baseEnd_320176 < baseStart_320176 := by decide
  rcases family_descends (prefixWord ++ tailWord_320176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320177 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 2, 3, 3]
def baseStart_320177 : Nat := 118140960795 + 320177 * 2 ^ 59
def prefixEnd_320177 : Nat := 4983230072969 + 3 ^ 40 * 320177 * 2
def baseEnd_320177 : Nat := 164404695514699039715039

theorem tailTrace_320177 : CollatzResearch.WordTrace tailWord_320177 prefixEnd_320177 164404695514699039715039 := by
  unfold tailWord_320177
  simp only [CollatzResearch.WordTrace]
  refine ⟨11677814561060885723262785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7785209707373923815508523 11677814561060885723262785)
  ·
    refine ⟨8758360920795664292447089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11677814561060885723262785 8758360920795664292447089)
    ·
      refine ⟨6568770690596748219335317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8758360920795664292447089 6568770690596748219335317)
      ·
        refine ⟨307911126121722572781343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6568770690596748219335317 307911126121722572781343)
        ·
          refine ⟨461866689182583859172015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307911126121722572781343 461866689182583859172015)
          ·
            refine ⟨692800033773875788758023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461866689182583859172015 692800033773875788758023)
            ·
              refine ⟨1039200050660813683137035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692800033773875788758023 1039200050660813683137035)
              ·
                refine ⟨1558800075991220524705553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1039200050660813683137035 1558800075991220524705553)
                ·
                  refine ⟨1169100056993415393529165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1558800075991220524705553 1169100056993415393529165)
                  ·
                    refine ⟨438412521372530772573437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1169100056993415393529165 438412521372530772573437)
                    ·
                      refine ⟨164404695514699039715039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 438412521372530772573437 164404695514699039715039)
                      ·
                        rfl

theorem cell23_320177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_320177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320177 prefixEnd_320177 := by exact prefixLift 320177
  have htrace : WordTrace (prefixWord ++ tailWord_320177) baseStart_320177 baseEnd_320177 := by
    simpa [prefixWord, tailWord_320177, baseEnd_320177] using wordTrace_append hprefix tailTrace_320177
  have hstable : (prefixWord ++ tailWord_320177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320177).length < 2 ^ (prefixWord ++ tailWord_320177).sum := by decide
  have hdescent : baseEnd_320177 < baseStart_320177 := by decide
  rcases family_descends (prefixWord ++ tailWord_320177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320200 : List Nat := [2, 1, 3, 1, 2, 3, 3, 1, 2, 1, 4]
def baseStart_320200 : Nat := 118140960795 + 320200 * 2 ^ 59
def prefixEnd_320200 : Nat := 4983230072969 + 3 ^ 40 * 320200 * 2
def baseEnd_320200 : Nat := 164416505569752449727433

theorem tailTrace_320200 : CollatzResearch.WordTrace tailWord_320200 prefixEnd_320200 164416505569752449727433 := by
  unfold tailWord_320200
  simp only [CollatzResearch.WordTrace]
  refine ⟨5839326719988780325675027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7785768959985040434233369 5839326719988780325675027)
  ·
    refine ⟨8758990079983170488512541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5839326719988780325675027 8758990079983170488512541)
    ·
      refine ⟨3284621279993688933192203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8758990079983170488512541 3284621279993688933192203)
      ·
        refine ⟨4926931919990533399788305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3284621279993688933192203 4926931919990533399788305)
        ·
          refine ⟨3695198939992900049841229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4926931919990533399788305 3695198939992900049841229)
          ·
            refine ⟨1385699602497337518690461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3695198939992900049841229 1385699602497337518690461)
            ·
              refine ⟨519637350936501569508923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1385699602497337518690461 519637350936501569508923)
              ·
                refine ⟨779456026404752354263385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519637350936501569508923 779456026404752354263385)
                ·
                  refine ⟨584592019803564265697539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 779456026404752354263385 584592019803564265697539)
                  ·
                    refine ⟨876888029705346398546309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 584592019803564265697539 876888029705346398546309)
                    ·
                      refine ⟨164416505569752449727433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 876888029705346398546309 164416505569752449727433)
                      ·
                        rfl

theorem cell23_320200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_320200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320200 prefixEnd_320200 := by exact prefixLift 320200
  have htrace : WordTrace (prefixWord ++ tailWord_320200) baseStart_320200 baseEnd_320200 := by
    simpa [prefixWord, tailWord_320200, baseEnd_320200] using wordTrace_append hprefix tailTrace_320200
  have hstable : (prefixWord ++ tailWord_320200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320200).length < 2 ^ (prefixWord ++ tailWord_320200).sum := by decide
  have hdescent : baseEnd_320200 < baseStart_320200 := by decide
  rcases family_descends (prefixWord ++ tailWord_320200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320223 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 8]
def baseStart_320223 : Nat := 118140960795 + 320223 * 2 ^ 59
def prefixEnd_320223 : Nat := 4983230072969 + 3 ^ 40 * 320223 * 2
def baseEnd_320223 : Nat := 18269812847200651082203

theorem tailTrace_320223 : CollatzResearch.WordTrace tailWord_320223 prefixEnd_320223 18269812847200651082203 := by
  unfold tailWord_320223
  simp only [CollatzResearch.WordTrace]
  refine ⟨11679492318894235579437323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7786328212596157052958215 11679492318894235579437323)
  ·
    refine ⟨17519238478341353369155985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11679492318894235579437323 17519238478341353369155985)
    ·
      refine ⟨13139428858756015026866989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17519238478341353369155985 13139428858756015026866989)
      ·
        refine ⟨4927285822033505635075121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13139428858756015026866989 4927285822033505635075121)
        ·
          refine ⟨3695464366525129226306341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4927285822033505635075121 3695464366525129226306341)
          ·
            refine ⟨692899568723461729932439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3695464366525129226306341 692899568723461729932439)
            ·
              refine ⟨1039349353085192594898659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692899568723461729932439 1039349353085192594898659)
              ·
                refine ⟨1559024029627788892347989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1039349353085192594898659 1559024029627788892347989)
                ·
                  refine ⟨18269812847200651082203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1559024029627788892347989 18269812847200651082203)
                  ·
                    rfl

theorem cell23_320223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 8].length) (baseStart_320223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320223 prefixEnd_320223 := by exact prefixLift 320223
  have htrace : WordTrace (prefixWord ++ tailWord_320223) baseStart_320223 baseEnd_320223 := by
    simpa [prefixWord, tailWord_320223, baseEnd_320223] using wordTrace_append hprefix tailTrace_320223
  have hstable : (prefixWord ++ tailWord_320223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320223).length < 2 ^ (prefixWord ++ tailWord_320223).sum := by decide
  have hdescent : baseEnd_320223 < baseStart_320223 := by decide
  rcases family_descends (prefixWord ++ tailWord_320223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320227 : List Nat := [1, 1, 1, 7, 1, 2, 2, 1, 3, 4]
def baseStart_320227 : Nat := 118140960795 + 320227 * 2 ^ 59
def prefixEnd_320227 : Nat := 4983230072969 + 3 ^ 40 * 320227 * 2
def baseEnd_320227 : Nat := 54810123182474614696603

theorem tailTrace_320227 : CollatzResearch.WordTrace tailWord_320227 prefixEnd_320227 54810123182474614696603 := by
  unfold tailWord_320227
  simp only [CollatzResearch.WordTrace]
  refine ⟨11679638210879744262582935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7786425473919829508388623 11679638210879744262582935)
  ·
    refine ⟨17519457316319616393874403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11679638210879744262582935 17519457316319616393874403)
    ·
      refine ⟨26279185974479424590811605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17519457316319616393874403 26279185974479424590811605)
      ·
        refine ⟨615918421276861513847147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 26279185974479424590811605 615918421276861513847147)
        ·
          refine ⟨923877631915292270770721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615918421276861513847147 923877631915292270770721)
          ·
            refine ⟨692908223936469203078041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 923877631915292270770721 692908223936469203078041)
            ·
              refine ⟨519681167952351902308531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692908223936469203078041 519681167952351902308531)
              ·
                refine ⟨779521751928527853462797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519681167952351902308531 779521751928527853462797)
                ·
                  refine ⟨292320656973197945048549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 779521751928527853462797 292320656973197945048549)
                  ·
                    refine ⟨54810123182474614696603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 292320656973197945048549 54810123182474614696603)
                    ·
                      rfl

theorem cell23_320227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 4].length) (baseStart_320227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320227 prefixEnd_320227 := by exact prefixLift 320227
  have htrace : WordTrace (prefixWord ++ tailWord_320227) baseStart_320227 baseEnd_320227 := by
    simpa [prefixWord, tailWord_320227, baseEnd_320227] using wordTrace_append hprefix tailTrace_320227
  have hstable : (prefixWord ++ tailWord_320227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320227).length < 2 ^ (prefixWord ++ tailWord_320227).sum := by decide
  have hdescent : baseEnd_320227 < baseStart_320227 := by decide
  rcases family_descends (prefixWord ++ tailWord_320227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320240 : List Nat := [2, 1, 1, 1, 3, 1, 7, 1, 6]
def baseStart_320240 : Nat := 118140960795 + 320240 * 2 ^ 59
def prefixEnd_320240 : Nat := 4983230072969 + 3 ^ 40 * 320240 * 2
def baseEnd_320240 : Nat := 18270782755103588136361

theorem tailTrace_320240 : CollatzResearch.WordTrace tailWord_320240 prefixEnd_320240 18270782755103588136361 := by
  unfold tailWord_320240
  simp only [CollatzResearch.WordTrace]
  refine ⟨5840056179916323741403087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7786741573221764988537449 5840056179916323741403087)
  ·
    refine ⟨8760084269874485612104631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5840056179916323741403087 8760084269874485612104631)
    ·
      refine ⟨13140126404811728418156947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8760084269874485612104631 13140126404811728418156947)
      ·
        refine ⟨19710189607217592627235421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13140126404811728418156947 19710189607217592627235421)
        ·
          refine ⟨7391321102706597235213283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19710189607217592627235421 7391321102706597235213283)
          ·
            refine ⟨11086981654059895852819925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7391321102706597235213283 11086981654059895852819925)
            ·
              refine ⟨259851132517028809050467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11086981654059895852819925 259851132517028809050467)
              ·
                refine ⟨389776698775543213575701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259851132517028809050467 389776698775543213575701)
                ·
                  refine ⟨18270782755103588136361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 389776698775543213575701 18270782755103588136361)
                  ·
                    rfl

theorem cell23_320240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 6].length) (baseStart_320240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320240 prefixEnd_320240 := by exact prefixLift 320240
  have htrace : WordTrace (prefixWord ++ tailWord_320240) baseStart_320240 baseEnd_320240 := by
    simpa [prefixWord, tailWord_320240, baseEnd_320240] using wordTrace_append hprefix tailTrace_320240
  have hstable : (prefixWord ++ tailWord_320240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320240).length < 2 ^ (prefixWord ++ tailWord_320240).sum := by decide
  have hdescent : baseEnd_320240 < baseStart_320240 := by decide
  rcases family_descends (prefixWord ++ tailWord_320240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320277 : List Nat := [1, 3, 2, 1, 2, 2, 3, 2, 2, 3, 2]
def baseStart_320277 : Nat := 118140960795 + 320277 * 2 ^ 59
def prefixEnd_320277 : Nat := 4983230072969 + 3 ^ 40 * 320277 * 2
def baseEnd_320277 : Nat := 164456043580148648464579

theorem tailTrace_320277 : CollatzResearch.WordTrace tailWord_320277 prefixEnd_320277 164456043580148648464579 := by
  unfold tailWord_320277
  simp only [CollatzResearch.WordTrace]
  refine ⟨11681461860698602801903085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7787641240465735201268723 11681461860698602801903085)
  ·
    refine ⟨4380548197761976050713657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11681461860698602801903085 4380548197761976050713657)
    ·
      refine ⟨3285411148321482038035243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4380548197761976050713657 3285411148321482038035243)
      ·
        refine ⟨4928116722482223057052865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3285411148321482038035243 4928116722482223057052865)
        ·
          refine ⟨3696087541861667292789649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4928116722482223057052865 3696087541861667292789649)
          ·
            refine ⟨2772065656396250469592237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3696087541861667292789649 2772065656396250469592237)
            ·
              refine ⟨1039524621148593926097089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2772065656396250469592237 1039524621148593926097089)
              ·
                refine ⟨779643465861445444572817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039524621148593926097089 779643465861445444572817)
                ·
                  refine ⟨584732599396084083429613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 779643465861445444572817 584732599396084083429613)
                  ·
                    refine ⟨219274724773531531286105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 584732599396084083429613 219274724773531531286105)
                    ·
                      refine ⟨164456043580148648464579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 219274724773531531286105 164456043580148648464579)
                      ·
                        rfl

theorem cell23_320277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_320277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320277 prefixEnd_320277 := by exact prefixLift 320277
  have htrace : WordTrace (prefixWord ++ tailWord_320277) baseStart_320277 baseEnd_320277 := by
    simpa [prefixWord, tailWord_320277, baseEnd_320277] using wordTrace_append hprefix tailTrace_320277
  have hstable : (prefixWord ++ tailWord_320277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320277).length < 2 ^ (prefixWord ++ tailWord_320277).sum := by decide
  have hdescent : baseEnd_320277 < baseStart_320277 := by decide
  rcases family_descends (prefixWord ++ tailWord_320277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320284 : List Nat := [2, 2, 3, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_320284 : Nat := 118140960795 + 320284 * 2 ^ 59
def prefixEnd_320284 : Nat := 4983230072969 + 3 ^ 40 * 320284 * 2
def baseEnd_320284 : Nat := 164459637944730121077047

theorem tailTrace_320284 : CollatzResearch.WordTrace tailWord_320284 prefixEnd_320284 164459637944730121077047 := by
  unfold tailWord_320284
  simp only [CollatzResearch.WordTrace]
  refine ⟨5840858585836621498703953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7787811447782161998271937 5840858585836621498703953)
  ·
    refine ⟨4380643939377466124027965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5840858585836621498703953 4380643939377466124027965)
    ·
      refine ⟨1642741477266549796510487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4380643939377466124027965 1642741477266549796510487)
      ·
        refine ⟨2464112215899824694765731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1642741477266549796510487 2464112215899824694765731)
        ·
          refine ⟨3696168323849737042148597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2464112215899824694765731 3696168323849737042148597)
          ·
            refine ⟨346515780360912847701431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3696168323849737042148597 346515780360912847701431)
            ·
              refine ⟨519773670541369271552147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346515780360912847701431 519773670541369271552147)
              ·
                refine ⟨779660505812053907328221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519773670541369271552147 779660505812053907328221)
                ·
                  refine ⟨292372689679520215248083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 779660505812053907328221 292372689679520215248083)
                  ·
                    refine ⟨438559034519280322872125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 292372689679520215248083 438559034519280322872125)
                    ·
                      refine ⟨164459637944730121077047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 438559034519280322872125 164459637944730121077047)
                      ·
                        rfl

theorem cell23_320284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_320284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320284 prefixEnd_320284 := by exact prefixLift 320284
  have htrace : WordTrace (prefixWord ++ tailWord_320284) baseStart_320284 baseEnd_320284 := by
    simpa [prefixWord, tailWord_320284, baseEnd_320284] using wordTrace_append hprefix tailTrace_320284
  have hstable : (prefixWord ++ tailWord_320284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320284).length < 2 ^ (prefixWord ++ tailWord_320284).sum := by decide
  have hdescent : baseEnd_320284 < baseStart_320284 := by decide
  rcases family_descends (prefixWord ++ tailWord_320284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320307 : List Nat := [1, 1, 1, 2, 6, 1, 3, 2, 1, 1, 4]
def baseStart_320307 : Nat := 118140960795 + 320307 * 2 ^ 59
def prefixEnd_320307 : Nat := 4983230072969 + 3 ^ 40 * 320307 * 2
def baseEnd_320307 : Nat := 164471447999783531089441

theorem tailTrace_320307 : CollatzResearch.WordTrace tailWord_320307 prefixEnd_320307 164471447999783531089441 := by
  unfold tailWord_320307
  simp only [CollatzResearch.WordTrace]
  refine ⟨11682556050589917925495175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7788370700393278616996783 11682556050589917925495175)
  ·
    refine ⟨17523834075884876888242763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11682556050589917925495175 17523834075884876888242763)
    ·
      refine ⟨26285751113827315332364145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17523834075884876888242763 26285751113827315332364145)
      ·
        refine ⟨19714313335370486499273109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26285751113827315332364145 19714313335370486499273109)
        ·
          refine ⟨924108437595491554653427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19714313335370486499273109 924108437595491554653427)
          ·
            refine ⟨1386162656393237331980141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924108437595491554653427 1386162656393237331980141)
            ·
              refine ⟨519810996147463999492553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1386162656393237331980141 519810996147463999492553)
              ·
                refine ⟨389858247110597999619415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 519810996147463999492553 389858247110597999619415)
                ·
                  refine ⟨584787370665896999429123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 389858247110597999619415 584787370665896999429123)
                  ·
                    refine ⟨877181055998845499143685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 584787370665896999429123 877181055998845499143685)
                    ·
                      refine ⟨164471447999783531089441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 877181055998845499143685 164471447999783531089441)
                      ·
                        rfl

theorem cell23_320307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 1, 4].length) (baseStart_320307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320307 prefixEnd_320307 := by exact prefixLift 320307
  have htrace : WordTrace (prefixWord ++ tailWord_320307) baseStart_320307 baseEnd_320307 := by
    simpa [prefixWord, tailWord_320307, baseEnd_320307] using wordTrace_append hprefix tailTrace_320307
  have hstable : (prefixWord ++ tailWord_320307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320307).length < 2 ^ (prefixWord ++ tailWord_320307).sum := by decide
  have hdescent : baseEnd_320307 < baseStart_320307 := by decide
  rcases family_descends (prefixWord ++ tailWord_320307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320317 : List Nat := [1, 4, 1, 4, 2, 1, 1, 2, 1, 6]
def baseStart_320317 : Nat := 118140960795 + 320317 * 2 ^ 59
def prefixEnd_320317 : Nat := 4983230072969 + 3 ^ 40 * 320317 * 2
def baseEnd_320317 : Nat := 54825527602109497321465

theorem tailTrace_320317 : CollatzResearch.WordTrace tailWord_320317 prefixEnd_320317 54825527602109497321465 := by
  unfold tailWord_320317
  simp only [CollatzResearch.WordTrace]
  refine ⟨11682920780553689633359205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7788613853702459755572803 11682920780553689633359205)
  ·
    refine ⟨2190547646353816806254851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11682920780553689633359205 2190547646353816806254851)
    ·
      refine ⟨3285821469530725209382277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2190547646353816806254851 3285821469530725209382277)
      ·
        refine ⟨616091525537010976759177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3285821469530725209382277 616091525537010976759177)
        ·
          refine ⟨462068644152758232569383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 616091525537010976759177 462068644152758232569383)
          ·
            refine ⟨693102966229137348854075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462068644152758232569383 693102966229137348854075)
            ·
              refine ⟨1039654449343706023281113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693102966229137348854075 1039654449343706023281113)
              ·
                refine ⟨779740837007779517460835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039654449343706023281113 779740837007779517460835)
                ·
                  refine ⟨1169611255511669276191253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779740837007779517460835 1169611255511669276191253)
                  ·
                    refine ⟨54825527602109497321465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1169611255511669276191253 54825527602109497321465)
                    ·
                      rfl

theorem cell23_320317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_320317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320317 prefixEnd_320317 := by exact prefixLift 320317
  have htrace : WordTrace (prefixWord ++ tailWord_320317) baseStart_320317 baseEnd_320317 := by
    simpa [prefixWord, tailWord_320317, baseEnd_320317] using wordTrace_append hprefix tailTrace_320317
  have hstable : (prefixWord ++ tailWord_320317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320317).length < 2 ^ (prefixWord ++ tailWord_320317).sum := by decide
  have hdescent : baseEnd_320317 < baseStart_320317 := by decide
  rcases family_descends (prefixWord ++ tailWord_320317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320321 : List Nat := [1, 2, 5, 3, 1, 1, 3, 1, 1, 5]
def baseStart_320321 : Nat := 118140960795 + 320321 * 2 ^ 59
def prefixEnd_320321 : Nat := 4983230072969 + 3 ^ 40 * 320321 * 2
def baseEnd_320321 : Nat := 54826212242982158771459

theorem tailTrace_320321 : CollatzResearch.WordTrace tailWord_320321 prefixEnd_320321 54826212242982158771459 := by
  unfold tailWord_320321
  simp only [CollatzResearch.WordTrace]
  refine ⟨11683066672539198316504817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7788711115026132211003211 11683066672539198316504817)
  ·
    refine ⟨8762300004404398737378613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11683066672539198316504817 8762300004404398737378613)
    ·
      refine ⟨821465625412912381629245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8762300004404398737378613 821465625412912381629245)
      ·
        refine ⟨308049609529842143110967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 821465625412912381629245 308049609529842143110967)
        ·
          refine ⟨462074414294763214666451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308049609529842143110967 462074414294763214666451)
          ·
            refine ⟨693111621442144821999677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462074414294763214666451 693111621442144821999677)
            ·
              refine ⟨259916858040804308249879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 693111621442144821999677 259916858040804308249879)
              ·
                refine ⟨389875287061206462374819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259916858040804308249879 389875287061206462374819)
                ·
                  refine ⟨584812930591809693562229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 389875287061206462374819 584812930591809693562229)
                  ·
                    refine ⟨54826212242982158771459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 584812930591809693562229 54826212242982158771459)
                    ·
                      rfl

theorem cell23_320321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_320321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320321 prefixEnd_320321 := by exact prefixLift 320321
  have htrace : WordTrace (prefixWord ++ tailWord_320321) baseStart_320321 baseEnd_320321 := by
    simpa [prefixWord, tailWord_320321, baseEnd_320321] using wordTrace_append hprefix tailTrace_320321
  have hstable : (prefixWord ++ tailWord_320321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320321).length < 2 ^ (prefixWord ++ tailWord_320321).sum := by decide
  have hdescent : baseEnd_320321 < baseStart_320321 := by decide
  rcases family_descends (prefixWord ++ tailWord_320321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320341 : List Nat := [1, 3, 2, 2, 2, 1, 3, 4, 1, 2, 2]
def baseStart_320341 : Nat := 118140960795 + 320341 * 2 ^ 59
def prefixEnd_320341 : Nat := 4983230072969 + 3 ^ 40 * 320341 * 2
def baseEnd_320341 : Nat := 164488906342036398064285

theorem tailTrace_320341 : CollatzResearch.WordTrace tailWord_320341 prefixEnd_320341 164488906342036398064285 := by
  unfold tailWord_320341
  simp only [CollatzResearch.WordTrace]
  refine ⟨11683796132466741732232877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7789197421644494488155251 11683796132466741732232877)
  ·
    refine ⟨4381423549675028149587329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11683796132466741732232877 4381423549675028149587329)
    ·
      refine ⟨3286067662256271112190497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4381423549675028149587329 3286067662256271112190497)
      ·
        refine ⟨2464550746692203334142873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3286067662256271112190497 2464550746692203334142873)
        ·
          refine ⟨1848413060019152500607155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2464550746692203334142873 1848413060019152500607155)
          ·
            refine ⟨2772619590028728750910733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1848413060019152500607155 2772619590028728750910733)
            ·
              refine ⟨1039732346260773281591525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2772619590028728750910733 1039732346260773281591525)
              ·
                refine ⟨194949814923894990298411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1039732346260773281591525 194949814923894990298411)
                ·
                  refine ⟨292424722385842485447617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194949814923894990298411 292424722385842485447617)
                  ·
                    refine ⟨219318541789381864085713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 292424722385842485447617 219318541789381864085713)
                    ·
                      refine ⟨164488906342036398064285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 219318541789381864085713 164488906342036398064285)
                      ·
                        rfl

theorem cell23_320341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_320341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320341 prefixEnd_320341 := by exact prefixLift 320341
  have htrace : WordTrace (prefixWord ++ tailWord_320341) baseStart_320341 baseEnd_320341 := by
    simpa [prefixWord, tailWord_320341, baseEnd_320341] using wordTrace_append hprefix tailTrace_320341
  have hstable : (prefixWord ++ tailWord_320341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320341).length < 2 ^ (prefixWord ++ tailWord_320341).sum := by decide
  have hdescent : baseEnd_320341 < baseStart_320341 := by decide
  rcases family_descends (prefixWord ++ tailWord_320341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320354 : List Nat := [3, 3, 2, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_320354 : Nat := 118140960795 + 320354 * 2 ^ 59
def prefixEnd_320354 : Nat := 4983230072969 + 3 ^ 40 * 320354 * 2
def baseEnd_320354 : Nat := 164495581590544847201725

theorem tailTrace_320354 : CollatzResearch.WordTrace tailWord_320354 prefixEnd_320354 164495581590544847201725 := by
  unfold tailWord_320354
  simp only [CollatzResearch.WordTrace]
  refine ⟨2921067570354911238114029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7789513520946429968304077 2921067570354911238114029)
  ·
    refine ⟨1095400338883091714292761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2921067570354911238114029 1095400338883091714292761)
    ·
      refine ⟨821550254162318785719571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1095400338883091714292761 821550254162318785719571)
      ·
        refine ⟨1232325381243478178579357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 821550254162318785719571 1232325381243478178579357)
        ·
          refine ⟨462122017966304316967259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1232325381243478178579357 462122017966304316967259)
          ·
            refine ⟨693183026949456475450889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462122017966304316967259 693183026949456475450889)
            ·
              refine ⟨519887270212092356588167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 693183026949456475450889 519887270212092356588167)
              ·
                refine ⟨779830905318138534882251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519887270212092356588167 779830905318138534882251)
                ·
                  refine ⟨1169746357977207802323377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779830905318138534882251 1169746357977207802323377)
                  ·
                    refine ⟨877309768482905851742533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1169746357977207802323377 877309768482905851742533)
                    ·
                      refine ⟨164495581590544847201725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 877309768482905851742533 164495581590544847201725)
                      ·
                        rfl

theorem cell23_320354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_320354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320354 prefixEnd_320354 := by exact prefixLift 320354
  have htrace : WordTrace (prefixWord ++ tailWord_320354) baseStart_320354 baseEnd_320354 := by
    simpa [prefixWord, tailWord_320354, baseEnd_320354] using wordTrace_append hprefix tailTrace_320354
  have hstable : (prefixWord ++ tailWord_320354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320354).length < 2 ^ (prefixWord ++ tailWord_320354).sum := by decide
  have hdescent : baseEnd_320354 < baseStart_320354 := by decide
  rcases family_descends (prefixWord ++ tailWord_320354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320374 : List Nat := [5, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_320374 : Nat := 118140960795 + 320374 * 2 ^ 59
def prefixEnd_320374 : Nat := 4983230072969 + 3 ^ 40 * 320374 * 2
def baseEnd_320374 : Nat := 164505851203634768951633

theorem tailTrace_320374 : CollatzResearch.WordTrace tailWord_320374 prefixEnd_320374 164505851203634768951633 := by
  unfold tailWord_320374
  simp only [CollatzResearch.WordTrace]
  refine ⟨730312483834199273011511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7789999827564792245456117 730312483834199273011511)
  ·
    refine ⟨1095468725751298909517267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 730312483834199273011511 1095468725751298909517267)
    ·
      refine ⟨1643203088626948364275901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1095468725751298909517267 1643203088626948364275901)
      ·
        refine ⟨616201158235105636603463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1643203088626948364275901 616201158235105636603463)
        ·
          refine ⟨924301737352658454905195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616201158235105636603463 924301737352658454905195)
          ·
            refine ⟨1386452606028987682357793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924301737352658454905195 1386452606028987682357793)
            ·
              refine ⟨1039839454521740761768345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1386452606028987682357793 1039839454521740761768345)
              ·
                refine ⟨779879590891305571326259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039839454521740761768345 779879590891305571326259)
                ·
                  refine ⟨1169819386336958356989389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779879590891305571326259 1169819386336958356989389)
                  ·
                    refine ⟨438682269876359383871021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1169819386336958356989389 438682269876359383871021)
                    ·
                      refine ⟨164505851203634768951633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 438682269876359383871021 164505851203634768951633)
                      ·
                        rfl

theorem cell23_320374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_320374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320374 prefixEnd_320374 := by exact prefixLift 320374
  have htrace : WordTrace (prefixWord ++ tailWord_320374) baseStart_320374 baseEnd_320374 := by
    simpa [prefixWord, tailWord_320374, baseEnd_320374] using wordTrace_append hprefix tailTrace_320374
  have hstable : (prefixWord ++ tailWord_320374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320374).length < 2 ^ (prefixWord ++ tailWord_320374).sum := by decide
  have hdescent : baseEnd_320374 < baseStart_320374 := by decide
  rcases family_descends (prefixWord ++ tailWord_320374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320391 : List Nat := [1, 1, 4, 2, 3, 3, 1, 2, 2, 1, 3]
def baseStart_320391 : Nat := 118140960795 + 320391 * 2 ^ 59
def prefixEnd_320391 : Nat := 4983230072969 + 3 ^ 40 * 320391 * 2
def baseEnd_320391 : Nat := 164514580374761202439055

theorem tailTrace_320391 : CollatzResearch.WordTrace tailWord_320391 prefixEnd_320391 164514580374761202439055 := by
  unfold tailWord_320391
  simp only [CollatzResearch.WordTrace]
  refine ⟨11685619782285600271553027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7790413188190400181035351 11685619782285600271553027)
  ·
    refine ⟨17528429673428400407329541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11685619782285600271553027 17528429673428400407329541)
    ·
      refine ⟨3286580563767825076374289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17528429673428400407329541 3286580563767825076374289)
      ·
        refine ⟨2464935422825868807280717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3286580563767825076374289 2464935422825868807280717)
        ·
          refine ⟨924350783559700802730269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2464935422825868807280717 924350783559700802730269)
          ·
            refine ⟨346631543834887801023851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 924350783559700802730269 346631543834887801023851)
            ·
              refine ⟨519947315752331701535777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346631543834887801023851 519947315752331701535777)
              ·
                refine ⟨389960486814248776151833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 519947315752331701535777 389960486814248776151833)
                ·
                  refine ⟨292470365110686582113875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 389960486814248776151833 292470365110686582113875)
                  ·
                    refine ⟨438705547666029873170813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 292470365110686582113875 438705547666029873170813)
                    ·
                      refine ⟨164514580374761202439055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 438705547666029873170813 164514580374761202439055)
                      ·
                        rfl

theorem cell23_320391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_320391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320391 prefixEnd_320391 := by exact prefixLift 320391
  have htrace : WordTrace (prefixWord ++ tailWord_320391) baseStart_320391 baseEnd_320391 := by
    simpa [prefixWord, tailWord_320391, baseEnd_320391] using wordTrace_append hprefix tailTrace_320391
  have hstable : (prefixWord ++ tailWord_320391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320391).length < 2 ^ (prefixWord ++ tailWord_320391).sum := by decide
  have hdescent : baseEnd_320391 < baseStart_320391 := by decide
  rcases family_descends (prefixWord ++ tailWord_320391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320420 : List Nat := [2, 3, 1, 2, 1, 2, 1, 4, 7]
def baseStart_320420 : Nat := 118140960795 + 320420 * 2 ^ 59
def prefixEnd_320420 : Nat := 4983230072969 + 3 ^ 40 * 320420 * 2
def baseEnd_320420 : Nat := 18281052368193509886269

theorem tailTrace_320420 : CollatzResearch.WordTrace tailWord_320420 prefixEnd_320420 18281052368193509886269 := by
  unfold tailWord_320420
  simp only [CollatzResearch.WordTrace]
  refine ⟨5843338749590269112179357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7791118332787025482905809 5843338749590269112179357)
  ·
    refine ⟨2191252031096350917067259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5843338749590269112179357 2191252031096350917067259)
    ·
      refine ⟨3286878046644526375600889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2191252031096350917067259 3286878046644526375600889)
      ·
        refine ⟨2465158534983394781700667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3286878046644526375600889 2465158534983394781700667)
        ·
          refine ⟨3697737802475092172551001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2465158534983394781700667 3697737802475092172551001)
          ·
            refine ⟨2773303351856319129413251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3697737802475092172551001 2773303351856319129413251)
            ·
              refine ⟨4159955027784478694119877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2773303351856319129413251 4159955027784478694119877)
              ·
                refine ⟨779991567709589755147477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4159955027784478694119877 779991567709589755147477)
                ·
                  refine ⟨18281052368193509886269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 779991567709589755147477 18281052368193509886269)
                  ·
                    rfl

theorem cell23_320420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_320420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320420 prefixEnd_320420 := by exact prefixLift 320420
  have htrace : WordTrace (prefixWord ++ tailWord_320420) baseStart_320420 baseEnd_320420 := by
    simpa [prefixWord, tailWord_320420, baseEnd_320420] using wordTrace_append hprefix tailTrace_320420
  have hstable : (prefixWord ++ tailWord_320420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320420).length < 2 ^ (prefixWord ++ tailWord_320420).sum := by decide
  have hdescent : baseEnd_320420 < baseStart_320420 := by decide
  rcases family_descends (prefixWord ++ tailWord_320420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320548 : List Nat := [2, 3, 1, 4, 1, 2, 2, 3, 1, 4]
def baseStart_320548 : Nat := 118140960795 + 320548 * 2 ^ 59
def prefixEnd_320548 : Nat := 4983230072969 + 3 ^ 40 * 320548 * 2
def baseEnd_320548 : Nat := 54865065612505696058611

theorem tailTrace_320548 : CollatzResearch.WordTrace tailWord_320548 prefixEnd_320548 54865065612505696058611 := by
  unfold tailWord_320548
  simp only [CollatzResearch.WordTrace]
  refine ⟨5845673021358408042509149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7794230695144544056678865 5845673021358408042509149)
  ·
    refine ⟨2192127383009403015940931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5845673021358408042509149 2192127383009403015940931)
    ·
      refine ⟨3288191074514104523911397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2192127383009403015940931 3288191074514104523911397)
      ·
        refine ⟨616535826471394598233387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3288191074514104523911397 616535826471394598233387)
        ·
          refine ⟨924803739707091897350081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616535826471394598233387 924803739707091897350081)
          ·
            refine ⟨693602804780318923012561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 924803739707091897350081 693602804780318923012561)
            ·
              refine ⟨520202103585239192259421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 693602804780318923012561 520202103585239192259421)
              ·
                refine ⟨195075788844464697097283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 520202103585239192259421 195075788844464697097283)
                ·
                  refine ⟨292613683266697045645925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195075788844464697097283 292613683266697045645925)
                  ·
                    refine ⟨54865065612505696058611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 292613683266697045645925 54865065612505696058611)
                    ·
                      rfl

theorem cell23_320548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_320548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320548 prefixEnd_320548 := by exact prefixLift 320548
  have htrace : WordTrace (prefixWord ++ tailWord_320548) baseStart_320548 baseEnd_320548 := by
    simpa [prefixWord, tailWord_320548, baseEnd_320548] using wordTrace_append hprefix tailTrace_320548
  have hstable : (prefixWord ++ tailWord_320548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320548).length < 2 ^ (prefixWord ++ tailWord_320548).sum := by decide
  have hdescent : baseEnd_320548 < baseStart_320548 := by decide
  rcases family_descends (prefixWord ++ tailWord_320548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320564 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_320564 : Nat := 118140960795 + 320564 * 2 ^ 59
def prefixEnd_320564 : Nat := 4983230072969 + 3 ^ 40 * 320564 * 2
def baseEnd_320564 : Nat := 164603412527989025575759

theorem tailTrace_320564 : CollatzResearch.WordTrace tailWord_320564 prefixEnd_320564 164603412527989025575759 := by
  unfold tailWord_320564
  simp only [CollatzResearch.WordTrace]
  refine ⟨5845964805329425408800373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7794619740439233878400497 5845964805329425408800373)
  ·
    refine ⟨548059200499633632075035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5845964805329425408800373 548059200499633632075035)
    ·
      refine ⟨822088800749450448112553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 548059200499633632075035 822088800749450448112553)
      ·
        refine ⟨616566600562087836084415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 822088800749450448112553 616566600562087836084415)
        ·
          refine ⟨924849900843131754126623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616566600562087836084415 924849900843131754126623)
          ·
            refine ⟨1387274851264697631189935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924849900843131754126623 1387274851264697631189935)
            ·
              refine ⟨2080912276897046446784903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1387274851264697631189935 2080912276897046446784903)
              ·
                refine ⟨3121368415345569670177355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2080912276897046446784903 3121368415345569670177355)
                ·
                  refine ⟨4682052623018354505266033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3121368415345569670177355 4682052623018354505266033)
                  ·
                    refine ⟨3511539467263765878949525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4682052623018354505266033 3511539467263765878949525)
                    ·
                      refine ⟨164603412527989025575759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3511539467263765878949525 164603412527989025575759)
                      ·
                        rfl

theorem cell23_320564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_320564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320564 prefixEnd_320564 := by exact prefixLift 320564
  have htrace : WordTrace (prefixWord ++ tailWord_320564) baseStart_320564 baseEnd_320564 := by
    simpa [prefixWord, tailWord_320564, baseEnd_320564] using wordTrace_append hprefix tailTrace_320564
  have hstable : (prefixWord ++ tailWord_320564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320564).length < 2 ^ (prefixWord ++ tailWord_320564).sum := by decide
  have hdescent : baseEnd_320564 < baseStart_320564 := by decide
  rcases family_descends (prefixWord ++ tailWord_320564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320587 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 8, 4]
def baseStart_320587 : Nat := 118140960795 + 320587 * 2 ^ 59
def prefixEnd_320587 : Nat := 4983230072969 + 3 ^ 40 * 320587 * 2
def baseEnd_320587 : Nat := 54871740861014145196051

theorem tailTrace_320587 : CollatzResearch.WordTrace tailWord_320587 prefixEnd_320587 54871740861014145196051 := by
  unfold tailWord_320587
  simp only [CollatzResearch.WordTrace]
  refine ⟨11692768489575525745688015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7795178993050350497125343 11692768489575525745688015)
  ·
    refine ⟨17539152734363288618532023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11692768489575525745688015 17539152734363288618532023)
    ·
      refine ⟨26308729101544932927798035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17539152734363288618532023 26308729101544932927798035)
      ·
        refine ⟨39463093652317399391697053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26308729101544932927798035 39463093652317399391697053)
        ·
          refine ⟨14798660119619024771886395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39463093652317399391697053 14798660119619024771886395)
          ·
            refine ⟨22197990179428537157829593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14798660119619024771886395 22197990179428537157829593)
            ·
              refine ⟨16648492634571402868372195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22197990179428537157829593 16648492634571402868372195)
              ·
                refine ⟨24972738951857104302558293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16648492634571402868372195 24972738951857104302558293)
                ·
                  refine ⟨292649284592075441045605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24972738951857104302558293 292649284592075441045605)
                  ·
                    refine ⟨54871740861014145196051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 292649284592075441045605 54871740861014145196051)
                    ·
                      rfl

theorem cell23_320587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 4].length) (baseStart_320587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320587 prefixEnd_320587 := by exact prefixLift 320587
  have htrace : WordTrace (prefixWord ++ tailWord_320587) baseStart_320587 baseEnd_320587 := by
    simpa [prefixWord, tailWord_320587, baseEnd_320587] using wordTrace_append hprefix tailTrace_320587
  have hstable : (prefixWord ++ tailWord_320587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320587).length < 2 ^ (prefixWord ++ tailWord_320587).sum := by decide
  have hdescent : baseEnd_320587 < baseStart_320587 := by decide
  rcases family_descends (prefixWord ++ tailWord_320587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320597 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_320597 : Nat := 118140960795 + 320597 * 2 ^ 59
def prefixEnd_320597 : Nat := 4983230072969 + 3 ^ 40 * 320597 * 2
def baseEnd_320597 : Nat := 164620357389587396463107

theorem tailTrace_320597 : CollatzResearch.WordTrace tailWord_320597 prefixEnd_320597 164620357389587396463107 := by
  unfold tailWord_320597
  simp only [CollatzResearch.WordTrace]
  refine ⟨11693133219539297453552045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7795422146359531635701363 11693133219539297453552045)
  ·
    refine ⟨4384924957327236545082017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11693133219539297453552045 4384924957327236545082017)
    ·
      refine ⟨3288693717995427408811513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4384924957327236545082017 3288693717995427408811513)
      ·
        refine ⟨2466520288496570556608635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3288693717995427408811513 2466520288496570556608635)
        ·
          refine ⟨3699780432744855834912953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2466520288496570556608635 3699780432744855834912953)
          ·
            refine ⟨2774835324558641876184715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3699780432744855834912953 2774835324558641876184715)
            ·
              refine ⟨4162252986837962814277073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2774835324558641876184715 4162252986837962814277073)
              ·
                refine ⟨3121689740128472110707805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4162252986837962814277073 3121689740128472110707805)
                ·
                  refine ⟨1170633652548177041515427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3121689740128472110707805 1170633652548177041515427)
                  ·
                    refine ⟨1755950478822265562273141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1170633652548177041515427 1755950478822265562273141)
                    ·
                      refine ⟨164620357389587396463107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1755950478822265562273141 164620357389587396463107)
                      ·
                        rfl

theorem cell23_320597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_320597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320597 prefixEnd_320597 := by exact prefixLift 320597
  have htrace : WordTrace (prefixWord ++ tailWord_320597) baseStart_320597 baseEnd_320597 := by
    simpa [prefixWord, tailWord_320597, baseEnd_320597] using wordTrace_append hprefix tailTrace_320597
  have hstable : (prefixWord ++ tailWord_320597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320597).length < 2 ^ (prefixWord ++ tailWord_320597).sum := by decide
  have hdescent : baseEnd_320597 < baseStart_320597 := by decide
  rcases family_descends (prefixWord ++ tailWord_320597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320604 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 6, 4]
def baseStart_320604 : Nat := 118140960795 + 320604 * 2 ^ 59
def prefixEnd_320604 : Nat := 4983230072969 + 3 ^ 40 * 320604 * 2
def baseEnd_320604 : Nat := 54874650584722956358525

theorem tailTrace_320604 : CollatzResearch.WordTrace tailWord_320604 prefixEnd_320604 54874650584722956358525 := by
  unfold tailWord_320604
  simp only [CollatzResearch.WordTrace]
  refine ⟨5846694265256968824528433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7795592353675958432704577 5846694265256968824528433)
  ·
    refine ⟨4385020698942726618396325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5846694265256968824528433 4385020698942726618396325)
    ·
      refine ⟨822191381051761240949311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4385020698942726618396325 822191381051761240949311)
      ·
        refine ⟨1233287071577641861423967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 822191381051761240949311 1233287071577641861423967)
        ·
          refine ⟨1849930607366462792135951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1233287071577641861423967 1849930607366462792135951)
          ·
            refine ⟨2774895911049694188203927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849930607366462792135951 2774895911049694188203927)
            ·
              refine ⟨4162343866574541282305891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2774895911049694188203927 4162343866574541282305891)
              ·
                refine ⟨6243515799861811923458837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4162343866574541282305891 6243515799861811923458837)
                ·
                  refine ⟨292664803118522433912133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6243515799861811923458837 292664803118522433912133)
                  ·
                    refine ⟨54874650584722956358525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 292664803118522433912133 54874650584722956358525)
                    ·
                      rfl

theorem cell23_320604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_320604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320604 prefixEnd_320604 := by exact prefixLift 320604
  have htrace : WordTrace (prefixWord ++ tailWord_320604) baseStart_320604 baseEnd_320604 := by
    simpa [prefixWord, tailWord_320604, baseEnd_320604] using wordTrace_append hprefix tailTrace_320604
  have hstable : (prefixWord ++ tailWord_320604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320604).length < 2 ^ (prefixWord ++ tailWord_320604).sum := by decide
  have hdescent : baseEnd_320604 < baseStart_320604 := by decide
  rcases family_descends (prefixWord ++ tailWord_320604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320607 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 4]
def baseStart_320607 : Nat := 118140960795 + 320607 * 2 ^ 59
def prefixEnd_320607 : Nat := 4983230072969 + 3 ^ 40 * 320607 * 2
def baseEnd_320607 : Nat := 164625492196132357338061

theorem tailTrace_320607 : CollatzResearch.WordTrace tailWord_320607 prefixEnd_320607 164625492196132357338061 := by
  unfold tailWord_320607
  simp only [CollatzResearch.WordTrace]
  refine ⟨11693497949503069161416075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7795665299668712774277383 11693497949503069161416075)
  ·
    refine ⟨17540246924254603742124113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11693497949503069161416075 17540246924254603742124113)
    ·
      refine ⟨13155185193190952806593085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17540246924254603742124113 13155185193190952806593085)
      ·
        refine ⟨4933194447446607302472407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13155185193190952806593085 4933194447446607302472407)
        ·
          refine ⟨7399791671169910953708611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4933194447446607302472407 7399791671169910953708611)
          ·
            refine ⟨11099687506754866430562917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7399791671169910953708611 11099687506754866430562917)
            ·
              refine ⟨2081191407516537455730547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11099687506754866430562917 2081191407516537455730547)
              ·
                refine ⟨3121787111274806183595821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2081191407516537455730547 3121787111274806183595821)
                ·
                  refine ⟨1170670166728052318848433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3121787111274806183595821 1170670166728052318848433)
                  ·
                    refine ⟨878002625046039239136325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1170670166728052318848433 878002625046039239136325)
                    ·
                      refine ⟨164625492196132357338061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 878002625046039239136325 164625492196132357338061)
                      ·
                        rfl

theorem cell23_320607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_320607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320607 prefixEnd_320607 := by exact prefixLift 320607
  have htrace : WordTrace (prefixWord ++ tailWord_320607) baseStart_320607 baseEnd_320607 := by
    simpa [prefixWord, tailWord_320607, baseEnd_320607] using wordTrace_append hprefix tailTrace_320607
  have hstable : (prefixWord ++ tailWord_320607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320607).length < 2 ^ (prefixWord ++ tailWord_320607).sum := by decide
  have hdescent : baseEnd_320607 < baseStart_320607 := by decide
  rcases family_descends (prefixWord ++ tailWord_320607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320617 : List Nat := [1, 2, 1, 1, 1, 8, 9]
def baseStart_320617 : Nat := 118140960795 + 320617 * 2 ^ 59
def prefixEnd_320617 : Nat := 4983230072969 + 3 ^ 40 * 320617 * 2
def baseEnd_320617 : Nat := 2032476876576263187815

theorem tailTrace_320617 : CollatzResearch.WordTrace tailWord_320617 prefixEnd_320617 2032476876576263187815 := by
  unfold tailWord_320617
  simp only [CollatzResearch.WordTrace]
  refine ⟨11693862679466840869280105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7795908452977893912853403 11693862679466840869280105)
  ·
    refine ⟨8770397009600130651960079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11693862679466840869280105 8770397009600130651960079)
    ·
      refine ⟨13155595514400195977940119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8770397009600130651960079 13155595514400195977940119)
      ·
        refine ⟨19733393271600293966910179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13155595514400195977940119 19733393271600293966910179)
        ·
          refine ⟨29600089907400440950365269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19733393271600293966910179 29600089907400440950365269)
          ·
            refine ⟨346876053602348917387093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 29600089907400440950365269 346876053602348917387093)
            ·
              refine ⟨2032476876576263187815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 346876053602348917387093 2032476876576263187815)
              ·
                rfl

theorem cell23_320617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 9].length) (baseStart_320617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320617 prefixEnd_320617 := by exact prefixLift 320617
  have htrace : WordTrace (prefixWord ++ tailWord_320617) baseStart_320617 baseEnd_320617 := by
    simpa [prefixWord, tailWord_320617, baseEnd_320617] using wordTrace_append hprefix tailTrace_320617
  have hstable : (prefixWord ++ tailWord_320617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320617).length < 2 ^ (prefixWord ++ tailWord_320617).sum := by decide
  have hdescent : baseEnd_320617 < baseStart_320617 := by decide
  rcases family_descends (prefixWord ++ tailWord_320617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320637 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_320637 : Nat := 118140960795 + 320637 * 2 ^ 59
def prefixEnd_320637 : Nat := 4983230072969 + 3 ^ 40 * 320637 * 2
def baseEnd_320637 : Nat := 164640896615767239962923

theorem tailTrace_320637 : CollatzResearch.WordTrace tailWord_320637 prefixEnd_320637 164640896615767239962923 := by
  unfold tailWord_320637
  simp only [CollatzResearch.WordTrace]
  refine ⟨11694592139394384285008165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7796394759596256190005443 11694592139394384285008165)
  ·
    refine ⟨2192736026136447053439031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11694592139394384285008165 2192736026136447053439031)
    ·
      refine ⟨3289104039204670580158547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2192736026136447053439031 3289104039204670580158547)
      ·
        refine ⟨4933656058807005870237821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3289104039204670580158547 4933656058807005870237821)
        ·
          refine ⟨1850121022052627201339183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4933656058807005870237821 1850121022052627201339183)
          ·
            refine ⟨2775181533078940802008775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1850121022052627201339183 2775181533078940802008775)
            ·
              refine ⟨4162772299618411203013163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2775181533078940802008775 4162772299618411203013163)
              ·
                refine ⟨6244158449427616804519745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4162772299618411203013163 6244158449427616804519745)
                ·
                  refine ⟨4683118837070712603389809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6244158449427616804519745 4683118837070712603389809)
                  ·
                    refine ⟨3512339127803034452542357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4683118837070712603389809 3512339127803034452542357)
                    ·
                      refine ⟨164640896615767239962923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3512339127803034452542357 164640896615767239962923)
                      ·
                        rfl

theorem cell23_320637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_320637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320637 prefixEnd_320637 := by exact prefixLift 320637
  have htrace : WordTrace (prefixWord ++ tailWord_320637) baseStart_320637 baseEnd_320637 := by
    simpa [prefixWord, tailWord_320637, baseEnd_320637] using wordTrace_append hprefix tailTrace_320637
  have hstable : (prefixWord ++ tailWord_320637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320637).length < 2 ^ (prefixWord ++ tailWord_320637).sum := by decide
  have hdescent : baseEnd_320637 < baseStart_320637 := by decide
  rcases family_descends (prefixWord ++ tailWord_320637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320679 : List Nat := [1, 1, 6, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_320679 : Nat := 118140960795 + 320679 * 2 ^ 59
def prefixEnd_320679 : Nat := 4983230072969 + 3 ^ 40 * 320679 * 2
def baseEnd_320679 : Nat := 164662462803256075637731

theorem tailTrace_320679 : CollatzResearch.WordTrace tailWord_320679 prefixEnd_320679 164662462803256075637731 := by
  unfold tailWord_320679
  simp only [CollatzResearch.WordTrace]
  refine ⟨11696124005242225458037091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7797416003494816972024727 11696124005242225458037091)
  ·
    refine ⟨17544186007863338187055637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11696124005242225458037091 17544186007863338187055637)
    ·
      refine ⟨822383719118593977518233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17544186007863338187055637 822383719118593977518233)
      ·
        refine ⟨616787789338945483138675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 822383719118593977518233 616787789338945483138675)
        ·
          refine ⟨925181684008418224708013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616787789338945483138675 925181684008418224708013)
          ·
            refine ⟨346943131503156834265505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 925181684008418224708013 346943131503156834265505)
            ·
              refine ⟨260207348627367625699129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346943131503156834265505 260207348627367625699129)
              ·
                refine ⟨195155511470525719274347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260207348627367625699129 195155511470525719274347)
                ·
                  refine ⟨292733267205788578911521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195155511470525719274347 292733267205788578911521)
                  ·
                    refine ⟨219549950404341434183641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 292733267205788578911521 219549950404341434183641)
                    ·
                      refine ⟨164662462803256075637731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 219549950404341434183641 164662462803256075637731)
                      ·
                        rfl

theorem cell23_320679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_320679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320679 prefixEnd_320679 := by exact prefixLift 320679
  have htrace : WordTrace (prefixWord ++ tailWord_320679) baseStart_320679 baseEnd_320679 := by
    simpa [prefixWord, tailWord_320679, baseEnd_320679] using wordTrace_append hprefix tailTrace_320679
  have hstable : (prefixWord ++ tailWord_320679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320679).length < 2 ^ (prefixWord ++ tailWord_320679).sum := by decide
  have hdescent : baseEnd_320679 < baseStart_320679 := by decide
  rcases family_descends (prefixWord ++ tailWord_320679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320687 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 5]
def baseStart_320687 : Nat := 118140960795 + 320687 * 2 ^ 59
def prefixEnd_320687 : Nat := 4983230072969 + 3 ^ 40 * 320687 * 2
def baseEnd_320687 : Nat := 164666570648492044337693

theorem tailTrace_320687 : CollatzResearch.WordTrace tailWord_320687 prefixEnd_320687 164666570648492044337693 := by
  unfold tailWord_320687
  simp only [CollatzResearch.WordTrace]
  refine ⟨11696415789213242824328315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7797610526142161882885543 11696415789213242824328315)
  ·
    refine ⟨17544623683819864236492473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11696415789213242824328315 17544623683819864236492473)
    ·
      refine ⟨13158467762864898177369355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17544623683819864236492473 13158467762864898177369355)
      ·
        refine ⟨19737701644297347266054033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13158467762864898177369355 19737701644297347266054033)
        ·
          refine ⟨14803276233223010449540525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19737701644297347266054033 14803276233223010449540525)
          ·
            refine ⟨5551228587458628918577697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14803276233223010449540525 5551228587458628918577697)
            ·
              refine ⟨4163421440593971688933273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5551228587458628918577697 4163421440593971688933273)
              ·
                refine ⟨3122566080445478766699955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4163421440593971688933273 3122566080445478766699955)
                ·
                  refine ⟨4683849120668218150049933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3122566080445478766699955 4683849120668218150049933)
                  ·
                    refine ⟨1756443420250581806268725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4683849120668218150049933 1756443420250581806268725)
                    ·
                      refine ⟨164666570648492044337693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1756443420250581806268725 164666570648492044337693)
                      ·
                        rfl

theorem cell23_320687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_320687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320687 prefixEnd_320687 := by exact prefixLift 320687
  have htrace : WordTrace (prefixWord ++ tailWord_320687) baseStart_320687 baseEnd_320687 := by
    simpa [prefixWord, tailWord_320687, baseEnd_320687] using wordTrace_append hprefix tailTrace_320687
  have hstable : (prefixWord ++ tailWord_320687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320687).length < 2 ^ (prefixWord ++ tailWord_320687).sum := by decide
  have hdescent : baseEnd_320687 < baseStart_320687 := by decide
  rcases family_descends (prefixWord ++ tailWord_320687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320701 : List Nat := [1, 4, 1, 2, 1, 1, 3, 3, 1, 4, 2]
def baseStart_320701 : Nat := 118140960795 + 320701 * 2 ^ 59
def prefixEnd_320701 : Nat := 4983230072969 + 3 ^ 40 * 320701 * 2
def baseEnd_320701 : Nat := 164673759377654989562629

theorem tailTrace_320701 : CollatzResearch.WordTrace tailWord_320701 prefixEnd_320701 164673759377654989562629 := by
  unfold tailWord_320701
  simp only [CollatzResearch.WordTrace]
  refine ⟨11696926411162523215337957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7797950940775015476891971 11696926411162523215337957)
  ·
    refine ⟨2193173702092973102875867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11696926411162523215337957 2193173702092973102875867)
    ·
      refine ⟨3289760553139459654313801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2193173702092973102875867 3289760553139459654313801)
      ·
        refine ⟨2467320414854594740735351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3289760553139459654313801 2467320414854594740735351)
        ·
          refine ⟨3700980622281892111103027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2467320414854594740735351 3700980622281892111103027)
          ·
            refine ⟨5551470933422838166654541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3700980622281892111103027 5551470933422838166654541)
            ·
              refine ⟨2081801600033564312495453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5551470933422838166654541 2081801600033564312495453)
              ·
                refine ⟨780675600012586617185795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2081801600033564312495453 780675600012586617185795)
                ·
                  refine ⟨1171013400018879925778693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780675600012586617185795 1171013400018879925778693)
                  ·
                    refine ⟨219565012503539986083505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1171013400018879925778693 219565012503539986083505)
                    ·
                      refine ⟨164673759377654989562629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 219565012503539986083505 164673759377654989562629)
                      ·
                        rfl

theorem cell23_320701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_320701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320701 prefixEnd_320701 := by exact prefixLift 320701
  have htrace : WordTrace (prefixWord ++ tailWord_320701) baseStart_320701 baseEnd_320701 := by
    simpa [prefixWord, tailWord_320701, baseEnd_320701] using wordTrace_append hprefix tailTrace_320701
  have hstable : (prefixWord ++ tailWord_320701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320701).length < 2 ^ (prefixWord ++ tailWord_320701).sum := by decide
  have hdescent : baseEnd_320701 < baseStart_320701 := by decide
  rcases family_descends (prefixWord ++ tailWord_320701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320741 : List Nat := [1, 3, 1, 4, 3, 1, 2, 1, 7]
def baseStart_320741 : Nat := 118140960795 + 320741 * 2 ^ 59
def prefixEnd_320741 : Nat := 4983230072969 + 3 ^ 40 * 320741 * 2
def baseEnd_320741 : Nat := 18299366511537203673605

theorem tailTrace_320741 : CollatzResearch.WordTrace tailWord_320741 prefixEnd_320741 18299366511537203673605 := by
  unfold tailWord_320741
  simp only [CollatzResearch.WordTrace]
  refine ⟨11698385331017610046794077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7798923554011740031196051 11698385331017610046794077)
  ·
    refine ⟨4386894499131603767547779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11698385331017610046794077 4386894499131603767547779)
    ·
      refine ⟨6580341748697405651321669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4386894499131603767547779 6580341748697405651321669)
      ·
        refine ⟨1233814077880763559622813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6580341748697405651321669 1233814077880763559622813)
        ·
          refine ⟨462680279205286334858555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1233814077880763559622813 462680279205286334858555)
          ·
            refine ⟨694020418807929502287833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462680279205286334858555 694020418807929502287833)
            ·
              refine ⟨520515314105947126715875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 694020418807929502287833 520515314105947126715875)
              ·
                refine ⟨780772971158920690073813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520515314105947126715875 780772971158920690073813)
                ·
                  refine ⟨18299366511537203673605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 780772971158920690073813 18299366511537203673605)
                  ·
                    rfl

theorem cell23_320741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 7].length) (baseStart_320741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320741 prefixEnd_320741 := by exact prefixLift 320741
  have htrace : WordTrace (prefixWord ++ tailWord_320741) baseStart_320741 baseEnd_320741 := by
    simpa [prefixWord, tailWord_320741, baseEnd_320741] using wordTrace_append hprefix tailTrace_320741
  have hstable : (prefixWord ++ tailWord_320741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320741).length < 2 ^ (prefixWord ++ tailWord_320741).sum := by decide
  have hdescent : baseEnd_320741 < baseStart_320741 := by decide
  rcases family_descends (prefixWord ++ tailWord_320741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320791 : List Nat := [1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 4]
def baseStart_320791 : Nat := 118140960795 + 320791 * 2 ^ 59
def prefixEnd_320791 : Nat := 4983230072969 + 3 ^ 40 * 320791 * 2
def baseEnd_320791 : Nat := 164719972636559637437215

theorem tailTrace_320791 : CollatzResearch.WordTrace tailWord_320791 prefixEnd_320791 164719972636559637437215 := by
  unfold tailWord_320791
  simp only [CollatzResearch.WordTrace]
  refine ⟨11700208980836468586114227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7800139320557645724076151 11700208980836468586114227)
  ·
    refine ⟨17550313471254702879171341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11700208980836468586114227 17550313471254702879171341)
    ·
      refine ⟨6581367551720513579689253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17550313471254702879171341 6581367551720513579689253)
      ·
        refine ⟨1234006415947596296191735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6581367551720513579689253 1234006415947596296191735)
        ·
          refine ⟨1851009623921394444287603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234006415947596296191735 1851009623921394444287603)
          ·
            refine ⟨2776514435882091666431405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1851009623921394444287603 2776514435882091666431405)
            ·
              refine ⟨1041192913455784374911777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2776514435882091666431405 1041192913455784374911777)
              ·
                refine ⟨780894685091838281183833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1041192913455784374911777 780894685091838281183833)
                ·
                  refine ⟨585671013818878710887875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 780894685091838281183833 585671013818878710887875)
                  ·
                    refine ⟨878506520728318066331813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 585671013818878710887875 878506520728318066331813)
                    ·
                      refine ⟨164719972636559637437215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 878506520728318066331813 164719972636559637437215)
                      ·
                        rfl

theorem cell23_320791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_320791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320791 prefixEnd_320791 := by exact prefixLift 320791
  have htrace : WordTrace (prefixWord ++ tailWord_320791) baseStart_320791 baseEnd_320791 := by
    simpa [prefixWord, tailWord_320791, baseEnd_320791] using wordTrace_append hprefix tailTrace_320791
  have hstable : (prefixWord ++ tailWord_320791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320791).length < 2 ^ (prefixWord ++ tailWord_320791).sum := by decide
  have hdescent : baseEnd_320791 < baseStart_320791 := by decide
  rcases family_descends (prefixWord ++ tailWord_320791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320828 : List Nat := [2, 2, 2, 2, 1, 4, 2, 1, 2, 2, 3]
def baseStart_320828 : Nat := 118140960795 + 320828 * 2 ^ 59
def prefixEnd_320828 : Nat := 4983230072969 + 3 ^ 40 * 320828 * 2
def baseEnd_320828 : Nat := 164738971420775992674545

theorem tailTrace_320828 : CollatzResearch.WordTrace tailWord_320828 prefixEnd_320828 164738971420775992674545 := by
  unfold tailWord_320828
  simp only [CollatzResearch.WordTrace]
  refine ⟨5850779240851211952605569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7801038987801615936807425 5850779240851211952605569)
  ·
    refine ⟨4388084430638408964454177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5850779240851211952605569 4388084430638408964454177)
    ·
      refine ⟨3291063322978806723340633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4388084430638408964454177 3291063322978806723340633)
      ·
        refine ⟨2468297492234105042505475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3291063322978806723340633 2468297492234105042505475)
        ·
          refine ⟨3702446238351157563758213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2468297492234105042505475 3702446238351157563758213)
          ·
            refine ⟨694208669690842043204665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3702446238351157563758213 694208669690842043204665)
            ·
              refine ⟨520656502268131532403499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 694208669690842043204665 520656502268131532403499)
              ·
                refine ⟨780984753402197298605249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520656502268131532403499 780984753402197298605249)
                ·
                  refine ⟨585738565051647973953937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 780984753402197298605249 585738565051647973953937)
                  ·
                    refine ⟨439303923788735980465453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 585738565051647973953937 439303923788735980465453)
                    ·
                      refine ⟨164738971420775992674545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 439303923788735980465453 164738971420775992674545)
                      ·
                        rfl

theorem cell23_320828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_320828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320828 prefixEnd_320828 := by exact prefixLift 320828
  have htrace : WordTrace (prefixWord ++ tailWord_320828) baseStart_320828 baseEnd_320828 := by
    simpa [prefixWord, tailWord_320828, baseEnd_320828] using wordTrace_append hprefix tailTrace_320828
  have hstable : (prefixWord ++ tailWord_320828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320828).length < 2 ^ (prefixWord ++ tailWord_320828).sum := by decide
  have hdescent : baseEnd_320828 < baseStart_320828 := by decide
  rcases family_descends (prefixWord ++ tailWord_320828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320881 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 3, 1, 4]
def baseStart_320881 : Nat := 118140960795 + 320881 * 2 ^ 59
def prefixEnd_320881 : Nat := 4983230072969 + 3 ^ 40 * 320881 * 2
def baseEnd_320881 : Nat := 164766185895464285311801

theorem tailTrace_320881 : CollatzResearch.WordTrace tailWord_320881 prefixEnd_320881 164766185895464285311801 := by
  unfold tailWord_320881
  simp only [CollatzResearch.WordTrace]
  refine ⟨11703491550510413956890497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7802327700340275971260331 11703491550510413956890497)
  ·
    refine ⟨8777618662882810467667873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11703491550510413956890497 8777618662882810467667873)
    ·
      refine ⟨6583213997162107850750905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8777618662882810467667873 6583213997162107850750905)
      ·
        refine ⟨4937410497871580888063179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6583213997162107850750905 4937410497871580888063179)
        ·
          refine ⟨7406115746807371332094769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4937410497871580888063179 7406115746807371332094769)
          ·
            refine ⟨5554586810105528499071077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7406115746807371332094769 5554586810105528499071077)
            ·
              refine ⟨1041485026894786593575827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5554586810105528499071077 1041485026894786593575827)
              ·
                refine ⟨1562227540342179890363741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1041485026894786593575827 1562227540342179890363741)
                ·
                  refine ⟨585835327628317458886403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1562227540342179890363741 585835327628317458886403)
                  ·
                    refine ⟨878752991442476188329605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 585835327628317458886403 878752991442476188329605)
                    ·
                      refine ⟨164766185895464285311801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 878752991442476188329605 164766185895464285311801)
                      ·
                        rfl

theorem cell23_320881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_320881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320881 prefixEnd_320881 := by exact prefixLift 320881
  have htrace : WordTrace (prefixWord ++ tailWord_320881) baseStart_320881 baseEnd_320881 := by
    simpa [prefixWord, tailWord_320881, baseEnd_320881] using wordTrace_append hprefix tailTrace_320881
  have hstable : (prefixWord ++ tailWord_320881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320881).length < 2 ^ (prefixWord ++ tailWord_320881).sum := by decide
  have hdescent : baseEnd_320881 < baseStart_320881 := by decide
  rcases family_descends (prefixWord ++ tailWord_320881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320885 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_320885 : Nat := 118140960795 + 320885 * 2 ^ 59
def prefixEnd_320885 : Nat := 4983230072969 + 3 ^ 40 * 320885 * 2
def baseEnd_320885 : Nat := 164768239818082269661783

theorem tailTrace_320885 : CollatzResearch.WordTrace tailWord_320885 prefixEnd_320885 164768239818082269661783 := by
  unfold tailWord_320885
  simp only [CollatzResearch.WordTrace]
  refine ⟨11703637442495922640036109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7802424961663948426690739 11703637442495922640036109)
  ·
    refine ⟨4388864040935970990013541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11703637442495922640036109 4388864040935970990013541)
    ·
      refine ⟨822912007675494560627539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4388864040935970990013541 822912007675494560627539)
      ·
        refine ⟨1234368011513241840941309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 822912007675494560627539 1234368011513241840941309)
        ·
          refine ⟨462888004317465690352991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1234368011513241840941309 462888004317465690352991)
          ·
            refine ⟨694332006476198535529487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462888004317465690352991 694332006476198535529487)
            ·
              refine ⟨1041498009714297803294231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 694332006476198535529487 1041498009714297803294231)
              ·
                refine ⟨1562247014571446704941347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1041498009714297803294231 1562247014571446704941347)
                ·
                  refine ⟨2343370521857170057412021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1562247014571446704941347 2343370521857170057412021)
                  ·
                    refine ⟨219690986424109692882377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2343370521857170057412021 219690986424109692882377)
                    ·
                      refine ⟨164768239818082269661783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 219690986424109692882377 164768239818082269661783)
                      ·
                        rfl

theorem cell23_320885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_320885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320885 prefixEnd_320885 := by exact prefixLift 320885
  have htrace : WordTrace (prefixWord ++ tailWord_320885) baseStart_320885 baseEnd_320885 := by
    simpa [prefixWord, tailWord_320885, baseEnd_320885] using wordTrace_append hprefix tailTrace_320885
  have hstable : (prefixWord ++ tailWord_320885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320885).length < 2 ^ (prefixWord ++ tailWord_320885).sum := by decide
  have hdescent : baseEnd_320885 < baseStart_320885 := by decide
  rcases family_descends (prefixWord ++ tailWord_320885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320891 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 4, 4]
def baseStart_320891 : Nat := 118140960795 + 320891 * 2 ^ 59
def prefixEnd_320891 : Nat := 4983230072969 + 3 ^ 40 * 320891 * 2
def baseEnd_320891 : Nat := 54923773567336415395585

theorem tailTrace_320891 : CollatzResearch.WordTrace tailWord_320891 prefixEnd_320891 54923773567336415395585 := by
  unfold tailWord_320891
  simp only [CollatzResearch.WordTrace]
  refine ⟨11703856280474185664754527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7802570853649457109836351 11703856280474185664754527)
  ·
    refine ⟨17555784420711278497131791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11703856280474185664754527 17555784420711278497131791)
    ·
      refine ⟨26333676631066917745697687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17555784420711278497131791 26333676631066917745697687)
      ·
        refine ⟨39500514946600376618546531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26333676631066917745697687 39500514946600376618546531)
        ·
          refine ⟨59250772419900564927819797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39500514946600376618546531 59250772419900564927819797)
          ·
            refine ⟨2777379957182838980991553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59250772419900564927819797 2777379957182838980991553)
            ·
              refine ⟨2083034967887129235743665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2777379957182838980991553 2083034967887129235743665)
              ·
                refine ⟨1562276225915346926807749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2083034967887129235743665 1562276225915346926807749)
                ·
                  refine ⟨292926792359127548776453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1562276225915346926807749 292926792359127548776453)
                  ·
                    refine ⟨54923773567336415395585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 292926792359127548776453 54923773567336415395585)
                    ·
                      rfl

theorem cell23_320891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 4].length) (baseStart_320891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320891 prefixEnd_320891 := by exact prefixLift 320891
  have htrace : WordTrace (prefixWord ++ tailWord_320891) baseStart_320891 baseEnd_320891 := by
    simpa [prefixWord, tailWord_320891, baseEnd_320891] using wordTrace_append hprefix tailTrace_320891
  have hstable : (prefixWord ++ tailWord_320891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320891).length < 2 ^ (prefixWord ++ tailWord_320891).sum := by decide
  have hdescent : baseEnd_320891 < baseStart_320891 := by decide
  rcases family_descends (prefixWord ++ tailWord_320891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320935 : List Nat := [1, 1, 6, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_320935 : Nat := 118140960795 + 320935 * 2 ^ 59
def prefixEnd_320935 : Nat := 4983230072969 + 3 ^ 40 * 320935 * 2
def baseEnd_320935 : Nat := 164793913850807074036553

theorem tailTrace_320935 : CollatzResearch.WordTrace tailWord_320935 prefixEnd_320935 164793913850807074036553 := by
  unfold tailWord_320935
  simp only [CollatzResearch.WordTrace]
  refine ⟨11705461092314781179356259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7803640728209854119570839 11705461092314781179356259)
  ·
    refine ⟨17558191638472171769034389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11705461092314781179356259 17558191638472171769034389)
    ·
      refine ⟨823040233053383051673487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17558191638472171769034389 823040233053383051673487)
      ·
        refine ⟨1234560349580074577510231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 823040233053383051673487 1234560349580074577510231)
        ·
          refine ⟨1851840524370111866265347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234560349580074577510231 1851840524370111866265347)
          ·
            refine ⟨2777760786555167799398021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1851840524370111866265347 2777760786555167799398021)
            ·
              refine ⟨520830147479093962387129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2777760786555167799398021 520830147479093962387129)
              ·
                refine ⟨390622610609320471790347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 520830147479093962387129 390622610609320471790347)
                ·
                  refine ⟨585933915913980707685521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390622610609320471790347 585933915913980707685521)
                  ·
                    refine ⟨439450436935485530764141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 585933915913980707685521 439450436935485530764141)
                    ·
                      refine ⟨164793913850807074036553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 439450436935485530764141 164793913850807074036553)
                      ·
                        rfl

theorem cell23_320935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_320935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320935 prefixEnd_320935 := by exact prefixLift 320935
  have htrace : WordTrace (prefixWord ++ tailWord_320935) baseStart_320935 baseEnd_320935 := by
    simpa [prefixWord, tailWord_320935, baseEnd_320935] using wordTrace_append hprefix tailTrace_320935
  have hstable : (prefixWord ++ tailWord_320935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320935).length < 2 ^ (prefixWord ++ tailWord_320935).sum := by decide
  have hdescent : baseEnd_320935 < baseStart_320935 := by decide
  rcases family_descends (prefixWord ++ tailWord_320935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320949 : List Nat := [1, 3, 3, 2, 2, 1, 3, 3, 1, 2, 2]
def baseStart_320949 : Nat := 118140960795 + 320949 * 2 ^ 59
def prefixEnd_320949 : Nat := 4983230072969 + 3 ^ 40 * 320949 * 2
def baseEnd_320949 : Nat := 164801102579970019261489

theorem tailTrace_320949 : CollatzResearch.WordTrace tailWord_320949 prefixEnd_320949 164801102579970019261489 := by
  unfold tailWord_320949
  simp only [CollatzResearch.WordTrace]
  refine ⟨11705971714264061570365901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7803981142842707713577267 11705971714264061570365901)
  ·
    refine ⟨4389739392849023088887213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11705971714264061570365901 4389739392849023088887213)
    ·
      refine ⟨1646152272318383658332705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4389739392849023088887213 1646152272318383658332705)
      ·
        refine ⟨1234614204238787743749529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1646152272318383658332705 1234614204238787743749529)
        ·
          refine ⟨925960653179090807812147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1234614204238787743749529 925960653179090807812147)
          ·
            refine ⟨1388940979768636211718221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925960653179090807812147 1388940979768636211718221)
            ·
              refine ⟨520852867413238579394333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1388940979768636211718221 520852867413238579394333)
              ·
                refine ⟨195319825279964467272875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 520852867413238579394333 195319825279964467272875)
                ·
                  refine ⟨292979737919946700909313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195319825279964467272875 292979737919946700909313)
                  ·
                    refine ⟨219734803439960025681985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 292979737919946700909313 219734803439960025681985)
                    ·
                      refine ⟨164801102579970019261489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 219734803439960025681985 164801102579970019261489)
                      ·
                        rfl

theorem cell23_320949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_320949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320949 prefixEnd_320949 := by exact prefixLift 320949
  have htrace : WordTrace (prefixWord ++ tailWord_320949) baseStart_320949 baseEnd_320949 := by
    simpa [prefixWord, tailWord_320949, baseEnd_320949] using wordTrace_append hprefix tailTrace_320949
  have hstable : (prefixWord ++ tailWord_320949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320949).length < 2 ^ (prefixWord ++ tailWord_320949).sum := by decide
  have hdescent : baseEnd_320949 < baseStart_320949 := by decide
  rcases family_descends (prefixWord ++ tailWord_320949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320981 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 1, 8]
def baseStart_320981 : Nat := 118140960795 + 320981 * 2 ^ 59
def prefixEnd_320981 : Nat := 4983230072969 + 3 ^ 40 * 320981 * 2
def baseEnd_320981 : Nat := 54939177986971298020447

theorem tailTrace_320981 : CollatzResearch.WordTrace tailWord_320981 prefixEnd_320981 54939177986971298020447 := by
  unfold tailWord_320981
  simp only [CollatzResearch.WordTrace]
  refine ⟨11707138850148131035530797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7804759233432087357020531 11707138850148131035530797)
  ·
    refine ⟨4390177068805549138324049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11707138850148131035530797 4390177068805549138324049)
    ·
      refine ⟨3292632801604161853743037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4390177068805549138324049 3292632801604161853743037)
      ·
        refine ⟨1234737300601560695153639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3292632801604161853743037 1234737300601560695153639)
        ·
          refine ⟨1852105950902341042730459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234737300601560695153639 1852105950902341042730459)
          ·
            refine ⟨2778158926353511564095689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1852105950902341042730459 2778158926353511564095689)
            ·
              refine ⟨2083619194765133673071767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2778158926353511564095689 2083619194765133673071767)
              ·
                refine ⟨3125428792147700509607651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2083619194765133673071767 3125428792147700509607651)
                ·
                  refine ⟨4688143188221550764411477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3125428792147700509607651 4688143188221550764411477)
                  ·
                    refine ⟨54939177986971298020447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4688143188221550764411477 54939177986971298020447)
                    ·
                      rfl

theorem cell23_320981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_320981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320981 prefixEnd_320981 := by exact prefixLift 320981
  have htrace : WordTrace (prefixWord ++ tailWord_320981) baseStart_320981 baseEnd_320981 := by
    simpa [prefixWord, tailWord_320981, baseEnd_320981] using wordTrace_append hprefix tailTrace_320981
  have hstable : (prefixWord ++ tailWord_320981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320981).length < 2 ^ (prefixWord ++ tailWord_320981).sum := by decide
  have hdescent : baseEnd_320981 < baseStart_320981 := by decide
  rcases family_descends (prefixWord ++ tailWord_320981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320991 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 5]
def baseStart_320991 : Nat := 118140960795 + 320991 * 2 ^ 59
def prefixEnd_320991 : Nat := 4983230072969 + 3 ^ 40 * 320991 * 2
def baseEnd_320991 : Nat := 164822668767458854936295

theorem tailTrace_320991 : CollatzResearch.WordTrace tailWord_320991 prefixEnd_320991 164822668767458854936295 := by
  unfold tailWord_320991
  simp only [CollatzResearch.WordTrace]
  refine ⟨11707503580111902743394827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7805002386741268495596551 11707503580111902743394827)
  ·
    refine ⟨17561255370167854115092241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11707503580111902743394827 17561255370167854115092241)
    ·
      refine ⟨13170941527625890586319181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17561255370167854115092241 13170941527625890586319181)
      ·
        refine ⟨4939103072859708969869693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13170941527625890586319181 4939103072859708969869693)
        ·
          refine ⟨1852163652322390863701135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4939103072859708969869693 1852163652322390863701135)
          ·
            refine ⟨2778245478483586295551703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1852163652322390863701135 2778245478483586295551703)
            ·
              refine ⟨4167368217725379443327555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2778245478483586295551703 4167368217725379443327555)
              ·
                refine ⟨6251052326588069164991333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4167368217725379443327555 6251052326588069164991333)
                ·
                  refine ⟨1172072311235262968435875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6251052326588069164991333 1172072311235262968435875)
                  ·
                    refine ⟨1758108466852894452653813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1172072311235262968435875 1758108466852894452653813)
                    ·
                      refine ⟨164822668767458854936295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1758108466852894452653813 164822668767458854936295)
                      ·
                        rfl

theorem cell23_320991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_320991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_320991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_320991 prefixEnd_320991 := by exact prefixLift 320991
  have htrace : WordTrace (prefixWord ++ tailWord_320991) baseStart_320991 baseEnd_320991 := by
    simpa [prefixWord, tailWord_320991, baseEnd_320991] using wordTrace_append hprefix tailTrace_320991
  have hstable : (prefixWord ++ tailWord_320991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320991).length < 2 ^ (prefixWord ++ tailWord_320991).sum := by decide
  have hdescent : baseEnd_320991 < baseStart_320991 := by decide
  rcases family_descends (prefixWord ++ tailWord_320991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321041 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 1, 7]
def baseStart_321041 : Nat := 118140960795 + 321041 * 2 ^ 59
def prefixEnd_321041 : Nat := 4983230072969 + 3 ^ 40 * 321041 * 2
def baseEnd_321041 : Nat := 54949447600061219770355

theorem tailTrace_321041 : CollatzResearch.WordTrace tailWord_321041 prefixEnd_321041 54949447600061219770355 := by
  unfold tailWord_321041
  simp only [CollatzResearch.WordTrace]
  refine ⟨11709327229930761282714977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7806218153287174188476651 11709327229930761282714977)
  ·
    refine ⟨8781995422448070962036233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11709327229930761282714977 8781995422448070962036233)
    ·
      refine ⟨6586496566836053221527175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8781995422448070962036233 6586496566836053221527175)
      ·
        refine ⟨9879744850254079832290763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6586496566836053221527175 9879744850254079832290763)
        ·
          refine ⟨14819617275381119748436145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9879744850254079832290763 14819617275381119748436145)
          ·
            refine ⟨11114712956535839811327109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14819617275381119748436145 11114712956535839811327109)
            ·
              refine ⟨2084008679350469964623833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11114712956535839811327109 2084008679350469964623833)
              ·
                refine ⟨1563006509512852473467875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2084008679350469964623833 1563006509512852473467875)
                ·
                  refine ⟨2344509764269278710201813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1563006509512852473467875 2344509764269278710201813)
                  ·
                    refine ⟨54949447600061219770355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2344509764269278710201813 54949447600061219770355)
                    ·
                      rfl

theorem cell23_321041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_321041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321041 prefixEnd_321041 := by exact prefixLift 321041
  have htrace : WordTrace (prefixWord ++ tailWord_321041) baseStart_321041 baseEnd_321041 := by
    simpa [prefixWord, tailWord_321041, baseEnd_321041] using wordTrace_append hprefix tailTrace_321041
  have hstable : (prefixWord ++ tailWord_321041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321041).length < 2 ^ (prefixWord ++ tailWord_321041).sum := by decide
  have hdescent : baseEnd_321041 < baseStart_321041 := by decide
  rcases family_descends (prefixWord ++ tailWord_321041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321098 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 3, 4, 3]
def baseStart_321098 : Nat := 118140960795 + 321098 * 2 ^ 59
def prefixEnd_321098 : Nat := 4983230072969 + 3 ^ 40 * 321098 * 2
def baseEnd_321098 : Nat := 164877611197489936298303

theorem tailTrace_321098 : CollatzResearch.WordTrace tailWord_321098 prefixEnd_321098 164877611197489936298303 := by
  unfold tailWord_321098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2927851547681065004384987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7807604127149506678359965 2927851547681065004384987)
  ·
    refine ⟨4391777321521597506577481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2927851547681065004384987 4391777321521597506577481)
    ·
      refine ⟨3293832991141198129933111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4391777321521597506577481 3293832991141198129933111)
      ·
        refine ⟨4940749486711797194899667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3293832991141198129933111 4940749486711797194899667)
        ·
          refine ⟨7411124230067695792349501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4940749486711797194899667 7411124230067695792349501)
          ·
            refine ⟨2779171586275385922131063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7411124230067695792349501 2779171586275385922131063)
            ·
              refine ⟨4168757379413078883196595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2779171586275385922131063 4168757379413078883196595)
              ·
                refine ⟨6253136069119618324794893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4168757379413078883196595 6253136069119618324794893)
                ·
                  refine ⟨2344926025919856871798085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6253136069119618324794893 2344926025919856871798085)
                  ·
                    refine ⟨439673629859973163462141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2344926025919856871798085 439673629859973163462141)
                    ·
                      refine ⟨164877611197489936298303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 439673629859973163462141 164877611197489936298303)
                      ·
                        rfl

theorem cell23_321098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_321098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321098 prefixEnd_321098 := by exact prefixLift 321098
  have htrace : WordTrace (prefixWord ++ tailWord_321098) baseStart_321098 baseEnd_321098 := by
    simpa [prefixWord, tailWord_321098, baseEnd_321098] using wordTrace_append hprefix tailTrace_321098
  have hstable : (prefixWord ++ tailWord_321098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321098).length < 2 ^ (prefixWord ++ tailWord_321098).sum := by decide
  have hdescent : baseEnd_321098 < baseStart_321098 := by decide
  rcases family_descends (prefixWord ++ tailWord_321098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321108 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_321108 : Nat := 118140960795 + 321108 * 2 ^ 59
def prefixEnd_321108 : Nat := 4983230072969 + 3 ^ 40 * 321108 * 2
def baseEnd_321108 : Nat := 164882746004034897173257

theorem tailTrace_321108 : CollatzResearch.WordTrace tailWord_321108 prefixEnd_321108 164882746004034897173257 := by
  unfold tailWord_321108
  simp only [CollatzResearch.WordTrace]
  refine ⟨5855885460344015862701989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7807847280458687816935985 5855885460344015862701989)
  ·
    refine ⟨1097978523814502974256623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5855885460344015862701989 1097978523814502974256623)
    ·
      refine ⟨1646967785721754461384935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1097978523814502974256623 1646967785721754461384935)
      ·
        refine ⟨2470451678582631692077403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1646967785721754461384935 2470451678582631692077403)
        ·
          refine ⟨3705677517873947538116105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2470451678582631692077403 3705677517873947538116105)
          ·
            refine ⟨2779258138405460653587079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3705677517873947538116105 2779258138405460653587079)
            ·
              refine ⟨4168887207608190980380619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2779258138405460653587079 4168887207608190980380619)
              ·
                refine ⟨6253330811412286470570929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4168887207608190980380619 6253330811412286470570929)
                ·
                  refine ⟨4689998108559214852928197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6253330811412286470570929 4689998108559214852928197)
                  ·
                    refine ⟨879374645354852784924037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4689998108559214852928197 879374645354852784924037)
                    ·
                      refine ⟨164882746004034897173257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 879374645354852784924037 164882746004034897173257)
                      ·
                        rfl

theorem cell23_321108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_321108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321108 prefixEnd_321108 := by exact prefixLift 321108
  have htrace : WordTrace (prefixWord ++ tailWord_321108) baseStart_321108 baseEnd_321108 := by
    simpa [prefixWord, tailWord_321108, baseEnd_321108] using wordTrace_append hprefix tailTrace_321108
  have hstable : (prefixWord ++ tailWord_321108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321108).length < 2 ^ (prefixWord ++ tailWord_321108).sum := by decide
  have hdescent : baseEnd_321108 < baseStart_321108 := by decide
  rcases family_descends (prefixWord ++ tailWord_321108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321131 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 1, 11]
def baseStart_321131 : Nat := 118140960795 + 321131 * 2 ^ 59
def prefixEnd_321131 : Nat := 4983230072969 + 3 ^ 40 * 321131 * 2
def baseEnd_321131 : Nat := 54964852019696102395217

theorem tailTrace_321131 : CollatzResearch.WordTrace tailWord_321131 prefixEnd_321131 54964852019696102395217 := by
  unfold tailWord_321131
  simp only [CollatzResearch.WordTrace]
  refine ⟨11712609799604706653491247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7808406533069804435660831 11712609799604706653491247)
  ·
    refine ⟨17568914699407059980236871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11712609799604706653491247 17568914699407059980236871)
    ·
      refine ⟨26353372049110589970355307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17568914699407059980236871 26353372049110589970355307)
      ·
        refine ⟨39530058073665884955532961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26353372049110589970355307 39530058073665884955532961)
        ·
          refine ⟨29647543555249413716649721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39530058073665884955532961 29647543555249413716649721)
          ·
            refine ⟨22235657666437060287487291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29647543555249413716649721 22235657666437060287487291)
            ·
              refine ⟨33353486499655590431230937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22235657666437060287487291 33353486499655590431230937)
              ·
                refine ⟨25015114874741692823423203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33353486499655590431230937 25015114874741692823423203)
                ·
                  refine ⟨37522672312112539235134805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25015114874741692823423203 37522672312112539235134805)
                  ·
                    refine ⟨54964852019696102395217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 37522672312112539235134805 54964852019696102395217)
                    ·
                      rfl

theorem cell23_321131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 11].length) (baseStart_321131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321131 prefixEnd_321131 := by exact prefixLift 321131
  have htrace : WordTrace (prefixWord ++ tailWord_321131) baseStart_321131 baseEnd_321131 := by
    simpa [prefixWord, tailWord_321131, baseEnd_321131] using wordTrace_append hprefix tailTrace_321131
  have hstable : (prefixWord ++ tailWord_321131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321131).length < 2 ^ (prefixWord ++ tailWord_321131).sum := by decide
  have hdescent : baseEnd_321131 < baseStart_321131 := by decide
  rcases family_descends (prefixWord ++ tailWord_321131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321148 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 3, 5]
def baseStart_321148 : Nat := 118140960795 + 321148 * 2 ^ 59
def prefixEnd_321148 : Nat := 4983230072969 + 3 ^ 40 * 321148 * 2
def baseEnd_321148 : Nat := 54967761743404913557691

theorem tailTrace_321148 : CollatzResearch.WordTrace tailWord_321148 prefixEnd_321148 54967761743404913557691 := by
  unfold tailWord_321148
  simp only [CollatzResearch.WordTrace]
  refine ⟨5856614920271559278430049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7808819893695412371240065 5856614920271559278430049)
  ·
    refine ⟨4392461190203669458822537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5856614920271559278430049 4392461190203669458822537)
    ·
      refine ⟨3294345892652752094116903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4392461190203669458822537 3294345892652752094116903)
      ·
        refine ⟨4941518838979128141175355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3294345892652752094116903 4941518838979128141175355)
        ·
          refine ⟨7412278258468692211763033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4941518838979128141175355 7412278258468692211763033)
          ·
            refine ⟨5559208693851519158822275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7412278258468692211763033 5559208693851519158822275)
            ·
              refine ⟨8338813040777278738233413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5559208693851519158822275 8338813040777278738233413)
              ·
                refine ⟨1563527445145739763418765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8338813040777278738233413 1563527445145739763418765)
                ·
                  refine ⟨586322791929652411282037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1563527445145739763418765 586322791929652411282037)
                  ·
                    refine ⟨54967761743404913557691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 586322791929652411282037 54967761743404913557691)
                    ·
                      rfl

theorem cell23_321148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_321148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321148 prefixEnd_321148 := by exact prefixLift 321148
  have htrace : WordTrace (prefixWord ++ tailWord_321148) baseStart_321148 baseEnd_321148 := by
    simpa [prefixWord, tailWord_321148, baseEnd_321148] using wordTrace_append hprefix tailTrace_321148
  have hstable : (prefixWord ++ tailWord_321148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321148).length < 2 ^ (prefixWord ++ tailWord_321148).sum := by decide
  have hdescent : baseEnd_321148 < baseStart_321148 := by decide
  rcases family_descends (prefixWord ++ tailWord_321148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321155 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 6, 3, 2]
def baseStart_321155 : Nat := 118140960795 + 321155 * 2 ^ 59
def prefixEnd_321155 : Nat := 4983230072969 + 3 ^ 40 * 321155 * 2
def baseEnd_321155 : Nat := 164906879594796213285541

theorem tailTrace_321155 : CollatzResearch.WordTrace tailWord_321155 prefixEnd_321155 164906879594796213285541 := by
  unfold tailWord_321155
  simp only [CollatzResearch.WordTrace]
  refine ⟨11713485151517758752364919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7808990101011839168243279 11713485151517758752364919)
  ·
    refine ⟨17570227727276638128547379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11713485151517758752364919 17570227727276638128547379)
    ·
      refine ⟨26355341590914957192821069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17570227727276638128547379 26355341590914957192821069)
      ·
        refine ⟨9883253096593108947307901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26355341590914957192821069 9883253096593108947307901)
        ·
          refine ⟨3706219911222415855240463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9883253096593108947307901 3706219911222415855240463)
          ·
            refine ⟨5559329866833623782860695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3706219911222415855240463 5559329866833623782860695)
            ·
              refine ⟨8338994800250435674291043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5559329866833623782860695 8338994800250435674291043)
              ·
                refine ⟨12508492200375653511436565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8338994800250435674291043 12508492200375653511436565)
                ·
                  refine ⟨586335571892608758348589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12508492200375653511436565 586335571892608758348589)
                  ·
                    refine ⟨219875839459728284380721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 586335571892608758348589 219875839459728284380721)
                    ·
                      refine ⟨164906879594796213285541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 219875839459728284380721 164906879594796213285541)
                      ·
                        rfl

theorem cell23_321155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 3, 2].length) (baseStart_321155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321155 prefixEnd_321155 := by exact prefixLift 321155
  have htrace : WordTrace (prefixWord ++ tailWord_321155) baseStart_321155 baseEnd_321155 := by
    simpa [prefixWord, tailWord_321155, baseEnd_321155] using wordTrace_append hprefix tailTrace_321155
  have hstable : (prefixWord ++ tailWord_321155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321155).length < 2 ^ (prefixWord ++ tailWord_321155).sum := by decide
  have hdescent : baseEnd_321155 < baseStart_321155 := by decide
  rcases family_descends (prefixWord ++ tailWord_321155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321212 : List Nat := [2, 2, 2, 3, 1, 2, 2, 3, 2, 4]
def baseStart_321212 : Nat := 118140960795 + 321212 * 2 ^ 59
def prefixEnd_321212 : Nat := 4983230072969 + 3 ^ 40 * 321212 * 2
def baseEnd_321212 : Nat := 54978715997367496757593

theorem tailTrace_321212 : CollatzResearch.WordTrace tailWord_321212 prefixEnd_321212 54978715997367496757593 := by
  unfold tailWord_321212
  simp only [CollatzResearch.WordTrace]
  refine ⟨5857782056155628743594945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7810376074874171658126593 5857782056155628743594945)
  ·
    refine ⟨4393336542116721557696209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5857782056155628743594945 4393336542116721557696209)
    ·
      refine ⟨3295002406587541168272157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4393336542116721557696209 3295002406587541168272157)
      ·
        refine ⟨1235625902470327938102059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3295002406587541168272157 1235625902470327938102059)
        ·
          refine ⟨1853438853705491907153089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1235625902470327938102059 1853438853705491907153089)
          ·
            refine ⟨1390079140279118930364817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1853438853705491907153089 1390079140279118930364817)
            ·
              refine ⟨1042559355209339197773613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1390079140279118930364817 1042559355209339197773613)
              ·
                refine ⟨390959758203502199165105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1042559355209339197773613 390959758203502199165105)
                ·
                  refine ⟨293219818652626649373829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390959758203502199165105 293219818652626649373829)
                  ·
                    refine ⟨54978715997367496757593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 293219818652626649373829 54978715997367496757593)
                    ·
                      rfl

theorem cell23_321212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_321212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321212 prefixEnd_321212 := by exact prefixLift 321212
  have htrace : WordTrace (prefixWord ++ tailWord_321212) baseStart_321212 baseEnd_321212 := by
    simpa [prefixWord, tailWord_321212, baseEnd_321212] using wordTrace_append hprefix tailTrace_321212
  have hstable : (prefixWord ++ tailWord_321212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321212).length < 2 ^ (prefixWord ++ tailWord_321212).sum := by decide
  have hdescent : baseEnd_321212 < baseStart_321212 := by decide
  rcases family_descends (prefixWord ++ tailWord_321212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321215 : List Nat := [1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 4]
def baseStart_321215 : Nat := 118140960795 + 321215 * 2 ^ 59
def prefixEnd_321215 : Nat := 4983230072969 + 3 ^ 40 * 321215 * 2
def baseEnd_321215 : Nat := 164937688434065978535265

theorem tailTrace_321215 : CollatzResearch.WordTrace tailWord_321215 prefixEnd_321215 164937688434065978535265 := by
  unfold tailWord_321215
  simp only [CollatzResearch.WordTrace]
  refine ⟨11715673531300388999549099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7810449020866925999699399 11715673531300388999549099)
  ·
    refine ⟨17573510296950583499323649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11715673531300388999549099 17573510296950583499323649)
    ·
      refine ⟨13180132722712937624492737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17573510296950583499323649 13180132722712937624492737)
      ·
        refine ⟨9885099542034703218369553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13180132722712937624492737 9885099542034703218369553)
        ·
          refine ⟨7413824656526027413777165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9885099542034703218369553 7413824656526027413777165)
          ·
            refine ⟨2780184246197260280166437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7413824656526027413777165 2780184246197260280166437)
            ·
              refine ⟨521284546161986302531207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2780184246197260280166437 521284546161986302531207)
              ·
                refine ⟨781926819242979453796811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521284546161986302531207 781926819242979453796811)
                ·
                  refine ⟨1172890228864469180695217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 781926819242979453796811 1172890228864469180695217)
                  ·
                    refine ⟨879667671648351885521413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1172890228864469180695217 879667671648351885521413)
                    ·
                      refine ⟨164937688434065978535265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 879667671648351885521413 164937688434065978535265)
                      ·
                        rfl

theorem cell23_321215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_321215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321215 prefixEnd_321215 := by exact prefixLift 321215
  have htrace : WordTrace (prefixWord ++ tailWord_321215) baseStart_321215 baseEnd_321215 := by
    simpa [prefixWord, tailWord_321215, baseEnd_321215] using wordTrace_append hprefix tailTrace_321215
  have hstable : (prefixWord ++ tailWord_321215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321215).length < 2 ^ (prefixWord ++ tailWord_321215).sum := by decide
  have hdescent : baseEnd_321215 < baseStart_321215 := by decide
  rcases family_descends (prefixWord ++ tailWord_321215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321236 : List Nat := [2, 4, 1, 3, 1, 3, 2, 1, 1, 1, 4]
def baseStart_321236 : Nat := 118140960795 + 321236 * 2 ^ 59
def prefixEnd_321236 : Nat := 4983230072969 + 3 ^ 40 * 321236 * 2
def baseEnd_321236 : Nat := 164948471527810396372669

theorem tailTrace_321236 : CollatzResearch.WordTrace tailWord_321236 prefixEnd_321236 164948471527810396372669 := by
  unfold tailWord_321236
  simp only [CollatzResearch.WordTrace]
  refine ⟨5858219732112154793031781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7810959642816206390709041 5858219732112154793031781)
  ·
    refine ⟨1098416199771029023693459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5858219732112154793031781 1098416199771029023693459)
    ·
      refine ⟨1647624299656543535540189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1098416199771029023693459 1647624299656543535540189)
      ·
        refine ⟨617859112371203825827571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1647624299656543535540189 617859112371203825827571)
        ·
          refine ⟨926788668556805738741357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617859112371203825827571 926788668556805738741357)
          ·
            refine ⟨347545750708802152028009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 926788668556805738741357 347545750708802152028009)
            ·
              refine ⟨260659313031601614021007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347545750708802152028009 260659313031601614021007)
              ·
                refine ⟨390988969547402421031511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260659313031601614021007 390988969547402421031511)
                ·
                  refine ⟨586483454321103631547267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390988969547402421031511 586483454321103631547267)
                  ·
                    refine ⟨879725181481655447320901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 586483454321103631547267 879725181481655447320901)
                    ·
                      refine ⟨164948471527810396372669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 879725181481655447320901 164948471527810396372669)
                      ·
                        rfl

theorem cell23_321236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_321236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321236 prefixEnd_321236 := by exact prefixLift 321236
  have htrace : WordTrace (prefixWord ++ tailWord_321236) baseStart_321236 baseEnd_321236 := by
    simpa [prefixWord, tailWord_321236, baseEnd_321236] using wordTrace_append hprefix tailTrace_321236
  have hstable : (prefixWord ++ tailWord_321236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321236).length < 2 ^ (prefixWord ++ tailWord_321236).sum := by decide
  have hdescent : baseEnd_321236 < baseStart_321236 := by decide
  rcases family_descends (prefixWord ++ tailWord_321236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321252 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 4, 1, 3]
def baseStart_321252 : Nat := 118140960795 + 321252 * 2 ^ 59
def prefixEnd_321252 : Nat := 4983230072969 + 3 ^ 40 * 321252 * 2
def baseEnd_321252 : Nat := 164956687218282333772595

theorem tailTrace_321252 : CollatzResearch.WordTrace tailWord_321252 prefixEnd_321252 164956687218282333772595 := by
  unfold tailWord_321252
  simp only [CollatzResearch.WordTrace]
  refine ⟨5858511516083172159323005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7811348688110896212430673 5858511516083172159323005)
  ·
    refine ⟨2196941818531189559746127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5858511516083172159323005 2196941818531189559746127)
    ·
      refine ⟨3295412727796784339619191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2196941818531189559746127 3295412727796784339619191)
      ·
        refine ⟨4943119091695176509428787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3295412727796784339619191 4943119091695176509428787)
        ·
          refine ⟨7414678637542764764143181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4943119091695176509428787 7414678637542764764143181)
          ·
            refine ⟨2780504489078536786553693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7414678637542764764143181 2780504489078536786553693)
            ·
              refine ⟨1042689183404451294957635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2780504489078536786553693 1042689183404451294957635)
              ·
                refine ⟨1564033775106676942436453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1042689183404451294957635 1564033775106676942436453)
                ·
                  refine ⟨293256332832501926706835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1564033775106676942436453 293256332832501926706835)
                  ·
                    refine ⟨439884499248752890060253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 293256332832501926706835 439884499248752890060253)
                    ·
                      refine ⟨164956687218282333772595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 439884499248752890060253 164956687218282333772595)
                      ·
                        rfl

theorem cell23_321252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_321252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321252 prefixEnd_321252 := by exact prefixLift 321252
  have htrace : WordTrace (prefixWord ++ tailWord_321252) baseStart_321252 baseEnd_321252 := by
    simpa [prefixWord, tailWord_321252, baseEnd_321252] using wordTrace_append hprefix tailTrace_321252
  have hstable : (prefixWord ++ tailWord_321252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321252).length < 2 ^ (prefixWord ++ tailWord_321252).sum := by decide
  have hdescent : baseEnd_321252 < baseStart_321252 := by decide
  rcases family_descends (prefixWord ++ tailWord_321252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321292 : List Nat := [2, 2, 1, 2, 2, 1, 2, 4, 1, 4, 2]
def baseStart_321292 : Nat := 118140960795 + 321292 * 2 ^ 59
def prefixEnd_321292 : Nat := 4983230072969 + 3 ^ 40 * 321292 * 2
def baseEnd_321292 : Nat := 164977226444462177272411

theorem tailTrace_321292 : CollatzResearch.WordTrace tailWord_321292 prefixEnd_321292 164977226444462177272411 := by
  unfold tailWord_321292
  simp only [CollatzResearch.WordTrace]
  refine ⟨5859240976010715575051065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7812321301347620766734753 5859240976010715575051065)
  ·
    refine ⟨4394430732008036681288299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5859240976010715575051065 4394430732008036681288299)
    ·
      refine ⟨6591646098012055021932449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4394430732008036681288299 6591646098012055021932449)
      ·
        refine ⟨4943734573509041266449337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6591646098012055021932449 4943734573509041266449337)
        ·
          refine ⟨3707800930131780949837003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4943734573509041266449337 3707800930131780949837003)
          ·
            refine ⟨5561701395197671424755505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3707800930131780949837003 5561701395197671424755505)
            ·
              refine ⟨4171276046398253568566629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5561701395197671424755505 4171276046398253568566629)
              ·
                refine ⟨782114258699672544106243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4171276046398253568566629 782114258699672544106243)
                ·
                  refine ⟨1173171388049508816159365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 782114258699672544106243 1173171388049508816159365)
                  ·
                    refine ⟨219969635259282903029881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1173171388049508816159365 219969635259282903029881)
                    ·
                      refine ⟨164977226444462177272411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 219969635259282903029881 164977226444462177272411)
                      ·
                        rfl

theorem cell23_321292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_321292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321292 prefixEnd_321292 := by exact prefixLift 321292
  have htrace : WordTrace (prefixWord ++ tailWord_321292) baseStart_321292 baseEnd_321292 := by
    simpa [prefixWord, tailWord_321292, baseEnd_321292] using wordTrace_append hprefix tailTrace_321292
  have hstable : (prefixWord ++ tailWord_321292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321292).length < 2 ^ (prefixWord ++ tailWord_321292).sum := by decide
  have hdescent : baseEnd_321292 < baseStart_321292 := by decide
  rcases family_descends (prefixWord ++ tailWord_321292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321293 : List Nat := [1, 7, 2, 1, 2, 1, 9]
def baseStart_321293 : Nat := 118140960795 + 321293 * 2 ^ 59
def prefixEnd_321293 : Nat := 4983230072969 + 3 ^ 40 * 321293 * 2
def baseEnd_321293 : Nat := 2036762221297736708147

theorem tailTrace_321293 : CollatzResearch.WordTrace tailWord_321293 prefixEnd_321293 2036762221297736708147 := by
  unfold tailWord_321293
  simp only [CollatzResearch.WordTrace]
  refine ⟨11718518425017808320888533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7812345616678538880592355 11718518425017808320888533)
  ·
    refine ⟨274652775586354882520825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 11718518425017808320888533 274652775586354882520825)
    ·
      refine ⟨205989581689766161890619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274652775586354882520825 205989581689766161890619)
      ·
        refine ⟨308984372534649242835929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205989581689766161890619 308984372534649242835929)
        ·
          refine ⟨231738279400986932126947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308984372534649242835929 231738279400986932126947)
          ·
            refine ⟨347607419101480398190421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231738279400986932126947 347607419101480398190421)
            ·
              refine ⟨2036762221297736708147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 347607419101480398190421 2036762221297736708147)
              ·
                rfl

theorem cell23_321293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 9].length) (baseStart_321293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321293 prefixEnd_321293 := by exact prefixLift 321293
  have htrace : WordTrace (prefixWord ++ tailWord_321293) baseStart_321293 baseEnd_321293 := by
    simpa [prefixWord, tailWord_321293, baseEnd_321293] using wordTrace_append hprefix tailTrace_321293
  have hstable : (prefixWord ++ tailWord_321293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321293).length < 2 ^ (prefixWord ++ tailWord_321293).sum := by decide
  have hdescent : baseEnd_321293 < baseStart_321293 := by decide
  rcases family_descends (prefixWord ++ tailWord_321293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321315 : List Nat := [1, 1, 1, 4, 2, 1, 5, 1, 7]
def baseStart_321315 : Nat := 118140960795 + 321315 * 2 ^ 59
def prefixEnd_321315 : Nat := 4983230072969 + 3 ^ 40 * 321315 * 2
def baseEnd_321315 : Nat := 18332115166612843031645

theorem tailTrace_321315 : CollatzResearch.WordTrace tailWord_321315 prefixEnd_321315 18332115166612843031645 := by
  unfold tailWord_321315
  simp only [CollatzResearch.WordTrace]
  refine ⟨11719320830938106078189399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7812880553958737385459599 11719320830938106078189399)
  ·
    refine ⟨17578981246407159117284099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11719320830938106078189399 17578981246407159117284099)
    ·
      refine ⟨26368471869610738675926149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17578981246407159117284099 26368471869610738675926149)
      ·
        refine ⟨4944088475552013501736153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26368471869610738675926149 4944088475552013501736153)
        ·
          refine ⟨3708066356664010126302115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4944088475552013501736153 3708066356664010126302115)
          ·
            refine ⟨5562099534996015189453173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3708066356664010126302115 5562099534996015189453173)
            ·
              refine ⟨521446831405876424011235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5562099534996015189453173 521446831405876424011235)
              ·
                refine ⟨782170247108814636016853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521446831405876424011235 782170247108814636016853)
                ·
                  refine ⟨18332115166612843031645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 782170247108814636016853 18332115166612843031645)
                  ·
                    rfl

theorem cell23_321315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 7].length) (baseStart_321315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321315 prefixEnd_321315 := by exact prefixLift 321315
  have htrace : WordTrace (prefixWord ++ tailWord_321315) baseStart_321315 baseEnd_321315 := by
    simpa [prefixWord, tailWord_321315, baseEnd_321315] using wordTrace_append hprefix tailTrace_321315
  have hstable : (prefixWord ++ tailWord_321315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321315).length < 2 ^ (prefixWord ++ tailWord_321315).sum := by decide
  have hdescent : baseEnd_321315 < baseStart_321315 := by decide
  rcases family_descends (prefixWord ++ tailWord_321315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321362 : List Nat := [3, 2, 2, 1, 1, 3, 2, 2, 2, 5]
def baseStart_321362 : Nat := 118140960795 + 321362 * 2 ^ 59
def prefixEnd_321362 : Nat := 4983230072969 + 3 ^ 40 * 321362 * 2
def baseEnd_321362 : Nat := 55004390030092301132363

theorem tailTrace_321362 : CollatzResearch.WordTrace tailWord_321362 prefixEnd_321362 55004390030092301132363 := by
  unfold tailWord_321362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2930258765441958276287585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7814023374511888736766893 2930258765441958276287585)
  ·
    refine ⟨2197694074081468707215689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2930258765441958276287585 2197694074081468707215689)
    ·
      refine ⟨1648270555561101530411767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2197694074081468707215689 1648270555561101530411767)
      ·
        refine ⟨2472405833341652295617651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1648270555561101530411767 2472405833341652295617651)
        ·
          refine ⟨3708608750012478443426477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2472405833341652295617651 3708608750012478443426477)
          ·
            refine ⟨1390728281254679416284929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3708608750012478443426477 1390728281254679416284929)
            ·
              refine ⟨1043046210941009562213697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1390728281254679416284929 1043046210941009562213697)
              ·
                refine ⟨782284658205757171660273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1043046210941009562213697 782284658205757171660273)
                ·
                  refine ⟨586713493654317878745205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 782284658205757171660273 586713493654317878745205)
                  ·
                    refine ⟨55004390030092301132363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 586713493654317878745205 55004390030092301132363)
                    ·
                      rfl

theorem cell23_321362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_321362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321362 prefixEnd_321362 := by exact prefixLift 321362
  have htrace : WordTrace (prefixWord ++ tailWord_321362) baseStart_321362 baseEnd_321362 := by
    simpa [prefixWord, tailWord_321362, baseEnd_321362] using wordTrace_append hprefix tailTrace_321362
  have hstable : (prefixWord ++ tailWord_321362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321362).length < 2 ^ (prefixWord ++ tailWord_321362).sum := by decide
  have hdescent : baseEnd_321362 < baseStart_321362 := by decide
  rcases family_descends (prefixWord ++ tailWord_321362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321405 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 8]
def baseStart_321405 : Nat := 118140960795 + 321405 * 2 ^ 59
def prefixEnd_321405 : Nat := 4983230072969 + 3 ^ 40 * 321405 * 2
def baseEnd_321405 : Nat := 18337249973157803906599

theorem tailTrace_321405 : CollatzResearch.WordTrace tailWord_321405 prefixEnd_321405 18337249973157803906599 := by
  unfold tailWord_321405
  simp only [CollatzResearch.WordTrace]
  refine ⟨11722603400612051448965669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7815068933741367632643779 11722603400612051448965669)
  ·
    refine ⟨2197988137614759646681063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11722603400612051448965669 2197988137614759646681063)
    ·
      refine ⟨3296982206422139470021595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2197988137614759646681063 3296982206422139470021595)
      ·
        refine ⟨4945473309633209205032393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3296982206422139470021595 4945473309633209205032393)
        ·
          refine ⟨3709104982224906903774295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4945473309633209205032393 3709104982224906903774295)
          ·
            refine ⟨5563657473337360355661443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3709104982224906903774295 5563657473337360355661443)
            ·
              refine ⟨8345486210006040533492165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5563657473337360355661443 8345486210006040533492165)
              ·
                refine ⟨1564778664376132600029781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8345486210006040533492165 1564778664376132600029781)
                ·
                  refine ⟨18337249973157803906599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1564778664376132600029781 18337249973157803906599)
                  ·
                    rfl

theorem cell23_321405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_321405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321405 prefixEnd_321405 := by exact prefixLift 321405
  have htrace : WordTrace (prefixWord ++ tailWord_321405) baseStart_321405 baseEnd_321405 := by
    simpa [prefixWord, tailWord_321405, baseEnd_321405] using wordTrace_append hprefix tailTrace_321405
  have hstable : (prefixWord ++ tailWord_321405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321405).length < 2 ^ (prefixWord ++ tailWord_321405).sum := by decide
  have hdescent : baseEnd_321405 < baseStart_321405 := by decide
  rcases family_descends (prefixWord ++ tailWord_321405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321425 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 6]
def baseStart_321425 : Nat := 118140960795 + 321425 * 2 ^ 59
def prefixEnd_321425 : Nat := 4983230072969 + 3 ^ 40 * 321425 * 2
def baseEnd_321425 : Nat := 165045519371510156909299

theorem tailTrace_321425 : CollatzResearch.WordTrace tailWord_321425 prefixEnd_321425 165045519371510156909299 := by
  unfold tailWord_321425
  simp only [CollatzResearch.WordTrace]
  refine ⟨11723332860539594864693729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7815555240359729909795819 11723332860539594864693729)
  ·
    refine ⟨8792499645404696148520297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11723332860539594864693729 8792499645404696148520297)
    ·
      refine ⟨6594374734053522111390223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8792499645404696148520297 6594374734053522111390223)
      ·
        refine ⟨9891562101080283167085335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6594374734053522111390223 9891562101080283167085335)
        ·
          refine ⟨14837343151620424750628003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9891562101080283167085335 14837343151620424750628003)
          ·
            refine ⟨22256014727430637125942005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14837343151620424750628003 22256014727430637125942005)
            ·
              refine ⟨2086501380696622230557063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22256014727430637125942005 2086501380696622230557063)
              ·
                refine ⟨3129752071044933345835595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086501380696622230557063 3129752071044933345835595)
                ·
                  refine ⟨4694628106567400018753393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3129752071044933345835595 4694628106567400018753393)
                  ·
                    refine ⟨3520971079925550014065045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4694628106567400018753393 3520971079925550014065045)
                    ·
                      refine ⟨165045519371510156909299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3520971079925550014065045 165045519371510156909299)
                      ·
                        rfl

theorem cell23_321425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_321425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321425 prefixEnd_321425 := by exact prefixLift 321425
  have htrace : WordTrace (prefixWord ++ tailWord_321425) baseStart_321425 baseEnd_321425 := by
    simpa [prefixWord, tailWord_321425, baseEnd_321425] using wordTrace_append hprefix tailTrace_321425
  have hstable : (prefixWord ++ tailWord_321425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321425).length < 2 ^ (prefixWord ++ tailWord_321425).sum := by decide
  have hdescent : baseEnd_321425 < baseStart_321425 := by decide
  rcases family_descends (prefixWord ++ tailWord_321425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321426 : List Nat := [3, 2, 3, 2, 1, 2, 2, 1, 3, 4]
def baseStart_321426 : Nat := 118140960795 + 321426 * 2 ^ 59
def prefixEnd_321426 : Nat := 4983230072969 + 3 ^ 40 * 321426 * 2
def baseEnd_321426 : Nat := 55015344284054884332265

theorem tailTrace_321426 : CollatzResearch.WordTrace tailWord_321426 prefixEnd_321426 55015344284054884332265 := by
  unfold tailWord_321426
  simp only [CollatzResearch.WordTrace]
  refine ⟨2930842333383993008870033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7815579555690648023653421 2930842333383993008870033)
  ·
    refine ⟨2198131750037994756652525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2930842333383993008870033 2198131750037994756652525)
    ·
      refine ⟨824299406264248033744697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2198131750037994756652525 824299406264248033744697)
      ·
        refine ⟨618224554698186025308523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 824299406264248033744697 618224554698186025308523)
        ·
          refine ⟨927336832047279037962785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 618224554698186025308523 927336832047279037962785)
          ·
            refine ⟨695502624035459278472089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 927336832047279037962785 695502624035459278472089)
            ·
              refine ⟨521626968026594458854067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695502624035459278472089 521626968026594458854067)
              ·
                refine ⟨782440452039891688281101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521626968026594458854067 782440452039891688281101)
                ·
                  refine ⟨293415169514959383105413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 782440452039891688281101 293415169514959383105413)
                  ·
                    refine ⟨55015344284054884332265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 293415169514959383105413 55015344284054884332265)
                    ·
                      rfl

theorem cell23_321426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_321426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321426 prefixEnd_321426 := by exact prefixLift 321426
  have htrace : WordTrace (prefixWord ++ tailWord_321426) baseStart_321426 baseEnd_321426 := by
    simpa [prefixWord, tailWord_321426, baseEnd_321426] using wordTrace_append hprefix tailTrace_321426
  have hstable : (prefixWord ++ tailWord_321426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321426).length < 2 ^ (prefixWord ++ tailWord_321426).sum := by decide
  have hdescent : baseEnd_321426 < baseStart_321426 := by decide
  rcases family_descends (prefixWord ++ tailWord_321426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321445 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 2, 1, 7]
def baseStart_321445 : Nat := 118140960795 + 321445 * 2 ^ 59
def prefixEnd_321445 : Nat := 4983230072969 + 3 ^ 40 * 321445 * 2
def baseEnd_321445 : Nat := 165055788984600078659207

theorem tailTrace_321445 : CollatzResearch.WordTrace tailWord_321445 prefixEnd_321445 165055788984600078659207 := by
  unfold tailWord_321445
  simp only [CollatzResearch.WordTrace]
  refine ⟨11724062320467138280421789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7816041546978092186947859 11724062320467138280421789)
  ·
    refine ⟨4396523370175176855158171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11724062320467138280421789 4396523370175176855158171)
    ·
      refine ⟨6594785055262765282737257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4396523370175176855158171 6594785055262765282737257)
      ·
        refine ⟨4946088791447073962052943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6594785055262765282737257 4946088791447073962052943)
        ·
          refine ⟨7419133187170610943079415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4946088791447073962052943 7419133187170610943079415)
          ·
            refine ⟨11128699780755916414619123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7419133187170610943079415 11128699780755916414619123)
            ·
              refine ⟨16693049671133874621928685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11128699780755916414619123 16693049671133874621928685)
              ·
                refine ⟨6259893626675202983223257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16693049671133874621928685 6259893626675202983223257)
                ·
                  refine ⟨4694920220006402237417443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6259893626675202983223257 4694920220006402237417443)
                  ·
                    refine ⟨7042380330009603356126165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4694920220006402237417443 7042380330009603356126165)
                    ·
                      refine ⟨165055788984600078659207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7042380330009603356126165 165055788984600078659207)
                      ·
                        rfl

theorem cell23_321445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_321445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321445 prefixEnd_321445 := by exact prefixLift 321445
  have htrace : WordTrace (prefixWord ++ tailWord_321445) baseStart_321445 baseEnd_321445 := by
    simpa [prefixWord, tailWord_321445, baseEnd_321445] using wordTrace_append hprefix tailTrace_321445
  have hstable : (prefixWord ++ tailWord_321445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321445).length < 2 ^ (prefixWord ++ tailWord_321445).sum := by decide
  have hdescent : baseEnd_321445 < baseStart_321445 := by decide
  rcases family_descends (prefixWord ++ tailWord_321445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321459 : List Nat := [1, 1, 1, 2, 3, 1, 4, 3, 2, 3, 2]
def baseStart_321459 : Nat := 118140960795 + 321459 * 2 ^ 59
def prefixEnd_321459 : Nat := 4983230072969 + 3 ^ 40 * 321459 * 2
def baseEnd_321459 : Nat := 165062977713763023884143

theorem tailTrace_321459 : CollatzResearch.WordTrace tailWord_321459 prefixEnd_321459 165062977713763023884143 := by
  unfold tailWord_321459
  simp only [CollatzResearch.WordTrace]
  refine ⟨11724572942416418671431431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7816381961610945780954287 11724572942416418671431431)
  ·
    refine ⟨17586859413624628007147147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11724572942416418671431431 17586859413624628007147147)
    ·
      refine ⟨26380289120436942010720721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17586859413624628007147147 26380289120436942010720721)
      ·
        refine ⟨19785216840327706508040541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26380289120436942010720721 19785216840327706508040541)
        ·
          refine ⟨7419456315122889940515203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19785216840327706508040541 7419456315122889940515203)
          ·
            refine ⟨11129184472684334910772805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7419456315122889940515203 11129184472684334910772805)
            ·
              refine ⟨2086722088628312795769901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11129184472684334910772805 2086722088628312795769901)
              ·
                refine ⟨782520783235617298413713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2086722088628312795769901 782520783235617298413713)
                ·
                  refine ⟨586890587426712973810285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 782520783235617298413713 586890587426712973810285)
                  ·
                    refine ⟨220083970285017365178857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 586890587426712973810285 220083970285017365178857)
                    ·
                      refine ⟨165062977713763023884143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 220083970285017365178857 165062977713763023884143)
                      ·
                        rfl

theorem cell23_321459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 3, 2].length) (baseStart_321459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321459 prefixEnd_321459 := by exact prefixLift 321459
  have htrace : WordTrace (prefixWord ++ tailWord_321459) baseStart_321459 baseEnd_321459 := by
    simpa [prefixWord, tailWord_321459, baseEnd_321459] using wordTrace_append hprefix tailTrace_321459
  have hstable : (prefixWord ++ tailWord_321459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321459).length < 2 ^ (prefixWord ++ tailWord_321459).sum := by decide
  have hdescent : baseEnd_321459 < baseStart_321459 := by decide
  rcases family_descends (prefixWord ++ tailWord_321459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321466 : List Nat := [3, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3]
def baseStart_321466 : Nat := 118140960795 + 321466 * 2 ^ 59
def prefixEnd_321466 : Nat := 4983230072969 + 3 ^ 40 * 321466 * 2
def baseEnd_321466 : Nat := 165066572078344496496611

theorem tailTrace_321466 : CollatzResearch.WordTrace tailWord_321466 prefixEnd_321466 165066572078344496496611 := by
  unfold tailWord_321466
  simp only [CollatzResearch.WordTrace]
  refine ⟨2931207063347764716734063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7816552168927372577957501 2931207063347764716734063)
  ·
    refine ⟨4396810595021647075101095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2931207063347764716734063 4396810595021647075101095)
    ·
      refine ⟨6595215892532470612651643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4396810595021647075101095 6595215892532470612651643)
      ·
        refine ⟨9892823838798705918977465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6595215892532470612651643 9892823838798705918977465)
        ·
          refine ⟨7419617879099029439233099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9892823838798705918977465 7419617879099029439233099)
          ·
            refine ⟨11129426818648544158849649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7419617879099029439233099 11129426818648544158849649)
            ·
              refine ⟨8347070113986408119137237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11129426818648544158849649 8347070113986408119137237)
              ·
                refine ⟨195634455796556440292279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8347070113986408119137237 195634455796556440292279)
                ·
                  refine ⟨293451683694834660438419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195634455796556440292279 293451683694834660438419)
                  ·
                    refine ⟨440177525542251990657629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 293451683694834660438419 440177525542251990657629)
                    ·
                      refine ⟨165066572078344496496611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 440177525542251990657629 165066572078344496496611)
                      ·
                        rfl

theorem cell23_321466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3].length) (baseStart_321466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321466 prefixEnd_321466 := by exact prefixLift 321466
  have htrace : WordTrace (prefixWord ++ tailWord_321466) baseStart_321466 baseEnd_321466 := by
    simpa [prefixWord, tailWord_321466, baseEnd_321466] using wordTrace_append hprefix tailTrace_321466
  have hstable : (prefixWord ++ tailWord_321466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321466).length < 2 ^ (prefixWord ++ tailWord_321466).sum := by decide
  have hdescent : baseEnd_321466 < baseStart_321466 := by decide
  rcases family_descends (prefixWord ++ tailWord_321466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321469 : List Nat := [1, 4, 1, 2, 3, 1, 2, 3, 1, 5]
def baseStart_321469 : Nat := 118140960795 + 321469 * 2 ^ 59
def prefixEnd_321469 : Nat := 4983230072969 + 3 ^ 40 * 321469 * 2
def baseEnd_321469 : Nat := 55022704173435994919699

theorem tailTrace_321469 : CollatzResearch.WordTrace tailWord_321469 prefixEnd_321469 55022704173435994919699 := by
  unfold tailWord_321469
  simp only [CollatzResearch.WordTrace]
  refine ⟨11724937672380190379295461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7816625114920126919530307 11724937672380190379295461)
  ·
    refine ⟨2198425813571285696117899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11724937672380190379295461 2198425813571285696117899)
    ·
      refine ⟨3297638720356928544176849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2198425813571285696117899 3297638720356928544176849)
      ·
        refine ⟨2473229040267696408132637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3297638720356928544176849 2473229040267696408132637)
        ·
          refine ⟨927460890100386153049739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2473229040267696408132637 927460890100386153049739)
          ·
            refine ⟨1391191335150579229574609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927460890100386153049739 1391191335150579229574609)
            ·
              refine ⟨1043393501362934422180957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1391191335150579229574609 1043393501362934422180957)
              ·
                refine ⟨391272563011100408317859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1043393501362934422180957 391272563011100408317859)
                ·
                  refine ⟨586908844516650612476789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 391272563011100408317859 586908844516650612476789)
                  ·
                    refine ⟨55022704173435994919699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 586908844516650612476789 55022704173435994919699)
                    ·
                      rfl

theorem cell23_321469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_321469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321469 prefixEnd_321469 := by exact prefixLift 321469
  have htrace : WordTrace (prefixWord ++ tailWord_321469) baseStart_321469 baseEnd_321469 := by
    simpa [prefixWord, tailWord_321469, baseEnd_321469] using wordTrace_append hprefix tailTrace_321469
  have hstable : (prefixWord ++ tailWord_321469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321469).length < 2 ^ (prefixWord ++ tailWord_321469).sum := by decide
  have hdescent : baseEnd_321469 < baseStart_321469 := by decide
  rcases family_descends (prefixWord ++ tailWord_321469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321483 : List Nat := [1, 1, 1, 1, 3, 4, 5, 2, 1, 1, 3]
def baseStart_321483 : Nat := 118140960795 + 321483 * 2 ^ 59
def prefixEnd_321483 : Nat := 4983230072969 + 3 ^ 40 * 321483 * 2
def baseEnd_321483 : Nat := 165075301249470929984033

theorem tailTrace_321483 : CollatzResearch.WordTrace tailWord_321483 prefixEnd_321483 165075301249470929984033 := by
  unfold tailWord_321483
  simp only [CollatzResearch.WordTrace]
  refine ⟨11725448294329470770305103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7816965529552980513536735 11725448294329470770305103)
  ·
    refine ⟨17588172441494206155457655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11725448294329470770305103 17588172441494206155457655)
    ·
      refine ⟨26382258662241309233186483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17588172441494206155457655 26382258662241309233186483)
      ·
        refine ⟨39573387993361963849779725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26382258662241309233186483 39573387993361963849779725)
        ·
          refine ⟨14840020497510736443667397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39573387993361963849779725 14840020497510736443667397)
          ·
            refine ⟨2782503843283263083187637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14840020497510736443667397 2782503843283263083187637)
            ·
              refine ⟨260859735307805914048841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2782503843283263083187637 260859735307805914048841)
              ·
                refine ⟨195644801480854435536631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260859735307805914048841 195644801480854435536631)
                ·
                  refine ⟨293467202221281653304947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195644801480854435536631 293467202221281653304947)
                  ·
                    refine ⟨440200803331922479957421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 293467202221281653304947 440200803331922479957421)
                    ·
                      refine ⟨165075301249470929984033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 440200803331922479957421 165075301249470929984033)
                      ·
                        rfl

theorem cell23_321483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 1, 1, 3].length) (baseStart_321483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321483 prefixEnd_321483 := by exact prefixLift 321483
  have htrace : WordTrace (prefixWord ++ tailWord_321483) baseStart_321483 baseEnd_321483 := by
    simpa [prefixWord, tailWord_321483, baseEnd_321483] using wordTrace_append hprefix tailTrace_321483
  have hstable : (prefixWord ++ tailWord_321483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321483).length < 2 ^ (prefixWord ++ tailWord_321483).sum := by decide
  have hdescent : baseEnd_321483 < baseStart_321483 := by decide
  rcases family_descends (prefixWord ++ tailWord_321483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321539 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 4, 1, 3]
def baseStart_321539 : Nat := 118140960795 + 321539 * 2 ^ 59
def prefixEnd_321539 : Nat := 4983230072969 + 3 ^ 40 * 321539 * 2
def baseEnd_321539 : Nat := 165104056166122710883775

theorem tailTrace_321539 : CollatzResearch.WordTrace tailWord_321539 prefixEnd_321539 165104056166122710883775 := by
  unfold tailWord_321539
  simp only [CollatzResearch.WordTrace]
  refine ⟨11727490782126592334343671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7818327188084394889562447 11727490782126592334343671)
  ·
    refine ⟨17591236173189888501515507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11727490782126592334343671 17591236173189888501515507)
    ·
      refine ⟨26386854259784832752273261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17591236173189888501515507 26386854259784832752273261)
      ·
        refine ⟨9895070347419312282102473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26386854259784832752273261 9895070347419312282102473)
        ·
          refine ⟨7421302760564484211576855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9895070347419312282102473 7421302760564484211576855)
          ·
            refine ⟨11131954140846726317365283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7421302760564484211576855 11131954140846726317365283)
            ·
              refine ⟨16697931211270089476047925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11131954140846726317365283 16697931211270089476047925)
              ·
                refine ⟨1565431051056570888379493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16697931211270089476047925 1565431051056570888379493)
                ·
                  refine ⟨293518322073107041571155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1565431051056570888379493 293518322073107041571155)
                  ·
                    refine ⟨440277483109660562356733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 293518322073107041571155 440277483109660562356733)
                    ·
                      refine ⟨165104056166122710883775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 440277483109660562356733 165104056166122710883775)
                      ·
                        rfl

theorem cell23_321539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 1, 3].length) (baseStart_321539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321539 prefixEnd_321539 := by exact prefixLift 321539
  have htrace : WordTrace (prefixWord ++ tailWord_321539) baseStart_321539 baseEnd_321539 := by
    simpa [prefixWord, tailWord_321539, baseEnd_321539] using wordTrace_append hprefix tailTrace_321539
  have hstable : (prefixWord ++ tailWord_321539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321539).length < 2 ^ (prefixWord ++ tailWord_321539).sum := by decide
  have hdescent : baseEnd_321539 < baseStart_321539 := by decide
  rcases family_descends (prefixWord ++ tailWord_321539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321546 : List Nat := [3, 1, 2, 2, 5, 1, 1, 8]
def baseStart_321546 : Nat := 118140960795 + 321546 * 2 ^ 59
def prefixEnd_321546 : Nat := 4983230072969 + 3 ^ 40 * 321546 * 2
def baseEnd_321546 : Nat := 6115098167803858648009

theorem tailTrace_321546 : CollatzResearch.WordTrace tailWord_321546 prefixEnd_321546 6115098167803858648009 := by
  unfold tailWord_321546
  simp only [CollatzResearch.WordTrace]
  refine ⟨2931936523275308132462123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7818497395400821686565661 2931936523275308132462123)
  ·
    refine ⟨4397904784912962198693185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2931936523275308132462123 4397904784912962198693185)
    ·
      refine ⟨3298428588684721649019889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4397904784912962198693185 3298428588684721649019889)
      ·
        refine ⟨2473821441513541236764917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3298428588684721649019889 2473821441513541236764917)
        ·
          refine ⟨231920760141894490946711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2473821441513541236764917 231920760141894490946711)
          ·
            refine ⟨347881140212841736420067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231920760141894490946711 347881140212841736420067)
            ·
              refine ⟨521821710319262604630101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347881140212841736420067 521821710319262604630101)
              ·
                refine ⟨6115098167803858648009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 521821710319262604630101 6115098167803858648009)
                ·
                  rfl

theorem cell23_321546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 8].length) (baseStart_321546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321546 prefixEnd_321546 := by exact prefixLift 321546
  have htrace : WordTrace (prefixWord ++ tailWord_321546) baseStart_321546 baseEnd_321546 := by
    simpa [prefixWord, tailWord_321546, baseEnd_321546] using wordTrace_append hprefix tailTrace_321546
  have hstable : (prefixWord ++ tailWord_321546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321546).length < 2 ^ (prefixWord ++ tailWord_321546).sum := by decide
  have hdescent : baseEnd_321546 < baseStart_321546 := by decide
  rcases family_descends (prefixWord ++ tailWord_321546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321579 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 3, 4, 2]
def baseStart_321579 : Nat := 118140960795 + 321579 * 2 ^ 59
def prefixEnd_321579 : Nat := 4983230072969 + 3 ^ 40 * 321579 * 2
def baseEnd_321579 : Nat := 165124595392302554383591

theorem tailTrace_321579 : CollatzResearch.WordTrace tailWord_321579 prefixEnd_321579 165124595392302554383591 := by
  unfold tailWord_321579
  simp only [CollatzResearch.WordTrace]
  refine ⟨11728949701981679165799791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7819299801321119443866527 11728949701981679165799791)
  ·
    refine ⟨17593424552972518748699687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11728949701981679165799791 17593424552972518748699687)
    ·
      refine ⟨26390136829458778123049531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17593424552972518748699687 26390136829458778123049531)
      ·
        refine ⟨39585205244188167184574297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26390136829458778123049531 39585205244188167184574297)
        ·
          refine ⟨29688903933141125388430723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39585205244188167184574297 29688903933141125388430723)
          ·
            refine ⟨44533355899711688082646085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29688903933141125388430723 44533355899711688082646085)
            ·
              refine ⟨8350004231195941515496141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44533355899711688082646085 8350004231195941515496141)
              ·
                refine ⟨3131251586698478068311053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8350004231195941515496141 3131251586698478068311053)
                ·
                  refine ⟨1174219345011929275616645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3131251586698478068311053 1174219345011929275616645)
                  ·
                    refine ⟨220166127189736739178121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1174219345011929275616645 220166127189736739178121)
                    ·
                      refine ⟨165124595392302554383591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 220166127189736739178121 165124595392302554383591)
                      ·
                        rfl

theorem cell23_321579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 4, 2].length) (baseStart_321579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321579 prefixEnd_321579 := by exact prefixLift 321579
  have htrace : WordTrace (prefixWord ++ tailWord_321579) baseStart_321579 baseEnd_321579 := by
    simpa [prefixWord, tailWord_321579, baseEnd_321579] using wordTrace_append hprefix tailTrace_321579
  have hstable : (prefixWord ++ tailWord_321579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321579).length < 2 ^ (prefixWord ++ tailWord_321579).sum := by decide
  have hdescent : baseEnd_321579 < baseStart_321579 := by decide
  rcases family_descends (prefixWord ++ tailWord_321579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321606 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_321606 : Nat := 118140960795 + 321606 * 2 ^ 59
def prefixEnd_321606 : Nat := 4983230072969 + 3 ^ 40 * 321606 * 2
def baseEnd_321606 : Nat := 55046153123324649581989

theorem tailTrace_321606 : CollatzResearch.WordTrace tailWord_321606 prefixEnd_321606 55046153123324649581989 := by
  unfold tailWord_321606
  simp only [CollatzResearch.WordTrace]
  refine ⟨366560452277620711782271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7819956315255908518021781 366560452277620711782271)
  ·
    refine ⟨549840678416431067673407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 366560452277620711782271 549840678416431067673407)
    ·
      refine ⟨824761017624646601510111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 549840678416431067673407 824761017624646601510111)
      ·
        refine ⟨1237141526436969902265167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 824761017624646601510111 1237141526436969902265167)
        ·
          refine ⟨1855712289655454853397751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1237141526436969902265167 1855712289655454853397751)
          ·
            refine ⟨2783568434483182280096627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1855712289655454853397751 2783568434483182280096627)
            ·
              refine ⟨4175352651724773420144941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2783568434483182280096627 4175352651724773420144941)
              ·
                refine ⟨1565757244396790032554353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4175352651724773420144941 1565757244396790032554353)
                ·
                  refine ⟨1174317933297592524415765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1565757244396790032554353 1174317933297592524415765)
                  ·
                    refine ⟨55046153123324649581989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1174317933297592524415765 55046153123324649581989)
                    ·
                      rfl

theorem cell23_321606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_321606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321606 prefixEnd_321606 := by exact prefixLift 321606
  have htrace : WordTrace (prefixWord ++ tailWord_321606) baseStart_321606 baseEnd_321606 := by
    simpa [prefixWord, tailWord_321606, baseEnd_321606] using wordTrace_append hprefix tailTrace_321606
  have hstable : (prefixWord ++ tailWord_321606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321606).length < 2 ^ (prefixWord ++ tailWord_321606).sum := by decide
  have hdescent : baseEnd_321606 < baseStart_321606 := by decide
  rcases family_descends (prefixWord ++ tailWord_321606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321636 : List Nat := [2, 3, 1, 1, 2, 1, 5, 3, 5]
def baseStart_321636 : Nat := 118140960795 + 321636 * 2 ^ 59
def prefixEnd_321636 : Nat := 4983230072969 + 3 ^ 40 * 321636 * 2
def baseEnd_321636 : Nat := 18350429309956536818981

theorem tailTrace_321636 : CollatzResearch.WordTrace tailWord_321636 prefixEnd_321636 18350429309956536818981 := by
  unfold tailWord_321636
  simp only [CollatzResearch.WordTrace]
  refine ⟨5865514331387588950312381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7820685775183451933749841 5865514331387588950312381)
  ·
    refine ⟨2199567874270345856367143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5865514331387588950312381 2199567874270345856367143)
    ·
      refine ⟨3299351811405518784550715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2199567874270345856367143 3299351811405518784550715)
      ·
        refine ⟨4949027717108278176826073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3299351811405518784550715 4949027717108278176826073)
        ·
          refine ⟨3711770787831208632619555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4949027717108278176826073 3711770787831208632619555)
          ·
            refine ⟨5567656181746812948929333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3711770787831208632619555 5567656181746812948929333)
            ·
              refine ⟨521967767038763713962125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5567656181746812948929333 521967767038763713962125)
              ·
                refine ⟨195737912639536392735797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 521967767038763713962125 195737912639536392735797)
                ·
                  refine ⟨18350429309956536818981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 195737912639536392735797 18350429309956536818981)
                  ·
                    rfl

theorem cell23_321636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_321636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321636 prefixEnd_321636 := by exact prefixLift 321636
  have htrace : WordTrace (prefixWord ++ tailWord_321636) baseStart_321636 baseEnd_321636 := by
    simpa [prefixWord, tailWord_321636, baseEnd_321636] using wordTrace_append hprefix tailTrace_321636
  have hstable : (prefixWord ++ tailWord_321636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321636).length < 2 ^ (prefixWord ++ tailWord_321636).sum := by decide
  have hdescent : baseEnd_321636 < baseStart_321636 := by decide
  rcases family_descends (prefixWord ++ tailWord_321636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321649 : List Nat := [1, 2, 2, 2, 1, 1, 5, 2, 2, 5]
def baseStart_321649 : Nat := 118140960795 + 321649 * 2 ^ 59
def prefixEnd_321649 : Nat := 4983230072969 + 3 ^ 40 * 321649 * 2
def baseEnd_321649 : Nat := 55053513012705760169423

theorem tailTrace_321649 : CollatzResearch.WordTrace tailWord_321649 prefixEnd_321649 55053513012705760169423 := by
  unfold tailWord_321649
  simp only [CollatzResearch.WordTrace]
  refine ⟨11731502811728081120848001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7821001874485387413898667 11731502811728081120848001)
  ·
    refine ⟨8798627108796060840636001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11731502811728081120848001 8798627108796060840636001)
    ·
      refine ⟨6598970331597045630477001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8798627108796060840636001 6598970331597045630477001)
      ·
        refine ⟨4949227748697784222857751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6598970331597045630477001 4949227748697784222857751)
        ·
          refine ⟨7423841623046676334286627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4949227748697784222857751 7423841623046676334286627)
          ·
            refine ⟨11135762434570014501429941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7423841623046676334286627 11135762434570014501429941)
            ·
              refine ⟨1043977728240938859509057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11135762434570014501429941 1043977728240938859509057)
              ·
                refine ⟨782983296180704144631793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1043977728240938859509057 782983296180704144631793)
                ·
                  refine ⟨587237472135528108473845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 782983296180704144631793 587237472135528108473845)
                  ·
                    refine ⟨55053513012705760169423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 587237472135528108473845 55053513012705760169423)
                    ·
                      rfl

theorem cell23_321649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_321649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321649 prefixEnd_321649 := by exact prefixLift 321649
  have htrace : WordTrace (prefixWord ++ tailWord_321649) baseStart_321649 baseEnd_321649 := by
    simpa [prefixWord, tailWord_321649, baseEnd_321649] using wordTrace_append hprefix tailTrace_321649
  have hstable : (prefixWord ++ tailWord_321649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321649).length < 2 ^ (prefixWord ++ tailWord_321649).sum := by decide
  have hdescent : baseEnd_321649 < baseStart_321649 := by decide
  rcases family_descends (prefixWord ++ tailWord_321649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321689 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 1, 4, 3]
def baseStart_321689 : Nat := 118140960795 + 321689 * 2 ^ 59
def prefixEnd_321689 : Nat := 4983230072969 + 3 ^ 40 * 321689 * 2
def baseEnd_321689 : Nat := 165181078264297124008085

theorem tailTrace_321689 : CollatzResearch.WordTrace tailWord_321689 prefixEnd_321689 165181078264297124008085 := by
  unfold tailWord_321689
  simp only [CollatzResearch.WordTrace]
  refine ⟨11732961731583167952304121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7821974487722111968202747 11732961731583167952304121)
  ·
    refine ⟨8799721298687375964228091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11732961731583167952304121 8799721298687375964228091)
    ·
      refine ⟨13199581948031063946342137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8799721298687375964228091 13199581948031063946342137)
      ·
        refine ⟨9899686461023297959756603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13199581948031063946342137 9899686461023297959756603)
        ·
          refine ⟨14849529691534946939634905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9899686461023297959756603 14849529691534946939634905)
          ·
            refine ⟨11137147268651210204726179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14849529691534946939634905 11137147268651210204726179)
            ·
              refine ⟨16705720902976815307089269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11137147268651210204726179 16705720902976815307089269)
              ·
                refine ⟨1566161334654076435039619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16705720902976815307089269 1566161334654076435039619)
                ·
                  refine ⟨2349242001981114652559429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1566161334654076435039619 2349242001981114652559429)
                  ·
                    refine ⟨440482875371458997354893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2349242001981114652559429 440482875371458997354893)
                    ·
                      refine ⟨165181078264297124008085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 440482875371458997354893 165181078264297124008085)
                      ·
                        rfl

theorem cell23_321689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_321689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321689 prefixEnd_321689 := by exact prefixLift 321689
  have htrace : WordTrace (prefixWord ++ tailWord_321689) baseStart_321689 baseEnd_321689 := by
    simpa [prefixWord, tailWord_321689, baseEnd_321689] using wordTrace_append hprefix tailTrace_321689
  have hstable : (prefixWord ++ tailWord_321689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321689).length < 2 ^ (prefixWord ++ tailWord_321689).sum := by decide
  have hdescent : baseEnd_321689 < baseStart_321689 := by decide
  rcases family_descends (prefixWord ++ tailWord_321689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321730 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_321730 : Nat := 118140960795 + 321730 * 2 ^ 59
def prefixEnd_321730 : Nat := 4983230072969 + 3 ^ 40 * 321730 * 2
def baseEnd_321730 : Nat := 55067376990377154531799

theorem tailTrace_321730 : CollatzResearch.WordTrace tailWord_321730 prefixEnd_321730 55067376990377154531799 := by
  unfold tailWord_321730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2933614281108657988636661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7822971416289754636364429 2933614281108657988636661)
  ·
    refine ⟨275026338853936686434687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2933614281108657988636661 275026338853936686434687)
    ·
      refine ⟨412539508280905029652031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275026338853936686434687 412539508280905029652031)
      ·
        refine ⟨618809262421357544478047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412539508280905029652031 618809262421357544478047)
        ·
          refine ⟨928213893632036316717071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 618809262421357544478047 928213893632036316717071)
          ·
            refine ⟨1392320840448054475075607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928213893632036316717071 1392320840448054475075607)
            ·
              refine ⟨2088481260672081712613411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1392320840448054475075607 2088481260672081712613411)
              ·
                refine ⟨3132721891008122568920117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2088481260672081712613411 3132721891008122568920117)
                ·
                  refine ⟨293692677282011490836261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3132721891008122568920117 293692677282011490836261)
                  ·
                    refine ⟨55067376990377154531799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 293692677282011490836261 55067376990377154531799)
                    ·
                      rfl

theorem cell23_321730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_321730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321730 prefixEnd_321730 := by exact prefixLift 321730
  have htrace : WordTrace (prefixWord ++ tailWord_321730) baseStart_321730 baseEnd_321730 := by
    simpa [prefixWord, tailWord_321730, baseEnd_321730] using wordTrace_append hprefix tailTrace_321730
  have hstable : (prefixWord ++ tailWord_321730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321730).length < 2 ^ (prefixWord ++ tailWord_321730).sum := by decide
  have hdescent : baseEnd_321730 < baseStart_321730 := by decide
  rcases family_descends (prefixWord ++ tailWord_321730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321739 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 3, 5]
def baseStart_321739 : Nat := 118140960795 + 321739 * 2 ^ 59
def prefixEnd_321739 : Nat := 4983230072969 + 3 ^ 40 * 321739 * 2
def baseEnd_321739 : Nat := 55068917432340642794285

theorem tailTrace_321739 : CollatzResearch.WordTrace tailWord_321739 prefixEnd_321739 55068917432340642794285 := by
  unfold tailWord_321739
  simp only [CollatzResearch.WordTrace]
  refine ⟨11734785381402026491624271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7823190254268017661082847 11734785381402026491624271)
  ·
    refine ⟨17602178072103039737436407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11734785381402026491624271 17602178072103039737436407)
    ·
      refine ⟨26403267108154559606154611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17602178072103039737436407 26403267108154559606154611)
      ·
        refine ⟨39604900662231839409231917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26403267108154559606154611 39604900662231839409231917)
        ·
          refine ⟨14851837748336939778461969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39604900662231839409231917 14851837748336939778461969)
          ·
            refine ⟨11138878311252704833846477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14851837748336939778461969 11138878311252704833846477)
            ·
              refine ⟨4177079366719764312692429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11138878311252704833846477 4177079366719764312692429)
              ·
                refine ⟨1566404762519911617259661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4177079366719764312692429 1566404762519911617259661)
                ·
                  refine ⟨587401785944966856472373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1566404762519911617259661 587401785944966856472373)
                  ·
                    refine ⟨55068917432340642794285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 587401785944966856472373 55068917432340642794285)
                    ·
                      rfl

theorem cell23_321739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 5].length) (baseStart_321739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321739 prefixEnd_321739 := by exact prefixLift 321739
  have htrace : WordTrace (prefixWord ++ tailWord_321739) baseStart_321739 baseEnd_321739 := by
    simpa [prefixWord, tailWord_321739, baseEnd_321739] using wordTrace_append hprefix tailTrace_321739
  have hstable : (prefixWord ++ tailWord_321739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321739).length < 2 ^ (prefixWord ++ tailWord_321739).sum := by decide
  have hdescent : baseEnd_321739 < baseStart_321739 := by decide
  rcases family_descends (prefixWord ++ tailWord_321739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321770 : List Nat := [3, 1, 3, 1, 1, 2, 1, 6, 1, 1, 3]
def baseStart_321770 : Nat := 118140960795 + 321770 * 2 ^ 59
def prefixEnd_321770 : Nat := 4983230072969 + 3 ^ 40 * 321770 * 2
def baseEnd_321770 : Nat := 165222670197311307095213

theorem tailTrace_321770 : CollatzResearch.WordTrace tailWord_321770 prefixEnd_321770 165222670197311307095213 := by
  unfold tailWord_321770
  simp only [CollatzResearch.WordTrace]
  refine ⟨2933979011072429696500691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7823944029526479190668509 2933979011072429696500691)
  ·
    refine ⟨4400968516608644544751037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2933979011072429696500691 4400968516608644544751037)
    ·
      refine ⟨1650363193728241704281639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4400968516608644544751037 1650363193728241704281639)
      ·
        refine ⟨2475544790592362556422459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1650363193728241704281639 2475544790592362556422459)
        ·
          refine ⟨3713317185888543834633689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2475544790592362556422459 3713317185888543834633689)
          ·
            refine ⟨2784987889416407875975267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3713317185888543834633689 2784987889416407875975267)
            ·
              refine ⟨4177481834124611813962901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2784987889416407875975267 4177481834124611813962901)
              ·
                refine ⟨195819460974591178779511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4177481834124611813962901 195819460974591178779511)
                ·
                  refine ⟨293729191461886768169267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195819460974591178779511 293729191461886768169267)
                  ·
                    refine ⟨440593787192830152253901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 293729191461886768169267 440593787192830152253901)
                    ·
                      refine ⟨165222670197311307095213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 440593787192830152253901 165222670197311307095213)
                      ·
                        rfl

theorem cell23_321770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_321770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321770 prefixEnd_321770 := by exact prefixLift 321770
  have htrace : WordTrace (prefixWord ++ tailWord_321770) baseStart_321770 baseEnd_321770 := by
    simpa [prefixWord, tailWord_321770, baseEnd_321770] using wordTrace_append hprefix tailTrace_321770
  have hstable : (prefixWord ++ tailWord_321770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321770).length < 2 ^ (prefixWord ++ tailWord_321770).sum := by decide
  have hdescent : baseEnd_321770 < baseStart_321770 := by decide
  rcases family_descends (prefixWord ++ tailWord_321770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321786 : List Nat := [3, 1, 1, 1, 1, 5, 3, 1, 1, 6]
def baseStart_321786 : Nat := 118140960795 + 321786 * 2 ^ 59
def prefixEnd_321786 : Nat := 4983230072969 + 3 ^ 40 * 321786 * 2
def baseEnd_321786 : Nat := 55076961962594414831713

theorem tailTrace_321786 : CollatzResearch.WordTrace tailWord_321786 prefixEnd_321786 55076961962594414831713 := by
  unfold tailWord_321786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2934124903057938379646303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7824333074821169012390141 2934124903057938379646303)
  ·
    refine ⟨4401187354586907569469455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2934124903057938379646303 4401187354586907569469455)
    ·
      refine ⟨6601781031880361354204183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4401187354586907569469455 6601781031880361354204183)
      ·
        refine ⟨9902671547820542031306275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6601781031880361354204183 9902671547820542031306275)
        ·
          refine ⟨14854007321730813046959413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9902671547820542031306275 14854007321730813046959413)
          ·
            refine ⟨1392563186412263723152445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14854007321730813046959413 1392563186412263723152445)
            ·
              refine ⟨522211194904598896182167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1392563186412263723152445 522211194904598896182167)
              ·
                refine ⟨783316792356898344273251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522211194904598896182167 783316792356898344273251)
                ·
                  refine ⟨1174975188535347516409877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 783316792356898344273251 1174975188535347516409877)
                  ·
                    refine ⟨55076961962594414831713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1174975188535347516409877 55076961962594414831713)
                    ·
                      rfl

theorem cell23_321786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_321786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321786 prefixEnd_321786 := by exact prefixLift 321786
  have htrace : WordTrace (prefixWord ++ tailWord_321786) baseStart_321786 baseEnd_321786 := by
    simpa [prefixWord, tailWord_321786, baseEnd_321786] using wordTrace_append hprefix tailTrace_321786
  have hstable : (prefixWord ++ tailWord_321786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321786).length < 2 ^ (prefixWord ++ tailWord_321786).sum := by decide
  have hdescent : baseEnd_321786 < baseStart_321786 := by decide
  rcases family_descends (prefixWord ++ tailWord_321786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321793 : List Nat := [1, 2, 4, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_321793 : Nat := 118140960795 + 321793 * 2 ^ 59
def prefixEnd_321793 : Nat := 4983230072969 + 3 ^ 40 * 321793 * 2
def baseEnd_321793 : Nat := 165234480252364717107607

theorem tailTrace_321793 : CollatzResearch.WordTrace tailWord_321793 prefixEnd_321793 165234480252364717107607 := by
  unfold tailWord_321793
  simp only [CollatzResearch.WordTrace]
  refine ⟨11736754923206393714090033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7824503282137595809393355 11736754923206393714090033)
  ·
    refine ⟨8802566192404795285567525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11736754923206393714090033 8802566192404795285567525)
    ·
      refine ⟨1650481161075899116043911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8802566192404795285567525 1650481161075899116043911)
      ·
        refine ⟨2475721741613848674065867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1650481161075899116043911 2475721741613848674065867)
        ·
          refine ⟨3713582612420773011098801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2475721741613848674065867 3713582612420773011098801)
          ·
            refine ⟨2785186959315579758324101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3713582612420773011098801 2785186959315579758324101)
            ·
              refine ⟨522222554871671204685769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2785186959315579758324101 522222554871671204685769)
              ·
                refine ⟨391666916153753403514327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522222554871671204685769 391666916153753403514327)
                ·
                  refine ⟨587500374230630105271491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 391666916153753403514327 587500374230630105271491)
                  ·
                    refine ⟨881250561345945157907237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 587500374230630105271491 881250561345945157907237)
                    ·
                      refine ⟨165234480252364717107607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 881250561345945157907237 165234480252364717107607)
                      ·
                        rfl

theorem cell23_321793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_321793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321793 prefixEnd_321793 := by exact prefixLift 321793
  have htrace : WordTrace (prefixWord ++ tailWord_321793) baseStart_321793 baseEnd_321793 := by
    simpa [prefixWord, tailWord_321793, baseEnd_321793] using wordTrace_append hprefix tailTrace_321793
  have hstable : (prefixWord ++ tailWord_321793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321793).length < 2 ^ (prefixWord ++ tailWord_321793).sum := by decide
  have hdescent : baseEnd_321793 < baseStart_321793 := by decide
  rcases family_descends (prefixWord ++ tailWord_321793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321806 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_321806 : Nat := 118140960795 + 321806 * 2 ^ 59
def prefixEnd_321806 : Nat := 4983230072969 + 3 ^ 40 * 321806 * 2
def baseEnd_321806 : Nat := 165241155500873166245047

theorem tailTrace_321806 : CollatzResearch.WordTrace tailWord_321806 prefixEnd_321806 165241155500873166245047 := by
  unfold tailWord_321806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1467153634019912116789159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7824819381439531289542181 1467153634019912116789159)
  ·
    refine ⟨2200730451029868175183739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1467153634019912116789159 2200730451029868175183739)
    ·
      refine ⟨3301095676544802262775609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2200730451029868175183739 3301095676544802262775609)
      ·
        refine ⟨2475821757408601697081707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3301095676544802262775609 2475821757408601697081707)
        ·
          refine ⟨3713732636112902545622561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2475821757408601697081707 3713732636112902545622561)
          ·
            refine ⟨2785299477084676909216921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3713732636112902545622561 2785299477084676909216921)
            ·
              refine ⟨2088974607813507681912691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2785299477084676909216921 2088974607813507681912691)
              ·
                refine ⟨3133461911720261522869037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2088974607813507681912691 3133461911720261522869037)
                ·
                  refine ⟨1175048216895098071075889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3133461911720261522869037 1175048216895098071075889)
                  ·
                    refine ⟨881286162671323553306917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1175048216895098071075889 881286162671323553306917)
                    ·
                      refine ⟨165241155500873166245047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 881286162671323553306917 165241155500873166245047)
                      ·
                        rfl

theorem cell23_321806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_321806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321806 prefixEnd_321806 := by exact prefixLift 321806
  have htrace : WordTrace (prefixWord ++ tailWord_321806) baseStart_321806 baseEnd_321806 := by
    simpa [prefixWord, tailWord_321806, baseEnd_321806] using wordTrace_append hprefix tailTrace_321806
  have hstable : (prefixWord ++ tailWord_321806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321806).length < 2 ^ (prefixWord ++ tailWord_321806).sum := by decide
  have hdescent : baseEnd_321806 < baseStart_321806 := by decide
  rcases family_descends (prefixWord ++ tailWord_321806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321813 : List Nat := [1, 3, 2, 1, 2, 1, 4, 3, 1, 2, 3]
def baseStart_321813 : Nat := 118140960795 + 321813 * 2 ^ 59
def prefixEnd_321813 : Nat := 4983230072969 + 3 ^ 40 * 321813 * 2
def baseEnd_321813 : Nat := 165244749865454638857515

theorem tailTrace_321813 : CollatzResearch.WordTrace tailWord_321813 prefixEnd_321813 165244749865454638857515 := by
  unfold tailWord_321813
  simp only [CollatzResearch.WordTrace]
  refine ⟨11737484383133937129818093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7824989588755958086545395 11737484383133937129818093)
  ·
    refine ⟨4401556643675226423681785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11737484383133937129818093 4401556643675226423681785)
    ·
      refine ⟨3301167482756419817761339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4401556643675226423681785 3301167482756419817761339)
      ·
        refine ⟨4951751224134629726642009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3301167482756419817761339 4951751224134629726642009)
        ·
          refine ⟨3713813418100972294981507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4951751224134629726642009 3713813418100972294981507)
          ·
            refine ⟨5570720127151458442472261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713813418100972294981507 5570720127151458442472261)
            ·
              refine ⟨1044510023840898457963549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5570720127151458442472261 1044510023840898457963549)
              ·
                refine ⟨391691258940336921736331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1044510023840898457963549 391691258940336921736331)
                ·
                  refine ⟨587536888410505382604497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 391691258940336921736331 587536888410505382604497)
                  ·
                    refine ⟨440652666307879036953373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 587536888410505382604497 440652666307879036953373)
                    ·
                      refine ⟨165244749865454638857515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 440652666307879036953373 165244749865454638857515)
                      ·
                        rfl

theorem cell23_321813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_321813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321813 prefixEnd_321813 := by exact prefixLift 321813
  have htrace : WordTrace (prefixWord ++ tailWord_321813) baseStart_321813 baseEnd_321813 := by
    simpa [prefixWord, tailWord_321813, baseEnd_321813] using wordTrace_append hprefix tailTrace_321813
  have hstable : (prefixWord ++ tailWord_321813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321813).length < 2 ^ (prefixWord ++ tailWord_321813).sum := by decide
  have hdescent : baseEnd_321813 < baseStart_321813 := by decide
  rcases family_descends (prefixWord ++ tailWord_321813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321837 : List Nat := [1, 5, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_321837 : Nat := 118140960795 + 321837 * 2 ^ 59
def prefixEnd_321837 : Nat := 4983230072969 + 3 ^ 40 * 321837 * 2
def baseEnd_321837 : Nat := 55085691133720848319135

theorem tailTrace_321837 : CollatzResearch.WordTrace tailWord_321837 prefixEnd_321837 55085691133720848319135 := by
  unfold tailWord_321837
  simp only [CollatzResearch.WordTrace]
  refine ⟨11738359735046989228691765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7825573156697992819127843 11738359735046989228691765)
  ·
    refine ⟨1100471225160655240189853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11738359735046989228691765 1100471225160655240189853)
    ·
      refine ⟨412676709435245715071195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1100471225160655240189853 412676709435245715071195)
      ·
        refine ⟨619015064152868572606793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412676709435245715071195 619015064152868572606793)
        ·
          refine ⟨464261298114651429455095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 619015064152868572606793 464261298114651429455095)
          ·
            refine ⟨696391947171977144182643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464261298114651429455095 696391947171977144182643)
            ·
              refine ⟨1044587920757965716273965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696391947171977144182643 1044587920757965716273965)
              ·
                refine ⟨391720470284237143602737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1044587920757965716273965 391720470284237143602737)
                ·
                  refine ⟨293790352713177857702053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 391720470284237143602737 293790352713177857702053)
                  ·
                    refine ⟨55085691133720848319135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 293790352713177857702053 55085691133720848319135)
                    ·
                      rfl

theorem cell23_321837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_321837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321837 prefixEnd_321837 := by exact prefixLift 321837
  have htrace : WordTrace (prefixWord ++ tailWord_321837) baseStart_321837 baseEnd_321837 := by
    simpa [prefixWord, tailWord_321837, baseEnd_321837] using wordTrace_append hprefix tailTrace_321837
  have hstable : (prefixWord ++ tailWord_321837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321837).length < 2 ^ (prefixWord ++ tailWord_321837).sum := by decide
  have hdescent : baseEnd_321837 < baseStart_321837 := by decide
  rcases family_descends (prefixWord ++ tailWord_321837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321877 : List Nat := [1, 3, 2, 2, 4, 1, 2, 2, 2, 1, 3]
def baseStart_321877 : Nat := 118140960795 + 321877 * 2 ^ 59
def prefixEnd_321877 : Nat := 4983230072969 + 3 ^ 40 * 321877 * 2
def baseEnd_321877 : Nat := 165277612627342388457221

theorem tailTrace_321877 : CollatzResearch.WordTrace tailWord_321877 prefixEnd_321877 165277612627342388457221 := by
  unfold tailWord_321877
  simp only [CollatzResearch.WordTrace]
  refine ⟨11739818654902076060147885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7826545769934717373431923 11739818654902076060147885)
  ·
    refine ⟨4402431995588278522555457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11739818654902076060147885 4402431995588278522555457)
    ·
      refine ⟨3301823996691208891916593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4402431995588278522555457 3301823996691208891916593)
      ·
        refine ⟨2476367997518406668937445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3301823996691208891916593 2476367997518406668937445)
        ·
          refine ⟨464318999534701250425771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2476367997518406668937445 464318999534701250425771)
          ·
            refine ⟨696478499302051875638657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464318999534701250425771 696478499302051875638657)
            ·
              refine ⟨522358874476538906728993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696478499302051875638657 522358874476538906728993)
              ·
                refine ⟨391769155857404180046745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522358874476538906728993 391769155857404180046745)
                ·
                  refine ⟨293826866893053135035059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 391769155857404180046745 293826866893053135035059)
                  ·
                    refine ⟨440740300339579702552589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 293826866893053135035059 440740300339579702552589)
                    ·
                      refine ⟨165277612627342388457221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 440740300339579702552589 165277612627342388457221)
                      ·
                        rfl

theorem cell23_321877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_321877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321877 prefixEnd_321877 := by exact prefixLift 321877
  have htrace : WordTrace (prefixWord ++ tailWord_321877) baseStart_321877 baseEnd_321877 := by
    simpa [prefixWord, tailWord_321877, baseEnd_321877] using wordTrace_append hprefix tailTrace_321877
  have hstable : (prefixWord ++ tailWord_321877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321877).length < 2 ^ (prefixWord ++ tailWord_321877).sum := by decide
  have hdescent : baseEnd_321877 < baseStart_321877 := by decide
  rcases family_descends (prefixWord ++ tailWord_321877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321906 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 9]
def baseStart_321906 : Nat := 118140960795 + 321906 * 2 ^ 59
def prefixEnd_321906 : Nat := 4983230072969 + 3 ^ 40 * 321906 * 2
def baseEnd_321906 : Nat := 18365833729591419443843

theorem tailTrace_321906 : CollatzResearch.WordTrace tailWord_321906 prefixEnd_321906 18365833729591419443843 := by
  unfold tailWord_321906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2935219092949253503238393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7827250914531342675302381 2935219092949253503238393)
  ·
    refine ⟨2201414319711940127428795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2935219092949253503238393 2201414319711940127428795)
    ·
      refine ⟨3302121479567910191143193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2201414319711940127428795 3302121479567910191143193)
      ·
        refine ⟨2476591109675932643357395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3302121479567910191143193 2476591109675932643357395)
        ·
          refine ⟨3714886664513898965036093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2476591109675932643357395 3714886664513898965036093)
          ·
            refine ⟨1393082499192712111888535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3714886664513898965036093 1393082499192712111888535)
            ·
              refine ⟨2089623748789068167832803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1393082499192712111888535 2089623748789068167832803)
              ·
                refine ⟨3134435623183602251749205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2089623748789068167832803 3134435623183602251749205)
                ·
                  refine ⟨18365833729591419443843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3134435623183602251749205 18365833729591419443843)
                  ·
                    rfl

theorem cell23_321906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_321906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321906 prefixEnd_321906 := by exact prefixLift 321906
  have htrace : WordTrace (prefixWord ++ tailWord_321906) baseStart_321906 baseEnd_321906 := by
    simpa [prefixWord, tailWord_321906, baseEnd_321906] using wordTrace_append hprefix tailTrace_321906
  have hstable : (prefixWord ++ tailWord_321906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321906).length < 2 ^ (prefixWord ++ tailWord_321906).sum := by decide
  have hdescent : baseEnd_321906 < baseStart_321906 := by decide
  rcases family_descends (prefixWord ++ tailWord_321906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321934 : List Nat := [4, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2]
def baseStart_321934 : Nat := 118140960795 + 321934 * 2 ^ 59
def prefixEnd_321934 : Nat := 4983230072969 + 3 ^ 40 * 321934 * 2
def baseEnd_321934 : Nat := 165306881024648665444459

theorem tailTrace_321934 : CollatzResearch.WordTrace tailWord_321934 prefixEnd_321934 165306881024648665444459 := by
  unfold tailWord_321934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1467737201961946849371607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7827931743797049863315237 1467737201961946849371607)
  ·
    refine ⟨2201605802942920274057411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1467737201961946849371607 2201605802942920274057411)
    ·
      refine ⟨3302408704414380411086117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2201605802942920274057411 3302408704414380411086117)
      ·
        refine ⟨619201632077696327078647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3302408704414380411086117 619201632077696327078647)
        ·
          refine ⟨928802448116544490617971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619201632077696327078647 928802448116544490617971)
          ·
            refine ⟨1393203672174816735926957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928802448116544490617971 1393203672174816735926957)
            ·
              refine ⟨522451377065556275972609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1393203672174816735926957 522451377065556275972609)
              ·
                refine ⟨391838532799167206979457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522451377065556275972609 391838532799167206979457)
                ·
                  refine ⟨293878899599375405234593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 391838532799167206979457 293878899599375405234593)
                  ·
                    refine ⟨220409174699531553925945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 293878899599375405234593 220409174699531553925945)
                    ·
                      refine ⟨165306881024648665444459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 220409174699531553925945 165306881024648665444459)
                      ·
                        rfl

theorem cell23_321934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_321934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321934 prefixEnd_321934 := by exact prefixLift 321934
  have htrace : WordTrace (prefixWord ++ tailWord_321934) baseStart_321934 baseEnd_321934 := by
    simpa [prefixWord, tailWord_321934, baseEnd_321934] using wordTrace_append hprefix tailTrace_321934
  have hstable : (prefixWord ++ tailWord_321934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321934).length < 2 ^ (prefixWord ++ tailWord_321934).sum := by decide
  have hdescent : baseEnd_321934 < baseStart_321934 := by decide
  rcases family_descends (prefixWord ++ tailWord_321934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321940 : List Nat := [2, 4, 2, 1, 3, 1, 2, 1, 7]
def baseStart_321940 : Nat := 118140960795 + 321940 * 2 ^ 59
def prefixEnd_321940 : Nat := 4983230072969 + 3 ^ 40 * 321940 * 2
def baseEnd_321940 : Nat := 18367773545397293552159

theorem tailTrace_321940 : CollatzResearch.WordTrace tailWord_321940 prefixEnd_321940 18367773545397293552159 := by
  unfold tailWord_321940
  simp only [CollatzResearch.WordTrace]
  refine ⟨5871058226836918909845637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7828077635782558546460849 5871058226836918909845637)
  ·
    refine ⟨1100823417531922295596057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5871058226836918909845637 1100823417531922295596057)
    ·
      refine ⟨825617563148941721697043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1100823417531922295596057 825617563148941721697043)
      ·
        refine ⟨1238426344723412582545565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 825617563148941721697043 1238426344723412582545565)
        ·
          refine ⟨464409879271279718454587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1238426344723412582545565 464409879271279718454587)
          ·
            refine ⟨696614818906919577681881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464409879271279718454587 696614818906919577681881)
            ·
              refine ⟨522461114180189683261411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696614818906919577681881 522461114180189683261411)
              ·
                refine ⟨783691671270284524892117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522461114180189683261411 783691671270284524892117)
                ·
                  refine ⟨18367773545397293552159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 783691671270284524892117 18367773545397293552159)
                  ·
                    rfl

theorem cell23_321940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_321940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321940 prefixEnd_321940 := by exact prefixLift 321940
  have htrace : WordTrace (prefixWord ++ tailWord_321940) baseStart_321940 baseEnd_321940 := by
    simpa [prefixWord, tailWord_321940, baseEnd_321940] using wordTrace_append hprefix tailTrace_321940
  have hstable : (prefixWord ++ tailWord_321940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321940).length < 2 ^ (prefixWord ++ tailWord_321940).sum := by decide
  have hdescent : baseEnd_321940 < baseStart_321940 := by decide
  rcases family_descends (prefixWord ++ tailWord_321940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321943 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 1, 7, 2]
def baseStart_321943 : Nat := 118140960795 + 321943 * 2 ^ 59
def prefixEnd_321943 : Nat := 4983230072969 + 3 ^ 40 * 321943 * 2
def baseEnd_321943 : Nat := 165311502350539130231917

theorem tailTrace_321943 : CollatzResearch.WordTrace tailWord_321943 prefixEnd_321943 165311502350539130231917 := by
  unfold tailWord_321943
  simp only [CollatzResearch.WordTrace]
  refine ⟨11742225872662969332050483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7828150581775312888033655 11742225872662969332050483)
  ·
    refine ⟨17613338808994453998075725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11742225872662969332050483 17613338808994453998075725)
    ·
      refine ⟨6605002053372920249278397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17613338808994453998075725 6605002053372920249278397)
      ·
        refine ⟨2476875770014845093479399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6605002053372920249278397 2476875770014845093479399)
        ·
          refine ⟨3715313655022267640219099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2476875770014845093479399 3715313655022267640219099)
          ·
            refine ⟨5572970482533401460328649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3715313655022267640219099 5572970482533401460328649)
            ·
              refine ⟨4179727861900051095246487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5572970482533401460328649 4179727861900051095246487)
              ·
                refine ⟨6269591792850076642869731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4179727861900051095246487 6269591792850076642869731)
                ·
                  refine ⟨9404387689275114964304597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6269591792850076642869731 9404387689275114964304597)
                  ·
                    refine ⟨220415336467385506975889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9404387689275114964304597 220415336467385506975889)
                    ·
                      refine ⟨165311502350539130231917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 220415336467385506975889 165311502350539130231917)
                      ·
                        rfl

theorem cell23_321943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_321943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321943 prefixEnd_321943 := by exact prefixLift 321943
  have htrace : WordTrace (prefixWord ++ tailWord_321943) baseStart_321943 baseEnd_321943 := by
    simpa [prefixWord, tailWord_321943, baseEnd_321943] using wordTrace_append hprefix tailTrace_321943
  have hstable : (prefixWord ++ tailWord_321943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321943).length < 2 ^ (prefixWord ++ tailWord_321943).sum := by decide
  have hdescent : baseEnd_321943 < baseStart_321943 := by decide
  rcases family_descends (prefixWord ++ tailWord_321943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321976 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 2, 3, 5]
def baseStart_321976 : Nat := 118140960795 + 321976 * 2 ^ 59
def prefixEnd_321976 : Nat := 4983230072969 + 3 ^ 40 * 321976 * 2
def baseEnd_321976 : Nat := 165328447212137501119265

theorem tailTrace_321976 : CollatzResearch.WordTrace tailWord_321976 prefixEnd_321976 165328447212137501119265 := by
  unfold tailWord_321976
  simp only [CollatzResearch.WordTrace]
  refine ⟨5871714740771707984000891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7828952987695610645334521 5871714740771707984000891)
  ·
    refine ⟨8807572111157561976001337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5871714740771707984000891 8807572111157561976001337)
    ·
      refine ⟨6605679083368171482001003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8807572111157561976001337 6605679083368171482001003)
      ·
        refine ⟨9908518625052257223001505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6605679083368171482001003 9908518625052257223001505)
        ·
          refine ⟨7431388968789192917251129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9908518625052257223001505 7431388968789192917251129)
          ·
            refine ⟨5573541726591894687938347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7431388968789192917251129 5573541726591894687938347)
            ·
              refine ⟨8360312589887842031907521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5573541726591894687938347 8360312589887842031907521)
              ·
                refine ⟨6270234442415881523930641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8360312589887842031907521 6270234442415881523930641)
                ·
                  refine ⟨4702675831811911142947981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6270234442415881523930641 4702675831811911142947981)
                  ·
                    refine ⟨1763503436929466678605493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4702675831811911142947981 1763503436929466678605493)
                    ·
                      refine ⟨165328447212137501119265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1763503436929466678605493 165328447212137501119265)
                      ·
                        rfl

theorem cell23_321976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_321976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321976 prefixEnd_321976 := by exact prefixLift 321976
  have htrace : WordTrace (prefixWord ++ tailWord_321976) baseStart_321976 baseEnd_321976 := by
    simpa [prefixWord, tailWord_321976, baseEnd_321976] using wordTrace_append hprefix tailTrace_321976
  have hstable : (prefixWord ++ tailWord_321976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321976).length < 2 ^ (prefixWord ++ tailWord_321976).sum := by decide
  have hdescent : baseEnd_321976 < baseStart_321976 := by decide
  rcases family_descends (prefixWord ++ tailWord_321976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_321993 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 4, 2, 3]
def baseStart_321993 : Nat := 118140960795 + 321993 * 2 ^ 59
def prefixEnd_321993 : Nat := 4983230072969 + 3 ^ 40 * 321993 * 2
def baseEnd_321993 : Nat := 165337176383263934606687

theorem tailTrace_321993 : CollatzResearch.WordTrace tailWord_321993 prefixEnd_321993 165337176383263934606687 := by
  unfold tailWord_321993
  simp only [CollatzResearch.WordTrace]
  refine ⟨11744049522481827871370633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7829366348321218580913755 11744049522481827871370633)
  ·
    refine ⟨8808037141861370903527975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11744049522481827871370633 8808037141861370903527975)
    ·
      refine ⟨13212055712792056355291963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8808037141861370903527975 13212055712792056355291963)
      ·
        refine ⟨19818083569188084532937945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13212055712792056355291963 19818083569188084532937945)
        ·
          refine ⟨14863562676891063399703459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19818083569188084532937945 14863562676891063399703459)
          ·
            refine ⟨22295344015336595099555189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14863562676891063399703459 22295344015336595099555189)
            ·
              refine ⟨2090188501437805790583299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22295344015336595099555189 2090188501437805790583299)
              ·
                refine ⟨3135282752156708685874949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2090188501437805790583299 3135282752156708685874949)
                ·
                  refine ⟨587865516029382878601553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3135282752156708685874949 587865516029382878601553)
                  ·
                    refine ⟨440899137022037158951165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 587865516029382878601553 440899137022037158951165)
                    ·
                      refine ⟨165337176383263934606687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 440899137022037158951165 165337176383263934606687)
                      ·
                        rfl

theorem cell23_321993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 2, 3].length) (baseStart_321993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_321993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_321993 prefixEnd_321993 := by exact prefixLift 321993
  have htrace : WordTrace (prefixWord ++ tailWord_321993) baseStart_321993 baseEnd_321993 := by
    simpa [prefixWord, tailWord_321993, baseEnd_321993] using wordTrace_append hprefix tailTrace_321993
  have hstable : (prefixWord ++ tailWord_321993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_321993).length < 2 ^ (prefixWord ++ tailWord_321993).sum := by decide
  have hdescent : baseEnd_321993 < baseStart_321993 := by decide
  rcases family_descends (prefixWord ++ tailWord_321993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322063 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 4]
def baseStart_322063 : Nat := 118140960795 + 322063 * 2 ^ 59
def prefixEnd_322063 : Nat := 4983230072969 + 3 ^ 40 * 322063 * 2
def baseEnd_322063 : Nat := 165373120029078660731365

theorem tailTrace_322063 : CollatzResearch.WordTrace tailWord_322063 prefixEnd_322063 165373120029078660731365 := by
  unfold tailWord_322063
  simp only [CollatzResearch.WordTrace]
  refine ⟨11746602632228229826418843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7831068421485486550945895 11746602632228229826418843)
  ·
    refine ⟨17619903948342344739628265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11746602632228229826418843 17619903948342344739628265)
    ·
      refine ⟨13214927961256758554721199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17619903948342344739628265 13214927961256758554721199)
      ·
        refine ⟨19822391941885137832081799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13214927961256758554721199 19822391941885137832081799)
        ·
          refine ⟨29733587912827706748122699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19822391941885137832081799 29733587912827706748122699)
          ·
            refine ⟨44600381869241560122184049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29733587912827706748122699 44600381869241560122184049)
            ·
              refine ⟨33450286401931170091638037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44600381869241560122184049 33450286401931170091638037)
              ·
                refine ⟨1567982175090523598045533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33450286401931170091638037 1567982175090523598045533)
                ·
                  refine ⟨587993315658946349267075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1567982175090523598045533 587993315658946349267075)
                  ·
                    refine ⟨881989973488419523900613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 587993315658946349267075 881989973488419523900613)
                    ·
                      refine ⟨165373120029078660731365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 881989973488419523900613 165373120029078660731365)
                      ·
                        rfl

theorem cell23_322063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 4].length) (baseStart_322063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322063 prefixEnd_322063 := by exact prefixLift 322063
  have htrace : WordTrace (prefixWord ++ tailWord_322063) baseStart_322063 baseEnd_322063 := by
    simpa [prefixWord, tailWord_322063, baseEnd_322063] using wordTrace_append hprefix tailTrace_322063
  have hstable : (prefixWord ++ tailWord_322063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322063).length < 2 ^ (prefixWord ++ tailWord_322063).sum := by decide
  have hdescent : baseEnd_322063 < baseStart_322063 := by decide
  rcases family_descends (prefixWord ++ tailWord_322063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322084 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 1, 5, 2]
def baseStart_322084 : Nat := 118140960795 + 322084 * 2 ^ 59
def prefixEnd_322084 : Nat := 4983230072969 + 3 ^ 40 * 322084 * 2
def baseEnd_322084 : Nat := 165383903122823078568769

theorem tailTrace_322084 : CollatzResearch.WordTrace tailWord_322084 prefixEnd_322084 165383903122823078568769 := by
  unfold tailWord_322084
  simp only [CollatzResearch.WordTrace]
  refine ⟨5873684282576075206466653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7831579043434766941955537 5873684282576075206466653)
  ·
    refine ⟨2202631605966028202424995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5873684282576075206466653 2202631605966028202424995)
    ·
      refine ⟨3303947408949042303637493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2202631605966028202424995 3303947408949042303637493)
      ·
        refine ⟨309745069588972715966015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3303947408949042303637493 309745069588972715966015)
        ·
          refine ⟨464617604383459073949023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309745069588972715966015 464617604383459073949023)
          ·
            refine ⟨696926406575188610923535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464617604383459073949023 696926406575188610923535)
            ·
              refine ⟨1045389609862782916385303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696926406575188610923535 1045389609862782916385303)
              ·
                refine ⟨1568084414794174374577955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1045389609862782916385303 1568084414794174374577955)
                ·
                  refine ⟨2352126622191261561866933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1568084414794174374577955 2352126622191261561866933)
                  ·
                    refine ⟨220511870830430771425025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2352126622191261561866933 220511870830430771425025)
                    ·
                      refine ⟨165383903122823078568769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 220511870830430771425025 165383903122823078568769)
                      ·
                        rfl

theorem cell23_322084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_322084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322084 prefixEnd_322084 := by exact prefixLift 322084
  have htrace : WordTrace (prefixWord ++ tailWord_322084) baseStart_322084 baseEnd_322084 := by
    simpa [prefixWord, tailWord_322084, baseEnd_322084] using wordTrace_append hprefix tailTrace_322084
  have hstable : (prefixWord ++ tailWord_322084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322084).length < 2 ^ (prefixWord ++ tailWord_322084).sum := by decide
  have hdescent : baseEnd_322084 < baseStart_322084 := by decide
  rcases family_descends (prefixWord ++ tailWord_322084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322090 : List Nat := [3, 1, 4, 1, 1, 2, 2, 2, 1, 6]
def baseStart_322090 : Nat := 118140960795 + 322090 * 2 ^ 59
def prefixEnd_322090 : Nat := 4983230072969 + 3 ^ 40 * 322090 * 2
def baseEnd_322090 : Nat := 55128994668916685031247

theorem tailTrace_322090 : CollatzResearch.WordTrace tailWord_322090 prefixEnd_322090 55128994668916685031247 := by
  unfold tailWord_322090
  simp only [CollatzResearch.WordTrace]
  refine ⟨2936896850782603359412931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7831724935420275625101149 2936896850782603359412931)
  ·
    refine ⟨4405345276173905039119397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2936896850782603359412931 4405345276173905039119397)
    ·
      refine ⟨826002239282607194834887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4405345276173905039119397 826002239282607194834887)
      ·
        refine ⟨1239003358923910792252331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 826002239282607194834887 1239003358923910792252331)
        ·
          refine ⟨1858505038385866188378497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1239003358923910792252331 1858505038385866188378497)
          ·
            refine ⟨1393878778789399641283873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1858505038385866188378497 1393878778789399641283873)
            ·
              refine ⟨1045409084092049730962905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1393878778789399641283873 1045409084092049730962905)
              ·
                refine ⟨784056813069037298222179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1045409084092049730962905 784056813069037298222179)
                ·
                  refine ⟨1176085219603555947333269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 784056813069037298222179 1176085219603555947333269)
                  ·
                    refine ⟨55128994668916685031247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1176085219603555947333269 55128994668916685031247)
                    ·
                      rfl

theorem cell23_322090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_322090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322090 prefixEnd_322090 := by exact prefixLift 322090
  have htrace : WordTrace (prefixWord ++ tailWord_322090) baseStart_322090 baseEnd_322090 := by
    simpa [prefixWord, tailWord_322090, baseEnd_322090] using wordTrace_append hprefix tailTrace_322090
  have hstable : (prefixWord ++ tailWord_322090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322090).length < 2 ^ (prefixWord ++ tailWord_322090).sum := by decide
  have hdescent : baseEnd_322090 < baseStart_322090 := by decide
  rcases family_descends (prefixWord ++ tailWord_322090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322097 : List Nat := [1, 2, 2, 3, 1, 1, 6, 1, 1, 1, 4]
def baseStart_322097 : Nat := 118140960795 + 322097 * 2 ^ 59
def prefixEnd_322097 : Nat := 4983230072969 + 3 ^ 40 * 322097 * 2
def baseEnd_322097 : Nat := 165390578371331527706209

theorem tailTrace_322097 : CollatzResearch.WordTrace tailWord_322097 prefixEnd_322097 165390578371331527706209 := by
  unfold tailWord_322097
  simp only [CollatzResearch.WordTrace]
  refine ⟨11747842714105053633156545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7831895142736702422104363 11747842714105053633156545)
  ·
    refine ⟨8810882035578790224867409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11747842714105053633156545 8810882035578790224867409)
    ·
      refine ⟨6608161526684092668650557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8810882035578790224867409 6608161526684092668650557)
      ·
        refine ⟨2478060572506534750743959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6608161526684092668650557 2478060572506534750743959)
        ·
          refine ⟨3717090858759802126115939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2478060572506534750743959 3717090858759802126115939)
          ·
            refine ⟨5575636288139703189173909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3717090858759802126115939 5575636288139703189173909)
            ·
              refine ⟨261357951006548586992527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5575636288139703189173909 261357951006548586992527)
              ·
                refine ⟨392036926509822880488791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261357951006548586992527 392036926509822880488791)
                ·
                  refine ⟨588055389764734320733187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392036926509822880488791 588055389764734320733187)
                  ·
                    refine ⟨882083084647101481099781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 588055389764734320733187 882083084647101481099781)
                    ·
                      refine ⟨165390578371331527706209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 882083084647101481099781 165390578371331527706209)
                      ·
                        rfl

theorem cell23_322097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_322097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322097 prefixEnd_322097 := by exact prefixLift 322097
  have htrace : WordTrace (prefixWord ++ tailWord_322097) baseStart_322097 baseEnd_322097 := by
    simpa [prefixWord, tailWord_322097, baseEnd_322097] using wordTrace_append hprefix tailTrace_322097
  have hstable : (prefixWord ++ tailWord_322097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322097).length < 2 ^ (prefixWord ++ tailWord_322097).sum := by decide
  have hdescent : baseEnd_322097 < baseStart_322097 := by decide
  rcases family_descends (prefixWord ++ tailWord_322097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322133 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 2, 7]
def baseStart_322133 : Nat := 118140960795 + 322133 * 2 ^ 59
def prefixEnd_322133 : Nat := 4983230072969 + 3 ^ 40 * 322133 * 2
def baseEnd_322133 : Nat := 55136354558297795618681

theorem tailTrace_322133 : CollatzResearch.WordTrace tailWord_322133 prefixEnd_322133 55136354558297795618681 := by
  unfold tailWord_322133
  simp only [CollatzResearch.WordTrace]
  refine ⟨11749155741974631781467053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7832770494649754520978035 11749155741974631781467053)
  ·
    refine ⟨4405933403240486918050145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11749155741974631781467053 4405933403240486918050145)
    ·
      refine ⟨3304450052430365188537609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4405933403240486918050145 3304450052430365188537609)
      ·
        refine ⟨2478337539322773891403207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3304450052430365188537609 2478337539322773891403207)
        ·
          refine ⟨3717506308984160837104811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2478337539322773891403207 3717506308984160837104811)
          ·
            refine ⟨5576259463476241255657217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3717506308984160837104811 5576259463476241255657217)
            ·
              refine ⟨4182194597607180941742913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5576259463476241255657217 4182194597607180941742913)
              ·
                refine ⟨3136645948205385706307185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4182194597607180941742913 3136645948205385706307185)
                ·
                  refine ⟨2352484461154039279730389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3136645948205385706307185 2352484461154039279730389)
                  ·
                    refine ⟨55136354558297795618681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2352484461154039279730389 55136354558297795618681)
                    ·
                      rfl

theorem cell23_322133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_322133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322133 prefixEnd_322133 := by exact prefixLift 322133
  have htrace : WordTrace (prefixWord ++ tailWord_322133) baseStart_322133 baseEnd_322133 := by
    simpa [prefixWord, tailWord_322133, baseEnd_322133] using wordTrace_append hprefix tailTrace_322133
  have hstable : (prefixWord ++ tailWord_322133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322133).length < 2 ^ (prefixWord ++ tailWord_322133).sum := by decide
  have hdescent : baseEnd_322133 < baseStart_322133 := by decide
  rcases family_descends (prefixWord ++ tailWord_322133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322142 : List Nat := [4, 4, 1, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_322142 : Nat := 118140960795 + 322142 * 2 ^ 59
def prefixEnd_322142 : Nat := 4983230072969 + 3 ^ 40 * 322142 * 2
def baseEnd_322142 : Nat := 165413685000783851643503

theorem tailTrace_322142 : CollatzResearch.WordTrace tailWord_322142 prefixEnd_322142 165413685000783851643503 := by
  unfold tailWord_322142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1468685499867753289818085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7832989332628017545696453 1468685499867753289818085)
  ·
    refine ⟨275378531225203741840891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1468685499867753289818085 275378531225203741840891)
    ·
      refine ⟨413067796837805612761337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275378531225203741840891 413067796837805612761337)
      ·
        refine ⟨309800847628354209571003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413067796837805612761337 309800847628354209571003)
        ·
          refine ⟨464701271442531314356505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309800847628354209571003 464701271442531314356505)
          ·
            refine ⟨348525953581898485767379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 464701271442531314356505 348525953581898485767379)
            ·
              refine ⟨522788930372847728651069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348525953581898485767379 522788930372847728651069)
              ·
                refine ⟨196045848889817898244151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 522788930372847728651069 196045848889817898244151)
                ·
                  refine ⟨294068773334726847366227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196045848889817898244151 294068773334726847366227)
                  ·
                    refine ⟨441103160002090271049341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 294068773334726847366227 441103160002090271049341)
                    ·
                      refine ⟨165413685000783851643503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 441103160002090271049341 165413685000783851643503)
                      ·
                        rfl

theorem cell23_322142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_322142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322142 prefixEnd_322142 := by exact prefixLift 322142
  have htrace : WordTrace (prefixWord ++ tailWord_322142) baseStart_322142 baseEnd_322142 := by
    simpa [prefixWord, tailWord_322142, baseEnd_322142] using wordTrace_append hprefix tailTrace_322142
  have hstable : (prefixWord ++ tailWord_322142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322142).length < 2 ^ (prefixWord ++ tailWord_322142).sum := by decide
  have hdescent : baseEnd_322142 < baseStart_322142 := by decide
  rcases family_descends (prefixWord ++ tailWord_322142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322153 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 1, 5, 4]
def baseStart_322153 : Nat := 118140960795 + 322153 * 2 ^ 59
def prefixEnd_322153 : Nat := 4983230072969 + 3 ^ 40 * 322153 * 2
def baseEnd_322153 : Nat := 165419333287983308605951

theorem tailTrace_322153 : CollatzResearch.WordTrace tailWord_322153 prefixEnd_322153 165419333287983308605951 := by
  unfold tailWord_322153
  simp only [CollatzResearch.WordTrace]
  refine ⟨11749885201902175197195113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7833256801268116798130075 11749885201902175197195113)
  ·
    refine ⟨8812413901426631397896335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11749885201902175197195113 8812413901426631397896335)
    ·
      refine ⟨13218620852139947096844503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8812413901426631397896335 13218620852139947096844503)
      ·
        refine ⟨19827931278209920645266755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13218620852139947096844503 19827931278209920645266755)
        ·
          refine ⟨29741896917314880967900133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19827931278209920645266755 29741896917314880967900133)
          ·
            refine ⟨5576605671996540181481275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29741896917314880967900133 5576605671996540181481275)
            ·
              refine ⟨8364908507994810272221913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5576605671996540181481275 8364908507994810272221913)
              ·
                refine ⟨6273681380996107704166435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8364908507994810272221913 6273681380996107704166435)
                ·
                  refine ⟨9410522071494161556249653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6273681380996107704166435 9410522071494161556249653)
                  ·
                    refine ⟨882236444202577645898405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9410522071494161556249653 882236444202577645898405)
                    ·
                      refine ⟨165419333287983308605951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 882236444202577645898405 165419333287983308605951)
                      ·
                        rfl

theorem cell23_322153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_322153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322153 prefixEnd_322153 := by exact prefixLift 322153
  have htrace : WordTrace (prefixWord ++ tailWord_322153) baseStart_322153 baseEnd_322153 := by
    simpa [prefixWord, tailWord_322153, baseEnd_322153] using wordTrace_append hprefix tailTrace_322153
  have hstable : (prefixWord ++ tailWord_322153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322153).length < 2 ^ (prefixWord ++ tailWord_322153).sum := by decide
  have hdescent : baseEnd_322153 < baseStart_322153 := by decide
  rcases family_descends (prefixWord ++ tailWord_322153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322163 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 2, 6]
def baseStart_322163 : Nat := 118140960795 + 322163 * 2 ^ 59
def prefixEnd_322163 : Nat := 4983230072969 + 3 ^ 40 * 322163 * 2
def baseEnd_322163 : Nat := 55141489364842756493635

theorem tailTrace_322163 : CollatzResearch.WordTrace tailWord_322163 prefixEnd_322163 55141489364842756493635 := by
  unfold tailWord_322163
  simp only [CollatzResearch.WordTrace]
  refine ⟨11750249931865946905059143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7833499954577297936706095 11750249931865946905059143)
  ·
    refine ⟨17625374897798920357588715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11750249931865946905059143 17625374897798920357588715)
    ·
      refine ⟨26438062346698380536383073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17625374897798920357588715 26438062346698380536383073)
      ·
        refine ⟨19828546760023785402287305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26438062346698380536383073 19828546760023785402287305)
        ·
          refine ⟨14871410070017839051715479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19828546760023785402287305 14871410070017839051715479)
          ·
            refine ⟨22307115105026758577573219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14871410070017839051715479 22307115105026758577573219)
            ·
              refine ⟨33460672657540137866359829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22307115105026758577573219 33460672657540137866359829)
              ·
                refine ⟨1568469030822193962485617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33460672657540137866359829 1568469030822193962485617)
                ·
                  refine ⟨1176351773116645471864213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1568469030822193962485617 1176351773116645471864213)
                  ·
                    refine ⟨55141489364842756493635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1176351773116645471864213 55141489364842756493635)
                    ·
                      rfl

theorem cell23_322163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 6].length) (baseStart_322163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322163 prefixEnd_322163 := by exact prefixLift 322163
  have htrace : WordTrace (prefixWord ++ tailWord_322163) baseStart_322163 baseEnd_322163 := by
    simpa [prefixWord, tailWord_322163, baseEnd_322163] using wordTrace_append hprefix tailTrace_322163
  have hstable : (prefixWord ++ tailWord_322163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322163).length < 2 ^ (prefixWord ++ tailWord_322163).sum := by decide
  have hdescent : baseEnd_322163 < baseStart_322163 := by decide
  rcases family_descends (prefixWord ++ tailWord_322163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322165 : List Nat := [1, 3, 4, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_322165 : Nat := 118140960795 + 322165 * 2 ^ 59
def prefixEnd_322165 : Nat := 4983230072969 + 3 ^ 40 * 322165 * 2
def baseEnd_322165 : Nat := 165425495055837261655897

theorem tailTrace_322165 : CollatzResearch.WordTrace tailWord_322165 prefixEnd_322165 165425495055837261655897 := by
  unfold tailWord_322165
  simp only [CollatzResearch.WordTrace]
  refine ⟨11750322877858701246631949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7833548585239134164421299 11750322877858701246631949)
  ·
    refine ⟨4406371079197012967486981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11750322877858701246631949 4406371079197012967486981)
    ·
      refine ⟨826194577349439931403809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4406371079197012967486981 826194577349439931403809)
      ·
        refine ⟨619645933012079948552857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 826194577349439931403809 619645933012079948552857)
        ·
          refine ⟨464734449759059961414643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 619645933012079948552857 464734449759059961414643)
          ·
            refine ⟨697101674638589942121965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464734449759059961414643 697101674638589942121965)
            ·
              refine ⟨261413127989471228295737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 697101674638589942121965 261413127989471228295737)
              ·
                refine ⟨196059845992103421221803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261413127989471228295737 196059845992103421221803)
                ·
                  refine ⟨294089768988155131832705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196059845992103421221803 294089768988155131832705)
                  ·
                    refine ⟨220567326741116348874529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 294089768988155131832705 220567326741116348874529)
                    ·
                      refine ⟨165425495055837261655897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 220567326741116348874529 165425495055837261655897)
                      ·
                        rfl

theorem cell23_322165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_322165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322165 prefixEnd_322165 := by exact prefixLift 322165
  have htrace : WordTrace (prefixWord ++ tailWord_322165) baseStart_322165 baseEnd_322165 := by
    simpa [prefixWord, tailWord_322165, baseEnd_322165] using wordTrace_append hprefix tailTrace_322165
  have hstable : (prefixWord ++ tailWord_322165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322165).length < 2 ^ (prefixWord ++ tailWord_322165).sum := by decide
  have hdescent : baseEnd_322165 < baseStart_322165 := by decide
  rcases family_descends (prefixWord ++ tailWord_322165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322181 : List Nat := [1, 3, 1, 1, 4, 4, 2, 1, 2, 1, 3]
def baseStart_322181 : Nat := 118140960795 + 322181 * 2 ^ 59
def prefixEnd_322181 : Nat := 4983230072969 + 3 ^ 40 * 322181 * 2
def baseEnd_322181 : Nat := 165433710746309199055823

theorem tailTrace_322181 : CollatzResearch.WordTrace tailWord_322181 prefixEnd_322181 165433710746309199055823 := by
  unfold tailWord_322181
  simp only [CollatzResearch.WordTrace]
  refine ⟨11750906445800735979214397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7833937630533823986142931 11750906445800735979214397)
  ·
    refine ⟨4406589917175275992205399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11750906445800735979214397 4406589917175275992205399)
    ·
      refine ⟨6609884875762913988308099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4406589917175275992205399 6609884875762913988308099)
      ·
        refine ⟨9914827313644370982462149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6609884875762913988308099 9914827313644370982462149)
        ·
          refine ⟨1859030121308319559211653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9914827313644370982462149 1859030121308319559211653)
          ·
            refine ⟨348568147745309917352185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1859030121308319559211653 348568147745309917352185)
            ·
              refine ⟨261426110808982438014139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 348568147745309917352185 261426110808982438014139)
              ·
                refine ⟨392139166213473657021209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261426110808982438014139 392139166213473657021209)
                ·
                  refine ⟨294104374660105242765907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392139166213473657021209 294104374660105242765907)
                  ·
                    refine ⟨441156561990157864148861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 294104374660105242765907 441156561990157864148861)
                    ·
                      refine ⟨165433710746309199055823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 441156561990157864148861 165433710746309199055823)
                      ·
                        rfl

theorem cell23_322181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 2, 1, 3].length) (baseStart_322181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322181 prefixEnd_322181 := by exact prefixLift 322181
  have htrace : WordTrace (prefixWord ++ tailWord_322181) baseStart_322181 baseEnd_322181 := by
    simpa [prefixWord, tailWord_322181, baseEnd_322181] using wordTrace_append hprefix tailTrace_322181
  have hstable : (prefixWord ++ tailWord_322181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322181).length < 2 ^ (prefixWord ++ tailWord_322181).sum := by decide
  have hdescent : baseEnd_322181 < baseStart_322181 := by decide
  rcases family_descends (prefixWord ++ tailWord_322181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322187 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 6, 2, 2]
def baseStart_322187 : Nat := 118140960795 + 322187 * 2 ^ 59
def prefixEnd_322187 : Nat := 4983230072969 + 3 ^ 40 * 322187 * 2
def baseEnd_322187 : Nat := 165436791630236175580795

theorem tailTrace_322187 : CollatzResearch.WordTrace tailWord_322187 prefixEnd_322187 165436791630236175580795 := by
  unfold tailWord_322187
  simp only [CollatzResearch.WordTrace]
  refine ⟨11751125283778999003932815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7834083522519332669288543 11751125283778999003932815)
  ·
    refine ⟨17626687925668498505899223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11751125283778999003932815 17626687925668498505899223)
    ·
      refine ⟨26440031888502747758848835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17626687925668498505899223 26440031888502747758848835)
      ·
        refine ⟨39660047832754121638273253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26440031888502747758848835 39660047832754121638273253)
        ·
          refine ⟨7436258968641397807176235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39660047832754121638273253 7436258968641397807176235)
          ·
            refine ⟨11154388452962096710764353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7436258968641397807176235 11154388452962096710764353)
            ·
              refine ⟨8365791339721572533073265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11154388452962096710764353 8365791339721572533073265)
              ·
                refine ⟨6274343504791179399804949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8365791339721572533073265 6274343504791179399804949)
                ·
                  refine ⟨294109851787086534365857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6274343504791179399804949 294109851787086534365857)
                  ·
                    refine ⟨220582388840314900774393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 294109851787086534365857 220582388840314900774393)
                    ·
                      refine ⟨165436791630236175580795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 220582388840314900774393 165436791630236175580795)
                      ·
                        rfl

theorem cell23_322187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 2, 2].length) (baseStart_322187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322187 prefixEnd_322187 := by exact prefixLift 322187
  have htrace : WordTrace (prefixWord ++ tailWord_322187) baseStart_322187 baseEnd_322187 := by
    simpa [prefixWord, tailWord_322187, baseEnd_322187] using wordTrace_append hprefix tailTrace_322187
  have hstable : (prefixWord ++ tailWord_322187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322187).length < 2 ^ (prefixWord ++ tailWord_322187).sum := by decide
  have hdescent : baseEnd_322187 < baseStart_322187 := by decide
  rcases family_descends (prefixWord ++ tailWord_322187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322190 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_322190 : Nat := 118140960795 + 322190 * 2 ^ 59
def prefixEnd_322190 : Nat := 4983230072969 + 3 ^ 40 * 322190 * 2
def baseEnd_322190 : Nat := 165438332072199663843281

theorem tailTrace_322190 : CollatzResearch.WordTrace tailWord_322190 prefixEnd_322190 165438332072199663843281 := by
  unfold tailWord_322190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1468904337846016314536503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7834156468512087010861349 1468904337846016314536503)
  ·
    refine ⟨2203356506769024471804755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1468904337846016314536503 2203356506769024471804755)
    ·
      refine ⟨3305034760153536707707133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2203356506769024471804755 3305034760153536707707133)
      ·
        refine ⟨1239388035057576265390175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3305034760153536707707133 1239388035057576265390175)
        ·
          refine ⟨1859082052586364398085263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1239388035057576265390175 1859082052586364398085263)
          ·
            refine ⟨2788623078879546597127895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1859082052586364398085263 2788623078879546597127895)
            ·
              refine ⟨4182934618319319895691843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2788623078879546597127895 4182934618319319895691843)
              ·
                refine ⟨6274401927478979843537765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4182934618319319895691843 6274401927478979843537765)
                ·
                  refine ⟨1176450361402308720663331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6274401927478979843537765 1176450361402308720663331)
                  ·
                    refine ⟨1764675542103463080994997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1176450361402308720663331 1764675542103463080994997)
                    ·
                      refine ⟨165438332072199663843281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1764675542103463080994997 165438332072199663843281)
                      ·
                        rfl

theorem cell23_322190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_322190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322190 prefixEnd_322190 := by exact prefixLift 322190
  have htrace : WordTrace (prefixWord ++ tailWord_322190) baseStart_322190 baseEnd_322190 := by
    simpa [prefixWord, tailWord_322190, baseEnd_322190] using wordTrace_append hprefix tailTrace_322190
  have hstable : (prefixWord ++ tailWord_322190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322190).length < 2 ^ (prefixWord ++ tailWord_322190).sum := by decide
  have hdescent : baseEnd_322190 < baseStart_322190 := by decide
  rcases family_descends (prefixWord ++ tailWord_322190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322204 : List Nat := [2, 2, 3, 2, 2, 2, 1, 2, 1, 4, 2]
def baseStart_322204 : Nat := 118140960795 + 322204 * 2 ^ 59
def prefixEnd_322204 : Nat := 4983230072969 + 3 ^ 40 * 322204 * 2
def baseEnd_322204 : Nat := 165445520801362609068217

theorem tailTrace_322204 : CollatzResearch.WordTrace tailWord_322204 prefixEnd_322204 165445520801362609068217 := by
  unfold tailWord_322204
  simp only [CollatzResearch.WordTrace]
  refine ⟨5875872662358705453650833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7834496883144940604867777 5875872662358705453650833)
  ·
    refine ⟨4406904496769029090238125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5875872662358705453650833 4406904496769029090238125)
    ·
      refine ⟨1652589186288385908839297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4406904496769029090238125 1652589186288385908839297)
      ·
        refine ⟨1239441889716289431629473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1652589186288385908839297 1239441889716289431629473)
        ·
          refine ⟨929581417287217073722105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1239441889716289431629473 929581417287217073722105)
          ·
            refine ⟨697186062965412805291579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 929581417287217073722105 697186062965412805291579)
            ·
              refine ⟨1045779094448119207937369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697186062965412805291579 1045779094448119207937369)
              ·
                refine ⟨784334320836089405953027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1045779094448119207937369 784334320836089405953027)
                ·
                  refine ⟨1176501481254134108929541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 784334320836089405953027 1176501481254134108929541)
                  ·
                    refine ⟨220594027735150145424289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1176501481254134108929541 220594027735150145424289)
                    ·
                      refine ⟨165445520801362609068217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 220594027735150145424289 165445520801362609068217)
                      ·
                        rfl

theorem cell23_322204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_322204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322204 prefixEnd_322204 := by exact prefixLift 322204
  have htrace : WordTrace (prefixWord ++ tailWord_322204) baseStart_322204 baseEnd_322204 := by
    simpa [prefixWord, tailWord_322204, baseEnd_322204] using wordTrace_append hprefix tailTrace_322204
  have hstable : (prefixWord ++ tailWord_322204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322204).length < 2 ^ (prefixWord ++ tailWord_322204).sum := by decide
  have hdescent : baseEnd_322204 < baseStart_322204 := by decide
  rcases family_descends (prefixWord ++ tailWord_322204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322221 : List Nat := [1, 5, 2, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_322221 : Nat := 118140960795 + 322221 * 2 ^ 59
def prefixEnd_322221 : Nat := 4983230072969 + 3 ^ 40 * 322221 * 2
def baseEnd_322221 : Nat := 165454249972489042555639

theorem tailTrace_322221 : CollatzResearch.WordTrace tailWord_322221 prefixEnd_322221 165454249972489042555639 := by
  unfold tailWord_322221
  simp only [CollatzResearch.WordTrace]
  refine ⟨11752365365655822810670517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7834910243770548540447011 11752365365655822810670517)
  ·
    refine ⟨1101784253030233388500361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11752365365655822810670517 1101784253030233388500361)
    ·
      refine ⟨826338189772675041375271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1101784253030233388500361 826338189772675041375271)
      ·
        refine ⟨1239507284659012562062907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 826338189772675041375271 1239507284659012562062907)
        ·
          refine ⟨1859260926988518843094361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1239507284659012562062907 1859260926988518843094361)
          ·
            refine ⟨1394445695241389132320771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1859260926988518843094361 1394445695241389132320771)
            ·
              refine ⟨2091668542862083698481157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1394445695241389132320771 2091668542862083698481157)
              ·
                refine ⟨392187851786640693465217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2091668542862083698481157 392187851786640693465217)
                ·
                  refine ⟨294140888839980520098913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392187851786640693465217 294140888839980520098913)
                  ·
                    refine ⟨220605666629985390074185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 294140888839980520098913 220605666629985390074185)
                    ·
                      refine ⟨165454249972489042555639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 220605666629985390074185 165454249972489042555639)
                      ·
                        rfl

theorem cell23_322221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_322221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322221 prefixEnd_322221 := by exact prefixLift 322221
  have htrace : WordTrace (prefixWord ++ tailWord_322221) baseStart_322221 baseEnd_322221 := by
    simpa [prefixWord, tailWord_322221, baseEnd_322221] using wordTrace_append hprefix tailTrace_322221
  have hstable : (prefixWord ++ tailWord_322221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322221).length < 2 ^ (prefixWord ++ tailWord_322221).sum := by decide
  have hdescent : baseEnd_322221 < baseStart_322221 := by decide
  rcases family_descends (prefixWord ++ tailWord_322221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322227 : List Nat := [1, 1, 1, 2, 3, 5, 1, 4, 5]
def baseStart_322227 : Nat := 118140960795 + 322227 * 2 ^ 59
def prefixEnd_322227 : Nat := 4983230072969 + 3 ^ 40 * 322227 * 2
def baseEnd_322227 : Nat := 18384147872935113231179

theorem tailTrace_322227 : CollatzResearch.WordTrace tailWord_322227 prefixEnd_322227 18384147872935113231179 := by
  unfold tailWord_322227
  simp only [CollatzResearch.WordTrace]
  refine ⟨11752584203634085835388935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7835056135756057223592623 11752584203634085835388935)
  ·
    refine ⟨17628876305451128753083403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11752584203634085835388935 17628876305451128753083403)
    ·
      refine ⟨26443314458176693129625105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17628876305451128753083403 26443314458176693129625105)
      ·
        refine ⟨19832485843632519847218829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26443314458176693129625105 19832485843632519847218829)
        ·
          refine ⟨7437182191362194942707061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19832485843632519847218829 7437182191362194942707061)
          ·
            refine ⟨697235830440205775878787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7437182191362194942707061 697235830440205775878787)
            ·
              refine ⟨1045853745660308663818181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697235830440205775878787 1045853745660308663818181)
              ·
                refine ⟨196097577311307874465909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1045853745660308663818181 196097577311307874465909)
                ·
                  refine ⟨18384147872935113231179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 196097577311307874465909 18384147872935113231179)
                  ·
                    rfl

theorem cell23_322227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 5].length) (baseStart_322227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322227 prefixEnd_322227 := by exact prefixLift 322227
  have htrace : WordTrace (prefixWord ++ tailWord_322227) baseStart_322227 baseEnd_322227 := by
    simpa [prefixWord, tailWord_322227, baseEnd_322227] using wordTrace_append hprefix tailTrace_322227
  have hstable : (prefixWord ++ tailWord_322227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322227).length < 2 ^ (prefixWord ++ tailWord_322227).sum := by decide
  have hdescent : baseEnd_322227 < baseStart_322227 := by decide
  rcases family_descends (prefixWord ++ tailWord_322227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322237 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 2, 3, 3]
def baseStart_322237 : Nat := 118140960795 + 322237 * 2 ^ 59
def prefixEnd_322237 : Nat := 4983230072969 + 3 ^ 40 * 322237 * 2
def baseEnd_322237 : Nat := 165462465662960979955565

theorem tailTrace_322237 : CollatzResearch.WordTrace tailWord_322237 prefixEnd_322237 165462465662960979955565 := by
  unfold tailWord_322237
  simp only [CollatzResearch.WordTrace]
  refine ⟨11752948933597857543252965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7835299289065238362168643 11752948933597857543252965)
  ·
    refine ⟨2203677925049598289359931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11752948933597857543252965 2203677925049598289359931)
    ·
      refine ⟨3305516887574397434039897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2203677925049598289359931 3305516887574397434039897)
      ·
        refine ⟨2479137665680798075529923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3305516887574397434039897 2479137665680798075529923)
        ·
          refine ⟨3718706498521197113294885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2479137665680798075529923 3718706498521197113294885)
          ·
            refine ⟨697257468472724458742791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3718706498521197113294885 697257468472724458742791)
            ·
              refine ⟨1045886202709086688114187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697257468472724458742791 1045886202709086688114187)
              ·
                refine ⟨1568829304063630032171281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1045886202709086688114187 1568829304063630032171281)
                ·
                  refine ⟨1176621978047722524128461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1568829304063630032171281 1176621978047722524128461)
                  ·
                    refine ⟨441233241767895946548173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1176621978047722524128461 441233241767895946548173)
                    ·
                      refine ⟨165462465662960979955565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 441233241767895946548173 165462465662960979955565)
                      ·
                        rfl

theorem cell23_322237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_322237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322237 prefixEnd_322237 := by exact prefixLift 322237
  have htrace : WordTrace (prefixWord ++ tailWord_322237) baseStart_322237 baseEnd_322237 := by
    simpa [prefixWord, tailWord_322237, baseEnd_322237] using wordTrace_append hprefix tailTrace_322237
  have hstable : (prefixWord ++ tailWord_322237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322237).length < 2 ^ (prefixWord ++ tailWord_322237).sum := by decide
  have hdescent : baseEnd_322237 < baseStart_322237 := by decide
  rcases family_descends (prefixWord ++ tailWord_322237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322261 : List Nat := [1, 3, 2, 5, 1, 1, 2, 3, 5]
def baseStart_322261 : Nat := 118140960795 + 322261 * 2 ^ 59
def prefixEnd_322261 : Nat := 4983230072969 + 3 ^ 40 * 322261 * 2
def baseEnd_322261 : Nat := 18386087688740987339495

theorem tailTrace_322261 : CollatzResearch.WordTrace tailWord_322261 prefixEnd_322261 18386087688740987339495 := by
  unfold tailWord_322261
  simp only [CollatzResearch.WordTrace]
  refine ⟨11753824285510909642126637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7835882857007273094751091 11753824285510909642126637)
  ·
    refine ⟨4407684107066591115797489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11753824285510909642126637 4407684107066591115797489)
    ·
      refine ⟨3305763080299943336848117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4407684107066591115797489 3305763080299943336848117)
      ·
        refine ⟨309915288778119687829511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3305763080299943336848117 309915288778119687829511)
        ·
          refine ⟨464872933167179531744267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309915288778119687829511 464872933167179531744267)
          ·
            refine ⟨697309399750769297616401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464872933167179531744267 697309399750769297616401)
            ·
              refine ⟨522982049813076973212301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 697309399750769297616401 522982049813076973212301)
              ·
                refine ⟨196118268679903864954613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 522982049813076973212301 196118268679903864954613)
                ·
                  refine ⟨18386087688740987339495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 196118268679903864954613 18386087688740987339495)
                  ·
                    rfl

theorem cell23_322261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 5].length) (baseStart_322261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322261 prefixEnd_322261 := by exact prefixLift 322261
  have htrace : WordTrace (prefixWord ++ tailWord_322261) baseStart_322261 baseEnd_322261 := by
    simpa [prefixWord, tailWord_322261, baseEnd_322261] using wordTrace_append hprefix tailTrace_322261
  have hstable : (prefixWord ++ tailWord_322261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322261).length < 2 ^ (prefixWord ++ tailWord_322261).sum := by decide
  have hdescent : baseEnd_322261 < baseStart_322261 := by decide
  rcases family_descends (prefixWord ++ tailWord_322261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322287 : List Nat := [1, 1, 2, 1, 5, 2, 1, 3, 3, 4]
def baseStart_322287 : Nat := 118140960795 + 322287 * 2 ^ 59
def prefixEnd_322287 : Nat := 4983230072969 + 3 ^ 40 * 322287 * 2
def baseEnd_322287 : Nat := 55162713231895261443445

theorem tailTrace_322287 : CollatzResearch.WordTrace tailWord_322287 prefixEnd_322287 55162713231895261443445 := by
  unfold tailWord_322287
  simp only [CollatzResearch.WordTrace]
  refine ⟨11754772583416716082573115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7836515055611144055048743 11754772583416716082573115)
  ·
    refine ⟨17632158875125074123859673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11754772583416716082573115 17632158875125074123859673)
    ·
      refine ⟨13224119156343805592894755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17632158875125074123859673 13224119156343805592894755)
      ·
        refine ⟨19836178734515708389342133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13224119156343805592894755 19836178734515708389342133)
        ·
          refine ⟨1859641756360847661500825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19836178734515708389342133 1859641756360847661500825)
          ·
            refine ⟨1394731317270635746125619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1859641756360847661500825 1394731317270635746125619)
            ·
              refine ⟨2092096975905953619188429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1394731317270635746125619 2092096975905953619188429)
              ·
                refine ⟨784536365964732607195661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2092096975905953619188429 784536365964732607195661)
                ·
                  refine ⟨294201137236774727698373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784536365964732607195661 294201137236774727698373)
                  ·
                    refine ⟨55162713231895261443445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 294201137236774727698373 55162713231895261443445)
                    ·
                      rfl

theorem cell23_322287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 4].length) (baseStart_322287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322287 prefixEnd_322287 := by exact prefixLift 322287
  have htrace : WordTrace (prefixWord ++ tailWord_322287) baseStart_322287 baseEnd_322287 := by
    simpa [prefixWord, tailWord_322287, baseEnd_322287] using wordTrace_append hprefix tailTrace_322287
  have hstable : (prefixWord ++ tailWord_322287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322287).length < 2 ^ (prefixWord ++ tailWord_322287).sum := by decide
  have hdescent : baseEnd_322287 < baseStart_322287 := by decide
  rcases family_descends (prefixWord ++ tailWord_322287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322294 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2]
def baseStart_322294 : Nat := 118140960795 + 322294 * 2 ^ 59
def prefixEnd_322294 : Nat := 4983230072969 + 3 ^ 40 * 322294 * 2
def baseEnd_322294 : Nat := 165491734060267256942803

theorem tailTrace_322294 : CollatzResearch.WordTrace tailWord_322294 prefixEnd_322294 165491734060267256942803 := by
  unfold tailWord_322294
  simp only [CollatzResearch.WordTrace]
  refine ⟨734689243399459767379871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7836685262927570852051957 734689243399459767379871)
  ·
    refine ⟨1102033865099189651069807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 734689243399459767379871 1102033865099189651069807)
    ·
      refine ⟨1653050797648784476604711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1102033865099189651069807 1653050797648784476604711)
      ·
        refine ⟨2479576196473176714907067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1653050797648784476604711 2479576196473176714907067)
        ·
          refine ⟨3719364294709765072360601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2479576196473176714907067 3719364294709765072360601)
          ·
            refine ⟨2789523221032323804270451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3719364294709765072360601 2789523221032323804270451)
            ·
              refine ⟨4184284831548485706405677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2789523221032323804270451 4184284831548485706405677)
              ·
                refine ⟨1569106811830682139902129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4184284831548485706405677 1569106811830682139902129)
                ·
                  refine ⟨1176830108873011604926597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1569106811830682139902129 1176830108873011604926597)
                  ·
                    refine ⟨220655645413689675923737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1176830108873011604926597 220655645413689675923737)
                    ·
                      refine ⟨165491734060267256942803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 220655645413689675923737 165491734060267256942803)
                      ·
                        rfl

theorem cell23_322294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_322294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322294 prefixEnd_322294 := by exact prefixLift 322294
  have htrace : WordTrace (prefixWord ++ tailWord_322294) baseStart_322294 baseEnd_322294 := by
    simpa [prefixWord, tailWord_322294, baseEnd_322294] using wordTrace_append hprefix tailTrace_322294
  have hstable : (prefixWord ++ tailWord_322294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322294).length < 2 ^ (prefixWord ++ tailWord_322294).sum := by decide
  have hdescent : baseEnd_322294 < baseStart_322294 := by decide
  rcases family_descends (prefixWord ++ tailWord_322294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322338 : List Nat := [3, 3, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_322338 : Nat := 118140960795 + 322338 * 2 ^ 59
def prefixEnd_322338 : Nat := 4983230072969 + 3 ^ 40 * 322338 * 2
def baseEnd_322338 : Nat := 55171442403021694930867

theorem tailTrace_322338 : CollatzResearch.WordTrace tailWord_322338 prefixEnd_322338 55171442403021694930867 := by
  unfold tailWord_322338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2939158176557987948169917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7837755137487967861786445 2939158176557987948169917)
  ·
    refine ⟨1102184316209245480563719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2939158176557987948169917 1102184316209245480563719)
    ·
      refine ⟨1653276474313868220845579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1102184316209245480563719 1653276474313868220845579)
      ·
        refine ⟨2479914711470802331268369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1653276474313868220845579 2479914711470802331268369)
        ·
          refine ⟨1859936033603101748451277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2479914711470802331268369 1859936033603101748451277)
          ·
            refine ⟨697476012601163155669229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1859936033603101748451277 697476012601163155669229)
            ·
              refine ⟨261553504725436183375961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 697476012601163155669229 261553504725436183375961)
              ·
                refine ⟨196165128544077137531971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261553504725436183375961 196165128544077137531971)
                ·
                  refine ⟨294247692816115706297957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196165128544077137531971 294247692816115706297957)
                  ·
                    refine ⟨55171442403021694930867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 294247692816115706297957 55171442403021694930867)
                    ·
                      rfl

theorem cell23_322338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_322338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322338 prefixEnd_322338 := by exact prefixLift 322338
  have htrace : WordTrace (prefixWord ++ tailWord_322338) baseStart_322338 baseEnd_322338 := by
    simpa [prefixWord, tailWord_322338, baseEnd_322338] using wordTrace_append hprefix tailTrace_322338
  have hstable : (prefixWord ++ tailWord_322338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322338).length < 2 ^ (prefixWord ++ tailWord_322338).sum := by decide
  have hdescent : baseEnd_322338 < baseStart_322338 := by decide
  rcases family_descends (prefixWord ++ tailWord_322338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322354 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2]
def baseStart_322354 : Nat := 118140960795 + 322354 * 2 ^ 59
def prefixEnd_322354 : Nat := 4983230072969 + 3 ^ 40 * 322354 * 2
def baseEnd_322354 : Nat := 165522542899537022192527

theorem tailTrace_322354 : CollatzResearch.WordTrace tailWord_322354 prefixEnd_322354 165522542899537022192527 := by
  unfold tailWord_322354
  simp only [CollatzResearch.WordTrace]
  refine ⟨2939304068543496631315529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7838144182782657683508077 2939304068543496631315529)
  ·
    refine ⟨2204478051407622473486647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2939304068543496631315529 2204478051407622473486647)
    ·
      refine ⟨3306717077111433710229971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2204478051407622473486647 3306717077111433710229971)
      ·
        refine ⟨4960075615667150565344957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3306717077111433710229971 4960075615667150565344957)
        ·
          refine ⟨1860028355875181462004359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4960075615667150565344957 1860028355875181462004359)
          ·
            refine ⟨2790042533812772193006539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1860028355875181462004359 2790042533812772193006539)
            ·
              refine ⟨4185063800719158289509809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2790042533812772193006539 4185063800719158289509809)
              ·
                refine ⟨3138797850539368717132357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4185063800719158289509809 3138797850539368717132357)
                ·
                  refine ⟨588524596976131634462317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3138797850539368717132357 588524596976131634462317)
                  ·
                    refine ⟨220696723866049362923369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 588524596976131634462317 220696723866049362923369)
                    ·
                      refine ⟨165522542899537022192527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 220696723866049362923369 165522542899537022192527)
                      ·
                        rfl

theorem cell23_322354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_322354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322354 prefixEnd_322354 := by exact prefixLift 322354
  have htrace : WordTrace (prefixWord ++ tailWord_322354) baseStart_322354 baseEnd_322354 := by
    simpa [prefixWord, tailWord_322354, baseEnd_322354] using wordTrace_append hprefix tailTrace_322354
  have hstable : (prefixWord ++ tailWord_322354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322354).length < 2 ^ (prefixWord ++ tailWord_322354).sum := by decide
  have hdescent : baseEnd_322354 < baseStart_322354 := by decide
  rcases family_descends (prefixWord ++ tailWord_322354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322377 : List Nat := [1, 2, 1, 1, 2, 6, 1, 2, 1, 6]
def baseStart_322377 : Nat := 118140960795 + 322377 * 2 ^ 59
def prefixEnd_322377 : Nat := 4983230072969 + 3 ^ 40 * 322377 * 2
def baseEnd_322377 : Nat := 55178117651530144068307

theorem tailTrace_322377 : CollatzResearch.WordTrace tailWord_322377 prefixEnd_322377 55178117651530144068307 := by
  unfold tailWord_322377
  simp only [CollatzResearch.WordTrace]
  refine ⟨11758055153090661453349385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7838703435393774302232923 11758055153090661453349385)
  ·
    refine ⟨8818541364817996090012039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11758055153090661453349385 8818541364817996090012039)
    ·
      refine ⟨13227812047226994135018059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8818541364817996090012039 13227812047226994135018059)
      ·
        refine ⟨19841718070840491202527089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13227812047226994135018059 19841718070840491202527089)
        ·
          refine ⟨14881288553130368401895317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19841718070840491202527089 14881288553130368401895317)
          ·
            refine ⟨697560400927986018838843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14881288553130368401895317 697560400927986018838843)
            ·
              refine ⟨1046340601391979028258265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697560400927986018838843 1046340601391979028258265)
              ·
                refine ⟨784755451043984271193699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1046340601391979028258265 784755451043984271193699)
                ·
                  refine ⟨1177133176565976406790549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 784755451043984271193699 1177133176565976406790549)
                  ·
                    refine ⟨55178117651530144068307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1177133176565976406790549 55178117651530144068307)
                    ·
                      rfl

theorem cell23_322377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 6].length) (baseStart_322377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322377 prefixEnd_322377 := by exact prefixLift 322377
  have htrace : WordTrace (prefixWord ++ tailWord_322377) baseStart_322377 baseEnd_322377 := by
    simpa [prefixWord, tailWord_322377, baseEnd_322377] using wordTrace_append hprefix tailTrace_322377
  have hstable : (prefixWord ++ tailWord_322377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322377).length < 2 ^ (prefixWord ++ tailWord_322377).sum := by decide
  have hdescent : baseEnd_322377 < baseStart_322377 := by decide
  rcases family_descends (prefixWord ++ tailWord_322377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322394 : List Nat := [3, 1, 1, 2, 1, 4, 1, 4, 2, 4]
def baseStart_322394 : Nat := 118140960795 + 322394 * 2 ^ 59
def prefixEnd_322394 : Nat := 4983230072969 + 3 ^ 40 * 322394 * 2
def baseEnd_322394 : Nat := 55181027375238955230781

theorem tailTrace_322394 : CollatzResearch.WordTrace tailWord_322394 prefixEnd_322394 55181027375238955230781 := by
  unfold tailWord_322394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2939668798507268339179559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7839116796019382237812157 2939668798507268339179559)
  ·
    refine ⟨4409503197760902508769339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2939668798507268339179559 4409503197760902508769339)
    ·
      refine ⟨6614254796641353763154009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4409503197760902508769339 6614254796641353763154009)
      ·
        refine ⟨4960691097481015322365507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6614254796641353763154009 4960691097481015322365507)
        ·
          refine ⟨7441036646221522983548261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4960691097481015322365507 7441036646221522983548261)
          ·
            refine ⟨1395194371166535559415299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7441036646221522983548261 1395194371166535559415299)
            ·
              refine ⟨2092791556749803339122949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1395194371166535559415299 2092791556749803339122949)
              ·
                refine ⟨392398416890588126085553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2092791556749803339122949 392398416890588126085553)
                ·
                  refine ⟨294298812667941094564165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392398416890588126085553 294298812667941094564165)
                  ·
                    refine ⟨55181027375238955230781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 294298812667941094564165 55181027375238955230781)
                    ·
                      rfl

theorem cell23_322394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_322394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322394 prefixEnd_322394 := by exact prefixLift 322394
  have htrace : WordTrace (prefixWord ++ tailWord_322394) baseStart_322394 baseEnd_322394 := by
    simpa [prefixWord, tailWord_322394, baseEnd_322394] using wordTrace_append hprefix tailTrace_322394
  have hstable : (prefixWord ++ tailWord_322394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322394).length < 2 ^ (prefixWord ++ tailWord_322394).sum := by decide
  have hdescent : baseEnd_322394 < baseStart_322394 := by decide
  rcases family_descends (prefixWord ++ tailWord_322394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322404 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 3, 2, 3]
def baseStart_322404 : Nat := 118140960795 + 322404 * 2 ^ 59
def prefixEnd_322404 : Nat := 4983230072969 + 3 ^ 40 * 322404 * 2
def baseEnd_322404 : Nat := 165548216932261826567297

theorem tailTrace_322404 : CollatzResearch.WordTrace tailWord_322404 prefixEnd_322404 165548216932261826567297 := by
  unfold tailWord_322404
  simp only [CollatzResearch.WordTrace]
  refine ⟨5879519961996422532291133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7839359949328563376388177 5879519961996422532291133)
  ·
    refine ⟨2204819985748658449609175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5879519961996422532291133 2204819985748658449609175)
    ·
      refine ⟨3307229978622987674413763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2204819985748658449609175 3307229978622987674413763)
      ·
        refine ⟨4960844967934481511620645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3307229978622987674413763 4960844967934481511620645)
        ·
          refine ⟨930158431487715283428871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4960844967934481511620645 930158431487715283428871)
          ·
            refine ⟨1395237647231572925143307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930158431487715283428871 1395237647231572925143307)
            ·
              refine ⟨2092856470847359387714961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1395237647231572925143307 2092856470847359387714961)
              ·
                refine ⟨1569642353135519540786221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2092856470847359387714961 1569642353135519540786221)
                ·
                  refine ⟨588615882425819827794833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1569642353135519540786221 588615882425819827794833)
                  ·
                    refine ⟨441461911819364870846125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 588615882425819827794833 441461911819364870846125)
                    ·
                      refine ⟨165548216932261826567297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 441461911819364870846125 165548216932261826567297)
                      ·
                        rfl

theorem cell23_322404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_322404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322404 prefixEnd_322404 := by exact prefixLift 322404
  have htrace : WordTrace (prefixWord ++ tailWord_322404) baseStart_322404 baseEnd_322404 := by
    simpa [prefixWord, tailWord_322404, baseEnd_322404] using wordTrace_append hprefix tailTrace_322404
  have hstable : (prefixWord ++ tailWord_322404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322404).length < 2 ^ (prefixWord ++ tailWord_322404).sum := by decide
  have hdescent : baseEnd_322404 < baseStart_322404 := by decide
  rcases family_descends (prefixWord ++ tailWord_322404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322407 : List Nat := [1, 1, 5, 1, 2, 2, 3, 8]
def baseStart_322407 : Nat := 118140960795 + 322407 * 2 ^ 59
def prefixEnd_322407 : Nat := 4983230072969 + 3 ^ 40 * 322407 * 2
def baseEnd_322407 : Nat := 6131472495341678327029

theorem tailTrace_322407 : CollatzResearch.WordTrace tailWord_322407 prefixEnd_322407 6131472495341678327029 := by
  unfold tailWord_322407
  simp only [CollatzResearch.WordTrace]
  refine ⟨11759149342981976576941475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7839432895321317717960983 11759149342981976576941475)
  ·
    refine ⟨17638724014472964865412213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11759149342981976576941475 17638724014472964865412213)
    ·
      refine ⟨1653630376356840456132395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17638724014472964865412213 1653630376356840456132395)
      ·
        refine ⟨2480445564535260684198593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1653630376356840456132395 2480445564535260684198593)
        ·
          refine ⟨1860334173401445513148945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2480445564535260684198593 1860334173401445513148945)
          ·
            refine ⟨1395250630051084134861709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1860334173401445513148945 1395250630051084134861709)
            ·
              refine ⟨523218986269156550573141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1395250630051084134861709 523218986269156550573141)
              ·
                refine ⟨6131472495341678327029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 523218986269156550573141 6131472495341678327029)
                ·
                  rfl

theorem cell23_322407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 8].length) (baseStart_322407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322407 prefixEnd_322407 := by exact prefixLift 322407
  have htrace : WordTrace (prefixWord ++ tailWord_322407) baseStart_322407 baseEnd_322407 := by
    simpa [prefixWord, tailWord_322407, baseEnd_322407] using wordTrace_append hprefix tailTrace_322407
  have hstable : (prefixWord ++ tailWord_322407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322407).length < 2 ^ (prefixWord ++ tailWord_322407).sum := by decide
  have hdescent : baseEnd_322407 < baseStart_322407 := by decide
  rcases family_descends (prefixWord ++ tailWord_322407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322467 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 2, 6]
def baseStart_322467 : Nat := 118140960795 + 322467 * 2 ^ 59
def prefixEnd_322467 : Nat := 4983230072969 + 3 ^ 40 * 322467 * 2
def baseEnd_322467 : Nat := 55193522071165026693169

theorem tailTrace_322467 : CollatzResearch.WordTrace tailWord_322467 prefixEnd_322467 55193522071165026693169 := by
  unfold tailWord_322467
  simp only [CollatzResearch.WordTrace]
  refine ⟨11761337722764606824125655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7840891815176404549417103 11761337722764606824125655)
  ·
    refine ⟨17642006584146910236188483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11761337722764606824125655 17642006584146910236188483)
    ·
      refine ⟨26463009876220365354282725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17642006584146910236188483 26463009876220365354282725)
      ·
        refine ⟨4961814351791318503928011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26463009876220365354282725 4961814351791318503928011)
        ·
          refine ⟨7442721527686977755892017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4961814351791318503928011 7442721527686977755892017)
          ·
            refine ⟨5582041145765233316919013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7442721527686977755892017 5582041145765233316919013)
            ·
              refine ⟨1046632714830981246922315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5582041145765233316919013 1046632714830981246922315)
              ·
                refine ⟨1569949072246471870383473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1046632714830981246922315 1569949072246471870383473)
                ·
                  refine ⟨1177461804184853902787605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1569949072246471870383473 1177461804184853902787605)
                  ·
                    refine ⟨55193522071165026693169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1177461804184853902787605 55193522071165026693169)
                    ·
                      rfl

theorem cell23_322467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 6].length) (baseStart_322467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322467 prefixEnd_322467 := by exact prefixLift 322467
  have htrace : WordTrace (prefixWord ++ tailWord_322467) baseStart_322467 baseEnd_322467 := by
    simpa [prefixWord, tailWord_322467, baseEnd_322467] using wordTrace_append hprefix tailTrace_322467
  have hstable : (prefixWord ++ tailWord_322467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322467).length < 2 ^ (prefixWord ++ tailWord_322467).sum := by decide
  have hdescent : baseEnd_322467 < baseStart_322467 := by decide
  rcases family_descends (prefixWord ++ tailWord_322467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322468 : List Nat := [2, 3, 1, 2, 1, 2, 5, 1, 2, 1, 3]
def baseStart_322468 : Nat := 118140960795 + 322468 * 2 ^ 59
def prefixEnd_322468 : Nat := 4983230072969 + 3 ^ 40 * 322468 * 2
def baseEnd_322468 : Nat := 165581079694149576167003

theorem tailTrace_322468 : CollatzResearch.WordTrace tailWord_322468 prefixEnd_322468 165581079694149576167003 := by
  unfold tailWord_322468
  simp only [CollatzResearch.WordTrace]
  refine ⟨5880687097880491997456029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7840916130507322663274705 5880687097880491997456029)
  ·
    refine ⟨2205257661705184499046011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5880687097880491997456029 2205257661705184499046011)
    ·
      refine ⟨3307886492557776748569017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2205257661705184499046011 3307886492557776748569017)
      ·
        refine ⟨2480914869418332561426763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3307886492557776748569017 2480914869418332561426763)
        ·
          refine ⟨3721372304127498842140145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2480914869418332561426763 3721372304127498842140145)
          ·
            refine ⟨2791029228095624131605109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3721372304127498842140145 2791029228095624131605109)
            ·
              refine ⟨261658990133964762337979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2791029228095624131605109 261658990133964762337979)
              ·
                refine ⟨392488485200947143506969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261658990133964762337979 392488485200947143506969)
                ·
                  refine ⟨294366363900710357630227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392488485200947143506969 294366363900710357630227)
                  ·
                    refine ⟨441549545851065536445341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 294366363900710357630227 441549545851065536445341)
                    ·
                      refine ⟨165581079694149576167003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 441549545851065536445341 165581079694149576167003)
                      ·
                        rfl

theorem cell23_322468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_322468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322468 prefixEnd_322468 := by exact prefixLift 322468
  have htrace : WordTrace (prefixWord ++ tailWord_322468) baseStart_322468 baseEnd_322468 := by
    simpa [prefixWord, tailWord_322468, baseEnd_322468] using wordTrace_append hprefix tailTrace_322468
  have hstable : (prefixWord ++ tailWord_322468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322468).length < 2 ^ (prefixWord ++ tailWord_322468).sum := by decide
  have hdescent : baseEnd_322468 < baseStart_322468 := by decide
  rcases family_descends (prefixWord ++ tailWord_322468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322487 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 4]
def baseStart_322487 : Nat := 118140960795 + 322487 * 2 ^ 59
def prefixEnd_322487 : Nat := 4983230072969 + 3 ^ 40 * 322487 * 2
def baseEnd_322487 : Nat := 165590835826585001829415

theorem tailTrace_322487 : CollatzResearch.WordTrace tailWord_322487 prefixEnd_322487 165590835826585001829415 := by
  unfold tailWord_322487
  simp only [CollatzResearch.WordTrace]
  refine ⟨11762067182692150239853715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7841378121794766826569143 11762067182692150239853715)
  ·
    refine ⟨17643100774038225359780573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11762067182692150239853715 17643100774038225359780573)
    ·
      refine ⟨6616162790264334509917715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17643100774038225359780573 6616162790264334509917715)
      ·
        refine ⟨9924244185396501764876573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6616162790264334509917715 9924244185396501764876573)
        ·
          refine ⟨3721591569523688161828715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9924244185396501764876573 3721591569523688161828715)
          ·
            refine ⟨5582387354285532242743073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3721591569523688161828715 5582387354285532242743073)
            ·
              refine ⟨4186790515714149182057305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5582387354285532242743073 4186790515714149182057305)
              ·
                refine ⟨3140092886785611886542979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4186790515714149182057305 3140092886785611886542979)
                ·
                  refine ⟨4710139330178417829814469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3140092886785611886542979 4710139330178417829814469)
                  ·
                    refine ⟨883151124408453343090213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4710139330178417829814469 883151124408453343090213)
                    ·
                      refine ⟨165590835826585001829415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 883151124408453343090213 165590835826585001829415)
                      ·
                        rfl

theorem cell23_322487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_322487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322487 prefixEnd_322487 := by exact prefixLift 322487
  have htrace : WordTrace (prefixWord ++ tailWord_322487) baseStart_322487 baseEnd_322487 := by
    simpa [prefixWord, tailWord_322487, baseEnd_322487] using wordTrace_append hprefix tailTrace_322487
  have hstable : (prefixWord ++ tailWord_322487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322487).length < 2 ^ (prefixWord ++ tailWord_322487).sum := by decide
  have hdescent : baseEnd_322487 < baseStart_322487 := by decide
  rcases family_descends (prefixWord ++ tailWord_322487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322494 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_322494 : Nat := 118140960795 + 322494 * 2 ^ 59
def prefixEnd_322494 : Nat := 4983230072969 + 3 ^ 40 * 322494 * 2
def baseEnd_322494 : Nat := 165594430191166474441883

theorem tailTrace_322494 : CollatzResearch.WordTrace tailWord_322494 prefixEnd_322494 165594430191166474441883 := by
  unfold tailWord_322494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1470290311708348804419817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7841548329111193623572357 1470290311708348804419817)
  ·
    refine ⟨1102717733781261603314863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1470290311708348804419817 1102717733781261603314863)
    ·
      refine ⟨1654076600671892404972295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1102717733781261603314863 1654076600671892404972295)
      ·
        refine ⟨2481114901007838607458443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1654076600671892404972295 2481114901007838607458443)
        ·
          refine ⟨3721672351511757911187665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2481114901007838607458443 3721672351511757911187665)
          ·
            refine ⟨2791254263633818433390749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3721672351511757911187665 2791254263633818433390749)
            ·
              refine ⟨1046720348862681912521531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2791254263633818433390749 1046720348862681912521531)
              ·
                refine ⟨1570080523294022868782297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1046720348862681912521531 1570080523294022868782297)
                ·
                  refine ⟨1177560392470517151586723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1570080523294022868782297 1177560392470517151586723)
                  ·
                    refine ⟨1766340588705775727380085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1177560392470517151586723 1766340588705775727380085)
                    ·
                      refine ⟨165594430191166474441883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1766340588705775727380085 165594430191166474441883)
                      ·
                        rfl

theorem cell23_322494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_322494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322494 prefixEnd_322494 := by exact prefixLift 322494
  have htrace : WordTrace (prefixWord ++ tailWord_322494) baseStart_322494 baseEnd_322494 := by
    simpa [prefixWord, tailWord_322494, baseEnd_322494] using wordTrace_append hprefix tailTrace_322494
  have hstable : (prefixWord ++ tailWord_322494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322494).length < 2 ^ (prefixWord ++ tailWord_322494).sum := by decide
  have hdescent : baseEnd_322494 < baseStart_322494 := by decide
  rcases family_descends (prefixWord ++ tailWord_322494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322508 : List Nat := [2, 2, 1, 4, 1, 1, 2, 4, 2, 2, 2]
def baseStart_322508 : Nat := 118140960795 + 322508 * 2 ^ 59
def prefixEnd_322508 : Nat := 4983230072969 + 3 ^ 40 * 322508 * 2
def baseEnd_322508 : Nat := 165601618920329419666819

theorem tailTrace_322508 : CollatzResearch.WordTrace tailWord_322508 prefixEnd_322508 165601618920329419666819 := by
  unfold tailWord_322508
  simp only [CollatzResearch.WordTrace]
  refine ⟨5881416557808035413184089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7841888743744047217578785 5881416557808035413184089)
  ·
    refine ⟨4411062418356026559888067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5881416557808035413184089 4411062418356026559888067)
    ·
      refine ⟨6616593627534039839832101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4411062418356026559888067 6616593627534039839832101)
      ·
        refine ⟨1240611305162632469968519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6616593627534039839832101 1240611305162632469968519)
        ·
          refine ⟨1860916957743948704952779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1240611305162632469968519 1860916957743948704952779)
          ·
            refine ⟨2791375436615923057429169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1860916957743948704952779 2791375436615923057429169)
            ·
              refine ⟨2093531577461942293071877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2791375436615923057429169 2093531577461942293071877)
              ·
                refine ⟨392537170774114179950977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2093531577461942293071877 392537170774114179950977)
                ·
                  refine ⟨294402878080585634963233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392537170774114179950977 294402878080585634963233)
                  ·
                    refine ⟨220802158560439226222425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 294402878080585634963233 220802158560439226222425)
                    ·
                      refine ⟨165601618920329419666819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 220802158560439226222425 165601618920329419666819)
                      ·
                        rfl

theorem cell23_322508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_322508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322508 prefixEnd_322508 := by exact prefixLift 322508
  have htrace : WordTrace (prefixWord ++ tailWord_322508) baseStart_322508 baseEnd_322508 := by
    simpa [prefixWord, tailWord_322508, baseEnd_322508] using wordTrace_append hprefix tailTrace_322508
  have hstable : (prefixWord ++ tailWord_322508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322508).length < 2 ^ (prefixWord ++ tailWord_322508).sum := by decide
  have hdescent : baseEnd_322508 < baseStart_322508 := by decide
  rcases family_descends (prefixWord ++ tailWord_322508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322525 : List Nat := [1, 4, 3, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_322525 : Nat := 118140960795 + 322525 * 2 ^ 59
def prefixEnd_322525 : Nat := 4983230072969 + 3 ^ 40 * 322525 * 2
def baseEnd_322525 : Nat := 165610348091455853154241

theorem tailTrace_322525 : CollatzResearch.WordTrace tailWord_322525 prefixEnd_322525 165610348091455853154241 := by
  unfold tailWord_322525
  simp only [CollatzResearch.WordTrace]
  refine ⟨11763453156554482729737029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7842302104369655153158019 11763453156554482729737029)
  ·
    refine ⟨2205647466853965511825693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11763453156554482729737029 2205647466853965511825693)
    ·
      refine ⟨827117800070237066934635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2205647466853965511825693 827117800070237066934635)
      ·
        refine ⟨1240676700105355600401953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 827117800070237066934635 1240676700105355600401953)
        ·
          refine ⟨930507525079016700301465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1240676700105355600401953 930507525079016700301465)
          ·
            refine ⟨697880643809262525226099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 930507525079016700301465 697880643809262525226099)
            ·
              refine ⟨1046820965713893787839149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697880643809262525226099 1046820965713893787839149)
              ·
                refine ⟨392557862142710170439681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1046820965713893787839149 392557862142710170439681)
                ·
                  refine ⟨294418396607032627829761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392557862142710170439681 294418396607032627829761)
                  ·
                    refine ⟨220813797455274470872321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 294418396607032627829761 220813797455274470872321)
                    ·
                      refine ⟨165610348091455853154241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 220813797455274470872321 165610348091455853154241)
                      ·
                        rfl

theorem cell23_322525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_322525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322525 prefixEnd_322525 := by exact prefixLift 322525
  have htrace : WordTrace (prefixWord ++ tailWord_322525) baseStart_322525 baseEnd_322525 := by
    simpa [prefixWord, tailWord_322525, baseEnd_322525] using wordTrace_append hprefix tailTrace_322525
  have hstable : (prefixWord ++ tailWord_322525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322525).length < 2 ^ (prefixWord ++ tailWord_322525).sum := by decide
  have hdescent : baseEnd_322525 < baseStart_322525 := by decide
  rcases family_descends (prefixWord ++ tailWord_322525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322581 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 1, 6, 2]
def baseStart_322581 : Nat := 118140960795 + 322581 * 2 ^ 59
def prefixEnd_322581 : Nat := 4983230072969 + 3 ^ 40 * 322581 * 2
def baseEnd_322581 : Nat := 165639103008107634053983

theorem tailTrace_322581 : CollatzResearch.WordTrace tailWord_322581 prefixEnd_322581 165639103008107634053983 := by
  unfold tailWord_322581
  simp only [CollatzResearch.WordTrace]
  refine ⟨11765495644351604293775597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7843663762901069529183731 11765495644351604293775597)
  ·
    refine ⟨4412060866631851610165849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11765495644351604293775597 4412060866631851610165849)
    ·
      refine ⟨3309045649973888707624387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4412060866631851610165849 3309045649973888707624387)
      ·
        refine ⟨4963568474960833061436581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3309045649973888707624387 4963568474960833061436581)
        ·
          refine ⟨930669089055156199019359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4963568474960833061436581 930669089055156199019359)
          ·
            refine ⟨1396003633582734298529039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930669089055156199019359 1396003633582734298529039)
            ·
              refine ⟨2094005450374101447793559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1396003633582734298529039 2094005450374101447793559)
              ·
                refine ⟨3141008175561152171690339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094005450374101447793559 3141008175561152171690339)
                ·
                  refine ⟨4711512263341728257535509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3141008175561152171690339 4711512263341728257535509)
                  ·
                    refine ⟨220852137344143512071977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4711512263341728257535509 220852137344143512071977)
                    ·
                      refine ⟨165639103008107634053983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 220852137344143512071977 165639103008107634053983)
                      ·
                        rfl

theorem cell23_322581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_322581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322581 prefixEnd_322581 := by exact prefixLift 322581
  have htrace : WordTrace (prefixWord ++ tailWord_322581) baseStart_322581 baseEnd_322581 := by
    simpa [prefixWord, tailWord_322581, baseEnd_322581] using wordTrace_append hprefix tailTrace_322581
  have hstable : (prefixWord ++ tailWord_322581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322581).length < 2 ^ (prefixWord ++ tailWord_322581).sum := by decide
  have hdescent : baseEnd_322581 < baseStart_322581 := by decide
  rcases family_descends (prefixWord ++ tailWord_322581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322591 : List Nat := [1, 1, 2, 4, 1, 4, 1, 2, 3, 4]
def baseStart_322591 : Nat := 118140960795 + 322591 * 2 ^ 59
def prefixEnd_322591 : Nat := 4983230072969 + 3 ^ 40 * 322591 * 2
def baseEnd_322591 : Nat := 55214745938217531642979

theorem tailTrace_322591 : CollatzResearch.WordTrace tailWord_322591 prefixEnd_322591 55214745938217531642979 := by
  unfold tailWord_322591
  simp only [CollatzResearch.WordTrace]
  refine ⟨11765860374315376001639627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7843906916210250667759751 11765860374315376001639627)
  ·
    refine ⟨17648790561473064002459441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11765860374315376001639627 17648790561473064002459441)
    ·
      refine ⟨13236592921104798001844581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17648790561473064002459441 13236592921104798001844581)
      ·
        refine ⟨2481861172707149625345859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13236592921104798001844581 2481861172707149625345859)
        ·
          refine ⟨3722791759060724438018789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2481861172707149625345859 3722791759060724438018789)
          ·
            refine ⟨698023454823885832128523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3722791759060724438018789 698023454823885832128523)
            ·
              refine ⟨1047035182235828748192785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698023454823885832128523 1047035182235828748192785)
              ·
                refine ⟨785276386676871561144589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1047035182235828748192785 785276386676871561144589)
                ·
                  refine ⟨294478645003826835429221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 785276386676871561144589 294478645003826835429221)
                  ·
                    refine ⟨55214745938217531642979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 294478645003826835429221 55214745938217531642979)
                    ·
                      rfl

theorem cell23_322591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 4].length) (baseStart_322591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322591 prefixEnd_322591 := by exact prefixLift 322591
  have htrace : WordTrace (prefixWord ++ tailWord_322591) baseStart_322591 baseEnd_322591 := by
    simpa [prefixWord, tailWord_322591, baseEnd_322591] using wordTrace_append hprefix tailTrace_322591
  have hstable : (prefixWord ++ tailWord_322591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322591).length < 2 ^ (prefixWord ++ tailWord_322591).sum := by decide
  have hdescent : baseEnd_322591 < baseStart_322591 := by decide
  rcases family_descends (prefixWord ++ tailWord_322591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322608 : List Nat := [2, 1, 1, 1, 2, 4, 4, 3, 1, 4]
def baseStart_322608 : Nat := 118140960795 + 322608 * 2 ^ 59
def prefixEnd_322608 : Nat := 4983230072969 + 3 ^ 40 * 322608 * 2
def baseEnd_322608 : Nat := 55217655661926342805453

theorem tailTrace_322608 : CollatzResearch.WordTrace tailWord_322608 prefixEnd_322608 55217655661926342805453 := by
  unfold tailWord_322608
  simp only [CollatzResearch.WordTrace]
  refine ⟨5883240207626893952504239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7844320276835858603338985 5883240207626893952504239)
  ·
    refine ⟨8824860311440340928756359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5883240207626893952504239 8824860311440340928756359)
    ·
      refine ⟨13237290467160511393134539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8824860311440340928756359 13237290467160511393134539)
      ·
        refine ⟨19855935700740767089701809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13237290467160511393134539 19855935700740767089701809)
        ·
          refine ⟨14891951775555575317276357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19855935700740767089701809 14891951775555575317276357)
          ·
            refine ⟨2792240957916670371989317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14891951775555575317276357 2792240957916670371989317)
            ·
              refine ⟨523545179609375694747997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2792240957916670371989317 523545179609375694747997)
              ·
                refine ⟨196329442353515885530499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 523545179609375694747997 196329442353515885530499)
                ·
                  refine ⟨294494163530273828295749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196329442353515885530499 294494163530273828295749)
                  ·
                    refine ⟨55217655661926342805453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 294494163530273828295749 55217655661926342805453)
                    ·
                      rfl

theorem cell23_322608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 1, 4].length) (baseStart_322608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322608 prefixEnd_322608 := by exact prefixLift 322608
  have htrace : WordTrace (prefixWord ++ tailWord_322608) baseStart_322608 baseEnd_322608 := by
    simpa [prefixWord, tailWord_322608, baseEnd_322608] using wordTrace_append hprefix tailTrace_322608
  have hstable : (prefixWord ++ tailWord_322608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322608).length < 2 ^ (prefixWord ++ tailWord_322608).sum := by decide
  have hdescent : baseEnd_322608 < baseStart_322608 := by decide
  rcases family_descends (prefixWord ++ tailWord_322608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322621 : List Nat := [1, 4, 1, 3, 1, 2, 3, 2, 6]
def baseStart_322621 : Nat := 118140960795 + 322621 * 2 ^ 59
def prefixEnd_322621 : Nat := 4983230072969 + 3 ^ 40 * 322621 * 2
def baseEnd_322621 : Nat := 18406626914920830839311

theorem tailTrace_322621 : CollatzResearch.WordTrace tailWord_322621 prefixEnd_322621 18406626914920830839311 := by
  unfold tailWord_322621
  simp only [CollatzResearch.WordTrace]
  refine ⟨11766954564206691125231717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7844636376137794083487811 11766954564206691125231717)
  ·
    refine ⟨2206303980788754585980947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11766954564206691125231717 2206303980788754585980947)
    ·
      refine ⟨3309455971183131878971421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2206303980788754585980947 3309455971183131878971421)
      ·
        refine ⟨1241045989193674454614283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3309455971183131878971421 1241045989193674454614283)
        ·
          refine ⟨1861568983790511681921425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1241045989193674454614283 1861568983790511681921425)
          ·
            refine ⟨1396176737842883761441069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1861568983790511681921425 1396176737842883761441069)
            ·
              refine ⟨523566276691081410540401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1396176737842883761441069 523566276691081410540401)
              ·
                refine ⟨392674707518311057905301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 523566276691081410540401 392674707518311057905301)
                ·
                  refine ⟨18406626914920830839311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 392674707518311057905301 18406626914920830839311)
                  ·
                    rfl

theorem cell23_322621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_322621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322621 prefixEnd_322621 := by exact prefixLift 322621
  have htrace : WordTrace (prefixWord ++ tailWord_322621) baseStart_322621 baseEnd_322621 := by
    simpa [prefixWord, tailWord_322621, baseEnd_322621] using wordTrace_append hprefix tailTrace_322621
  have hstable : (prefixWord ++ tailWord_322621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322621).length < 2 ^ (prefixWord ++ tailWord_322621).sum := by decide
  have hdescent : baseEnd_322621 < baseStart_322621 := by decide
  rcases family_descends (prefixWord ++ tailWord_322621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322634 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 5, 5]
def baseStart_322634 : Nat := 118140960795 + 322634 * 2 ^ 59
def prefixEnd_322634 : Nat := 4983230072969 + 3 ^ 40 * 322634 * 2
def baseEnd_322634 : Nat := 55222105827598642230413

theorem tailTrace_322634 : CollatzResearch.WordTrace tailWord_322634 prefixEnd_322634 55222105827598642230413 := by
  unfold tailWord_322634
  simp only [CollatzResearch.WordTrace]
  refine ⟨2941857178289898586363739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7844952475439729563636637 2941857178289898586363739)
  ·
    refine ⟨4412785767434847879545609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2941857178289898586363739 4412785767434847879545609)
    ·
      refine ⟨3309589325576135909659207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4412785767434847879545609 3309589325576135909659207)
      ·
        refine ⟨4964383988364203864488811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3309589325576135909659207 4964383988364203864488811)
        ·
          refine ⟨7446575982546305796733217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4964383988364203864488811 7446575982546305796733217)
          ·
            refine ⟨5584931986909729347549913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7446575982546305796733217 5584931986909729347549913)
            ·
              refine ⟨4188698990182297010662435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5584931986909729347549913 4188698990182297010662435)
              ·
                refine ⟨6283048485273445515993653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4188698990182297010662435 6283048485273445515993653)
                ·
                  refine ⟨589035795494385517124405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6283048485273445515993653 589035795494385517124405)
                  ·
                    refine ⟨55222105827598642230413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 589035795494385517124405 55222105827598642230413)
                    ·
                      rfl

theorem cell23_322634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_322634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322634 prefixEnd_322634 := by exact prefixLift 322634
  have htrace : WordTrace (prefixWord ++ tailWord_322634) baseStart_322634 baseEnd_322634 := by
    simpa [prefixWord, tailWord_322634, baseEnd_322634] using wordTrace_append hprefix tailTrace_322634
  have hstable : (prefixWord ++ tailWord_322634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322634).length < 2 ^ (prefixWord ++ tailWord_322634).sum := by decide
  have hdescent : baseEnd_322634 < baseStart_322634 := by decide
  rcases family_descends (prefixWord ++ tailWord_322634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322641 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 1, 5, 2]
def baseStart_322641 : Nat := 118140960795 + 322641 * 2 ^ 59
def prefixEnd_322641 : Nat := 4983230072969 + 3 ^ 40 * 322641 * 2
def baseEnd_322641 : Nat := 165669911847377399303707

theorem tailTrace_322641 : CollatzResearch.WordTrace tailWord_322641 prefixEnd_322641 165669911847377399303707 := by
  unfold tailWord_322641
  simp only [CollatzResearch.WordTrace]
  refine ⟨11767684024134234540959777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7845122682756156360639851 11767684024134234540959777)
  ·
    refine ⟨8825763018100675905719833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11767684024134234540959777 8825763018100675905719833)
    ·
      refine ⟨6619322263575506929289875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8825763018100675905719833 6619322263575506929289875)
      ·
        refine ⟨9928983395363260393934813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6619322263575506929289875 9928983395363260393934813)
        ·
          refine ⟨3723368773261222647725555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9928983395363260393934813 3723368773261222647725555)
          ·
            refine ⟨5585053159891833971588333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3723368773261222647725555 5585053159891833971588333)
            ·
              refine ⟨2094394934959437739345625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5585053159891833971588333 2094394934959437739345625)
              ·
                refine ⟨1570796201219578304509219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2094394934959437739345625 1570796201219578304509219)
                ·
                  refine ⟨2356194301829367456763829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1570796201219578304509219 2356194301829367456763829)
                  ·
                    refine ⟨220893215796503199071609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2356194301829367456763829 220893215796503199071609)
                    ·
                      refine ⟨165669911847377399303707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 220893215796503199071609 165669911847377399303707)
                      ·
                        rfl

theorem cell23_322641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 5, 2].length) (baseStart_322641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322641 prefixEnd_322641 := by exact prefixLift 322641
  have htrace : WordTrace (prefixWord ++ tailWord_322641) baseStart_322641 baseEnd_322641 := by
    simpa [prefixWord, tailWord_322641, baseEnd_322641] using wordTrace_append hprefix tailTrace_322641
  have hstable : (prefixWord ++ tailWord_322641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322641).length < 2 ^ (prefixWord ++ tailWord_322641).sum := by decide
  have hdescent : baseEnd_322641 < baseStart_322641 := by decide
  rcases family_descends (prefixWord ++ tailWord_322641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322644 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_322644 : Nat := 118140960795 + 322644 * 2 ^ 59
def prefixEnd_322644 : Nat := 4983230072969 + 3 ^ 40 * 322644 * 2
def baseEnd_322644 : Nat := 165671452289340887566193

theorem tailTrace_322644 : CollatzResearch.WordTrace tailWord_322644 prefixEnd_322644 165671452289340887566193 := by
  unfold tailWord_322644
  simp only [CollatzResearch.WordTrace]
  refine ⟨5883896721561683026659493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7845195628748910702212657 5883896721561683026659493)
  ·
    refine ⟨1103230635292815567498655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5883896721561683026659493 1103230635292815567498655)
    ·
      refine ⟨1654845952939223351247983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1103230635292815567498655 1654845952939223351247983)
      ·
        refine ⟨2482268929408835026871975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1654845952939223351247983 2482268929408835026871975)
        ·
          refine ⟨3723403394113252540307963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2482268929408835026871975 3723403394113252540307963)
          ·
            refine ⟨5585105091169878810461945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3723403394113252540307963 5585105091169878810461945)
            ·
              refine ⟨4188828818377409107846459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5585105091169878810461945 4188828818377409107846459)
              ·
                refine ⟨6283243227566113661769689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4188828818377409107846459 6283243227566113661769689)
                ·
                  refine ⟨4712432420674585246327267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6283243227566113661769689 4712432420674585246327267)
                  ·
                    refine ⟨7068648631011877869490901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4712432420674585246327267 7068648631011877869490901)
                    ·
                      refine ⟨165671452289340887566193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7068648631011877869490901 165671452289340887566193)
                      ·
                        rfl

theorem cell23_322644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_322644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322644 prefixEnd_322644 := by exact prefixLift 322644
  have htrace : WordTrace (prefixWord ++ tailWord_322644) baseStart_322644 baseEnd_322644 := by
    simpa [prefixWord, tailWord_322644, baseEnd_322644] using wordTrace_append hprefix tailTrace_322644
  have hstable : (prefixWord ++ tailWord_322644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322644).length < 2 ^ (prefixWord ++ tailWord_322644).sum := by decide
  have hdescent : baseEnd_322644 < baseStart_322644 := by decide
  rcases family_descends (prefixWord ++ tailWord_322644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322665 : List Nat := [1, 2, 1, 1, 1, 6, 3, 3, 1, 1, 3]
def baseStart_322665 : Nat := 118140960795 + 322665 * 2 ^ 59
def prefixEnd_322665 : Nat := 4983230072969 + 3 ^ 40 * 322665 * 2
def baseEnd_322665 : Nat := 165682235383085305403597

theorem tailTrace_322665 : CollatzResearch.WordTrace tailWord_322665 prefixEnd_322665 165682235383085305403597 := by
  unfold tailWord_322665
  simp only [CollatzResearch.WordTrace]
  refine ⟨11768559376047286639833449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7845706250698191093222299 11768559376047286639833449)
  ·
    refine ⟨8826419532035464979875087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11768559376047286639833449 8826419532035464979875087)
    ·
      refine ⟨13239629298053197469812631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8826419532035464979875087 13239629298053197469812631)
      ·
        refine ⟨19859443947079796204718947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13239629298053197469812631 19859443947079796204718947)
        ·
          refine ⟨29789165920619694307078421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19859443947079796204718947 29789165920619694307078421)
          ·
            refine ⟨1396367152529048170644301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29789165920619694307078421 1396367152529048170644301)
            ·
              refine ⟨523637682198393063991613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1396367152529048170644301 523637682198393063991613)
              ·
                refine ⟨196364130824397398996855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 523637682198393063991613 196364130824397398996855)
                ·
                  refine ⟨294546196236596098495283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196364130824397398996855 294546196236596098495283)
                  ·
                    refine ⟨441819294354894147742925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 294546196236596098495283 441819294354894147742925)
                    ·
                      refine ⟨165682235383085305403597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 441819294354894147742925 165682235383085305403597)
                      ·
                        rfl

theorem cell23_322665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 1, 1, 3].length) (baseStart_322665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322665 prefixEnd_322665 := by exact prefixLift 322665
  have htrace : WordTrace (prefixWord ++ tailWord_322665) baseStart_322665 baseEnd_322665 := by
    simpa [prefixWord, tailWord_322665, baseEnd_322665] using wordTrace_append hprefix tailTrace_322665
  have hstable : (prefixWord ++ tailWord_322665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322665).length < 2 ^ (prefixWord ++ tailWord_322665).sum := by decide
  have hdescent : baseEnd_322665 < baseStart_322665 := by decide
  rcases family_descends (prefixWord ++ tailWord_322665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322671 : List Nat := [1, 1, 2, 1, 3, 3, 1, 5, 1, 1, 4]
def baseStart_322671 : Nat := 118140960795 + 322671 * 2 ^ 59
def prefixEnd_322671 : Nat := 4983230072969 + 3 ^ 40 * 322671 * 2
def baseEnd_322671 : Nat := 165685316267012281928569

theorem tailTrace_322671 : CollatzResearch.WordTrace tailWord_322671 prefixEnd_322671 165685316267012281928569 := by
  unfold tailWord_322671
  simp only [CollatzResearch.WordTrace]
  refine ⟨11768778214025549664551867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7845852142683699776367911 11768778214025549664551867)
  ·
    refine ⟨17653167321038324496827801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11768778214025549664551867 17653167321038324496827801)
    ·
      refine ⟨13239875490778743372620851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17653167321038324496827801 13239875490778743372620851)
      ·
        refine ⟨19859813236168115058931277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13239875490778743372620851 19859813236168115058931277)
        ·
          refine ⟨7447429963563043147099229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19859813236168115058931277 7447429963563043147099229)
          ·
            refine ⟨2792786236336141180162211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7447429963563043147099229 2792786236336141180162211)
            ·
              refine ⟨4189179354504211770243317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2792786236336141180162211 4189179354504211770243317)
              ·
                refine ⟨392735564484769853460311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4189179354504211770243317 392735564484769853460311)
                ·
                  refine ⟨589103346727154780190467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392735564484769853460311 589103346727154780190467)
                  ·
                    refine ⟨883655020090732170285701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 589103346727154780190467 883655020090732170285701)
                    ·
                      refine ⟨165685316267012281928569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 883655020090732170285701 165685316267012281928569)
                      ·
                        rfl

theorem cell23_322671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 1, 4].length) (baseStart_322671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322671 prefixEnd_322671 := by exact prefixLift 322671
  have htrace : WordTrace (prefixWord ++ tailWord_322671) baseStart_322671 baseEnd_322671 := by
    simpa [prefixWord, tailWord_322671, baseEnd_322671] using wordTrace_append hprefix tailTrace_322671
  have hstable : (prefixWord ++ tailWord_322671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322671).length < 2 ^ (prefixWord ++ tailWord_322671).sum := by decide
  have hdescent : baseEnd_322671 < baseStart_322671 := by decide
  rcases family_descends (prefixWord ++ tailWord_322671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322684 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_322684 : Nat := 118140960795 + 322684 * 2 ^ 59
def prefixEnd_322684 : Nat := 4983230072969 + 3 ^ 40 * 322684 * 2
def baseEnd_322684 : Nat := 165691991515520731066009

theorem tailTrace_322684 : CollatzResearch.WordTrace tailWord_322684 prefixEnd_322684 165691991515520731066009 := by
  unfold tailWord_322684
  simp only [CollatzResearch.WordTrace]
  refine ⟨5884626181489226442387553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7846168241985635256516737 5884626181489226442387553)
  ·
    refine ⟨4413469636116919831790665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5884626181489226442387553 4413469636116919831790665)
    ·
      refine ⟨3310102227087689873842999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4413469636116919831790665 3310102227087689873842999)
      ·
        refine ⟨4965153340631534810764499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3310102227087689873842999 4965153340631534810764499)
        ·
          refine ⟨7447730010947302216146749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4965153340631534810764499 7447730010947302216146749)
          ·
            refine ⟨2792898754105238331055031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7447730010947302216146749 2792898754105238331055031)
            ·
              refine ⟨4189348131157857496582547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2792898754105238331055031 4189348131157857496582547)
              ·
                refine ⟨6284022196736786244873821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4189348131157857496582547 6284022196736786244873821)
                ·
                  refine ⟨2356508323776294841827683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6284022196736786244873821 2356508323776294841827683)
                  ·
                    refine ⟨3534762485664442262741525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2356508323776294841827683 3534762485664442262741525)
                    ·
                      refine ⟨165691991515520731066009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3534762485664442262741525 165691991515520731066009)
                      ·
                        rfl

theorem cell23_322684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_322684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322684 prefixEnd_322684 := by exact prefixLift 322684
  have htrace : WordTrace (prefixWord ++ tailWord_322684) baseStart_322684 baseEnd_322684 := by
    simpa [prefixWord, tailWord_322684, baseEnd_322684] using wordTrace_append hprefix tailTrace_322684
  have hstable : (prefixWord ++ tailWord_322684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322684).length < 2 ^ (prefixWord ++ tailWord_322684).sum := by decide
  have hdescent : baseEnd_322684 < baseStart_322684 := by decide
  rcases family_descends (prefixWord ++ tailWord_322684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322691 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 3]
def baseStart_322691 : Nat := 118140960795 + 322691 * 2 ^ 59
def prefixEnd_322691 : Nat := 4983230072969 + 3 ^ 40 * 322691 * 2
def baseEnd_322691 : Nat := 165695585880102203678477

theorem tailTrace_322691 : CollatzResearch.WordTrace tailWord_322691 prefixEnd_322691 165695585880102203678477 := by
  unfold tailWord_322691
  simp only [CollatzResearch.WordTrace]
  refine ⟨11769507673953093080279927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7846338449302062053519951 11769507673953093080279927)
  ·
    refine ⟨17654261510929639620419891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11769507673953093080279927 17654261510929639620419891)
    ·
      refine ⟨26481392266394459430629837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17654261510929639620419891 26481392266394459430629837)
      ·
        refine ⟨9930522099897922286486189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26481392266394459430629837 9930522099897922286486189)
        ·
          refine ⟨3723945787461720857432321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9930522099897922286486189 3723945787461720857432321)
          ·
            refine ⟨2792959340596290643074241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3723945787461720857432321 2792959340596290643074241)
            ·
              refine ⟨2094719505447217982305681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2792959340596290643074241 2094719505447217982305681)
              ·
                refine ⟨1571039629085413486729261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2094719505447217982305681 1571039629085413486729261)
                ·
                  refine ⟨589139860907030057523473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1571039629085413486729261 589139860907030057523473)
                  ·
                    refine ⟨441854895680272543142605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 589139860907030057523473 441854895680272543142605)
                    ·
                      refine ⟨165695585880102203678477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 441854895680272543142605 165695585880102203678477)
                      ·
                        rfl

theorem cell23_322691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_322691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322691 prefixEnd_322691 := by exact prefixLift 322691
  have htrace : WordTrace (prefixWord ++ tailWord_322691) baseStart_322691 baseEnd_322691 := by
    simpa [prefixWord, tailWord_322691, baseEnd_322691] using wordTrace_append hprefix tailTrace_322691
  have hstable : (prefixWord ++ tailWord_322691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322691).length < 2 ^ (prefixWord ++ tailWord_322691).sum := by decide
  have hdescent : baseEnd_322691 < baseStart_322691 := by decide
  rcases family_descends (prefixWord ++ tailWord_322691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322698 : List Nat := [3, 1, 2, 3, 1, 1, 3, 3, 2, 4]
def baseStart_322698 : Nat := 118140960795 + 322698 * 2 ^ 59
def prefixEnd_322698 : Nat := 4983230072969 + 3 ^ 40 * 322698 * 2
def baseEnd_322698 : Nat := 55233060081561225430315

theorem tailTrace_322698 : CollatzResearch.WordTrace tailWord_322698 prefixEnd_322698 55233060081561225430315 := by
  unfold tailWord_322698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2942440746231933318946187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7846508656618488850523165 2942440746231933318946187)
  ·
    refine ⟨4413661119347899978419281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2942440746231933318946187 4413661119347899978419281)
    ·
      refine ⟨3310245839510924983814461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4413661119347899978419281 3310245839510924983814461)
      ·
        refine ⟨1241342189816596868930423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3310245839510924983814461 1241342189816596868930423)
        ·
          refine ⟨1862013284724895303395635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1241342189816596868930423 1862013284724895303395635)
          ·
            refine ⟨2793019927087342955093453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1862013284724895303395635 2793019927087342955093453)
            ·
              refine ⟨1047382472657753608160045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2793019927087342955093453 1047382472657753608160045)
              ·
                refine ⟨392768427246657603060017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1047382472657753608160045 392768427246657603060017)
                ·
                  refine ⟨294576320434993202295013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392768427246657603060017 294576320434993202295013)
                  ·
                    refine ⟨55233060081561225430315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 294576320434993202295013 55233060081561225430315)
                    ·
                      rfl

theorem cell23_322698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_322698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322698 prefixEnd_322698 := by exact prefixLift 322698
  have htrace : WordTrace (prefixWord ++ tailWord_322698) baseStart_322698 baseEnd_322698 := by
    simpa [prefixWord, tailWord_322698, baseEnd_322698] using wordTrace_append hprefix tailTrace_322698
  have hstable : (prefixWord ++ tailWord_322698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322698).length < 2 ^ (prefixWord ++ tailWord_322698).sum := by decide
  have hdescent : baseEnd_322698 < baseStart_322698 := by decide
  rcases family_descends (prefixWord ++ tailWord_322698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322718 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_322718 : Nat := 118140960795 + 322718 * 2 ^ 59
def prefixEnd_322718 : Nat := 4983230072969 + 3 ^ 40 * 322718 * 2
def baseEnd_322718 : Nat := 165709449857773598040853

theorem tailTrace_322718 : CollatzResearch.WordTrace tailWord_322718 prefixEnd_322718 165709449857773598040853 := by
  unfold tailWord_322718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1471311555606909586439101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7846994963236851127675205 1471311555606909586439101)
  ·
    refine ⟨551741833352591094914663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1471311555606909586439101 551741833352591094914663)
    ·
      refine ⟨827612750028886642371995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 551741833352591094914663 827612750028886642371995)
      ·
        refine ⟨1241419125043329963557993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 827612750028886642371995 1241419125043329963557993)
        ·
          refine ⟨931064343782497472668495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1241419125043329963557993 931064343782497472668495)
          ·
            refine ⟨1396596515673746209002743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931064343782497472668495 1396596515673746209002743)
            ·
              refine ⟨2094894773510619313504115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1396596515673746209002743 2094894773510619313504115)
              ·
                refine ⟨3142342160265928970256173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094894773510619313504115 3142342160265928970256173)
                ·
                  refine ⟨1178378310099723363846065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3142342160265928970256173 1178378310099723363846065)
                  ·
                    refine ⟨883783732574792522884549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1178378310099723363846065 883783732574792522884549)
                    ·
                      refine ⟨165709449857773598040853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 883783732574792522884549 165709449857773598040853)
                      ·
                        rfl

theorem cell23_322718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_322718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322718 prefixEnd_322718 := by exact prefixLift 322718
  have htrace : WordTrace (prefixWord ++ tailWord_322718) baseStart_322718 baseEnd_322718 := by
    simpa [prefixWord, tailWord_322718, baseEnd_322718] using wordTrace_append hprefix tailTrace_322718
  have hstable : (prefixWord ++ tailWord_322718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322718).length < 2 ^ (prefixWord ++ tailWord_322718).sum := by decide
  have hdescent : baseEnd_322718 < baseStart_322718 := by decide
  rcases family_descends (prefixWord ++ tailWord_322718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322722 : List Nat := [3, 3, 1, 3, 2, 1, 3, 1, 1, 1, 4]
def baseStart_322722 : Nat := 118140960795 + 322722 * 2 ^ 59
def prefixEnd_322722 : Nat := 4983230072969 + 3 ^ 40 * 322722 * 2
def baseEnd_322722 : Nat := 165711503780391582390835

theorem tailTrace_322722 : CollatzResearch.WordTrace tailWord_322722 prefixEnd_322722 165711503780391582390835 := by
  unfold tailWord_322722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2942659584210196343664605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7847092224560523583105613 2942659584210196343664605)
  ·
    refine ⟨1103497344078823628874227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2942659584210196343664605 1103497344078823628874227)
    ·
      refine ⟨1655246016118235443311341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1103497344078823628874227 1655246016118235443311341)
      ·
        refine ⟨620717256044338291241753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1655246016118235443311341 620717256044338291241753)
        ·
          refine ⟨465537942033253718431315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 620717256044338291241753 465537942033253718431315)
          ·
            refine ⟨698306913049880577646973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465537942033253718431315 698306913049880577646973)
            ·
              refine ⟨261865092393705216617615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 698306913049880577646973 261865092393705216617615)
              ·
                refine ⟨392797638590557824926423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261865092393705216617615 392797638590557824926423)
                ·
                  refine ⟨589196457885836737389635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392797638590557824926423 589196457885836737389635)
                  ·
                    refine ⟨883794686828755106084453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 589196457885836737389635 883794686828755106084453)
                    ·
                      refine ⟨165711503780391582390835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 883794686828755106084453 165711503780391582390835)
                      ·
                        rfl

theorem cell23_322722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_322722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322722 prefixEnd_322722 := by exact prefixLift 322722
  have htrace : WordTrace (prefixWord ++ tailWord_322722) baseStart_322722 baseEnd_322722 := by
    simpa [prefixWord, tailWord_322722, baseEnd_322722] using wordTrace_append hprefix tailTrace_322722
  have hstable : (prefixWord ++ tailWord_322722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322722).length < 2 ^ (prefixWord ++ tailWord_322722).sum := by decide
  have hdescent : baseEnd_322722 < baseStart_322722 := by decide
  rcases family_descends (prefixWord ++ tailWord_322722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322725 : List Nat := [1, 3, 1, 2, 1, 5, 3, 1, 1, 2, 3]
def baseStart_322725 : Nat := 118140960795 + 322725 * 2 ^ 59
def prefixEnd_322725 : Nat := 4983230072969 + 3 ^ 40 * 322725 * 2
def baseEnd_322725 : Nat := 165713044222355070653321

theorem tailTrace_322725 : CollatzResearch.WordTrace tailWord_322725 prefixEnd_322725 165713044222355070653321 := by
  unfold tailWord_322725
  simp only [CollatzResearch.WordTrace]
  refine ⟨11770747755829916887017629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7847165170553277924678419 11770747755829916887017629)
  ·
    refine ⟨4414030408436218832631611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11770747755829916887017629 4414030408436218832631611)
    ·
      refine ⟨6621045612654328248947417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4414030408436218832631611 6621045612654328248947417)
      ·
        refine ⟨4965784209490746186710563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6621045612654328248947417 4965784209490746186710563)
        ·
          refine ⟨7448676314236119280065845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4965784209490746186710563 7448676314236119280065845)
          ·
            refine ⟨698313404459636182506173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7448676314236119280065845 698313404459636182506173)
            ·
              refine ⟨261867526672363568439815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 698313404459636182506173 261867526672363568439815)
              ·
                refine ⟨392801290008545352659723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261867526672363568439815 392801290008545352659723)
                ·
                  refine ⟨589201935012818028989585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392801290008545352659723 589201935012818028989585)
                  ·
                    refine ⟨441901451259613521742189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 589201935012818028989585 441901451259613521742189)
                    ·
                      refine ⟨165713044222355070653321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 441901451259613521742189 165713044222355070653321)
                      ·
                        rfl

theorem cell23_322725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_322725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322725 prefixEnd_322725 := by exact prefixLift 322725
  have htrace : WordTrace (prefixWord ++ tailWord_322725) baseStart_322725 baseEnd_322725 := by
    simpa [prefixWord, tailWord_322725, baseEnd_322725] using wordTrace_append hprefix tailTrace_322725
  have hstable : (prefixWord ++ tailWord_322725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322725).length < 2 ^ (prefixWord ++ tailWord_322725).sum := by decide
  have hdescent : baseEnd_322725 < baseStart_322725 := by decide
  rcases family_descends (prefixWord ++ tailWord_322725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322789 : List Nat := [1, 3, 1, 4, 4, 1, 1, 2, 2, 1, 3]
def baseStart_322789 : Nat := 118140960795 + 322789 * 2 ^ 59
def prefixEnd_322789 : Nat := 4983230072969 + 3 ^ 40 * 322789 * 2
def baseEnd_322789 : Nat := 165745906984242820253027

theorem tailTrace_322789 : CollatzResearch.WordTrace tailWord_322789 prefixEnd_322789 165745906984242820253027 := by
  unfold tailWord_322789
  simp only [CollatzResearch.WordTrace]
  refine ⟨11773082027598055817347421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7848721351732037211564947 11773082027598055817347421)
  ·
    refine ⟨4414905760349270931505283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11773082027598055817347421 4414905760349270931505283)
    ·
      refine ⟨6622358640523906397257925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4414905760349270931505283 6622358640523906397257925)
      ·
        refine ⟨1241692245098232449485861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6622358640523906397257925 1241692245098232449485861)
        ·
          refine ⟨232817295955918584278599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1241692245098232449485861 232817295955918584278599)
          ·
            refine ⟨349225943933877876417899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232817295955918584278599 349225943933877876417899)
            ·
              refine ⟨523838915900816814626849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349225943933877876417899 523838915900816814626849)
              ·
                refine ⟨392879186925612610970137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 523838915900816814626849 392879186925612610970137)
                ·
                  refine ⟨294659390194209458227603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392879186925612610970137 294659390194209458227603)
                  ·
                    refine ⟨441989085291314187341405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 294659390194209458227603 441989085291314187341405)
                    ·
                      refine ⟨165745906984242820253027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 441989085291314187341405 165745906984242820253027)
                      ·
                        rfl

theorem cell23_322789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_322789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322789 prefixEnd_322789 := by exact prefixLift 322789
  have htrace : WordTrace (prefixWord ++ tailWord_322789) baseStart_322789 baseEnd_322789 := by
    simpa [prefixWord, tailWord_322789, baseEnd_322789] using wordTrace_append hprefix tailTrace_322789
  have hstable : (prefixWord ++ tailWord_322789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322789).length < 2 ^ (prefixWord ++ tailWord_322789).sum := by decide
  have hdescent : baseEnd_322789 < baseStart_322789 := by decide
  rcases family_descends (prefixWord ++ tailWord_322789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322795 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 4, 2, 2]
def baseStart_322795 : Nat := 118140960795 + 322795 * 2 ^ 59
def prefixEnd_322795 : Nat := 4983230072969 + 3 ^ 40 * 322795 * 2
def baseEnd_322795 : Nat := 165748987868169796777999

theorem tailTrace_322795 : CollatzResearch.WordTrace tailWord_322795 prefixEnd_322795 165748987868169796777999 := by
  unfold tailWord_322795
  simp only [CollatzResearch.WordTrace]
  refine ⟨11773300865576318842065839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7848867243717545894710559 11773300865576318842065839)
  ·
    refine ⟨17659951298364478263098759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11773300865576318842065839 17659951298364478263098759)
    ·
      refine ⟨26489926947546717394648139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17659951298364478263098759 26489926947546717394648139)
      ·
        refine ⟨39734890421320076091972209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26489926947546717394648139 39734890421320076091972209)
        ·
          refine ⟨29801167815990057068979157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39734890421320076091972209 29801167815990057068979157)
          ·
            refine ⟨698464870687266962554199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 29801167815990057068979157 698464870687266962554199)
            ·
              refine ⟨1047697306030900443831299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698464870687266962554199 1047697306030900443831299)
              ·
                refine ⟨1571545959046350665746949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1047697306030900443831299 1571545959046350665746949)
                ·
                  refine ⟨294664867321190749827553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1571545959046350665746949 294664867321190749827553)
                  ·
                    refine ⟨220998650490893062370665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 294664867321190749827553 220998650490893062370665)
                    ·
                      refine ⟨165748987868169796777999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 220998650490893062370665 165748987868169796777999)
                      ·
                        rfl

theorem cell23_322795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 2, 2].length) (baseStart_322795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322795 prefixEnd_322795 := by exact prefixLift 322795
  have htrace : WordTrace (prefixWord ++ tailWord_322795) baseStart_322795 baseEnd_322795 := by
    simpa [prefixWord, tailWord_322795, baseEnd_322795] using wordTrace_append hprefix tailTrace_322795
  have hstable : (prefixWord ++ tailWord_322795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322795).length < 2 ^ (prefixWord ++ tailWord_322795).sum := by decide
  have hdescent : baseEnd_322795 < baseStart_322795 := by decide
  rcases family_descends (prefixWord ++ tailWord_322795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322812 : List Nat := [2, 2, 2, 1, 5, 2, 1, 1, 1, 4, 2]
def baseStart_322812 : Nat := 118140960795 + 322812 * 2 ^ 59
def prefixEnd_322812 : Nat := 4983230072969 + 3 ^ 40 * 322812 * 2
def baseEnd_322812 : Nat := 165757717039296230265421

theorem tailTrace_322812 : CollatzResearch.WordTrace tailWord_322812 prefixEnd_322812 165757717039296230265421 := by
  unfold tailWord_322812
  simp only [CollatzResearch.WordTrace]
  refine ⟨5886960453257365372717345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7849280604343153830289793 5886960453257365372717345)
  ·
    refine ⟨4415220339943024029538009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5886960453257365372717345 4415220339943024029538009)
    ·
      refine ⟨3311415254957268022153507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4415220339943024029538009 3311415254957268022153507)
      ·
        refine ⟨4967122882435902033230261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3311415254957268022153507 4967122882435902033230261)
        ·
          refine ⟨465667770228365815615337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4967122882435902033230261 465667770228365815615337)
          ·
            refine ⟨349250827671274361711503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 465667770228365815615337 349250827671274361711503)
            ·
              refine ⟨523876241506911542567255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349250827671274361711503 523876241506911542567255)
              ·
                refine ⟨785814362260367313850883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 523876241506911542567255 785814362260367313850883)
                ·
                  refine ⟨1178721543390550970776325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 785814362260367313850883 1178721543390550970776325)
                  ·
                    refine ⟨221010289385728307020561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1178721543390550970776325 221010289385728307020561)
                    ·
                      refine ⟨165757717039296230265421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221010289385728307020561 165757717039296230265421)
                      ·
                        rfl

theorem cell23_322812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_322812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322812 prefixEnd_322812 := by exact prefixLift 322812
  have htrace : WordTrace (prefixWord ++ tailWord_322812) baseStart_322812 baseEnd_322812 := by
    simpa [prefixWord, tailWord_322812, baseEnd_322812] using wordTrace_append hprefix tailTrace_322812
  have hstable : (prefixWord ++ tailWord_322812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322812).length < 2 ^ (prefixWord ++ tailWord_322812).sum := by decide
  have hdescent : baseEnd_322812 < baseStart_322812 := by decide
  rcases family_descends (prefixWord ++ tailWord_322812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322858 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_322858 : Nat := 118140960795 + 322858 * 2 ^ 59
def prefixEnd_322858 : Nat := 4983230072969 + 3 ^ 40 * 322858 * 2
def baseEnd_322858 : Nat := 165781337149403050290209

theorem tailTrace_322858 : CollatzResearch.WordTrace tailWord_322858 prefixEnd_322858 165781337149403050290209 := by
  unfold tailWord_322858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2943899666087020150402307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7850399109565387067739485 2943899666087020150402307)
  ·
    refine ⟨4415849499130530225603461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2943899666087020150402307 4415849499130530225603461)
    ·
      refine ⟨827971781086974417300649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4415849499130530225603461 827971781086974417300649)
      ·
        refine ⟨620978835815230812975487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 827971781086974417300649 620978835815230812975487)
        ·
          refine ⟨931468253722846219463231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620978835815230812975487 931468253722846219463231)
          ·
            refine ⟨1397202380584269329194847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931468253722846219463231 1397202380584269329194847)
            ·
              refine ⟨2095803570876403993792271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1397202380584269329194847 2095803570876403993792271)
              ·
                refine ⟨3143705356314605990688407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2095803570876403993792271 3143705356314605990688407)
                ·
                  refine ⟨4715558034471908986032611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3143705356314605990688407 4715558034471908986032611)
                  ·
                    refine ⟨7073337051707863479048917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4715558034471908986032611 7073337051707863479048917)
                    ·
                      refine ⟨165781337149403050290209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7073337051707863479048917 165781337149403050290209)
                      ·
                        rfl

theorem cell23_322858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_322858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322858 prefixEnd_322858 := by exact prefixLift 322858
  have htrace : WordTrace (prefixWord ++ tailWord_322858) baseStart_322858 baseEnd_322858 := by
    simpa [prefixWord, tailWord_322858, baseEnd_322858] using wordTrace_append hprefix tailTrace_322858
  have hstable : (prefixWord ++ tailWord_322858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322858).length < 2 ^ (prefixWord ++ tailWord_322858).sum := by decide
  have hdescent : baseEnd_322858 < baseStart_322858 := by decide
  rcases family_descends (prefixWord ++ tailWord_322858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322911 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 6]
def baseStart_322911 : Nat := 118140960795 + 322911 * 2 ^ 59
def prefixEnd_322911 : Nat := 4983230072969 + 3 ^ 40 * 322911 * 2
def baseEnd_322911 : Nat := 165808551624091342927465

theorem tailTrace_322911 : CollatzResearch.WordTrace tailWord_322911 prefixEnd_322911 165808551624091342927465 := by
  unfold tailWord_322911
  simp only [CollatzResearch.WordTrace]
  refine ⟨11777531733156070653288587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7851687822104047102192391 11777531733156070653288587)
  ·
    refine ⟨17666297599734105979932881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11777531733156070653288587 17666297599734105979932881)
    ·
      refine ⟨13249723199800579484949661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17666297599734105979932881 13249723199800579484949661)
      ·
        refine ⟨4968646199925217306856123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13249723199800579484949661 4968646199925217306856123)
        ·
          refine ⟨7452969299887825960284185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4968646199925217306856123 7452969299887825960284185)
          ·
            refine ⟨5589726974915869470213139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7452969299887825960284185 5589726974915869470213139)
            ·
              refine ⟨8384590462373804205319709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5589726974915869470213139 8384590462373804205319709)
              ·
                refine ⟨3144221423390176576994891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8384590462373804205319709 3144221423390176576994891)
                ·
                  refine ⟨4716332135085264865492337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3144221423390176576994891 4716332135085264865492337)
                  ·
                    refine ⟨3537249101313948649119253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4716332135085264865492337 3537249101313948649119253)
                    ·
                      refine ⟨165808551624091342927465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3537249101313948649119253 165808551624091342927465)
                      ·
                        rfl

theorem cell23_322911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_322911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322911 prefixEnd_322911 := by exact prefixLift 322911
  have htrace : WordTrace (prefixWord ++ tailWord_322911) baseStart_322911 baseEnd_322911 := by
    simpa [prefixWord, tailWord_322911, baseEnd_322911] using wordTrace_append hprefix tailTrace_322911
  have hstable : (prefixWord ++ tailWord_322911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322911).length < 2 ^ (prefixWord ++ tailWord_322911).sum := by decide
  have hdescent : baseEnd_322911 < baseStart_322911 := by decide
  rcases family_descends (prefixWord ++ tailWord_322911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322912 : List Nat := [2, 1, 1, 3, 4, 2, 1, 4, 1, 4]
def baseStart_322912 : Nat := 118140960795 + 322912 * 2 ^ 59
def prefixEnd_322912 : Nat := 4983230072969 + 3 ^ 40 * 322912 * 2
def baseEnd_322912 : Nat := 55269688368248613004987

theorem tailTrace_322912 : CollatzResearch.WordTrace tailWord_322912 prefixEnd_322912 55269688368248613004987 := by
  unfold tailWord_322912
  simp only [CollatzResearch.WordTrace]
  refine ⟨5888784103076223912037495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7851712137434965216049993 5888784103076223912037495)
  ·
    refine ⟨8833176154614335868056243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5888784103076223912037495 8833176154614335868056243)
    ·
      refine ⟨13249764231921503802084365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8833176154614335868056243 13249764231921503802084365)
      ·
        refine ⟨4968661586970563925781637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13249764231921503802084365 4968661586970563925781637)
        ·
          refine ⟨931624047556980736084057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4968661586970563925781637 931624047556980736084057)
          ·
            refine ⟨698718035667735552063043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 931624047556980736084057 698718035667735552063043)
            ·
              refine ⟨1048077053501603328094565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698718035667735552063043 1048077053501603328094565)
              ·
                refine ⟨196514447531550624017731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1048077053501603328094565 196514447531550624017731)
                ·
                  refine ⟨294771671297325936026597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196514447531550624017731 294771671297325936026597)
                  ·
                    refine ⟨55269688368248613004987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 294771671297325936026597 55269688368248613004987)
                    ·
                      rfl

theorem cell23_322912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 1, 4].length) (baseStart_322912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322912 prefixEnd_322912 := by exact prefixLift 322912
  have htrace : WordTrace (prefixWord ++ tailWord_322912) baseStart_322912 baseEnd_322912 := by
    simpa [prefixWord, tailWord_322912, baseEnd_322912] using wordTrace_append hprefix tailTrace_322912
  have hstable : (prefixWord ++ tailWord_322912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322912).length < 2 ^ (prefixWord ++ tailWord_322912).sum := by decide
  have hdescent : baseEnd_322912 < baseStart_322912 := by decide
  rcases family_descends (prefixWord ++ tailWord_322912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322935 : List Nat := [1, 1, 3, 1, 1, 2, 5, 2, 3, 1, 3]
def baseStart_322935 : Nat := 118140960795 + 322935 * 2 ^ 59
def prefixEnd_322935 : Nat := 4983230072969 + 3 ^ 40 * 322935 * 2
def baseEnd_322935 : Nat := 165820875159799249027355

theorem tailTrace_322935 : CollatzResearch.WordTrace tailWord_322935 prefixEnd_322935 165820875159799249027355 := by
  unfold tailWord_322935
  simp only [CollatzResearch.WordTrace]
  refine ⟨11778407085069122752162259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7852271390046081834774839 11778407085069122752162259)
  ·
    refine ⟨17667610627603684128243389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11778407085069122752162259 17667610627603684128243389)
    ·
      refine ⟨6625353985351381548091271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17667610627603684128243389 6625353985351381548091271)
      ·
        refine ⟨9938030978027072322136907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6625353985351381548091271 9938030978027072322136907)
        ·
          refine ⟨14907046467040608483205361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9938030978027072322136907 14907046467040608483205361)
          ·
            refine ⟨11180284850280456362404021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14907046467040608483205361 11180284850280456362404021)
            ·
              refine ⟨1048151704713792783975377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11180284850280456362404021 1048151704713792783975377)
              ·
                refine ⟨786113778535344587981533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1048151704713792783975377 786113778535344587981533)
                ·
                  refine ⟨294792666950754220493075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 786113778535344587981533 294792666950754220493075)
                  ·
                    refine ⟨442189000426131330739613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 294792666950754220493075 442189000426131330739613)
                    ·
                      refine ⟨165820875159799249027355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 442189000426131330739613 165820875159799249027355)
                      ·
                        rfl

theorem cell23_322935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 1, 3].length) (baseStart_322935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322935 prefixEnd_322935 := by exact prefixLift 322935
  have htrace : WordTrace (prefixWord ++ tailWord_322935) baseStart_322935 baseEnd_322935 := by
    simpa [prefixWord, tailWord_322935, baseEnd_322935] using wordTrace_append hprefix tailTrace_322935
  have hstable : (prefixWord ++ tailWord_322935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322935).length < 2 ^ (prefixWord ++ tailWord_322935).sum := by decide
  have hdescent : baseEnd_322935 < baseStart_322935 := by decide
  rcases family_descends (prefixWord ++ tailWord_322935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322946 : List Nat := [3, 4, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_322946 : Nat := 118140960795 + 322946 * 2 ^ 59
def prefixEnd_322946 : Nat := 4983230072969 + 3 ^ 40 * 322946 * 2
def baseEnd_322946 : Nat := 55275507815666235329935

theorem tailTrace_322946 : CollatzResearch.WordTrace tailWord_322946 prefixEnd_322946 55275507815666235329935 := by
  unfold tailWord_322946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2944702072007317907703173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7852538858686181087208461 2944702072007317907703173)
  ·
    refine ⟨552131638501372107694345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2944702072007317907703173 552131638501372107694345)
    ·
      refine ⟨414098728876029080770759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 552131638501372107694345 414098728876029080770759)
      ·
        refine ⟨621148093314043621156139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414098728876029080770759 621148093314043621156139)
        ·
          refine ⟨931722139971065431734209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621148093314043621156139 931722139971065431734209)
          ·
            refine ⟨698791604978299073800657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 931722139971065431734209 698791604978299073800657)
            ·
              refine ⟨524093703733724305350493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698791604978299073800657 524093703733724305350493)
              ·
                refine ⟨196535138900146614506435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 524093703733724305350493 196535138900146614506435)
                ·
                  refine ⟨294802708350219921759653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196535138900146614506435 294802708350219921759653)
                  ·
                    refine ⟨55275507815666235329935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 294802708350219921759653 55275507815666235329935)
                    ·
                      rfl

theorem cell23_322946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_322946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_322946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_322946 prefixEnd_322946 := by exact prefixLift 322946
  have htrace : WordTrace (prefixWord ++ tailWord_322946) baseStart_322946 baseEnd_322946 := by
    simpa [prefixWord, tailWord_322946, baseEnd_322946] using wordTrace_append hprefix tailTrace_322946
  have hstable : (prefixWord ++ tailWord_322946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322946).length < 2 ^ (prefixWord ++ tailWord_322946).sum := by decide
  have hdescent : baseEnd_322946 < baseStart_322946 := by decide
  rcases family_descends (prefixWord ++ tailWord_322946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323012 : List Nat := [2, 3, 3, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_323012 : Nat := 118140960795 + 323012 * 2 ^ 59
def prefixEnd_323012 : Nat := 4983230072969 + 3 ^ 40 * 323012 * 2
def baseEnd_323012 : Nat := 165860413170195447764501

theorem tailTrace_323012 : CollatzResearch.WordTrace tailWord_323012 prefixEnd_323012 165860413170195447764501 := by
  unfold tailWord_323012
  simp only [CollatzResearch.WordTrace]
  refine ⟨5890607752895082451357645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7854143670526776601810193 5890607752895082451357645)
  ·
    refine ⟨2208977907335655919259117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5890607752895082451357645 2208977907335655919259117)
    ·
      refine ⟨828366715250870969722169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2208977907335655919259117 828366715250870969722169)
      ·
        refine ⟨621275036438153227291627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 828366715250870969722169 621275036438153227291627)
        ·
          refine ⟨931912554657229840937441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621275036438153227291627 931912554657229840937441)
          ·
            refine ⟨698934415992922380703081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 931912554657229840937441 698934415992922380703081)
            ·
              refine ⟨524200811994691785527311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698934415992922380703081 524200811994691785527311)
              ·
                refine ⟨786301217992037678290967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524200811994691785527311 786301217992037678290967)
                ·
                  refine ⟨1179451826988056517436451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 786301217992037678290967 1179451826988056517436451)
                  ·
                    refine ⟨1769177740482084776154677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1179451826988056517436451 1769177740482084776154677)
                    ·
                      refine ⟨165860413170195447764501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1769177740482084776154677 165860413170195447764501)
                      ·
                        rfl

theorem cell23_323012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_323012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323012 prefixEnd_323012 := by exact prefixLift 323012
  have htrace : WordTrace (prefixWord ++ tailWord_323012) baseStart_323012 baseEnd_323012 := by
    simpa [prefixWord, tailWord_323012, baseEnd_323012] using wordTrace_append hprefix tailTrace_323012
  have hstable : (prefixWord ++ tailWord_323012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323012).length < 2 ^ (prefixWord ++ tailWord_323012).sum := by decide
  have hdescent : baseEnd_323012 < baseStart_323012 := by decide
  rcases family_descends (prefixWord ++ tailWord_323012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323035 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 9, 3, 2]
def baseStart_323035 : Nat := 118140960795 + 323035 * 2 ^ 59
def prefixEnd_323035 : Nat := 4983230072969 + 3 ^ 40 * 323035 * 2
def baseEnd_323035 : Nat := 165872223225248857776895

theorem tailTrace_323035 : CollatzResearch.WordTrace tailWord_323035 prefixEnd_323035 165872223225248857776895 := by
  unfold tailWord_323035
  simp only [CollatzResearch.WordTrace]
  refine ⟨11782054384706839830802559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7854702923137893220535039 11782054384706839830802559)
  ·
    refine ⟨17673081577060259746203839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11782054384706839830802559 17673081577060259746203839)
    ·
      refine ⟨26509622365590389619305759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17673081577060259746203839 26509622365590389619305759)
      ·
        refine ⟨39764433548385584428958639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26509622365590389619305759 39764433548385584428958639)
        ·
          refine ⟨59646650322578376643437959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39764433548385584428958639 59646650322578376643437959)
          ·
            refine ⟨89469975483867564965156939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59646650322578376643437959 89469975483867564965156939)
            ·
              refine ⟨134204963225801347447735409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89469975483867564965156939 134204963225801347447735409)
              ·
                refine ⟨100653722419351010585801557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134204963225801347447735409 100653722419351010585801557)
                ·
                  refine ⟨589767904800884827651181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 100653722419351010585801557 589767904800884827651181)
                  ·
                    refine ⟨221162964300331810369193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 589767904800884827651181 221162964300331810369193)
                    ·
                      refine ⟨165872223225248857776895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221162964300331810369193 165872223225248857776895)
                      ·
                        rfl

theorem cell23_323035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 3, 2].length) (baseStart_323035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323035 prefixEnd_323035 := by exact prefixLift 323035
  have htrace : WordTrace (prefixWord ++ tailWord_323035) baseStart_323035 baseEnd_323035 := by
    simpa [prefixWord, tailWord_323035, baseEnd_323035] using wordTrace_append hprefix tailTrace_323035
  have hstable : (prefixWord ++ tailWord_323035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323035).length < 2 ^ (prefixWord ++ tailWord_323035).sum := by decide
  have hdescent : baseEnd_323035 < baseStart_323035 := by decide
  rcases family_descends (prefixWord ++ tailWord_323035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323052 : List Nat := [2, 2, 1, 1, 2, 1, 2, 6, 1, 3, 2]
def baseStart_323052 : Nat := 118140960795 + 323052 * 2 ^ 59
def prefixEnd_323052 : Nat := 4983230072969 + 3 ^ 40 * 323052 * 2
def baseEnd_323052 : Nat := 165880952396375291264317

theorem tailTrace_323052 : CollatzResearch.WordTrace tailWord_323052 prefixEnd_323052 165880952396375291264317 := by
  unfold tailWord_323052
  simp only [CollatzResearch.WordTrace]
  refine ⟨5891337212822625867085705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7855116283763501156114273 5891337212822625867085705)
  ·
    refine ⟨4418502909616969400314279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5891337212822625867085705 4418502909616969400314279)
    ·
      refine ⟨6627754364425454100471419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4418502909616969400314279 6627754364425454100471419)
      ·
        refine ⟨9941631546638181150707129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6627754364425454100471419 9941631546638181150707129)
        ·
          refine ⟨7456223659978635863030347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9941631546638181150707129 7456223659978635863030347)
          ·
            refine ⟨11184335489967953794545521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7456223659978635863030347 11184335489967953794545521)
            ·
              refine ⟨8388251617475965345909141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11184335489967953794545521 8388251617475965345909141)
              ·
                refine ⟨393199294569185875589491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8388251617475965345909141 393199294569185875589491)
                ·
                  refine ⟨589798941853778813384237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 393199294569185875589491 589798941853778813384237)
                  ·
                    refine ⟨221174603195167055019089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 589798941853778813384237 221174603195167055019089)
                    ·
                      refine ⟨165880952396375291264317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221174603195167055019089 165880952396375291264317)
                      ·
                        rfl

theorem cell23_323052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 3, 2].length) (baseStart_323052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323052 prefixEnd_323052 := by exact prefixLift 323052
  have htrace : WordTrace (prefixWord ++ tailWord_323052) baseStart_323052 baseEnd_323052 := by
    simpa [prefixWord, tailWord_323052, baseEnd_323052] using wordTrace_append hprefix tailTrace_323052
  have hstable : (prefixWord ++ tailWord_323052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323052).length < 2 ^ (prefixWord ++ tailWord_323052).sum := by decide
  have hdescent : baseEnd_323052 < baseStart_323052 := by decide
  rcases family_descends (prefixWord ++ tailWord_323052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323076 : List Nat := [2, 3, 2, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_323076 : Nat := 118140960795 + 323076 * 2 ^ 59
def prefixEnd_323076 : Nat := 4983230072969 + 3 ^ 40 * 323076 * 2
def baseEnd_323076 : Nat := 165893275932083197364207

theorem tailTrace_323076 : CollatzResearch.WordTrace tailWord_323076 prefixEnd_323076 165893275932083197364207 := by
  unfold tailWord_323076
  simp only [CollatzResearch.WordTrace]
  refine ⟨5891774888779151916522541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7855699851705535888696721 5891774888779151916522541)
  ·
    refine ⟨2209415583292181968695953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5891774888779151916522541 2209415583292181968695953)
    ·
      refine ⟨1657061687469136476521965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2209415583292181968695953 1657061687469136476521965)
      ·
        refine ⟨621398132800926178695737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1657061687469136476521965 621398132800926178695737)
        ·
          refine ⟨466048599600694634021803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 621398132800926178695737 466048599600694634021803)
          ·
            refine ⟨699072899401041951032705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466048599600694634021803 699072899401041951032705)
            ·
              refine ⟨524304674550781463274529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 699072899401041951032705 524304674550781463274529)
              ·
                refine ⟨393228505913086097455897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524304674550781463274529 393228505913086097455897)
                ·
                  refine ⟨294921379434814573091923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393228505913086097455897 294921379434814573091923)
                  ·
                    refine ⟨442382069152221859637885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 294921379434814573091923 442382069152221859637885)
                    ·
                      refine ⟨165893275932083197364207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 442382069152221859637885 165893275932083197364207)
                      ·
                        rfl

theorem cell23_323076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_323076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323076 prefixEnd_323076 := by exact prefixLift 323076
  have htrace : WordTrace (prefixWord ++ tailWord_323076) baseStart_323076 baseEnd_323076 := by
    simpa [prefixWord, tailWord_323076, baseEnd_323076] using wordTrace_append hprefix tailTrace_323076
  have hstable : (prefixWord ++ tailWord_323076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323076).length < 2 ^ (prefixWord ++ tailWord_323076).sum := by decide
  have hdescent : baseEnd_323076 < baseStart_323076 := by decide
  rcases family_descends (prefixWord ++ tailWord_323076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323105 : List Nat := [1, 2, 3, 2, 2, 3, 1, 2, 7]
def baseStart_323105 : Nat := 118140960795 + 323105 * 2 ^ 59
def prefixEnd_323105 : Nat := 4983230072969 + 3 ^ 40 * 323105 * 2
def baseEnd_323105 : Nat := 18434240763451509322397

theorem tailTrace_323105 : CollatzResearch.WordTrace tailWord_323105 prefixEnd_323105 18434240763451509322397 := by
  unfold tailWord_323105
  simp only [CollatzResearch.WordTrace]
  refine ⟨11784607494453241785850769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7856404996302161190567179 11784607494453241785850769)
  ·
    refine ⟨8838455620839931339388077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11784607494453241785850769 8838455620839931339388077)
    ·
      refine ⟨3314420857814974252270529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8838455620839931339388077 3314420857814974252270529)
      ·
        refine ⟨2485815643361230689202897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3314420857814974252270529 2485815643361230689202897)
        ·
          refine ⟨1864361732520923016902173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2485815643361230689202897 1864361732520923016902173)
          ·
            refine ⟨699135649695346131338315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1864361732520923016902173 699135649695346131338315)
            ·
              refine ⟨1048703474543019197007473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699135649695346131338315 1048703474543019197007473)
              ·
                refine ⟨786527605907264397755605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1048703474543019197007473 786527605907264397755605)
                ·
                  refine ⟨18434240763451509322397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 786527605907264397755605 18434240763451509322397)
                  ·
                    rfl

theorem cell23_323105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 7].length) (baseStart_323105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323105 prefixEnd_323105 := by exact prefixLift 323105
  have htrace : WordTrace (prefixWord ++ tailWord_323105) baseStart_323105 baseEnd_323105 := by
    simpa [prefixWord, tailWord_323105, baseEnd_323105] using wordTrace_append hprefix tailTrace_323105
  have hstable : (prefixWord ++ tailWord_323105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323105).length < 2 ^ (prefixWord ++ tailWord_323105).sum := by decide
  have hdescent : baseEnd_323105 < baseStart_323105 := by decide
  rcases family_descends (prefixWord ++ tailWord_323105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323133 : List Nat := [1, 4, 1, 3, 3, 2, 1, 2, 2, 2, 2]
def baseStart_323133 : Nat := 118140960795 + 323133 * 2 ^ 59
def prefixEnd_323133 : Nat := 4983230072969 + 3 ^ 40 * 323133 * 2
def baseEnd_323133 : Nat := 165922544329389474351445

theorem tailTrace_323133 : CollatzResearch.WordTrace tailWord_323133 prefixEnd_323133 165922544329389474351445 := by
  unfold tailWord_323133
  simp only [CollatzResearch.WordTrace]
  refine ⟨11785628738351802567870053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7857085825567868378580035 11785628738351802567870053)
  ·
    refine ⟨2209805388440962981475635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11785628738351802567870053 2209805388440962981475635)
    ·
      refine ⟨3314708082661444472213453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2209805388440962981475635 3314708082661444472213453)
      ·
        refine ⟨1243015530998041677080045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3314708082661444472213453 1243015530998041677080045)
        ·
          refine ⟨466130824124265628905017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1243015530998041677080045 466130824124265628905017)
          ·
            refine ⟨349598118093199221678763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 466130824124265628905017 349598118093199221678763)
            ·
              refine ⟨524397177139798832518145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349598118093199221678763 524397177139798832518145)
              ·
                refine ⟨393297882854849124388609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524397177139798832518145 393297882854849124388609)
                ·
                  refine ⟨294973412141136843291457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393297882854849124388609 294973412141136843291457)
                  ·
                    refine ⟨221230059105852632468593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 294973412141136843291457 221230059105852632468593)
                    ·
                      refine ⟨165922544329389474351445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221230059105852632468593 165922544329389474351445)
                      ·
                        rfl

theorem cell23_323133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_323133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323133 prefixEnd_323133 := by exact prefixLift 323133
  have htrace : WordTrace (prefixWord ++ tailWord_323133) baseStart_323133 baseEnd_323133 := by
    simpa [prefixWord, tailWord_323133, baseEnd_323133] using wordTrace_append hprefix tailTrace_323133
  have hstable : (prefixWord ++ tailWord_323133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323133).length < 2 ^ (prefixWord ++ tailWord_323133).sum := by decide
  have hdescent : baseEnd_323133 < baseStart_323133 := by decide
  rcases family_descends (prefixWord ++ tailWord_323133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323189 : List Nat := [1, 3, 4, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_323189 : Nat := 118140960795 + 323189 * 2 ^ 59
def prefixEnd_323189 : Nat := 4983230072969 + 3 ^ 40 * 323189 * 2
def baseEnd_323189 : Nat := 165951299246041255251187

theorem tailTrace_323189 : CollatzResearch.WordTrace tailWord_323189 prefixEnd_323189 165951299246041255251187 := by
  unfold tailWord_323189
  simp only [CollatzResearch.WordTrace]
  refine ⟨11787671226148924131908621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7858447484099282754605747 11787671226148924131908621)
  ·
    refine ⟨4420376709805846549465733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11787671226148924131908621 4420376709805846549465733)
    ·
      refine ⟨828820633088596228024825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4420376709805846549465733 828820633088596228024825)
      ·
        refine ⟨621615474816447171018619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 828820633088596228024825 621615474816447171018619)
        ·
          refine ⟨932423212224670756527929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621615474816447171018619 932423212224670756527929)
          ·
            refine ⟨699317409168503067395947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 932423212224670756527929 699317409168503067395947)
            ·
              refine ⟨1048976113752754601093921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699317409168503067395947 1048976113752754601093921)
              ·
                refine ⟨786732085314565950820441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1048976113752754601093921 786732085314565950820441)
                ·
                  refine ⟨590049063985924463115331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 786732085314565950820441 590049063985924463115331)
                  ·
                    refine ⟨885073595978886694672997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 590049063985924463115331 885073595978886694672997)
                    ·
                      refine ⟨165951299246041255251187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 885073595978886694672997 165951299246041255251187)
                      ·
                        rfl

theorem cell23_323189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_323189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323189 prefixEnd_323189 := by exact prefixLift 323189
  have htrace : WordTrace (prefixWord ++ tailWord_323189) baseStart_323189 baseEnd_323189 := by
    simpa [prefixWord, tailWord_323189, baseEnd_323189] using wordTrace_append hprefix tailTrace_323189
  have hstable : (prefixWord ++ tailWord_323189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323189).length < 2 ^ (prefixWord ++ tailWord_323189).sum := by decide
  have hdescent : baseEnd_323189 < baseStart_323189 := by decide
  rcases family_descends (prefixWord ++ tailWord_323189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323195 : List Nat := [1, 1, 1, 1, 1, 4, 4, 4, 6]
def baseStart_323195 : Nat := 118140960795 + 323195 * 2 ^ 59
def prefixEnd_323195 : Nat := 4983230072969 + 3 ^ 40 * 323195 * 2
def baseEnd_323195 : Nat := 18439375569996470197351

theorem tailTrace_323195 : CollatzResearch.WordTrace tailWord_323195 prefixEnd_323195 18439375569996470197351 := by
  unfold tailWord_323195
  simp only [CollatzResearch.WordTrace]
  refine ⟨11787890064127187156627039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7858593376084791437751359 11787890064127187156627039)
  ·
    refine ⟨17681835096190780734940559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11787890064127187156627039 17681835096190780734940559)
    ·
      refine ⟨26522752644286171102410839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17681835096190780734940559 26522752644286171102410839)
      ·
        refine ⟨39784128966429256653616259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26522752644286171102410839 39784128966429256653616259)
        ·
          refine ⟨59676193449643884980424389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39784128966429256653616259 59676193449643884980424389)
          ·
            refine ⟨11189286271808228433829573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59676193449643884980424389 11189286271808228433829573)
            ·
              refine ⟨2097991175964042831343045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11189286271808228433829573 2097991175964042831343045)
              ·
                refine ⟨393373345493258030876821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2097991175964042831343045 393373345493258030876821)
                ·
                  refine ⟨18439375569996470197351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 393373345493258030876821 18439375569996470197351)
                  ·
                    rfl

theorem cell23_323195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 6].length) (baseStart_323195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323195 prefixEnd_323195 := by exact prefixLift 323195
  have htrace : WordTrace (prefixWord ++ tailWord_323195) baseStart_323195 baseEnd_323195 := by
    simpa [prefixWord, tailWord_323195, baseEnd_323195] using wordTrace_append hprefix tailTrace_323195
  have hstable : (prefixWord ++ tailWord_323195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323195).length < 2 ^ (prefixWord ++ tailWord_323195).sum := by decide
  have hdescent : baseEnd_323195 < baseStart_323195 := by decide
  rcases family_descends (prefixWord ++ tailWord_323195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323246 : List Nat := [4, 1, 4, 1, 2, 1, 2, 2, 6]
def baseStart_323246 : Nat := 118140960795 + 323246 * 2 ^ 59
def prefixEnd_323246 : Nat := 4983230072969 + 3 ^ 40 * 323246 * 2
def baseEnd_323246 : Nat := 18442285293705281359825

theorem tailTrace_323246 : CollatzResearch.WordTrace tailWord_323246 prefixEnd_323246 18442285293705281359825 := by
  unfold tailWord_323246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1473718773367802858341699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7859833457961615244489061 1473718773367802858341699)
  ·
    refine ⟨2210578160051704287512549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1473718773367802858341699 2210578160051704287512549)
    ·
      refine ⟨414483405009694553908603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2210578160051704287512549 414483405009694553908603)
      ·
        refine ⟨621725107514541830862905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414483405009694553908603 621725107514541830862905)
        ·
          refine ⟨466293830635906373147179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 621725107514541830862905 466293830635906373147179)
          ·
            refine ⟨699440745953859559720769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466293830635906373147179 699440745953859559720769)
            ·
              refine ⟨524580559465394669790577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 699440745953859559720769 524580559465394669790577)
              ·
                refine ⟨393435419599046002342933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524580559465394669790577 393435419599046002342933)
                ·
                  refine ⟨18442285293705281359825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 393435419599046002342933 18442285293705281359825)
                  ·
                    rfl

theorem cell23_323246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_323246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323246 prefixEnd_323246 := by exact prefixLift 323246
  have htrace : WordTrace (prefixWord ++ tailWord_323246) baseStart_323246 baseEnd_323246 := by
    simpa [prefixWord, tailWord_323246, baseEnd_323246] using wordTrace_append hprefix tailTrace_323246
  have hstable : (prefixWord ++ tailWord_323246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323246).length < 2 ^ (prefixWord ++ tailWord_323246).sum := by decide
  have hdescent : baseEnd_323246 < baseStart_323246 := by decide
  rcases family_descends (prefixWord ++ tailWord_323246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323272 : List Nat := [2, 1, 3, 1, 2, 2, 4, 1, 1, 6]
def baseStart_323272 : Nat := 118140960795 + 323272 * 2 ^ 59
def prefixEnd_323272 : Nat := 4983230072969 + 3 ^ 40 * 323272 * 2
def baseEnd_323272 : Nat := 55331306046788143504435

theorem tailTrace_323272 : CollatzResearch.WordTrace tailWord_323272 prefixEnd_323272 55331306046788143504435 := by
  unfold tailWord_323272
  simp only [CollatzResearch.WordTrace]
  refine ⟨5895349242424114653590035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7860465656565486204786713 5895349242424114653590035)
  ·
    refine ⟨8843023863636171980385053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5895349242424114653590035 8843023863636171980385053)
    ·
      refine ⟨3316133948863564492644395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8843023863636171980385053 3316133948863564492644395)
      ·
        refine ⟨4974200923295346738966593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3316133948863564492644395 4974200923295346738966593)
        ·
          refine ⟨3730650692471510054224945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4974200923295346738966593 3730650692471510054224945)
          ·
            refine ⟨2797988019353632540668709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3730650692471510054224945 2797988019353632540668709)
            ·
              refine ⟨524622753628806101375383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2797988019353632540668709 524622753628806101375383)
              ·
                refine ⟨786934130443209152063075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524622753628806101375383 786934130443209152063075)
                ·
                  refine ⟨1180401195664813728094613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 786934130443209152063075 1180401195664813728094613)
                  ·
                    refine ⟨55331306046788143504435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1180401195664813728094613 55331306046788143504435)
                    ·
                      rfl

theorem cell23_323272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_323272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323272 prefixEnd_323272 := by exact prefixLift 323272
  have htrace : WordTrace (prefixWord ++ tailWord_323272) baseStart_323272 baseEnd_323272 := by
    simpa [prefixWord, tailWord_323272, baseEnd_323272] using wordTrace_append hprefix tailTrace_323272
  have hstable : (prefixWord ++ tailWord_323272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323272).length < 2 ^ (prefixWord ++ tailWord_323272).sum := by decide
  have hdescent : baseEnd_323272 < baseStart_323272 := by decide
  rcases family_descends (prefixWord ++ tailWord_323272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323275 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 6]
def baseStart_323275 : Nat := 118140960795 + 323275 * 2 ^ 59
def prefixEnd_323275 : Nat := 4983230072969 + 3 ^ 40 * 323275 * 2
def baseEnd_323275 : Nat := 165995458582327918775791

theorem tailTrace_323275 : CollatzResearch.WordTrace tailWord_323275 prefixEnd_323275 165995458582327918775791 := by
  unfold tailWord_323275
  simp only [CollatzResearch.WordTrace]
  refine ⟨11790807903837360819539279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7860538602558240546359519 11790807903837360819539279)
  ·
    refine ⟨17686211855756041229308919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11790807903837360819539279 17686211855756041229308919)
    ·
      refine ⟨26529317783634061843963379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17686211855756041229308919 26529317783634061843963379)
      ·
        refine ⟨39793976675451092765945069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26529317783634061843963379 39793976675451092765945069)
        ·
          refine ⟨14922741253294159787229401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39793976675451092765945069 14922741253294159787229401)
          ·
            refine ⟨11192055939970619840422051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14922741253294159787229401 11192055939970619840422051)
            ·
              refine ⟨16788083909955929760633077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11192055939970619840422051 16788083909955929760633077)
              ·
                refine ⟨1573882866558368415059351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16788083909955929760633077 1573882866558368415059351)
                ·
                  refine ⟨2360824299837552622589027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573882866558368415059351 2360824299837552622589027)
                  ·
                    refine ⟨3541236449756328933883541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2360824299837552622589027 3541236449756328933883541)
                    ·
                      refine ⟨165995458582327918775791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3541236449756328933883541 165995458582327918775791)
                      ·
                        rfl

theorem cell23_323275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 6].length) (baseStart_323275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323275 prefixEnd_323275 := by exact prefixLift 323275
  have htrace : WordTrace (prefixWord ++ tailWord_323275) baseStart_323275 baseEnd_323275 := by
    simpa [prefixWord, tailWord_323275, baseEnd_323275] using wordTrace_append hprefix tailTrace_323275
  have hstable : (prefixWord ++ tailWord_323275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323275).length < 2 ^ (prefixWord ++ tailWord_323275).sum := by decide
  have hdescent : baseEnd_323275 < baseStart_323275 := by decide
  rcases family_descends (prefixWord ++ tailWord_323275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323305 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 2, 2, 6]
def baseStart_323305 : Nat := 118140960795 + 323305 * 2 ^ 59
def prefixEnd_323305 : Nat := 4983230072969 + 3 ^ 40 * 323305 * 2
def baseEnd_323305 : Nat := 166010863001962801400653

theorem tailTrace_323305 : CollatzResearch.WordTrace tailWord_323305 prefixEnd_323305 166010863001962801400653 := by
  unfold tailWord_323305
  simp only [CollatzResearch.WordTrace]
  refine ⟨11791902093728675943131369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7861268062485783962087579 11791902093728675943131369)
  ·
    refine ⟨8843926570296506957348527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11791902093728675943131369 8843926570296506957348527)
    ·
      refine ⟨13265889855444760436022791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8843926570296506957348527 13265889855444760436022791)
      ·
        refine ⟨19898834783167140654034187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13265889855444760436022791 19898834783167140654034187)
        ·
          refine ⟨29848252174750710981051281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19898834783167140654034187 29848252174750710981051281)
          ·
            refine ⟨22386189131063033235788461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29848252174750710981051281 22386189131063033235788461)
            ·
              refine ⟨8394820924148637463420673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22386189131063033235788461 8394820924148637463420673)
              ·
                refine ⟨6296115693111478097565505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8394820924148637463420673 6296115693111478097565505)
                ·
                  refine ⟨4722086769833608573174129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6296115693111478097565505 4722086769833608573174129)
                  ·
                    refine ⟨3541565077375206429880597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4722086769833608573174129 3541565077375206429880597)
                    ·
                      refine ⟨166010863001962801400653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3541565077375206429880597 166010863001962801400653)
                      ·
                        rfl

theorem cell23_323305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_323305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323305 prefixEnd_323305 := by exact prefixLift 323305
  have htrace : WordTrace (prefixWord ++ tailWord_323305) baseStart_323305 baseEnd_323305 := by
    simpa [prefixWord, tailWord_323305, baseEnd_323305] using wordTrace_append hprefix tailTrace_323305
  have hstable : (prefixWord ++ tailWord_323305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323305).length < 2 ^ (prefixWord ++ tailWord_323305).sum := by decide
  have hdescent : baseEnd_323305 < baseStart_323305 := by decide
  rcases family_descends (prefixWord ++ tailWord_323305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323313 : List Nat := [1, 2, 2, 2, 2, 3, 2, 4, 1, 2, 2]
def baseStart_323313 : Nat := 118140960795 + 323313 * 2 ^ 59
def prefixEnd_323313 : Nat := 4983230072969 + 3 ^ 40 * 323313 * 2
def baseEnd_323313 : Nat := 166014970847198770100617

theorem tailTrace_323313 : CollatzResearch.WordTrace tailWord_323313 prefixEnd_323313 166014970847198770100617 := by
  unfold tailWord_323313
  simp only [CollatzResearch.WordTrace]
  refine ⟨11792193877699693309422593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7861462585133128872948395 11792193877699693309422593)
  ·
    refine ⟨8844145408274769982066945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11792193877699693309422593 8844145408274769982066945)
    ·
      refine ⟨6633109056206077486550209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8844145408274769982066945 6633109056206077486550209)
      ·
        refine ⟨4974831792154558114912657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6633109056206077486550209 4974831792154558114912657)
        ·
          refine ⟨3731123844115918586184493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4974831792154558114912657 3731123844115918586184493)
          ·
            refine ⟨1399171441543469469819185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3731123844115918586184493 1399171441543469469819185)
            ·
              refine ⟨1049378581157602102364389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1399171441543469469819185 1049378581157602102364389)
              ·
                refine ⟨196758483967050394193323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1049378581157602102364389 196758483967050394193323)
                ·
                  refine ⟨295137725950575591289985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196758483967050394193323 295137725950575591289985)
                  ·
                    refine ⟨221353294462931693467489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 295137725950575591289985 221353294462931693467489)
                    ·
                      refine ⟨166014970847198770100617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221353294462931693467489 166014970847198770100617)
                      ·
                        rfl

theorem cell23_323313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 1, 2, 2].length) (baseStart_323313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323313 prefixEnd_323313 := by exact prefixLift 323313
  have htrace : WordTrace (prefixWord ++ tailWord_323313) baseStart_323313 baseEnd_323313 := by
    simpa [prefixWord, tailWord_323313, baseEnd_323313] using wordTrace_append hprefix tailTrace_323313
  have hstable : (prefixWord ++ tailWord_323313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323313).length < 2 ^ (prefixWord ++ tailWord_323313).sum := by decide
  have hdescent : baseEnd_323313 < baseStart_323313 := by decide
  rcases family_descends (prefixWord ++ tailWord_323313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323315 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 1, 9]
def baseStart_323315 : Nat := 118140960795 + 323315 * 2 ^ 59
def prefixEnd_323315 : Nat := 4983230072969 + 3 ^ 40 * 323315 * 2
def baseEnd_323315 : Nat := 55338665936169254091869

theorem tailTrace_323315 : CollatzResearch.WordTrace tailWord_323315 prefixEnd_323315 55338665936169254091869 := by
  unfold tailWord_323315
  simp only [CollatzResearch.WordTrace]
  refine ⟨11792266823692447650995399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7861511215794965100663599 11792266823692447650995399)
  ·
    refine ⟨17688400235538671476493099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11792266823692447650995399 17688400235538671476493099)
    ·
      refine ⟨26532600353308007214739649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17688400235538671476493099 26532600353308007214739649)
      ·
        refine ⟨19899450264981005411054737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26532600353308007214739649 19899450264981005411054737)
        ·
          refine ⟨14924587698735754058291053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19899450264981005411054737 14924587698735754058291053)
          ·
            refine ⟨5596720387025907771859145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14924587698735754058291053 5596720387025907771859145)
            ·
              refine ⟨4197540290269430828894359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5596720387025907771859145 4197540290269430828894359)
              ·
                refine ⟨6296310435404146243341539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4197540290269430828894359 6296310435404146243341539)
                ·
                  refine ⟨9444465653106219365012309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6296310435404146243341539 9444465653106219365012309)
                  ·
                    refine ⟨55338665936169254091869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 9444465653106219365012309 55338665936169254091869)
                    ·
                      rfl

theorem cell23_323315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 9].length) (baseStart_323315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323315 prefixEnd_323315 := by exact prefixLift 323315
  have htrace : WordTrace (prefixWord ++ tailWord_323315) baseStart_323315 baseEnd_323315 := by
    simpa [prefixWord, tailWord_323315, baseEnd_323315] using wordTrace_append hprefix tailTrace_323315
  have hstable : (prefixWord ++ tailWord_323315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323315).length < 2 ^ (prefixWord ++ tailWord_323315).sum := by decide
  have hdescent : baseEnd_323315 < baseStart_323315 := by decide
  rcases family_descends (prefixWord ++ tailWord_323315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323316 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_323316 : Nat := 118140960795 + 323316 * 2 ^ 59
def prefixEnd_323316 : Nat := 4983230072969 + 3 ^ 40 * 323316 * 2
def baseEnd_323316 : Nat := 166016511289162258363103

theorem tailTrace_323316 : CollatzResearch.WordTrace tailWord_323316 prefixEnd_323316 166016511289162258363103 := by
  unfold tailWord_323316
  simp only [CollatzResearch.WordTrace]
  refine ⟨5896151648344412410890901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7861535531125883214521201 5896151648344412410890901)
  ·
    refine ⟨276382108516144331760511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5896151648344412410890901 276382108516144331760511)
    ·
      refine ⟨414573162774216497640767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276382108516144331760511 414573162774216497640767)
      ·
        refine ⟨621859744161324746461151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414573162774216497640767 621859744161324746461151)
        ·
          refine ⟨932789616241987119691727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621859744161324746461151 932789616241987119691727)
          ·
            refine ⟨1399184424362980679537591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 932789616241987119691727 1399184424362980679537591)
            ·
              refine ⟨2098776636544471019306387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399184424362980679537591 2098776636544471019306387)
              ·
                refine ⟨3148164954816706528959581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2098776636544471019306387 3148164954816706528959581)
                ·
                  refine ⟨1180561858056264948359843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3148164954816706528959581 1180561858056264948359843)
                  ·
                    refine ⟨1770842787084397422539765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1180561858056264948359843 1770842787084397422539765)
                    ·
                      refine ⟨166016511289162258363103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1770842787084397422539765 166016511289162258363103)
                      ·
                        rfl

theorem cell23_323316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_323316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323316 prefixEnd_323316 := by exact prefixLift 323316
  have htrace : WordTrace (prefixWord ++ tailWord_323316) baseStart_323316 baseEnd_323316 := by
    simpa [prefixWord, tailWord_323316, baseEnd_323316] using wordTrace_append hprefix tailTrace_323316
  have hstable : (prefixWord ++ tailWord_323316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323316).length < 2 ^ (prefixWord ++ tailWord_323316).sum := by decide
  have hdescent : baseEnd_323316 < baseStart_323316 := by decide
  rcases family_descends (prefixWord ++ tailWord_323316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323329 : List Nat := [1, 2, 4, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_323329 : Nat := 118140960795 + 323329 * 2 ^ 59
def prefixEnd_323329 : Nat := 4983230072969 + 3 ^ 40 * 323329 * 2
def baseEnd_323329 : Nat := 166023186537670707500543

theorem tailTrace_323329 : CollatzResearch.WordTrace tailWord_323329 prefixEnd_323329 166023186537670707500543 := by
  unfold tailWord_323329
  simp only [CollatzResearch.WordTrace]
  refine ⟨11792777445641728042005041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7861851630427818694670027 11792777445641728042005041)
  ·
    refine ⟨8844583084231296031503781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11792777445641728042005041 8844583084231296031503781)
    ·
      refine ⟨1658359328293368005906959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8844583084231296031503781 1658359328293368005906959)
      ·
        refine ⟨2487538992440052008860439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1658359328293368005906959 2487538992440052008860439)
        ·
          refine ⟨3731308488660078013290659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2487538992440052008860439 3731308488660078013290659)
          ·
            refine ⟨5596962732990117019935989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3731308488660078013290659 5596962732990117019935989)
            ·
              refine ⟨524715256217823470618999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5596962732990117019935989 524715256217823470618999)
              ·
                refine ⟨787072884326735205928499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524715256217823470618999 787072884326735205928499)
                ·
                  refine ⟨1180609326490102808892749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 787072884326735205928499 1180609326490102808892749)
                  ·
                    refine ⟨442728497433788553334781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1180609326490102808892749 442728497433788553334781)
                    ·
                      refine ⟨166023186537670707500543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 442728497433788553334781 166023186537670707500543)
                      ·
                        rfl

theorem cell23_323329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_323329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323329 prefixEnd_323329 := by exact prefixLift 323329
  have htrace : WordTrace (prefixWord ++ tailWord_323329) baseStart_323329 baseEnd_323329 := by
    simpa [prefixWord, tailWord_323329, baseEnd_323329] using wordTrace_append hprefix tailTrace_323329
  have hstable : (prefixWord ++ tailWord_323329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323329).length < 2 ^ (prefixWord ++ tailWord_323329).sum := by decide
  have hdescent : baseEnd_323329 < baseStart_323329 := by decide
  rcases family_descends (prefixWord ++ tailWord_323329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323339 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 3, 3, 2]
def baseStart_323339 : Nat := 118140960795 + 323339 * 2 ^ 59
def prefixEnd_323339 : Nat := 4983230072969 + 3 ^ 40 * 323339 * 2
def baseEnd_323339 : Nat := 166028321344215668375497

theorem tailTrace_323339 : CollatzResearch.WordTrace tailWord_323339 prefixEnd_323339 166028321344215668375497 := by
  unfold tailWord_323339
  simp only [CollatzResearch.WordTrace]
  refine ⟨11793142175605499749869071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7862094783736999833246047 11793142175605499749869071)
  ·
    refine ⟨17689713263408249624803607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11793142175605499749869071 17689713263408249624803607)
    ·
      refine ⟨26534569895112374437205411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17689713263408249624803607 26534569895112374437205411)
      ·
        refine ⟨39801854842668561655808117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26534569895112374437205411 39801854842668561655808117)
        ·
          refine ⟨3731423891500177655232011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39801854842668561655808117 3731423891500177655232011)
          ·
            refine ⟨5597135837250266482848017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3731423891500177655232011 5597135837250266482848017)
            ·
              refine ⟨4197851877937699862136013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5597135837250266482848017 4197851877937699862136013)
              ·
                refine ⟨1574194454226637448301005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4197851877937699862136013 1574194454226637448301005)
                ·
                  refine ⟨590322920334989043112877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1574194454226637448301005 590322920334989043112877)
                  ·
                    refine ⟨221371095125620891167329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 590322920334989043112877 221371095125620891167329)
                    ·
                      refine ⟨166028321344215668375497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221371095125620891167329 166028321344215668375497)
                      ·
                        rfl

theorem cell23_323339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 3, 2].length) (baseStart_323339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323339 prefixEnd_323339 := by exact prefixLift 323339
  have htrace : WordTrace (prefixWord ++ tailWord_323339) baseStart_323339 baseEnd_323339 := by
    simpa [prefixWord, tailWord_323339, baseEnd_323339] using wordTrace_append hprefix tailTrace_323339
  have hstable : (prefixWord ++ tailWord_323339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323339).length < 2 ^ (prefixWord ++ tailWord_323339).sum := by decide
  have hdescent : baseEnd_323339 < baseStart_323339 := by decide
  rcases family_descends (prefixWord ++ tailWord_323339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323341 : List Nat := [1, 7, 2, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_323341 : Nat := 118140960795 + 323341 * 2 ^ 59
def prefixEnd_323341 : Nat := 4983230072969 + 3 ^ 40 * 323341 * 2
def baseEnd_323341 : Nat := 166029348305524660550489

theorem tailTrace_323341 : CollatzResearch.WordTrace tailWord_323341 prefixEnd_323341 166029348305524660550489 := by
  unfold tailWord_323341
  simp only [CollatzResearch.WordTrace]
  refine ⟨11793215121598254091441877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7862143414398836060961251 11793215121598254091441877)
  ·
    refine ⟨276403479412459080268169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 11793215121598254091441877 276403479412459080268169)
    ·
      refine ⟨207302609559344310201127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276403479412459080268169 207302609559344310201127)
      ·
        refine ⟨310953914339016465301691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207302609559344310201127 310953914339016465301691)
        ·
          refine ⟨466430871508524697952537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310953914339016465301691 466430871508524697952537)
          ·
            refine ⟨349823153631393523464403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 466430871508524697952537 349823153631393523464403)
            ·
              refine ⟨524734730447090285196605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349823153631393523464403 524734730447090285196605)
              ·
                refine ⟨196775523917658856948727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 524734730447090285196605 196775523917658856948727)
                ·
                  refine ⟨295163285876488285423091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196775523917658856948727 295163285876488285423091)
                  ·
                    refine ⟨442744928814732428134637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 295163285876488285423091 442744928814732428134637)
                    ·
                      refine ⟨166029348305524660550489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 442744928814732428134637 166029348305524660550489)
                      ·
                        rfl

theorem cell23_323341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_323341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323341 prefixEnd_323341 := by exact prefixLift 323341
  have htrace : WordTrace (prefixWord ++ tailWord_323341) baseStart_323341 baseEnd_323341 := by
    simpa [prefixWord, tailWord_323341, baseEnd_323341] using wordTrace_append hprefix tailTrace_323341
  have hstable : (prefixWord ++ tailWord_323341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323341).length < 2 ^ (prefixWord ++ tailWord_323341).sum := by decide
  have hdescent : baseEnd_323341 < baseStart_323341 := by decide
  rcases family_descends (prefixWord ++ tailWord_323341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323342 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_323342 : Nat := 118140960795 + 323342 * 2 ^ 59
def prefixEnd_323342 : Nat := 4983230072969 + 3 ^ 40 * 323342 * 2
def baseEnd_323342 : Nat := 166029861786179156637983

theorem tailTrace_323342 : CollatzResearch.WordTrace tailWord_323342 prefixEnd_323342 166029861786179156637983 := by
  unfold tailWord_323342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1474156449324328907778535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7862167729729754174818853 1474156449324328907778535)
  ·
    refine ⟨2211234673986493361667803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1474156449324328907778535 2211234673986493361667803)
    ·
      refine ⟨3316852010979740042501705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2211234673986493361667803 3316852010979740042501705)
      ·
        refine ⟨2487639008234805031876279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3316852010979740042501705 2487639008234805031876279)
        ·
          refine ⟨3731458512352207547814419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2487639008234805031876279 3731458512352207547814419)
          ·
            refine ⟨5597187768528311321721629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3731458512352207547814419 5597187768528311321721629)
            ·
              refine ⟨2098945413198116745645611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5597187768528311321721629 2098945413198116745645611)
              ·
                refine ⟨3148418119797175118468417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2098945413198116745645611 3148418119797175118468417)
                ·
                  refine ⟨2361313589847881338851313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3148418119797175118468417 2361313589847881338851313)
                  ·
                    refine ⟨1770985192385911004138485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2361313589847881338851313 1770985192385911004138485)
                    ·
                      refine ⟨166029861786179156637983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1770985192385911004138485 166029861786179156637983)
                      ·
                        rfl

theorem cell23_323342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_323342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323342 prefixEnd_323342 := by exact prefixLift 323342
  have htrace : WordTrace (prefixWord ++ tailWord_323342) baseStart_323342 baseEnd_323342 := by
    simpa [prefixWord, tailWord_323342, baseEnd_323342] using wordTrace_append hprefix tailTrace_323342
  have hstable : (prefixWord ++ tailWord_323342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323342).length < 2 ^ (prefixWord ++ tailWord_323342).sum := by decide
  have hdescent : baseEnd_323342 < baseStart_323342 := by decide
  rcases family_descends (prefixWord ++ tailWord_323342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323356 : List Nat := [2, 2, 3, 1, 1, 2, 1, 5, 1, 3, 2]
def baseStart_323356 : Nat := 118140960795 + 323356 * 2 ^ 59
def prefixEnd_323356 : Nat := 4983230072969 + 3 ^ 40 * 323356 * 2
def baseEnd_323356 : Nat := 166037050515342101862919

theorem tailTrace_323356 : CollatzResearch.WordTrace tailWord_323356 prefixEnd_323356 166037050515342101862919 := by
  unfold tailWord_323356
  simp only [CollatzResearch.WordTrace]
  refine ⟨5896881108271955826618961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7862508144362607768825281 5896881108271955826618961)
  ·
    refine ⟨4422660831203966869964221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5896881108271955826618961 4422660831203966869964221)
    ·
      refine ⟨1658497811701487576236583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4422660831203966869964221 1658497811701487576236583)
      ·
        refine ⟨2487746717552231364354875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1658497811701487576236583 2487746717552231364354875)
        ·
          refine ⟨3731620076328347046532313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2487746717552231364354875 3731620076328347046532313)
          ·
            refine ⟨2798715057246260284899235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3731620076328347046532313 2798715057246260284899235)
            ·
              refine ⟨4198072585869390427348853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2798715057246260284899235 4198072585869390427348853)
              ·
                refine ⟨393569304925255352563955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4198072585869390427348853 393569304925255352563955)
                ·
                  refine ⟨590353957387883028845933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 393569304925255352563955 590353957387883028845933)
                  ·
                    refine ⟨221382734020456135817225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 590353957387883028845933 221382734020456135817225)
                    ·
                      refine ⟨166037050515342101862919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221382734020456135817225 166037050515342101862919)
                      ·
                        rfl

theorem cell23_323356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_323356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323356 prefixEnd_323356 := by exact prefixLift 323356
  have htrace : WordTrace (prefixWord ++ tailWord_323356) baseStart_323356 baseEnd_323356 := by
    simpa [prefixWord, tailWord_323356, baseEnd_323356] using wordTrace_append hprefix tailTrace_323356
  have hstable : (prefixWord ++ tailWord_323356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323356).length < 2 ^ (prefixWord ++ tailWord_323356).sum := by decide
  have hdescent : baseEnd_323356 < baseStart_323356 := by decide
  rcases family_descends (prefixWord ++ tailWord_323356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323380 : List Nat := [2, 5, 1, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_323380 : Nat := 118140960795 + 323380 * 2 ^ 59
def prefixEnd_323380 : Nat := 4983230072969 + 3 ^ 40 * 323380 * 2
def baseEnd_323380 : Nat := 166049374051050007962809

theorem tailTrace_323380 : CollatzResearch.WordTrace tailWord_323380 prefixEnd_323380 166049374051050007962809 := by
  unfold tailWord_323380
  simp only [CollatzResearch.WordTrace]
  refine ⟨5897318784228481876055797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7863091712304642501407729 5897318784228481876055797)
  ·
    refine ⟨552873636021420175880231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5897318784228481876055797 552873636021420175880231)
    ·
      refine ⟨829310454032130263820347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 552873636021420175880231 829310454032130263820347)
      ·
        refine ⟨1243965681048195395730521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 829310454032130263820347 1243965681048195395730521)
        ·
          refine ⟨932974260786146546797891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1243965681048195395730521 932974260786146546797891)
          ·
            refine ⟨1399461391179219820196837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 932974260786146546797891 1399461391179219820196837)
            ·
              refine ⟨262399010846103716286907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1399461391179219820196837 262399010846103716286907)
              ·
                refine ⟨393598516269155574430361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262399010846103716286907 393598516269155574430361)
                ·
                  refine ⟨295198887201866680822771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393598516269155574430361 295198887201866680822771)
                  ·
                    refine ⟨442798330802800021234157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 295198887201866680822771 442798330802800021234157)
                    ·
                      refine ⟨166049374051050007962809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 442798330802800021234157 166049374051050007962809)
                      ·
                        rfl

theorem cell23_323380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_323380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323380 prefixEnd_323380 := by exact prefixLift 323380
  have htrace : WordTrace (prefixWord ++ tailWord_323380) baseStart_323380 baseEnd_323380 := by
    simpa [prefixWord, tailWord_323380, baseEnd_323380] using wordTrace_append hprefix tailTrace_323380
  have hstable : (prefixWord ++ tailWord_323380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323380).length < 2 ^ (prefixWord ++ tailWord_323380).sum := by decide
  have hdescent : baseEnd_323380 < baseStart_323380 := by decide
  rcases family_descends (prefixWord ++ tailWord_323380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323389 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_323389 : Nat := 118140960795 + 323389 * 2 ^ 59
def prefixEnd_323389 : Nat := 4983230072969 + 3 ^ 40 * 323389 * 2
def baseEnd_323389 : Nat := 166053995376940472750267

theorem tailTrace_323389 : CollatzResearch.WordTrace tailWord_323389 prefixEnd_323389 166053995376940472750267 := by
  unfold tailWord_323389
  simp only [CollatzResearch.WordTrace]
  refine ⟨11794965825424358289189221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7863310550282905526126147 11794965825424358289189221)
  ·
    refine ⟨2211556092267067179222979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11794965825424358289189221 2211556092267067179222979)
    ·
      refine ⟨3317334138400600768834469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2211556092267067179222979 3317334138400600768834469)
      ·
        refine ⟨622000150950112644156463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3317334138400600768834469 622000150950112644156463)
        ·
          refine ⟨933000226425168966234695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622000150950112644156463 933000226425168966234695)
          ·
            refine ⟨1399500339637753449352043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933000226425168966234695 1399500339637753449352043)
            ·
              refine ⟨2099250509456630174028065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399500339637753449352043 2099250509456630174028065)
              ·
                refine ⟨1574437882092472630521049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2099250509456630174028065 1574437882092472630521049)
                ·
                  refine ⟨1180828411569354472890787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1574437882092472630521049 1180828411569354472890787)
                  ·
                    refine ⟨1771242617354031709336181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1180828411569354472890787 1771242617354031709336181)
                    ·
                      refine ⟨166053995376940472750267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1771242617354031709336181 166053995376940472750267)
                      ·
                        rfl

theorem cell23_323389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_323389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323389 prefixEnd_323389 := by exact prefixLift 323389
  have htrace : WordTrace (prefixWord ++ tailWord_323389) baseStart_323389 baseEnd_323389 := by
    simpa [prefixWord, tailWord_323389, baseEnd_323389] using wordTrace_append hprefix tailTrace_323389
  have hstable : (prefixWord ++ tailWord_323389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323389).length < 2 ^ (prefixWord ++ tailWord_323389).sum := by decide
  have hdescent : baseEnd_323389 < baseStart_323389 := by decide
  rcases family_descends (prefixWord ++ tailWord_323389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323390 : List Nat := [4, 2, 1, 2, 2, 3, 1, 2, 1, 3, 2]
def baseStart_323390 : Nat := 118140960795 + 323390 * 2 ^ 59
def prefixEnd_323390 : Nat := 4983230072969 + 3 ^ 40 * 323390 * 2
def baseEnd_323390 : Nat := 166054508857594968837763

theorem tailTrace_323390 : CollatzResearch.WordTrace tailWord_323390 prefixEnd_323390 166054508857594968837763 := by
  unfold tailWord_323390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1474375287302591932496953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7863334865613823639983749 1474375287302591932496953)
  ·
    refine ⟨1105781465476943949372715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1474375287302591932496953 1105781465476943949372715)
    ·
      refine ⟨1658672198215415924059073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1105781465476943949372715 1658672198215415924059073)
      ·
        refine ⟨1244004148661561943044305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1658672198215415924059073 1244004148661561943044305)
        ·
          refine ⟨933003111496171457283229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1244004148661561943044305 933003111496171457283229)
          ·
            refine ⟨349876166811064296481211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 933003111496171457283229 349876166811064296481211)
            ·
              refine ⟨524814250216596444721817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349876166811064296481211 524814250216596444721817)
              ·
                refine ⟨393610687662447333541363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524814250216596444721817 393610687662447333541363)
                ·
                  refine ⟨590416031493671000312045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 393610687662447333541363 590416031493671000312045)
                  ·
                    refine ⟨221406011810126625117017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 590416031493671000312045 221406011810126625117017)
                    ·
                      refine ⟨166054508857594968837763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221406011810126625117017 166054508857594968837763)
                      ·
                        rfl

theorem cell23_323390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_323390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323390 prefixEnd_323390 := by exact prefixLift 323390
  have htrace : WordTrace (prefixWord ++ tailWord_323390) baseStart_323390 baseEnd_323390 := by
    simpa [prefixWord, tailWord_323390, baseEnd_323390] using wordTrace_append hprefix tailTrace_323390
  have hstable : (prefixWord ++ tailWord_323390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323390).length < 2 ^ (prefixWord ++ tailWord_323390).sum := by decide
  have hdescent : baseEnd_323390 < baseStart_323390 := by decide
  rcases family_descends (prefixWord ++ tailWord_323390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323459 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 4]
def baseStart_323459 : Nat := 118140960795 + 323459 * 2 ^ 59
def prefixEnd_323459 : Nat := 4983230072969 + 3 ^ 40 * 323459 * 2
def baseEnd_323459 : Nat := 166089939022755198874945

theorem tailTrace_323459 : CollatzResearch.WordTrace tailWord_323459 prefixEnd_323459 166089939022755198874945 := by
  unfold tailWord_323459
  simp only [CollatzResearch.WordTrace]
  refine ⟨11797518935170760244237431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7865012623447173496158287 11797518935170760244237431)
  ·
    refine ⟨17696278402756140366356147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11797518935170760244237431 17696278402756140366356147)
    ·
      refine ⟨26544417604134210549534221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17696278402756140366356147 26544417604134210549534221)
      ·
        refine ⟨9954156601550328956075333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26544417604134210549534221 9954156601550328956075333)
        ·
          refine ⟨1866404362790686679264125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9954156601550328956075333 1866404362790686679264125)
          ·
            refine ⟨699901636046507504724047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1866404362790686679264125 699901636046507504724047)
            ·
              refine ⟨1049852454069761257086071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699901636046507504724047 1049852454069761257086071)
              ·
                refine ⟨1574778681104641885629107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1049852454069761257086071 1574778681104641885629107)
                ·
                  refine ⟨2362168021656962828443661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1574778681104641885629107 2362168021656962828443661)
                  ·
                    refine ⟨885813008121361060666373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2362168021656962828443661 885813008121361060666373)
                    ·
                      refine ⟨166089939022755198874945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 885813008121361060666373 166089939022755198874945)
                      ·
                        rfl

theorem cell23_323459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_323459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323459 prefixEnd_323459 := by exact prefixLift 323459
  have htrace : WordTrace (prefixWord ++ tailWord_323459) baseStart_323459 baseEnd_323459 := by
    simpa [prefixWord, tailWord_323459, baseEnd_323459] using wordTrace_append hprefix tailTrace_323459
  have hstable : (prefixWord ++ tailWord_323459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323459).length < 2 ^ (prefixWord ++ tailWord_323459).sum := by decide
  have hdescent : baseEnd_323459 < baseStart_323459 := by decide
  rcases family_descends (prefixWord ++ tailWord_323459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323472 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 6]
def baseStart_323472 : Nat := 118140960795 + 323472 * 2 ^ 59
def prefixEnd_323472 : Nat := 4983230072969 + 3 ^ 40 * 323472 * 2
def baseEnd_323472 : Nat := 166096614271263648012385

theorem tailTrace_323472 : CollatzResearch.WordTrace tailWord_323472 prefixEnd_323472 166096614271263648012385 := by
  unfold tailWord_323472
  simp only [CollatzResearch.WordTrace]
  refine ⟨5898996542061831732230335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7865328722749108976307113 5898996542061831732230335)
  ·
    refine ⟨8848494813092747598345503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5898996542061831732230335 8848494813092747598345503)
    ·
      refine ⟨13272742219639121397518255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8848494813092747598345503 13272742219639121397518255)
      ·
        refine ⟨19909113329458682096277383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13272742219639121397518255 19909113329458682096277383)
        ·
          refine ⟨29863669994188023144416075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19909113329458682096277383 29863669994188023144416075)
          ·
            refine ⟨44795504991282034716624113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29863669994188023144416075 44795504991282034716624113)
            ·
              refine ⟨33596628743461526037468085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44795504991282034716624113 33596628743461526037468085)
              ·
                refine ⟨3149683944699518066012633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33596628743461526037468085 3149683944699518066012633)
                ·
                  refine ⟨2362262958524638549509475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3149683944699518066012633 2362262958524638549509475)
                  ·
                    refine ⟨3543394437786957824264213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2362262958524638549509475 3543394437786957824264213)
                    ·
                      refine ⟨166096614271263648012385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3543394437786957824264213 166096614271263648012385)
                      ·
                        rfl

theorem cell23_323472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_323472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323472 prefixEnd_323472 := by exact prefixLift 323472
  have htrace : WordTrace (prefixWord ++ tailWord_323472) baseStart_323472 baseEnd_323472 := by
    simpa [prefixWord, tailWord_323472, baseEnd_323472] using wordTrace_append hprefix tailTrace_323472
  have hstable : (prefixWord ++ tailWord_323472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323472).length < 2 ^ (prefixWord ++ tailWord_323472).sum := by decide
  have hdescent : baseEnd_323472 < baseStart_323472 := by decide
  rcases family_descends (prefixWord ++ tailWord_323472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323536 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 4, 3, 2]
def baseStart_323536 : Nat := 118140960795 + 323536 * 2 ^ 59
def prefixEnd_323536 : Nat := 4983230072969 + 3 ^ 40 * 323536 * 2
def baseEnd_323536 : Nat := 166129477033151397612091

theorem tailTrace_323536 : CollatzResearch.WordTrace tailWord_323536 prefixEnd_323536 166129477033151397612091 := by
  unfold tailWord_323536
  simp only [CollatzResearch.WordTrace]
  refine ⟨5900163677945901197395231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7866884903927868263193641 5900163677945901197395231)
  ·
    refine ⟨8850245516918851796092847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5900163677945901197395231 8850245516918851796092847)
    ·
      refine ⟨13275368275378277694139271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8850245516918851796092847 13275368275378277694139271)
      ·
        refine ⟨19913052413067416541208907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13275368275378277694139271 19913052413067416541208907)
        ·
          refine ⟨29869578619601124811813361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19913052413067416541208907 29869578619601124811813361)
          ·
            refine ⟨22402183964700843608860021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29869578619601124811813361 22402183964700843608860021)
            ·
              refine ⟨2100204746690704088330627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22402183964700843608860021 2100204746690704088330627)
              ·
                refine ⟨3150307120036056132495941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2100204746690704088330627 3150307120036056132495941)
                ·
                  refine ⟨590682585006760524842989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3150307120036056132495941 590682585006760524842989)
                  ·
                    refine ⟨221505969377535196816121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 590682585006760524842989 221505969377535196816121)
                    ·
                      refine ⟨166129477033151397612091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221505969377535196816121 166129477033151397612091)
                      ·
                        rfl

theorem cell23_323536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 4, 3, 2].length) (baseStart_323536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323536 prefixEnd_323536 := by exact prefixLift 323536
  have htrace : WordTrace (prefixWord ++ tailWord_323536) baseStart_323536 baseEnd_323536 := by
    simpa [prefixWord, tailWord_323536, baseEnd_323536] using wordTrace_append hprefix tailTrace_323536
  have hstable : (prefixWord ++ tailWord_323536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323536).length < 2 ^ (prefixWord ++ tailWord_323536).sum := by decide
  have hdescent : baseEnd_323536 < baseStart_323536 := by decide
  rcases family_descends (prefixWord ++ tailWord_323536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323579 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 4]
def baseStart_323579 : Nat := 118140960795 + 323579 * 2 ^ 59
def prefixEnd_323579 : Nat := 4983230072969 + 3 ^ 40 * 323579 * 2
def baseEnd_323579 : Nat := 166151556701294729374393

theorem tailTrace_323579 : CollatzResearch.WordTrace tailWord_323579 prefixEnd_323579 166151556701294729374393 := by
  unfold tailWord_323579
  simp only [CollatzResearch.WordTrace]
  refine ⟨11801895694736020738605791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7867930463157347159070527 11801895694736020738605791)
  ·
    refine ⟨17702843542104031107908687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11801895694736020738605791 17702843542104031107908687)
    ·
      refine ⟨26554265313156046661863031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17702843542104031107908687 26554265313156046661863031)
      ·
        refine ⟨39831397969734069992794547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26554265313156046661863031 39831397969734069992794547)
        ·
          refine ⟨59747096954601104989191821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39831397969734069992794547 59747096954601104989191821)
          ·
            refine ⟨22405161357975414370946933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59747096954601104989191821 22405161357975414370946933)
            ·
              refine ⟨2100483877310195097276275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22405161357975414370946933 2100483877310195097276275)
              ·
                refine ⟨3150725815965292645914413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2100483877310195097276275 3150725815965292645914413)
                ·
                  refine ⟨1181522180986984742217905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3150725815965292645914413 1181522180986984742217905)
                  ·
                    refine ⟨886141635740238556663429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1181522180986984742217905 886141635740238556663429)
                    ·
                      refine ⟨166151556701294729374393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 886141635740238556663429 166151556701294729374393)
                      ·
                        rfl

theorem cell23_323579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 4].length) (baseStart_323579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323579 prefixEnd_323579 := by exact prefixLift 323579
  have htrace : WordTrace (prefixWord ++ tailWord_323579) baseStart_323579 baseEnd_323579 := by
    simpa [prefixWord, tailWord_323579, baseEnd_323579] using wordTrace_append hprefix tailTrace_323579
  have hstable : (prefixWord ++ tailWord_323579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323579).length < 2 ^ (prefixWord ++ tailWord_323579).sum := by decide
  have hdescent : baseEnd_323579 < baseStart_323579 := by decide
  rcases family_descends (prefixWord ++ tailWord_323579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323594 : List Nat := [3, 1, 2, 2, 4, 2, 2, 2, 1, 1, 3]
def baseStart_323594 : Nat := 118140960795 + 323594 * 2 ^ 59
def prefixEnd_323594 : Nat := 4983230072969 + 3 ^ 40 * 323594 * 2
def baseEnd_323594 : Nat := 166159258911112170686825

theorem tailTrace_323594 : CollatzResearch.WordTrace tailWord_323594 prefixEnd_323594 166159258911112170686825 := by
  unfold tailWord_323594
  simp only [CollatzResearch.WordTrace]
  refine ⟨2950610697420419575100459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7868295193121118866934557 2950610697420419575100459)
  ·
    refine ⟨4425916046130629362650689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2950610697420419575100459 4425916046130629362650689)
    ·
      refine ⟨3319437034597972021988017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4425916046130629362650689 3319437034597972021988017)
      ·
        refine ⟨2489577775948479016491013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3319437034597972021988017 2489577775948479016491013)
        ·
          refine ⟨466795832990339815592065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2489577775948479016491013 466795832990339815592065)
          ·
            refine ⟨350096874742754861694049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 466795832990339815592065 350096874742754861694049)
            ·
              refine ⟨262572656057066146270537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 350096874742754861694049 262572656057066146270537)
              ·
                refine ⟨196929492042799609702903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262572656057066146270537 196929492042799609702903)
                ·
                  refine ⟨295394238064199414554355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196929492042799609702903 295394238064199414554355)
                  ·
                    refine ⟨443091357096299121831533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 295394238064199414554355 443091357096299121831533)
                    ·
                      refine ⟨166159258911112170686825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 443091357096299121831533 166159258911112170686825)
                      ·
                        rfl

theorem cell23_323594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_323594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323594 prefixEnd_323594 := by exact prefixLift 323594
  have htrace : WordTrace (prefixWord ++ tailWord_323594) baseStart_323594 baseEnd_323594 := by
    simpa [prefixWord, tailWord_323594, baseEnd_323594] using wordTrace_append hprefix tailTrace_323594
  have hstable : (prefixWord ++ tailWord_323594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323594).length < 2 ^ (prefixWord ++ tailWord_323594).sum := by decide
  have hdescent : baseEnd_323594 < baseStart_323594 := by decide
  rcases family_descends (prefixWord ++ tailWord_323594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323599 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 3]
def baseStart_323599 : Nat := 118140960795 + 323599 * 2 ^ 59
def prefixEnd_323599 : Nat := 4983230072969 + 3 ^ 40 * 323599 * 2
def baseEnd_323599 : Nat := 166161826314384651124301

theorem tailTrace_323599 : CollatzResearch.WordTrace tailWord_323599 prefixEnd_323599 166161826314384651124301 := by
  unfold tailWord_323599
  simp only [CollatzResearch.WordTrace]
  refine ⟨11802625154663564154333851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7868416769775709436222567 11802625154663564154333851)
  ·
    refine ⟨17703937731995346231500777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11802625154663564154333851 17703937731995346231500777)
    ·
      refine ⟨13277953298996509673625583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17703937731995346231500777 13277953298996509673625583)
      ·
        refine ⟨19916929948494764510438375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13277953298996509673625583 19916929948494764510438375)
        ·
          refine ⟨29875394922742146765657563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19916929948494764510438375 29875394922742146765657563)
          ·
            refine ⟨44813092384113220148486345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29875394922742146765657563 44813092384113220148486345)
            ·
              refine ⟨33609819288084915111364759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44813092384113220148486345 33609819288084915111364759)
              ·
                refine ⟨50414728932127372667047139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33609819288084915111364759 50414728932127372667047139)
                ·
                  refine ⟨75622093398191059000570709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50414728932127372667047139 75622093398191059000570709)
                  ·
                    refine ⟨443098203505025736331469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 75622093398191059000570709 443098203505025736331469)
                    ·
                      refine ⟨166161826314384651124301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 443098203505025736331469 166161826314384651124301)
                      ·
                        rfl

theorem cell23_323599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 3].length) (baseStart_323599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323599 prefixEnd_323599 := by exact prefixLift 323599
  have htrace : WordTrace (prefixWord ++ tailWord_323599) baseStart_323599 baseEnd_323599 := by
    simpa [prefixWord, tailWord_323599, baseEnd_323599] using wordTrace_append hprefix tailTrace_323599
  have hstable : (prefixWord ++ tailWord_323599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323599).length < 2 ^ (prefixWord ++ tailWord_323599).sum := by decide
  have hdescent : baseEnd_323599 < baseStart_323599 := by decide
  rcases family_descends (prefixWord ++ tailWord_323599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323600 : List Nat := [2, 1, 1, 1, 1, 1, 1, 10, 1, 2, 2]
def baseStart_323600 : Nat := 118140960795 + 323600 * 2 ^ 59
def prefixEnd_323600 : Nat := 4983230072969 + 3 ^ 40 * 323600 * 2
def baseEnd_323600 : Nat := 166162339795039147211797

theorem tailTrace_323600 : CollatzResearch.WordTrace tailWord_323600 prefixEnd_323600 166162339795039147211797 := by
  unfold tailWord_323600
  simp only [CollatzResearch.WordTrace]
  refine ⟨5901330813829970662560127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7868441085106627550080169 5901330813829970662560127)
  ·
    refine ⟨8851996220744955993840191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5901330813829970662560127 8851996220744955993840191)
    ·
      refine ⟨13277994331117433990760287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8851996220744955993840191 13277994331117433990760287)
      ·
        refine ⟨19916991496676150986140431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13277994331117433990760287 19916991496676150986140431)
        ·
          refine ⟨29875487245014226479210647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19916991496676150986140431 29875487245014226479210647)
          ·
            refine ⟨44813230867521339718815971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29875487245014226479210647 44813230867521339718815971)
            ·
              refine ⟨67219846301282009578223957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44813230867521339718815971 67219846301282009578223957)
              ·
                refine ⟨196933143460787137436203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 67219846301282009578223957 196933143460787137436203)
                ·
                  refine ⟨295399715191180706154305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196933143460787137436203 295399715191180706154305)
                  ·
                    refine ⟨221549786393385529615729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 295399715191180706154305 221549786393385529615729)
                    ·
                      refine ⟨166162339795039147211797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221549786393385529615729 166162339795039147211797)
                      ·
                        rfl

theorem cell23_323600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 1, 2, 2].length) (baseStart_323600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323600 prefixEnd_323600 := by exact prefixLift 323600
  have htrace : WordTrace (prefixWord ++ tailWord_323600) baseStart_323600 baseEnd_323600 := by
    simpa [prefixWord, tailWord_323600, baseEnd_323600] using wordTrace_append hprefix tailTrace_323600
  have hstable : (prefixWord ++ tailWord_323600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323600).length < 2 ^ (prefixWord ++ tailWord_323600).sum := by decide
  have hdescent : baseEnd_323600 < baseStart_323600 := by decide
  rcases family_descends (prefixWord ++ tailWord_323600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323613 : List Nat := [1, 4, 2, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_323613 : Nat := 118140960795 + 323613 * 2 ^ 59
def prefixEnd_323613 : Nat := 4983230072969 + 3 ^ 40 * 323613 * 2
def baseEnd_323613 : Nat := 166169015043547596349237

theorem tailTrace_323613 : CollatzResearch.WordTrace tailWord_323613 prefixEnd_323613 166169015043547596349237 := by
  unfold tailWord_323613
  simp only [CollatzResearch.WordTrace]
  refine ⟨11803135776612844545343493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7868757184408563030228995 11803135776612844545343493)
  ·
    refine ⟨2213087958114908352251905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11803135776612844545343493 2213087958114908352251905)
    ·
      refine ⟨1659815968586181264188929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2213087958114908352251905 1659815968586181264188929)
      ·
        refine ⟨1244861976439635948141697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1659815968586181264188929 1244861976439635948141697)
        ·
          refine ⟨933646482329726961106273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1244861976439635948141697 933646482329726961106273)
          ·
            refine ⟨700234861747295220829705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 933646482329726961106273 700234861747295220829705)
            ·
              refine ⟨525176146310471415622279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700234861747295220829705 525176146310471415622279)
              ·
                refine ⟨787764219465707123433419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525176146310471415622279 787764219465707123433419)
                ·
                  refine ⟨1181646329198560685150129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 787764219465707123433419 1181646329198560685150129)
                  ·
                    refine ⟨886234746898920513862597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1181646329198560685150129 886234746898920513862597)
                    ·
                      refine ⟨166169015043547596349237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 886234746898920513862597 166169015043547596349237)
                      ·
                        rfl

theorem cell23_323613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_323613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323613 prefixEnd_323613 := by exact prefixLift 323613
  have htrace : WordTrace (prefixWord ++ tailWord_323613) baseStart_323613 baseEnd_323613 := by
    simpa [prefixWord, tailWord_323613, baseEnd_323613] using wordTrace_append hprefix tailTrace_323613
  have hstable : (prefixWord ++ tailWord_323613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323613).length < 2 ^ (prefixWord ++ tailWord_323613).sum := by decide
  have hdescent : baseEnd_323613 < baseStart_323613 := by decide
  rcases family_descends (prefixWord ++ tailWord_323613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323619 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 2, 7]
def baseStart_323619 : Nat := 118140960795 + 323619 * 2 ^ 59
def prefixEnd_323619 : Nat := 4983230072969 + 3 ^ 40 * 323619 * 2
def baseEnd_323619 : Nat := 55390698642491524291403

theorem tailTrace_323619 : CollatzResearch.WordTrace tailWord_323619 prefixEnd_323619 55390698642491524291403 := by
  unfold tailWord_323619
  simp only [CollatzResearch.WordTrace]
  refine ⟨11803354614591107570061911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7868903076394071713374607 11803354614591107570061911)
  ·
    refine ⟨17705031921886661355092867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11803354614591107570061911 17705031921886661355092867)
    ·
      refine ⟨26557547882829992032639301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17705031921886661355092867 26557547882829992032639301)
      ·
        refine ⟨4979540228030623506119869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26557547882829992032639301 4979540228030623506119869)
        ·
          refine ⟨1867327585511483814794951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4979540228030623506119869 1867327585511483814794951)
          ·
            refine ⟨2800991378267225722192427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1867327585511483814794951 2800991378267225722192427)
            ·
              refine ⟨4201487067400838583288641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2800991378267225722192427 4201487067400838583288641)
              ·
                refine ⟨3151115300550628937466481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4201487067400838583288641 3151115300550628937466481)
                ·
                  refine ⟨2363336475412971703099861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3151115300550628937466481 2363336475412971703099861)
                  ·
                    refine ⟨55390698642491524291403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2363336475412971703099861 55390698642491524291403)
                    ·
                      rfl

theorem cell23_323619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 7].length) (baseStart_323619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323619 prefixEnd_323619 := by exact prefixLift 323619
  have htrace : WordTrace (prefixWord ++ tailWord_323619) baseStart_323619 baseEnd_323619 := by
    simpa [prefixWord, tailWord_323619, baseEnd_323619] using wordTrace_append hprefix tailTrace_323619
  have hstable : (prefixWord ++ tailWord_323619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323619).length < 2 ^ (prefixWord ++ tailWord_323619).sum := by decide
  have hdescent : baseEnd_323619 < baseStart_323619 := by decide
  rcases family_descends (prefixWord ++ tailWord_323619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323643 : List Nat := [1, 1, 1, 1, 1, 2, 1, 9, 1, 3, 2]
def baseStart_323643 : Nat := 118140960795 + 323643 * 2 ^ 59
def prefixEnd_323643 : Nat := 4983230072969 + 3 ^ 40 * 323643 * 2
def baseEnd_323643 : Nat := 166184419463182478974099

theorem tailTrace_323643 : CollatzResearch.WordTrace tailWord_323643 prefixEnd_323643 166184419463182478974099 := by
  unfold tailWord_323643
  simp only [CollatzResearch.WordTrace]
  refine ⟨11804229966504159668935583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7869486644336106445957055 11804229966504159668935583)
  ·
    refine ⟨17706344949756239503403375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11804229966504159668935583 17706344949756239503403375)
    ·
      refine ⟨26559517424634359255105063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17706344949756239503403375 26559517424634359255105063)
      ·
        refine ⟨39839276136951538882657595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26559517424634359255105063 39839276136951538882657595)
        ·
          refine ⟨59758914205427308323986393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39839276136951538882657595 59758914205427308323986393)
          ·
            refine ⟨44819185654070481242989795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59758914205427308323986393 44819185654070481242989795)
            ·
              refine ⟨67228778481105721864484693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44819185654070481242989795 67228778481105721864484693)
              ·
                refine ⟨393918623912728839049715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 67228778481105721864484693 393918623912728839049715)
                ·
                  refine ⟨590877935869093258574573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 393918623912728839049715 590877935869093258574573)
                  ·
                    refine ⟨221579225950909971965465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 590877935869093258574573 221579225950909971965465)
                    ·
                      refine ⟨166184419463182478974099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221579225950909971965465 166184419463182478974099)
                      ·
                        rfl

theorem cell23_323643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 3, 2].length) (baseStart_323643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323643 prefixEnd_323643 := by exact prefixLift 323643
  have htrace : WordTrace (prefixWord ++ tailWord_323643) baseStart_323643 baseEnd_323643 := by
    simpa [prefixWord, tailWord_323643, baseEnd_323643] using wordTrace_append hprefix tailTrace_323643
  have hstable : (prefixWord ++ tailWord_323643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323643).length < 2 ^ (prefixWord ++ tailWord_323643).sum := by decide
  have hdescent : baseEnd_323643 < baseStart_323643 := by decide
  rcases family_descends (prefixWord ++ tailWord_323643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323659 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 5]
def baseStart_323659 : Nat := 118140960795 + 323659 * 2 ^ 59
def prefixEnd_323659 : Nat := 4983230072969 + 3 ^ 40 * 323659 * 2
def baseEnd_323659 : Nat := 166192635153654416374025

theorem tailTrace_323659 : CollatzResearch.WordTrace tailWord_323659 prefixEnd_323659 166192635153654416374025 := by
  unfold tailWord_323659
  simp only [CollatzResearch.WordTrace]
  refine ⟨11804813534446194401518031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7869875689630796267678687 11804813534446194401518031)
  ·
    refine ⟨17707220301669291602277047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11804813534446194401518031 17707220301669291602277047)
    ·
      refine ⟨26560830452503937403415571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17707220301669291602277047 26560830452503937403415571)
      ·
        refine ⟨39841245678755906105123357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26560830452503937403415571 39841245678755906105123357)
        ·
          refine ⟨14940467129533464789421259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39841245678755906105123357 14940467129533464789421259)
          ·
            refine ⟨22410700694300197184131889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14940467129533464789421259 22410700694300197184131889)
            ·
              refine ⟨16808025520725147888098917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22410700694300197184131889 16808025520725147888098917)
              ·
                refine ⟨3151504785135965229018547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16808025520725147888098917 3151504785135965229018547)
                ·
                  refine ⟨4727257177703947843527821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3151504785135965229018547 4727257177703947843527821)
                  ·
                    refine ⟨1772721441638980441322933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4727257177703947843527821 1772721441638980441322933)
                    ·
                      refine ⟨166192635153654416374025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1772721441638980441322933 166192635153654416374025)
                      ·
                        rfl

theorem cell23_323659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 5].length) (baseStart_323659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323659 prefixEnd_323659 := by exact prefixLift 323659
  have htrace : WordTrace (prefixWord ++ tailWord_323659) baseStart_323659 baseEnd_323659 := by
    simpa [prefixWord, tailWord_323659, baseEnd_323659] using wordTrace_append hprefix tailTrace_323659
  have hstable : (prefixWord ++ tailWord_323659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323659).length < 2 ^ (prefixWord ++ tailWord_323659).sum := by decide
  have hdescent : baseEnd_323659 < baseStart_323659 := by decide
  rcases family_descends (prefixWord ++ tailWord_323659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323677 : List Nat := [1, 4, 4, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_323677 : Nat := 118140960795 + 323677 * 2 ^ 59
def prefixEnd_323677 : Nat := 4983230072969 + 3 ^ 40 * 323677 * 2
def baseEnd_323677 : Nat := 166201877805435345948943

theorem tailTrace_323677 : CollatzResearch.WordTrace tailWord_323677 prefixEnd_323677 166201877805435345948943 := by
  unfold tailWord_323677
  simp only [CollatzResearch.WordTrace]
  refine ⟨11805470048380983475673285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7870313365587322317115523 11805470048380983475673285)
  ·
    refine ⟨2213525634071434401688741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11805470048380983475673285 2213525634071434401688741)
    ·
      refine ⟨415036056388393950316639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2213525634071434401688741 415036056388393950316639)
      ·
        refine ⟨622554084582590925474959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415036056388393950316639 622554084582590925474959)
        ·
          refine ⟨933831126873886388212439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622554084582590925474959 933831126873886388212439)
          ·
            refine ⟨1400746690310829582318659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933831126873886388212439 1400746690310829582318659)
            ·
              refine ⟨2101120035466244373477989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1400746690310829582318659 2101120035466244373477989)
              ·
                refine ⟨393960006649920820027123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2101120035466244373477989 393960006649920820027123)
                ·
                  refine ⟨590940009974881230040685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 393960006649920820027123 590940009974881230040685)
                  ·
                    refine ⟨221602503740580461265257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 590940009974881230040685 221602503740580461265257)
                    ·
                      refine ⟨166201877805435345948943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221602503740580461265257 166201877805435345948943)
                      ·
                        rfl

theorem cell23_323677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_323677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323677 prefixEnd_323677 := by exact prefixLift 323677
  have htrace : WordTrace (prefixWord ++ tailWord_323677) baseStart_323677 baseEnd_323677 := by
    simpa [prefixWord, tailWord_323677, baseEnd_323677] using wordTrace_append hprefix tailTrace_323677
  have hstable : (prefixWord ++ tailWord_323677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323677).length < 2 ^ (prefixWord ++ tailWord_323677).sum := by decide
  have hdescent : baseEnd_323677 < baseStart_323677 := by decide
  rcases family_descends (prefixWord ++ tailWord_323677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323679 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 9]
def baseStart_323679 : Nat := 118140960795 + 323679 * 2 ^ 59
def prefixEnd_323679 : Nat := 4983230072969 + 3 ^ 40 * 323679 * 2
def baseEnd_323679 : Nat := 18466989418527148680437

theorem tailTrace_323679 : CollatzResearch.WordTrace tailWord_323679 prefixEnd_323679 18466989418527148680437 := by
  unfold tailWord_323679
  simp only [CollatzResearch.WordTrace]
  refine ⟨11805542994373737817246091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7870361996249158544830727 11805542994373737817246091)
  ·
    refine ⟨17708314491560606725869137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11805542994373737817246091 17708314491560606725869137)
    ·
      refine ⟨13281235868670455044401853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17708314491560606725869137 13281235868670455044401853)
      ·
        refine ⟨4980463450751420641650695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13281235868670455044401853 4980463450751420641650695)
        ·
          refine ⟨7470695176127130962476043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4980463450751420641650695 7470695176127130962476043)
          ·
            refine ⟨11206042764190696443714065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7470695176127130962476043 11206042764190696443714065)
            ·
              refine ⟨8404532073143022332785549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11206042764190696443714065 8404532073143022332785549)
              ·
                refine ⟨3151699527428633374794581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8404532073143022332785549 3151699527428633374794581)
                ·
                  refine ⟨18466989418527148680437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3151699527428633374794581 18466989418527148680437)
                  ·
                    rfl

theorem cell23_323679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 9].length) (baseStart_323679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323679 prefixEnd_323679 := by exact prefixLift 323679
  have htrace : WordTrace (prefixWord ++ tailWord_323679) baseStart_323679 baseEnd_323679 := by
    simpa [prefixWord, tailWord_323679, baseEnd_323679] using wordTrace_append hprefix tailTrace_323679
  have hstable : (prefixWord ++ tailWord_323679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323679).length < 2 ^ (prefixWord ++ tailWord_323679).sum := by decide
  have hdescent : baseEnd_323679 < baseStart_323679 := by decide
  rcases family_descends (prefixWord ++ tailWord_323679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323699 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 6]
def baseStart_323699 : Nat := 118140960795 + 323699 * 2 ^ 59
def prefixEnd_323699 : Nat := 4983230072969 + 3 ^ 40 * 323699 * 2
def baseEnd_323699 : Nat := 166213174379834259873841

theorem tailTrace_323699 : CollatzResearch.WordTrace tailWord_323699 prefixEnd_323699 166213174379834259873841 := by
  unfold tailWord_323699
  simp only [CollatzResearch.WordTrace]
  refine ⟨11806272454301281232974151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7870848302867520821982767 11806272454301281232974151)
  ·
    refine ⟨17709408681451921849461227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11806272454301281232974151 17709408681451921849461227)
    ·
      refine ⟨26564113022177882774191841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17709408681451921849461227 26564113022177882774191841)
      ·
        refine ⟨19923084766633412080643881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26564113022177882774191841 19923084766633412080643881)
        ·
          refine ⟨14942313574975059060482911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19923084766633412080643881 14942313574975059060482911)
          ·
            refine ⟨22413470362462588590724367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14942313574975059060482911 22413470362462588590724367)
            ·
              refine ⟨33620205543693882886086551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22413470362462588590724367 33620205543693882886086551)
              ·
                refine ⟨50430308315540824329129827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33620205543693882886086551 50430308315540824329129827)
                ·
                  refine ⟨75645462473311236493694741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50430308315540824329129827 75645462473311236493694741)
                  ·
                    refine ⟨3545881053436464210641941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75645462473311236493694741 3545881053436464210641941)
                    ·
                      refine ⟨166213174379834259873841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3545881053436464210641941 166213174379834259873841)
                      ·
                        rfl

theorem cell23_323699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_323699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323699 prefixEnd_323699 := by exact prefixLift 323699
  have htrace : WordTrace (prefixWord ++ tailWord_323699) baseStart_323699 baseEnd_323699 := by
    simpa [prefixWord, tailWord_323699, baseEnd_323699] using wordTrace_append hprefix tailTrace_323699
  have hstable : (prefixWord ++ tailWord_323699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323699).length < 2 ^ (prefixWord ++ tailWord_323699).sum := by decide
  have hdescent : baseEnd_323699 < baseStart_323699 := by decide
  rcases family_descends (prefixWord ++ tailWord_323699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323743 : List Nat := [1, 1, 2, 6, 1, 1, 1, 3, 2, 5]
def baseStart_323743 : Nat := 118140960795 + 323743 * 2 ^ 59
def prefixEnd_323743 : Nat := 4983230072969 + 3 ^ 40 * 323743 * 2
def baseEnd_323743 : Nat := 55411922509544029241213

theorem tailTrace_323743 : CollatzResearch.WordTrace tailWord_323743 prefixEnd_323743 55411922509544029241213 := by
  unfold tailWord_323743
  simp only [CollatzResearch.WordTrace]
  refine ⟨11807877266141876747575883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7871918177427917831717255 11807877266141876747575883)
  ·
    refine ⟨17711815899212815121363825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11807877266141876747575883 17711815899212815121363825)
    ·
      refine ⟨13283861924409611341022869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17711815899212815121363825 13283861924409611341022869)
      ·
        refine ⟨622681027706700531610447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13283861924409611341022869 622681027706700531610447)
        ·
          refine ⟨934021541560050797415671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622681027706700531610447 934021541560050797415671)
          ·
            refine ⟨1401032312340076196123507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934021541560050797415671 1401032312340076196123507)
            ·
              refine ⟨2101548468510114294185261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1401032312340076196123507 2101548468510114294185261)
              ·
                refine ⟨788080675691292860319473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2101548468510114294185261 788080675691292860319473)
                ·
                  refine ⟨591060506768469645239605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 788080675691292860319473 591060506768469645239605)
                  ·
                    refine ⟨55411922509544029241213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 591060506768469645239605 55411922509544029241213)
                    ·
                      rfl

theorem cell23_323743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 5].length) (baseStart_323743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323743 prefixEnd_323743 := by exact prefixLift 323743
  have htrace : WordTrace (prefixWord ++ tailWord_323743) baseStart_323743 baseEnd_323743 := by
    simpa [prefixWord, tailWord_323743, baseEnd_323743] using wordTrace_append hprefix tailTrace_323743
  have hstable : (prefixWord ++ tailWord_323743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323743).length < 2 ^ (prefixWord ++ tailWord_323743).sum := by decide
  have hdescent : baseEnd_323743 < baseStart_323743 := by decide
  rcases family_descends (prefixWord ++ tailWord_323743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323763 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 2, 4, 2]
def baseStart_323763 : Nat := 118140960795 + 323763 * 2 ^ 59
def prefixEnd_323763 : Nat := 4983230072969 + 3 ^ 40 * 323763 * 2
def baseEnd_323763 : Nat := 166246037141722009473547

theorem tailTrace_323763 : CollatzResearch.WordTrace tailWord_323763 prefixEnd_323763 166246037141722009473547 := by
  unfold tailWord_323763
  simp only [CollatzResearch.WordTrace]
  refine ⟨11808606726069420163303943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7872404484046280108869295 11808606726069420163303943)
  ·
    refine ⟨17712910089104130244955915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11808606726069420163303943 17712910089104130244955915)
    ·
      refine ⟨26569365133656195367433873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17712910089104130244955915 26569365133656195367433873)
      ·
        refine ⟨19927023850242146525575405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26569365133656195367433873 19927023850242146525575405)
        ·
          refine ⟨7472633943840804947090777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19927023850242146525575405 7472633943840804947090777)
          ·
            refine ⟨5604475457880603710318083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7472633943840804947090777 5604475457880603710318083)
            ·
              refine ⟨8406713186820905565477125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5604475457880603710318083 8406713186820905565477125)
              ·
                refine ⟨1576258722528919793526961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8406713186820905565477125 1576258722528919793526961)
                ·
                  refine ⟨1182194041896689845145221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1576258722528919793526961 1182194041896689845145221)
                  ·
                    refine ⟨221661382855629345964729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1182194041896689845145221 221661382855629345964729)
                    ·
                      refine ⟨166246037141722009473547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221661382855629345964729 166246037141722009473547)
                      ·
                        rfl

theorem cell23_323763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 4, 2].length) (baseStart_323763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323763 prefixEnd_323763 := by exact prefixLift 323763
  have htrace : WordTrace (prefixWord ++ tailWord_323763) baseStart_323763 baseEnd_323763 := by
    simpa [prefixWord, tailWord_323763, baseEnd_323763] using wordTrace_append hprefix tailTrace_323763
  have hstable : (prefixWord ++ tailWord_323763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323763).length < 2 ^ (prefixWord ++ tailWord_323763).sum := by decide
  have hdescent : baseEnd_323763 < baseStart_323763 := by decide
  rcases family_descends (prefixWord ++ tailWord_323763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323773 : List Nat := [1, 4, 1, 2, 1, 1, 1, 5, 3, 4]
def baseStart_323773 : Nat := 118140960795 + 323773 * 2 ^ 59
def prefixEnd_323773 : Nat := 4983230072969 + 3 ^ 40 * 323773 * 2
def baseEnd_323773 : Nat := 55417057316088990116167

theorem tailTrace_323773 : CollatzResearch.WordTrace tailWord_323773 prefixEnd_323773 55417057316088990116167 := by
  unfold tailWord_323773
  simp only [CollatzResearch.WordTrace]
  refine ⟨11808971456033191871167973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7872647637355461247445315 11808971456033191871167973)
  ·
    refine ⟨2214182148006223475843995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11808971456033191871167973 2214182148006223475843995)
    ·
      refine ⟨3321273222009335213765993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2214182148006223475843995 3321273222009335213765993)
      ·
        refine ⟨2490954916507001410324495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3321273222009335213765993 2490954916507001410324495)
        ·
          refine ⟨3736432374760502115486743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2490954916507001410324495 3736432374760502115486743)
          ·
            refine ⟨5604648562140753173230115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3736432374760502115486743 5604648562140753173230115)
            ·
              refine ⟨8406972843211129759845173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5604648562140753173230115 8406972843211129759845173)
              ·
                refine ⟨788153704051043414985485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8406972843211129759845173 788153704051043414985485)
                ·
                  refine ⟨295557639019141280619557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 788153704051043414985485 295557639019141280619557)
                  ·
                    refine ⟨55417057316088990116167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 295557639019141280619557 55417057316088990116167)
                    ·
                      rfl

theorem cell23_323773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_323773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323773 prefixEnd_323773 := by exact prefixLift 323773
  have htrace : WordTrace (prefixWord ++ tailWord_323773) baseStart_323773 baseEnd_323773 := by
    simpa [prefixWord, tailWord_323773, baseEnd_323773] using wordTrace_append hprefix tailTrace_323773
  have hstable : (prefixWord ++ tailWord_323773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323773).length < 2 ^ (prefixWord ++ tailWord_323773).sum := by decide
  have hdescent : baseEnd_323773 < baseStart_323773 := by decide
  rcases family_descends (prefixWord ++ tailWord_323773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323780 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_323780 : Nat := 118140960795 + 323780 * 2 ^ 59
def prefixEnd_323780 : Nat := 4983230072969 + 3 ^ 40 * 323780 * 2
def baseEnd_323780 : Nat := 166254766312848442960969

theorem tailTrace_323780 : CollatzResearch.WordTrace tailWord_323780 prefixEnd_323780 166254766312848442960969 := by
  unfold tailWord_323780
  simp only [CollatzResearch.WordTrace]
  refine ⟨5904613383503916033336397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7872817844671888044448529 5904613383503916033336397)
  ·
    refine ⟨2214230018813968512501149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5904613383503916033336397 2214230018813968512501149)
    ·
      refine ⟨830336257055238192187931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2214230018813968512501149 830336257055238192187931)
      ·
        refine ⟨1245504385582857288281897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 830336257055238192187931 1245504385582857288281897)
        ·
          refine ⟨934128289187142966211423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1245504385582857288281897 934128289187142966211423)
          ·
            refine ⟨1401192433780714449317135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934128289187142966211423 1401192433780714449317135)
            ·
              refine ⟨2101788650671071673975703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1401192433780714449317135 2101788650671071673975703)
              ·
                refine ⟨3152682976006607510963555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2101788650671071673975703 3152682976006607510963555)
                ·
                  refine ⟨4729024464009911266445333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3152682976006607510963555 4729024464009911266445333)
                  ·
                    refine ⟨221673021750464590614625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4729024464009911266445333 221673021750464590614625)
                    ·
                      refine ⟨166254766312848442960969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221673021750464590614625 166254766312848442960969)
                      ·
                        rfl

theorem cell23_323780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_323780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323780 prefixEnd_323780 := by exact prefixLift 323780
  have htrace : WordTrace (prefixWord ++ tailWord_323780) baseStart_323780 baseEnd_323780 := by
    simpa [prefixWord, tailWord_323780, baseEnd_323780] using wordTrace_append hprefix tailTrace_323780
  have hstable : (prefixWord ++ tailWord_323780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323780).length < 2 ^ (prefixWord ++ tailWord_323780).sum := by decide
  have hdescent : baseEnd_323780 < baseStart_323780 := by decide
  rcases family_descends (prefixWord ++ tailWord_323780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323790 : List Nat := [4, 1, 1, 1, 4, 2, 1, 2, 3, 4]
def baseStart_323790 : Nat := 118140960795 + 323790 * 2 ^ 59
def prefixEnd_323790 : Nat := 4983230072969 + 3 ^ 40 * 323790 * 2
def baseEnd_323790 : Nat := 55419967039797801278641

theorem tailTrace_323790 : CollatzResearch.WordTrace tailWord_323790 prefixEnd_323790 55419967039797801278641 := by
  unfold tailWord_323790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1476198937121450471817103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7873060997981069183024549 1476198937121450471817103)
  ·
    refine ⟨2214298405682175707725655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1476198937121450471817103 2214298405682175707725655)
    ·
      refine ⟨3321447608523263561588483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2214298405682175707725655 3321447608523263561588483)
      ·
        refine ⟨4982171412784895342382725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3321447608523263561588483 4982171412784895342382725)
        ·
          refine ⟨934157139897167876696761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4982171412784895342382725 934157139897167876696761)
          ·
            refine ⟨700617854922875907522571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 934157139897167876696761 700617854922875907522571)
            ·
              refine ⟨1050926782384313861283857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700617854922875907522571 1050926782384313861283857)
              ·
                refine ⟨788195086788235395962893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1050926782384313861283857 788195086788235395962893)
                ·
                  refine ⟨295573157545588273486085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 788195086788235395962893 295573157545588273486085)
                  ·
                    refine ⟨55419967039797801278641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 295573157545588273486085 55419967039797801278641)
                    ·
                      rfl

theorem cell23_323790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_323790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323790 prefixEnd_323790 := by exact prefixLift 323790
  have htrace : WordTrace (prefixWord ++ tailWord_323790) baseStart_323790 baseEnd_323790 := by
    simpa [prefixWord, tailWord_323790, baseEnd_323790] using wordTrace_append hprefix tailTrace_323790
  have hstable : (prefixWord ++ tailWord_323790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323790).length < 2 ^ (prefixWord ++ tailWord_323790).sum := by decide
  have hdescent : baseEnd_323790 < baseStart_323790 := by decide
  rcases family_descends (prefixWord ++ tailWord_323790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323797 : List Nat := [1, 3, 2, 4, 2, 2, 1, 1, 2, 1, 4]
def baseStart_323797 : Nat := 118140960795 + 323797 * 2 ^ 59
def prefixEnd_323797 : Nat := 4983230072969 + 3 ^ 40 * 323797 * 2
def baseEnd_323797 : Nat := 166263495483974876448391

theorem tailTrace_323797 : CollatzResearch.WordTrace tailWord_323797 prefixEnd_323797 166263495483974876448391 := by
  unfold tailWord_323797
  simp only [CollatzResearch.WordTrace]
  refine ⟨11809846807946243970041645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7873231205297495980027763 11809846807946243970041645)
  ·
    refine ⟨4428692552979841488765617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11809846807946243970041645 4428692552979841488765617)
    ·
      refine ⟨3321519414734881116574213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4428692552979841488765617 3321519414734881116574213)
      ·
        refine ⟨622784890262790209357665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3321519414734881116574213 622784890262790209357665)
        ·
          refine ⟨467088667697092657018249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 622784890262790209357665 467088667697092657018249)
          ·
            refine ⟨350316500772819492763687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 467088667697092657018249 350316500772819492763687)
            ·
              refine ⟨525474751159229239145531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350316500772819492763687 525474751159229239145531)
              ·
                refine ⟨788212126738843858718297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525474751159229239145531 788212126738843858718297)
                ·
                  refine ⟨591159095054132894038723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 788212126738843858718297 591159095054132894038723)
                  ·
                    refine ⟨886738642581199341058085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 591159095054132894038723 886738642581199341058085)
                    ·
                      refine ⟨166263495483974876448391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 886738642581199341058085 166263495483974876448391)
                      ·
                        rfl

theorem cell23_323797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_323797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323797 prefixEnd_323797 := by exact prefixLift 323797
  have htrace : WordTrace (prefixWord ++ tailWord_323797) baseStart_323797 baseEnd_323797 := by
    simpa [prefixWord, tailWord_323797, baseEnd_323797] using wordTrace_append hprefix tailTrace_323797
  have hstable : (prefixWord ++ tailWord_323797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323797).length < 2 ^ (prefixWord ++ tailWord_323797).sum := by decide
  have hdescent : baseEnd_323797 < baseStart_323797 := by decide
  rcases family_descends (prefixWord ++ tailWord_323797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323800 : List Nat := [2, 1, 2, 2, 4, 1, 3, 1, 2, 2, 3]
def baseStart_323800 : Nat := 118140960795 + 323800 * 2 ^ 59
def prefixEnd_323800 : Nat := 4983230072969 + 3 ^ 40 * 323800 * 2
def baseEnd_323800 : Nat := 166265035925938364710877

theorem tailTrace_323800 : CollatzResearch.WordTrace tailWord_323800 prefixEnd_323800 166265035925938364710877 := by
  unfold tailWord_323800
  simp only [CollatzResearch.WordTrace]
  refine ⟨5904978113467687741200427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7873304151290250321600569 5904978113467687741200427)
  ·
    refine ⟨8857467170201531611800641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5904978113467687741200427 8857467170201531611800641)
    ·
      refine ⟨6643100377651148708850481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8857467170201531611800641 6643100377651148708850481)
      ·
        refine ⟨4982325283238361531637861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6643100377651148708850481 4982325283238361531637861)
        ·
          refine ⟨934185990607192787182099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4982325283238361531637861 934185990607192787182099)
          ·
            refine ⟨1401278985910789180773149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934185990607192787182099 1401278985910789180773149)
            ·
              refine ⟨525479619716545942789931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1401278985910789180773149 525479619716545942789931)
              ·
                refine ⟨788219429574818914184897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525479619716545942789931 788219429574818914184897)
                ·
                  refine ⟨591164572181114185638673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 788219429574818914184897 591164572181114185638673)
                  ·
                    refine ⟨443373429135835639229005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 591164572181114185638673 443373429135835639229005)
                    ·
                      refine ⟨166265035925938364710877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 443373429135835639229005 166265035925938364710877)
                      ·
                        rfl

theorem cell23_323800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_323800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323800 prefixEnd_323800 := by exact prefixLift 323800
  have htrace : WordTrace (prefixWord ++ tailWord_323800) baseStart_323800 baseEnd_323800 := by
    simpa [prefixWord, tailWord_323800, baseEnd_323800] using wordTrace_append hprefix tailTrace_323800
  have hstable : (prefixWord ++ tailWord_323800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323800).length < 2 ^ (prefixWord ++ tailWord_323800).sum := by decide
  have hdescent : baseEnd_323800 < baseStart_323800 := by decide
  rcases family_descends (prefixWord ++ tailWord_323800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323873 : List Nat := [1, 2, 3, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_323873 : Nat := 118140960795 + 323873 * 2 ^ 59
def prefixEnd_323873 : Nat := 4983230072969 + 3 ^ 40 * 323873 * 2
def baseEnd_323873 : Nat := 166302520013716579098041

theorem tailTrace_323873 : CollatzResearch.WordTrace tailWord_323873 prefixEnd_323873 166302520013716579098041 := by
  unfold tailWord_323873
  simp only [CollatzResearch.WordTrace]
  refine ⟨11812618755670908949808273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7875079170447272633205515 11812618755670908949808273)
  ·
    refine ⟨8859464066753181712356205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11812618755670908949808273 8859464066753181712356205)
    ·
      refine ⟨3322299025032443142133577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8859464066753181712356205 3322299025032443142133577)
      ·
        refine ⟨2491724268774332356600183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3322299025032443142133577 2491724268774332356600183)
        ·
          refine ⟨3737586403161498534900275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2491724268774332356600183 3737586403161498534900275)
          ·
            refine ⟨5606379604742247802350413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3737586403161498534900275 5606379604742247802350413)
            ·
              refine ⟨2102392351778342925881405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5606379604742247802350413 2102392351778342925881405)
              ·
                refine ⟨788397131916878597205527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2102392351778342925881405 788397131916878597205527)
                ·
                  refine ⟨1182595697875317895808291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788397131916878597205527 1182595697875317895808291)
                  ·
                    refine ⟨1773893546812976843712437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1182595697875317895808291 1773893546812976843712437)
                    ·
                      refine ⟨166302520013716579098041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1773893546812976843712437 166302520013716579098041)
                      ·
                        rfl

theorem cell23_323873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_323873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323873 prefixEnd_323873 := by exact prefixLift 323873
  have htrace : WordTrace (prefixWord ++ tailWord_323873) baseStart_323873 baseEnd_323873 := by
    simpa [prefixWord, tailWord_323873, baseEnd_323873] using wordTrace_append hprefix tailTrace_323873
  have hstable : (prefixWord ++ tailWord_323873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323873).length < 2 ^ (prefixWord ++ tailWord_323873).sum := by decide
  have hdescent : baseEnd_323873 < baseStart_323873 := by decide
  rcases family_descends (prefixWord ++ tailWord_323873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323887 : List Nat := [1, 1, 2, 1, 2, 1, 7, 1, 3, 2, 2]
def baseStart_323887 : Nat := 118140960795 + 323887 * 2 ^ 59
def prefixEnd_323887 : Nat := 4983230072969 + 3 ^ 40 * 323887 * 2
def baseEnd_323887 : Nat := 166309708742879524322977

theorem tailTrace_323887 : CollatzResearch.WordTrace tailWord_323887 prefixEnd_323887 166309708742879524322977 := by
  unfold tailWord_323887
  simp only [CollatzResearch.WordTrace]
  refine ⟨11813129377620189340817915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7875419585080126227211943 11813129377620189340817915)
  ·
    refine ⟨17719694066430284011226873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11813129377620189340817915 17719694066430284011226873)
    ·
      refine ⟨13289770549822713008420155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17719694066430284011226873 13289770549822713008420155)
      ·
        refine ⟨19934655824734069512630233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13289770549822713008420155 19934655824734069512630233)
        ·
          refine ⟨14950991868550552134472675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19934655824734069512630233 14950991868550552134472675)
          ·
            refine ⟨22426487802825828201709013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14950991868550552134472675 22426487802825828201709013)
            ·
              refine ⟨525620807878730348477555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 22426487802825828201709013 525620807878730348477555)
              ·
                refine ⟨788431211818095522716333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525620807878730348477555 788431211818095522716333)
                ·
                  refine ⟨295661704431785821018625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 788431211818095522716333 295661704431785821018625)
                  ·
                    refine ⟨221746278323839365763969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 295661704431785821018625 221746278323839365763969)
                    ·
                      refine ⟨166309708742879524322977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221746278323839365763969 166309708742879524322977)
                      ·
                        rfl

theorem cell23_323887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 2, 2].length) (baseStart_323887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323887 prefixEnd_323887 := by exact prefixLift 323887
  have htrace : WordTrace (prefixWord ++ tailWord_323887) baseStart_323887 baseEnd_323887 := by
    simpa [prefixWord, tailWord_323887, baseEnd_323887] using wordTrace_append hprefix tailTrace_323887
  have hstable : (prefixWord ++ tailWord_323887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323887).length < 2 ^ (prefixWord ++ tailWord_323887).sum := by decide
  have hdescent : baseEnd_323887 < baseStart_323887 := by decide
  rcases family_descends (prefixWord ++ tailWord_323887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323893 : List Nat := [1, 3, 3, 1, 2, 1, 4, 8]
def baseStart_323893 : Nat := 118140960795 + 323893 * 2 ^ 59
def prefixEnd_323893 : Nat := 4983230072969 + 3 ^ 40 * 323893 * 2
def baseEnd_323893 : Nat := 6159732949140981512887

theorem tailTrace_323893 : CollatzResearch.WordTrace tailWord_323893 prefixEnd_323893 6159732949140981512887 := by
  unfold tailWord_323893
  simp only [CollatzResearch.WordTrace]
  refine ⟨11813348215598452365536333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7875565477065634910357555 11813348215598452365536333)
  ·
    refine ⟨4430005580849419637076125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11813348215598452365536333 4430005580849419637076125)
    ·
      refine ⟨1661252092818532363903547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4430005580849419637076125 1661252092818532363903547)
      ·
        refine ⟨2491878139227798545855321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1661252092818532363903547 2491878139227798545855321)
        ·
          refine ⟨1868908604420848909391491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2491878139227798545855321 1868908604420848909391491)
          ·
            refine ⟨2803362906631273364087237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868908604420848909391491 2803362906631273364087237)
            ·
              refine ⟨525630544993363755766357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2803362906631273364087237 525630544993363755766357)
              ·
                refine ⟨6159732949140981512887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 525630544993363755766357 6159732949140981512887)
                ·
                  rfl

theorem cell23_323893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 8].length) (baseStart_323893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323893 prefixEnd_323893 := by exact prefixLift 323893
  have htrace : WordTrace (prefixWord ++ tailWord_323893) baseStart_323893 baseEnd_323893 := by
    simpa [prefixWord, tailWord_323893, baseEnd_323893] using wordTrace_append hprefix tailTrace_323893
  have hstable : (prefixWord ++ tailWord_323893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323893).length < 2 ^ (prefixWord ++ tailWord_323893).sum := by decide
  have hdescent : baseEnd_323893 < baseStart_323893 := by decide
  rcases family_descends (prefixWord ++ tailWord_323893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323897 : List Nat := [1, 2, 1, 6, 1, 2, 1, 3, 2, 4]
def baseStart_323897 : Nat := 118140960795 + 323897 * 2 ^ 59
def prefixEnd_323897 : Nat := 4983230072969 + 3 ^ 40 * 323897 * 2
def baseEnd_323897 : Nat := 55438281183141495065977

theorem tailTrace_323897 : CollatzResearch.WordTrace tailWord_323897 prefixEnd_323897 55438281183141495065977 := by
  unfold tailWord_323897
  simp only [CollatzResearch.WordTrace]
  refine ⟨11813494107583961048681945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7875662738389307365787963 11813494107583961048681945)
  ·
    refine ⟨8860120580687970786511459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11813494107583961048681945 8860120580687970786511459)
    ·
      refine ⟨13290180871031956179767189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8860120580687970786511459 13290180871031956179767189)
      ·
        refine ⟨622977228329622945926587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13290180871031956179767189 622977228329622945926587)
        ·
          refine ⟨934465842494434418889881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622977228329622945926587 934465842494434418889881)
          ·
            refine ⟨700849381870825814167411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 934465842494434418889881 700849381870825814167411)
            ·
              refine ⟨1051274072806238721251117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700849381870825814167411 1051274072806238721251117)
              ·
                refine ⟨394227777302339520469169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1051274072806238721251117 394227777302339520469169)
                ·
                  refine ⟨295670832976754640351877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394227777302339520469169 295670832976754640351877)
                  ·
                    refine ⟨55438281183141495065977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 295670832976754640351877 55438281183141495065977)
                    ·
                      rfl

theorem cell23_323897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 4].length) (baseStart_323897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323897 prefixEnd_323897 := by exact prefixLift 323897
  have htrace : WordTrace (prefixWord ++ tailWord_323897) baseStart_323897 baseEnd_323897 := by
    simpa [prefixWord, tailWord_323897, baseEnd_323897] using wordTrace_append hprefix tailTrace_323897
  have hstable : (prefixWord ++ tailWord_323897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323897).length < 2 ^ (prefixWord ++ tailWord_323897).sum := by decide
  have hdescent : baseEnd_323897 < baseStart_323897 := by decide
  rcases family_descends (prefixWord ++ tailWord_323897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323920 : List Nat := [2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 3]
def baseStart_323920 : Nat := 118140960795 + 323920 * 2 ^ 59
def prefixEnd_323920 : Nat := 4983230072969 + 3 ^ 40 * 323920 * 2
def baseEnd_323920 : Nat := 166326653604477895210325

theorem tailTrace_323920 : CollatzResearch.WordTrace tailWord_323920 prefixEnd_323920 166326653604477895210325 := by
  unfold tailWord_323920
  simp only [CollatzResearch.WordTrace]
  refine ⟨5907166493250317988384607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7876221991000423984512809 5907166493250317988384607)
  ·
    refine ⟨8860749739875476982576911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5907166493250317988384607 8860749739875476982576911)
    ·
      refine ⟨13291124609813215473865367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8860749739875476982576911 13291124609813215473865367)
      ·
        refine ⟨19936686914719823210798051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13291124609813215473865367 19936686914719823210798051)
        ·
          refine ⟨29905030372079734816197077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19936686914719823210798051 29905030372079734816197077)
          ·
            refine ⟨700899149345618784754619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 29905030372079734816197077 700899149345618784754619)
            ·
              refine ⟨1051348724018428177131929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700899149345618784754619 1051348724018428177131929)
              ·
                refine ⟨788511543013821132848947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1051348724018428177131929 788511543013821132848947)
                ·
                  refine ⟨1182767314520731699273421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788511543013821132848947 1182767314520731699273421)
                  ·
                    refine ⟨443537742945274387227533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1182767314520731699273421 443537742945274387227533)
                    ·
                      refine ⟨166326653604477895210325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 443537742945274387227533 166326653604477895210325)
                      ·
                        rfl

theorem cell23_323920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 3].length) (baseStart_323920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323920 prefixEnd_323920 := by exact prefixLift 323920
  have htrace : WordTrace (prefixWord ++ tailWord_323920) baseStart_323920 baseEnd_323920 := by
    simpa [prefixWord, tailWord_323920, baseEnd_323920] using wordTrace_append hprefix tailTrace_323920
  have hstable : (prefixWord ++ tailWord_323920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323920).length < 2 ^ (prefixWord ++ tailWord_323920).sum := by decide
  have hdescent : baseEnd_323920 < baseStart_323920 := by decide
  rcases family_descends (prefixWord ++ tailWord_323920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323924 : List Nat := [2, 4, 1, 1, 2, 3, 3, 1, 1, 2, 3]
def baseStart_323924 : Nat := 118140960795 + 323924 * 2 ^ 59
def prefixEnd_323924 : Nat := 4983230072969 + 3 ^ 40 * 323924 * 2
def baseEnd_323924 : Nat := 166328707527095879560307

theorem tailTrace_323924 : CollatzResearch.WordTrace tailWord_323924 prefixEnd_323924 166328707527095879560307 := by
  unfold tailWord_323924
  simp only [CollatzResearch.WordTrace]
  refine ⟨5907239439243072329957413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7876319252324096439943217 5907239439243072329957413)
  ·
    refine ⟨1107607394858076061867015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5907239439243072329957413 1107607394858076061867015)
    ·
      refine ⟨1661411092287114092800523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1107607394858076061867015 1661411092287114092800523)
      ·
        refine ⟨2492116638430671139200785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1661411092287114092800523 2492116638430671139200785)
        ·
          refine ⟨1869087478823003354400589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2492116638430671139200785 1869087478823003354400589)
          ·
            refine ⟨700907804558626257900221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1869087478823003354400589 700907804558626257900221)
            ·
              refine ⟨262840426709484846712583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 700907804558626257900221 262840426709484846712583)
              ·
                refine ⟨394260640064227270068875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262840426709484846712583 394260640064227270068875)
                ·
                  refine ⟨591390960096340905103313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 394260640064227270068875 591390960096340905103313)
                  ·
                    refine ⟨443543220072255678827485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 591390960096340905103313 443543220072255678827485)
                    ·
                      refine ⟨166328707527095879560307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 443543220072255678827485 166328707527095879560307)
                      ·
                        rfl

theorem cell23_323924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_323924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323924 prefixEnd_323924 := by exact prefixLift 323924
  have htrace : WordTrace (prefixWord ++ tailWord_323924) baseStart_323924 baseEnd_323924 := by
    simpa [prefixWord, tailWord_323924, baseEnd_323924] using wordTrace_append hprefix tailTrace_323924
  have hstable : (prefixWord ++ tailWord_323924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323924).length < 2 ^ (prefixWord ++ tailWord_323924).sum := by decide
  have hdescent : baseEnd_323924 < baseStart_323924 := by decide
  rcases family_descends (prefixWord ++ tailWord_323924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323938 : List Nat := [3, 3, 2, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_323938 : Nat := 118140960795 + 323938 * 2 ^ 59
def prefixEnd_323938 : Nat := 4983230072969 + 3 ^ 40 * 323938 * 2
def baseEnd_323938 : Nat := 166335896256258824785243

theorem tailTrace_323938 : CollatzResearch.WordTrace tailWord_323938 prefixEnd_323938 166335896256258824785243 := by
  unfold tailWord_323938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2953747375108856262731117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7876659666956950033949645 2953747375108856262731117)
  ·
    refine ⟨1107655265665821098524169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2953747375108856262731117 1107655265665821098524169)
    ·
      refine ⟨830741449249365823893127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1107655265665821098524169 830741449249365823893127)
      ·
        refine ⟨1246112173874048735839691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 830741449249365823893127 1246112173874048735839691)
        ·
          refine ⟨1869168260811073103759537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246112173874048735839691 1869168260811073103759537)
          ·
            refine ⟨1401876195608304827819653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1869168260811073103759537 1401876195608304827819653)
            ·
              refine ⟨262851786676557155216185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1401876195608304827819653 262851786676557155216185)
              ·
                refine ⟨197138840007417866412139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262851786676557155216185 197138840007417866412139)
                ·
                  refine ⟨295708260011126799618209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197138840007417866412139 295708260011126799618209)
                  ·
                    refine ⟨221781195008345099713657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 295708260011126799618209 221781195008345099713657)
                    ·
                      refine ⟨166335896256258824785243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221781195008345099713657 166335896256258824785243)
                      ·
                        rfl

theorem cell23_323938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_323938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323938 prefixEnd_323938 := by exact prefixLift 323938
  have htrace : WordTrace (prefixWord ++ tailWord_323938) baseStart_323938 baseEnd_323938 := by
    simpa [prefixWord, tailWord_323938, baseEnd_323938] using wordTrace_append hprefix tailTrace_323938
  have hstable : (prefixWord ++ tailWord_323938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323938).length < 2 ^ (prefixWord ++ tailWord_323938).sum := by decide
  have hdescent : baseEnd_323938 < baseStart_323938 := by decide
  rcases family_descends (prefixWord ++ tailWord_323938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323973 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 3, 4, 4]
def baseStart_323973 : Nat := 118140960795 + 323973 * 2 ^ 59
def prefixEnd_323973 : Nat := 4983230072969 + 3 ^ 40 * 323973 * 2
def baseEnd_323973 : Nat := 166353868079166187847581

theorem tailTrace_323973 : CollatzResearch.WordTrace tailWord_323973 prefixEnd_323973 166353868079166187847581 := by
  unfold tailWord_323973
  simp only [CollatzResearch.WordTrace]
  refine ⟨11816266055308626028448573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7877510703539084018965715 11816266055308626028448573)
  ·
    refine ⟨4431099770740734760668215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11816266055308626028448573 4431099770740734760668215)
    ·
      refine ⟨6646649656111102141002323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4431099770740734760668215 6646649656111102141002323)
      ·
        refine ⟨9969974484166653211503485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6646649656111102141002323 9969974484166653211503485)
        ·
          refine ⟨3738740431562494954313807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9969974484166653211503485 3738740431562494954313807)
          ·
            refine ⟨5608110647343742431470711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3738740431562494954313807 5608110647343742431470711)
            ·
              refine ⟨8412165971015613647206067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5608110647343742431470711 8412165971015613647206067)
              ·
                refine ⟨12618248956523420470809101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8412165971015613647206067 12618248956523420470809101)
                ·
                  refine ⟨4731843358696282676553413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12618248956523420470809101 4731843358696282676553413)
                  ·
                    refine ⟨887220629755553001853765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4731843358696282676553413 887220629755553001853765)
                    ·
                      refine ⟨166353868079166187847581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 887220629755553001853765 166353868079166187847581)
                      ·
                        rfl

theorem cell23_323973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_323973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323973 prefixEnd_323973 := by exact prefixLift 323973
  have htrace : WordTrace (prefixWord ++ tailWord_323973) baseStart_323973 baseEnd_323973 := by
    simpa [prefixWord, tailWord_323973, baseEnd_323973] using wordTrace_append hprefix tailTrace_323973
  have hstable : (prefixWord ++ tailWord_323973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323973).length < 2 ^ (prefixWord ++ tailWord_323973).sum := by decide
  have hdescent : baseEnd_323973 < baseStart_323973 := by decide
  rcases family_descends (prefixWord ++ tailWord_323973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323977 : List Nat := [1, 2, 1, 1, 6, 1, 2, 2, 1, 4, 2]
def baseStart_323977 : Nat := 118140960795 + 323977 * 2 ^ 59
def prefixEnd_323977 : Nat := 4983230072969 + 3 ^ 40 * 323977 * 2
def baseEnd_323977 : Nat := 166355922001784172197563

theorem tailTrace_323977 : CollatzResearch.WordTrace tailWord_323977 prefixEnd_323977 166355922001784172197563 := by
  unfold tailWord_323977
  simp only [CollatzResearch.WordTrace]
  refine ⟨11816411947294134711594185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7877607964862756474396123 11816411947294134711594185)
  ·
    refine ⟨8862308960470601033695639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11816411947294134711594185 8862308960470601033695639)
    ·
      refine ⟨13293463440705901550543459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8862308960470601033695639 13293463440705901550543459)
      ·
        refine ⟨19940195161058852325815189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13293463440705901550543459 19940195161058852325815189)
        ·
          refine ⟨934696648174633702772587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19940195161058852325815189 934696648174633702772587)
          ·
            refine ⟨1402044972261950554158881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934696648174633702772587 1402044972261950554158881)
            ·
              refine ⟨1051533729196462915619161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1402044972261950554158881 1051533729196462915619161)
              ·
                refine ⟨788650296897347186714371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1051533729196462915619161 788650296897347186714371)
                ·
                  refine ⟨1182975445346020780071557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788650296897347186714371 1182975445346020780071557)
                  ·
                    refine ⟨221807896002378896263417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1182975445346020780071557 221807896002378896263417)
                    ·
                      refine ⟨166355922001784172197563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221807896002378896263417 166355922001784172197563)
                      ·
                        rfl

theorem cell23_323977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 4, 2].length) (baseStart_323977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323977 prefixEnd_323977 := by exact prefixLift 323977
  have htrace : WordTrace (prefixWord ++ tailWord_323977) baseStart_323977 baseEnd_323977 := by
    simpa [prefixWord, tailWord_323977, baseEnd_323977] using wordTrace_append hprefix tailTrace_323977
  have hstable : (prefixWord ++ tailWord_323977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323977).length < 2 ^ (prefixWord ++ tailWord_323977).sum := by decide
  have hdescent : baseEnd_323977 < baseStart_323977 := by decide
  rcases family_descends (prefixWord ++ tailWord_323977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323988 : List Nat := [2, 4, 2, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_323988 : Nat := 118140960795 + 323988 * 2 ^ 59
def prefixEnd_323988 : Nat := 4983230072969 + 3 ^ 40 * 323988 * 2
def baseEnd_323988 : Nat := 166361570288983629160013

theorem tailTrace_323988 : CollatzResearch.WordTrace tailWord_323988 prefixEnd_323988 166361570288983629160013 := by
  unfold tailWord_323988
  simp only [CollatzResearch.WordTrace]
  refine ⟨5908406575127141795122309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7877875433502855726829745 5908406575127141795122309)
  ·
    refine ⟨1107826232836339086585433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5908406575127141795122309 1107826232836339086585433)
    ·
      refine ⟨830869674627254314939075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1107826232836339086585433 830869674627254314939075)
      ·
        refine ⟨1246304511940881472408613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 830869674627254314939075 1246304511940881472408613)
        ·
          refine ⟨233682095988915276076615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1246304511940881472408613 233682095988915276076615)
          ·
            refine ⟨350523143983372914114923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233682095988915276076615 350523143983372914114923)
            ·
              refine ⟨525784715975059371172385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350523143983372914114923 525784715975059371172385)
              ·
                refine ⟨394338536981294528379289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 525784715975059371172385 394338536981294528379289)
                ·
                  refine ⟨295753902735970896284467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394338536981294528379289 295753902735970896284467)
                  ·
                    refine ⟨443630854103956344426701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 295753902735970896284467 443630854103956344426701)
                    ·
                      refine ⟨166361570288983629160013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 443630854103956344426701 166361570288983629160013)
                      ·
                        rfl

theorem cell23_323988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_323988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323988 prefixEnd_323988 := by exact prefixLift 323988
  have htrace : WordTrace (prefixWord ++ tailWord_323988) baseStart_323988 baseEnd_323988 := by
    simpa [prefixWord, tailWord_323988, baseEnd_323988] using wordTrace_append hprefix tailTrace_323988
  have hstable : (prefixWord ++ tailWord_323988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323988).length < 2 ^ (prefixWord ++ tailWord_323988).sum := by decide
  have hdescent : baseEnd_323988 < baseStart_323988 := by decide
  rcases family_descends (prefixWord ++ tailWord_323988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323994 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2]
def baseStart_323994 : Nat := 118140960795 + 323994 * 2 ^ 59
def prefixEnd_323994 : Nat := 4983230072969 + 3 ^ 40 * 323994 * 2
def baseEnd_323994 : Nat := 166364651172910605684985

theorem tailTrace_323994 : CollatzResearch.WordTrace tailWord_323994 prefixEnd_323994 166364651172910605684985 := by
  unfold tailWord_323994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2954257997058136653740759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7878021325488364409975357 2954257997058136653740759)
  ·
    refine ⟨4431386995587204980611139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2954257997058136653740759 4431386995587204980611139)
    ·
      refine ⟨6647080493380807470916709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4431386995587204980611139 6647080493380807470916709)
      ·
        refine ⟨1246327592508901400796883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6647080493380807470916709 1246327592508901400796883)
        ·
          refine ⟨1869491388763352101195325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246327592508901400796883 1869491388763352101195325)
          ·
            refine ⟨701059270786257037948247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1869491388763352101195325 701059270786257037948247)
            ·
              refine ⟨1051588906179385556922371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701059270786257037948247 1051588906179385556922371)
              ·
                refine ⟨1577383359269078335383557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051588906179385556922371 1577383359269078335383557)
                ·
                  refine ⟨295759379862952187884417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1577383359269078335383557 295759379862952187884417)
                  ·
                    refine ⟨221819534897214140913313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 295759379862952187884417 221819534897214140913313)
                    ·
                      refine ⟨166364651172910605684985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221819534897214140913313 166364651172910605684985)
                      ·
                        rfl

theorem cell23_323994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_323994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_323994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_323994 prefixEnd_323994 := by exact prefixLift 323994
  have htrace : WordTrace (prefixWord ++ tailWord_323994) baseStart_323994 baseEnd_323994 := by
    simpa [prefixWord, tailWord_323994, baseEnd_323994] using wordTrace_append hprefix tailTrace_323994
  have hstable : (prefixWord ++ tailWord_323994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323994).length < 2 ^ (prefixWord ++ tailWord_323994).sum := by decide
  have hdescent : baseEnd_323994 < baseStart_323994 := by decide
  rcases family_descends (prefixWord ++ tailWord_323994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324000 : List Nat := [2, 1, 1, 4, 1, 4, 2, 1, 7]
def baseStart_324000 : Nat := 118140960795 + 324000 * 2 ^ 59
def prefixEnd_324000 : Nat := 4983230072969 + 3 ^ 40 * 324000 * 2
def baseEnd_324000 : Nat := 18485303561870842467773

theorem tailTrace_324000 : CollatzResearch.WordTrace tailWord_324000 prefixEnd_324000 18485303561870842467773 := by
  unfold tailWord_324000
  simp only [CollatzResearch.WordTrace]
  refine ⟨5908625413105404819840727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7878167217473873093120969 5908625413105404819840727)
  ·
    refine ⟨8862938119658107229761091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5908625413105404819840727 8862938119658107229761091)
    ·
      refine ⟨13294407179487160844641637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8862938119658107229761091 13294407179487160844641637)
      ·
        refine ⟨2492701346153842658370307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13294407179487160844641637 2492701346153842658370307)
        ·
          refine ⟨3739052019230763987555461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2492701346153842658370307 3739052019230763987555461)
          ·
            refine ⟨701072253605768247666649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3739052019230763987555461 701072253605768247666649)
            ·
              refine ⟨525804190204326185749987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 701072253605768247666649 525804190204326185749987)
              ·
                refine ⟨788706285306489278624981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525804190204326185749987 788706285306489278624981)
                ·
                  refine ⟨18485303561870842467773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 788706285306489278624981 18485303561870842467773)
                  ·
                    rfl

theorem cell23_324000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 7].length) (baseStart_324000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324000 prefixEnd_324000 := by exact prefixLift 324000
  have htrace : WordTrace (prefixWord ++ tailWord_324000) baseStart_324000 baseEnd_324000 := by
    simpa [prefixWord, tailWord_324000, baseEnd_324000] using wordTrace_append hprefix tailTrace_324000
  have hstable : (prefixWord ++ tailWord_324000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324000).length < 2 ^ (prefixWord ++ tailWord_324000).sum := by decide
  have hdescent : baseEnd_324000 < baseStart_324000 := by decide
  rcases family_descends (prefixWord ++ tailWord_324000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324030 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_324030 : Nat := 118140960795 + 324030 * 2 ^ 59
def prefixEnd_324030 : Nat := 4983230072969 + 3 ^ 40 * 324030 * 2
def baseEnd_324030 : Nat := 55461045492157488278273

theorem tailTrace_324030 : CollatzResearch.WordTrace tailWord_324030 prefixEnd_324030 55461045492157488278273 := by
  unfold tailWord_324030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1477293127012765595409193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7878896677401416508849029 1477293127012765595409193)
  ·
    refine ⟨1107969845259574196556895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1477293127012765595409193 1107969845259574196556895)
    ·
      refine ⟨1661954767889361294835343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1107969845259574196556895 1661954767889361294835343)
      ·
        refine ⟨2492932151834041942253015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1661954767889361294835343 2492932151834041942253015)
        ·
          refine ⟨3739398227751062913379523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2492932151834041942253015 3739398227751062913379523)
          ·
            refine ⟨5609097341626594370069285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3739398227751062913379523 5609097341626594370069285)
            ·
              refine ⟨1051705751554986444387991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5609097341626594370069285 1051705751554986444387991)
              ·
                refine ⟨1577558627332479666581987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051705751554986444387991 1577558627332479666581987)
                ·
                  refine ⟨2366337940998719499872981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1577558627332479666581987 2366337940998719499872981)
                  ·
                    refine ⟨55461045492157488278273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2366337940998719499872981 55461045492157488278273)
                    ·
                      rfl

theorem cell23_324030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_324030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324030 prefixEnd_324030 := by exact prefixLift 324030
  have htrace : WordTrace (prefixWord ++ tailWord_324030) baseStart_324030 baseEnd_324030 := by
    simpa [prefixWord, tailWord_324030, baseEnd_324030] using wordTrace_append hprefix tailTrace_324030
  have hstable : (prefixWord ++ tailWord_324030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324030).length < 2 ^ (prefixWord ++ tailWord_324030).sum := by decide
  have hdescent : baseEnd_324030 < baseStart_324030 := by decide
  rcases family_descends (prefixWord ++ tailWord_324030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324054 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_324054 : Nat := 118140960795 + 324054 * 2 ^ 59
def prefixEnd_324054 : Nat := 4983230072969 + 3 ^ 40 * 324054 * 2
def baseEnd_324054 : Nat := 166395460012180370934709

theorem tailTrace_324054 : CollatzResearch.WordTrace tailWord_324054 prefixEnd_324054 166395460012180370934709 := by
  unfold tailWord_324054
  simp only [CollatzResearch.WordTrace]
  refine ⟨738701273000948553884201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7879480245343451241431477 738701273000948553884201)
  ·
    refine ⟨554025954750711415413151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 738701273000948553884201 554025954750711415413151)
    ·
      refine ⟨831038932126067123119727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 554025954750711415413151 831038932126067123119727)
      ·
        refine ⟨1246558398189100684679591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831038932126067123119727 1246558398189100684679591)
        ·
          refine ⟨1869837597283651027019387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246558398189100684679591 1869837597283651027019387)
          ·
            refine ⟨2804756395925476540529081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869837597283651027019387 2804756395925476540529081)
            ·
              refine ⟨2103567296944107405396811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2804756395925476540529081 2103567296944107405396811)
              ·
                refine ⟨3155350945416161108095217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2103567296944107405396811 3155350945416161108095217)
                ·
                  refine ⟨2366513209062120831071413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3155350945416161108095217 2366513209062120831071413)
                  ·
                    refine ⟨221860613349573827912945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2366513209062120831071413 221860613349573827912945)
                    ·
                      refine ⟨166395460012180370934709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221860613349573827912945 166395460012180370934709)
                      ·
                        rfl

theorem cell23_324054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_324054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324054 prefixEnd_324054 := by exact prefixLift 324054
  have htrace : WordTrace (prefixWord ++ tailWord_324054) baseStart_324054 baseEnd_324054 := by
    simpa [prefixWord, tailWord_324054, baseEnd_324054] using wordTrace_append hprefix tailTrace_324054
  have hstable : (prefixWord ++ tailWord_324054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324054).length < 2 ^ (prefixWord ++ tailWord_324054).sum := by decide
  have hdescent : baseEnd_324054 < baseStart_324054 := by decide
  rcases family_descends (prefixWord ++ tailWord_324054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324073 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 10]
def baseStart_324073 : Nat := 118140960795 + 324073 * 2 ^ 59
def prefixEnd_324073 : Nat := 4983230072969 + 3 ^ 40 * 324073 * 2
def baseEnd_324073 : Nat := 18489468460512866288569

theorem tailTrace_324073 : CollatzResearch.WordTrace tailWord_324073 prefixEnd_324073 18489468460512866288569 := by
  unfold tailWord_324073
  simp only [CollatzResearch.WordTrace]
  refine ⟨11819913354946343107088873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7879942236630895404725915 11819913354946343107088873)
  ·
    refine ⟨8864935016209757330316655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11819913354946343107088873 8864935016209757330316655)
    ·
      refine ⟨13297402524314635995474983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8864935016209757330316655 13297402524314635995474983)
      ·
        refine ⟨19946103786471953993212475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13297402524314635995474983 19946103786471953993212475)
        ·
          refine ⟨29919155679707930989818713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19946103786471953993212475 29919155679707930989818713)
          ·
            refine ⟨22439366759780948242364035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29919155679707930989818713 22439366759780948242364035)
            ·
              refine ⟨33659050139671422363546053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22439366759780948242364035 33659050139671422363546053)
              ·
                refine ⟨6311071901188391693164885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33659050139671422363546053 6311071901188391693164885)
                ·
                  refine ⟨18489468460512866288569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 6311071901188391693164885 18489468460512866288569)
                  ·
                    rfl

theorem cell23_324073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 10].length) (baseStart_324073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324073 prefixEnd_324073 := by exact prefixLift 324073
  have htrace : WordTrace (prefixWord ++ tailWord_324073) baseStart_324073 baseEnd_324073 := by
    simpa [prefixWord, tailWord_324073, baseEnd_324073] using wordTrace_append hprefix tailTrace_324073
  have hstable : (prefixWord ++ tailWord_324073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324073).length < 2 ^ (prefixWord ++ tailWord_324073).sum := by decide
  have hdescent : baseEnd_324073 < baseStart_324073 := by decide
  rcases family_descends (prefixWord ++ tailWord_324073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324107 : List Nat := [1, 1, 1, 1, 7, 2, 2, 2, 6]
def baseStart_324107 : Nat := 118140960795 + 324107 * 2 ^ 59
def prefixEnd_324107 : Nat := 4983230072969 + 3 ^ 40 * 324107 * 2
def baseEnd_324107 : Nat := 18491408276318740396885

theorem tailTrace_324107 : CollatzResearch.WordTrace tailWord_324107 prefixEnd_324107 18491408276318740396885 := by
  unfold tailWord_324107
  simp only [CollatzResearch.WordTrace]
  refine ⟨11821153436823166913826575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7880768957882111275884383 11821153436823166913826575)
  ·
    refine ⟨17731730155234750370739863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11821153436823166913826575 17731730155234750370739863)
    ·
      refine ⟨26597595232852125556109795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17731730155234750370739863 26597595232852125556109795)
      ·
        refine ⟨39896392849278188334164693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26597595232852125556109795 39896392849278188334164693)
        ·
          refine ⟨935071707404957539081985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 39896392849278188334164693 935071707404957539081985)
          ·
            refine ⟨701303780553718154311489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 935071707404957539081985 701303780553718154311489)
            ·
              refine ⟨525977835415288615733617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 701303780553718154311489 525977835415288615733617)
              ·
                refine ⟨394483376561466461800213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 525977835415288615733617 394483376561466461800213)
                ·
                  refine ⟨18491408276318740396885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 394483376561466461800213 18491408276318740396885)
                  ·
                    rfl

theorem cell23_324107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 6].length) (baseStart_324107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324107 prefixEnd_324107 := by exact prefixLift 324107
  have htrace : WordTrace (prefixWord ++ tailWord_324107) baseStart_324107 baseEnd_324107 := by
    simpa [prefixWord, tailWord_324107, baseEnd_324107] using wordTrace_append hprefix tailTrace_324107
  have hstable : (prefixWord ++ tailWord_324107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324107).length < 2 ^ (prefixWord ++ tailWord_324107).sum := by decide
  have hdescent : baseEnd_324107 < baseStart_324107 := by decide
  rcases family_descends (prefixWord ++ tailWord_324107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324127 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 1, 5, 2]
def baseStart_324127 : Nat := 118140960795 + 324127 * 2 ^ 59
def prefixEnd_324127 : Nat := 4983230072969 + 3 ^ 40 * 324127 * 2
def baseEnd_324127 : Nat := 166432944099958585321873

theorem tailTrace_324127 : CollatzResearch.WordTrace tailWord_324127 prefixEnd_324127 166432944099958585321873 := by
  unfold tailWord_324127
  simp only [CollatzResearch.WordTrace]
  refine ⟨11821882896750710329554635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7881255264500473553036423 11821882896750710329554635)
  ·
    refine ⟨17732824345126065494331953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11821882896750710329554635 17732824345126065494331953)
    ·
      refine ⟨13299618258844549120748965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17732824345126065494331953 13299618258844549120748965)
      ·
        refine ⟨2493678423533352960140431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13299618258844549120748965 2493678423533352960140431)
        ·
          refine ⟨3740517635300029440210647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2493678423533352960140431 3740517635300029440210647)
          ·
            refine ⟨5610776452950044160315971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3740517635300029440210647 5610776452950044160315971)
            ·
              refine ⟨8416164679425066240473957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5610776452950044160315971 8416164679425066240473957)
              ·
                refine ⟨1578030877392199920088867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8416164679425066240473957 1578030877392199920088867)
                ·
                  refine ⟨2367046316088299880133301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1578030877392199920088867 2367046316088299880133301)
                  ·
                    refine ⟨221910592133278113762497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2367046316088299880133301 221910592133278113762497)
                    ·
                      refine ⟨166432944099958585321873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221910592133278113762497 166432944099958585321873)
                      ·
                        rfl

theorem cell23_324127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_324127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324127 prefixEnd_324127 := by exact prefixLift 324127
  have htrace : WordTrace (prefixWord ++ tailWord_324127) baseStart_324127 baseEnd_324127 := by
    simpa [prefixWord, tailWord_324127, baseEnd_324127] using wordTrace_append hprefix tailTrace_324127
  have hstable : (prefixWord ++ tailWord_324127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324127).length < 2 ^ (prefixWord ++ tailWord_324127).sum := by decide
  have hdescent : baseEnd_324127 < baseStart_324127 := by decide
  rcases family_descends (prefixWord ++ tailWord_324127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324130 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_324130 : Nat := 118140960795 + 324130 * 2 ^ 59
def prefixEnd_324130 : Nat := 4983230072969 + 3 ^ 40 * 324130 * 2
def baseEnd_324130 : Nat := 166434484541922073584359

theorem tailTrace_324130 : CollatzResearch.WordTrace tailWord_324130 prefixEnd_324130 166434484541922073584359 := by
  unfold tailWord_324130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2955498078934960460478461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7881328210493227894609229 2955498078934960460478461)
  ·
    refine ⟨1108311779600610172679423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2955498078934960460478461 1108311779600610172679423)
    ·
      refine ⟨1662467669400915259019135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1108311779600610172679423 1662467669400915259019135)
      ·
        refine ⟨2493701504101372888528703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1662467669400915259019135 2493701504101372888528703)
        ·
          refine ⟨3740552256152059332793055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2493701504101372888528703 3740552256152059332793055)
          ·
            refine ⟨5610828384228088999189583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3740552256152059332793055 5610828384228088999189583)
            ·
              refine ⟨8416242576342133498784375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5610828384228088999189583 8416242576342133498784375)
              ·
                refine ⟨12624363864513200248176563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8416242576342133498784375 12624363864513200248176563)
                ·
                  refine ⟨18936545796769800372264845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12624363864513200248176563 18936545796769800372264845)
                  ·
                    refine ⟨7101204673788675139599317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18936545796769800372264845 7101204673788675139599317)
                    ·
                      refine ⟨166434484541922073584359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7101204673788675139599317 166434484541922073584359)
                      ·
                        rfl

theorem cell23_324130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_324130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324130 prefixEnd_324130 := by exact prefixLift 324130
  have htrace : WordTrace (prefixWord ++ tailWord_324130) baseStart_324130 baseEnd_324130 := by
    simpa [prefixWord, tailWord_324130, baseEnd_324130] using wordTrace_append hprefix tailTrace_324130
  have hstable : (prefixWord ++ tailWord_324130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324130).length < 2 ^ (prefixWord ++ tailWord_324130).sum := by decide
  have hdescent : baseEnd_324130 < baseStart_324130 := by decide
  rcases family_descends (prefixWord ++ tailWord_324130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324144 : List Nat := [2, 1, 1, 1, 2, 3, 5, 1, 2, 3, 2]
def baseStart_324144 : Nat := 118140960795 + 324144 * 2 ^ 59
def prefixEnd_324144 : Nat := 4983230072969 + 3 ^ 40 * 324144 * 2
def baseEnd_324144 : Nat := 166441673271085018809295

theorem tailTrace_324144 : CollatzResearch.WordTrace tailWord_324144 prefixEnd_324144 166441673271085018809295 := by
  unfold tailWord_324144
  simp only [CollatzResearch.WordTrace]
  refine ⟨5911251468844561116461743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7881668625126081488615657 5911251468844561116461743)
  ·
    refine ⟨8866877203266841674692615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5911251468844561116461743 8866877203266841674692615)
    ·
      refine ⟨13300315804900262512038923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8866877203266841674692615 13300315804900262512038923)
      ·
        refine ⟨19950473707350393768058385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13300315804900262512038923 19950473707350393768058385)
        ·
          refine ⟨14962855280512795326043789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19950473707350393768058385 14962855280512795326043789)
          ·
            refine ⟨5611070730192298247266421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14962855280512795326043789 5611070730192298247266421)
            ·
              refine ⟨526037880955527960681227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5611070730192298247266421 526037880955527960681227)
              ·
                refine ⟨789056821433291941021841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526037880955527960681227 789056821433291941021841)
                ·
                  refine ⟨591792616074968955766381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 789056821433291941021841 591792616074968955766381)
                  ·
                    refine ⟨221922231028113358412393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 591792616074968955766381 221922231028113358412393)
                    ·
                      refine ⟨166441673271085018809295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221922231028113358412393 166441673271085018809295)
                      ·
                        rfl

theorem cell23_324144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 2, 3, 2].length) (baseStart_324144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324144 prefixEnd_324144 := by exact prefixLift 324144
  have htrace : WordTrace (prefixWord ++ tailWord_324144) baseStart_324144 baseEnd_324144 := by
    simpa [prefixWord, tailWord_324144, baseEnd_324144] using wordTrace_append hprefix tailTrace_324144
  have hstable : (prefixWord ++ tailWord_324144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324144).length < 2 ^ (prefixWord ++ tailWord_324144).sum := by decide
  have hdescent : baseEnd_324144 < baseStart_324144 := by decide
  rcases family_descends (prefixWord ++ tailWord_324144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324151 : List Nat := [1, 1, 3, 1, 2, 3, 4, 3, 1, 1, 3]
def baseStart_324151 : Nat := 118140960795 + 324151 * 2 ^ 59
def prefixEnd_324151 : Nat := 4983230072969 + 3 ^ 40 * 324151 * 2
def baseEnd_324151 : Nat := 166445267635666491421763

theorem tailTrace_324151 : CollatzResearch.WordTrace tailWord_324151 prefixEnd_324151 166445267635666491421763 := by
  unfold tailWord_324151
  simp only [CollatzResearch.WordTrace]
  refine ⟨11822758248663762428428307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7881838832442508285618871 11822758248663762428428307)
  ·
    refine ⟨17734137372995643642642461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11822758248663762428428307 17734137372995643642642461)
    ·
      refine ⟨6650301514873366365990923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17734137372995643642642461 6650301514873366365990923)
      ·
        refine ⟨9975452272310049548986385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6650301514873366365990923 9975452272310049548986385)
        ·
          refine ⟨7481589204232537161739789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9975452272310049548986385 7481589204232537161739789)
          ·
            refine ⟨2805595951587201435652421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7481589204232537161739789 2805595951587201435652421)
            ·
              refine ⟨526049240922600269184829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2805595951587201435652421 526049240922600269184829)
              ·
                refine ⟨197268465345975100944311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 526049240922600269184829 197268465345975100944311)
                ·
                  refine ⟨295902698018962651416467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197268465345975100944311 295902698018962651416467)
                  ·
                    refine ⟨443854047028443977124701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 295902698018962651416467 443854047028443977124701)
                    ·
                      refine ⟨166445267635666491421763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 443854047028443977124701 166445267635666491421763)
                      ·
                        rfl

theorem cell23_324151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 1, 1, 3].length) (baseStart_324151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324151 prefixEnd_324151 := by exact prefixLift 324151
  have htrace : WordTrace (prefixWord ++ tailWord_324151) baseStart_324151 baseEnd_324151 := by
    simpa [prefixWord, tailWord_324151, baseEnd_324151] using wordTrace_append hprefix tailTrace_324151
  have hstable : (prefixWord ++ tailWord_324151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324151).length < 2 ^ (prefixWord ++ tailWord_324151).sum := by decide
  have hdescent : baseEnd_324151 < baseStart_324151 := by decide
  rcases family_descends (prefixWord ++ tailWord_324151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324154 : List Nat := [3, 1, 1, 1, 3, 3, 4, 1, 1, 5]
def baseStart_324154 : Nat := 118140960795 + 324154 * 2 ^ 59
def prefixEnd_324154 : Nat := 4983230072969 + 3 ^ 40 * 324154 * 2
def baseEnd_324154 : Nat := 55482269359209993228083

theorem tailTrace_324154 : CollatzResearch.WordTrace tailWord_324154 prefixEnd_324154 55482269359209993228083 := by
  unfold tailWord_324154
  simp only [CollatzResearch.WordTrace]
  refine ⟨2955716916913223485196879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7881911778435262627191677 2955716916913223485196879)
  ·
    refine ⟨4433575375369835227795319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2955716916913223485196879 4433575375369835227795319)
    ·
      refine ⟨6650363063054752841692979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4433575375369835227795319 6650363063054752841692979)
      ·
        refine ⟨9975544594582129262539469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6650363063054752841692979 9975544594582129262539469)
        ·
          refine ⟨3740829222968298473452301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9975544594582129262539469 3740829222968298473452301)
          ·
            refine ⟨1402810958613111927544613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3740829222968298473452301 1402810958613111927544613)
            ·
              refine ⟨263027054739958486414615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1402810958613111927544613 263027054739958486414615)
              ·
                refine ⟨394540582109937729621923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263027054739958486414615 394540582109937729621923)
                ·
                  refine ⟨591810873164906594432885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 394540582109937729621923 591810873164906594432885)
                  ·
                    refine ⟨55482269359209993228083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 591810873164906594432885 55482269359209993228083)
                    ·
                      rfl

theorem cell23_324154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 1, 5].length) (baseStart_324154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324154 prefixEnd_324154 := by exact prefixLift 324154
  have htrace : WordTrace (prefixWord ++ tailWord_324154) baseStart_324154 baseEnd_324154 := by
    simpa [prefixWord, tailWord_324154, baseEnd_324154] using wordTrace_append hprefix tailTrace_324154
  have hstable : (prefixWord ++ tailWord_324154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324154).length < 2 ^ (prefixWord ++ tailWord_324154).sum := by decide
  have hdescent : baseEnd_324154 < baseStart_324154 := by decide
  rcases family_descends (prefixWord ++ tailWord_324154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324158 : List Nat := [4, 2, 1, 4, 2, 1, 1, 2, 6]
def baseStart_324158 : Nat := 118140960795 + 324158 * 2 ^ 59
def prefixEnd_324158 : Nat := 4983230072969 + 3 ^ 40 * 324158 * 2
def baseEnd_324158 : Nat := 18494318000027551559359

theorem tailTrace_324158 : CollatzResearch.WordTrace tailWord_324158 prefixEnd_324158 18494318000027551559359 := by
  unfold tailWord_324158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1477876694954800327991641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7882009039758935082622085 1477876694954800327991641)
  ·
    refine ⟨1108407521216100245993731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1477876694954800327991641 1108407521216100245993731)
    ·
      refine ⟨1662611281824150368990597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1108407521216100245993731 1662611281824150368990597)
      ·
        refine ⟨311739615342028194185737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1662611281824150368990597 311739615342028194185737)
        ·
          refine ⟨233804711506521145639303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311739615342028194185737 233804711506521145639303)
          ·
            refine ⟨350707067259781718458955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233804711506521145639303 350707067259781718458955)
            ·
              refine ⟨526060600889672577688433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350707067259781718458955 526060600889672577688433)
              ·
                refine ⟨394545450667254433266325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 526060600889672577688433 394545450667254433266325)
                ·
                  refine ⟨18494318000027551559359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 394545450667254433266325 18494318000027551559359)
                  ·
                    rfl

theorem cell23_324158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_324158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324158 prefixEnd_324158 := by exact prefixLift 324158
  have htrace : WordTrace (prefixWord ++ tailWord_324158) baseStart_324158 baseEnd_324158 := by
    simpa [prefixWord, tailWord_324158, baseEnd_324158] using wordTrace_append hprefix tailTrace_324158
  have hstable : (prefixWord ++ tailWord_324158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324158).length < 2 ^ (prefixWord ++ tailWord_324158).sum := by decide
  have hdescent : baseEnd_324158 < baseStart_324158 := by decide
  rcases family_descends (prefixWord ++ tailWord_324158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324177 : List Nat := [1, 2, 2, 1, 3, 4, 1, 2, 1, 1, 5]
def baseStart_324177 : Nat := 118140960795 + 324177 * 2 ^ 59
def prefixEnd_324177 : Nat := 4983230072969 + 3 ^ 40 * 324177 * 2
def baseEnd_324177 : Nat := 166458618132683389696643

theorem tailTrace_324177 : CollatzResearch.WordTrace tailWord_324177 prefixEnd_324177 166458618132683389696643 := by
  unfold tailWord_324177
  simp only [CollatzResearch.WordTrace]
  refine ⟨11823706546569568868874785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7882471031046379245916523 11823706546569568868874785)
  ·
    refine ⟨8867779909927176651656089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11823706546569568868874785 8867779909927176651656089)
    ·
      refine ⟨6650834932445382488742067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8867779909927176651656089 6650834932445382488742067)
      ·
        refine ⟨9976252398668073733113101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6650834932445382488742067 9976252398668073733113101)
        ·
          refine ⟨3741094649500527649917413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9976252398668073733113101 3741094649500527649917413)
          ·
            refine ⟨701455246781348934359515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3741094649500527649917413 701455246781348934359515)
            ·
              refine ⟨1052182870172023401539273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701455246781348934359515 1052182870172023401539273)
              ·
                refine ⟨789137152629017551154455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1052182870172023401539273 789137152629017551154455)
                ·
                  refine ⟨1183705728943526326731683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 789137152629017551154455 1183705728943526326731683)
                  ·
                    refine ⟨1775558593415289490097525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1183705728943526326731683 1775558593415289490097525)
                    ·
                      refine ⟨166458618132683389696643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1775558593415289490097525 166458618132683389696643)
                      ·
                        rfl

theorem cell23_324177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_324177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324177 prefixEnd_324177 := by exact prefixLift 324177
  have htrace : WordTrace (prefixWord ++ tailWord_324177) baseStart_324177 baseEnd_324177 := by
    simpa [prefixWord, tailWord_324177, baseEnd_324177] using wordTrace_append hprefix tailTrace_324177
  have hstable : (prefixWord ++ tailWord_324177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324177).length < 2 ^ (prefixWord ++ tailWord_324177).sum := by decide
  have hdescent : baseEnd_324177 < baseStart_324177 := by decide
  rcases family_descends (prefixWord ++ tailWord_324177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324197 : List Nat := [1, 3, 1, 3, 4, 1, 1, 9]
def baseStart_324197 : Nat := 118140960795 + 324197 * 2 ^ 59
def prefixEnd_324197 : Nat := 4983230072969 + 3 ^ 40 * 324197 * 2
def baseEnd_324197 : Nat := 6165514360954567090613

theorem tailTrace_324197 : CollatzResearch.WordTrace tailWord_324197 prefixEnd_324197 6165514360954567090613 := by
  unfold tailWord_324197
  simp only [CollatzResearch.WordTrace]
  refine ⟨11824436006497112284602845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7882957337664741523068563 11824436006497112284602845)
  ·
    refine ⟨4434163502436417106726067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11824436006497112284602845 4434163502436417106726067)
    ·
      refine ⟨6651245253654625660089101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4434163502436417106726067 6651245253654625660089101)
      ·
        refine ⟨2494216970120484622533413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6651245253654625660089101 2494216970120484622533413)
        ·
          refine ⟨467665681897590866725015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2494216970120484622533413 467665681897590866725015)
          ·
            refine ⟨701498522846386300087523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467665681897590866725015 701498522846386300087523)
            ·
              refine ⟨1052247784269579450131285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701498522846386300087523 1052247784269579450131285)
              ·
                refine ⟨6165514360954567090613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1052247784269579450131285 6165514360954567090613)
                ·
                  rfl

theorem cell23_324197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 9].length) (baseStart_324197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324197 prefixEnd_324197 := by exact prefixLift 324197
  have htrace : WordTrace (prefixWord ++ tailWord_324197) baseStart_324197 baseEnd_324197 := by
    simpa [prefixWord, tailWord_324197, baseEnd_324197] using wordTrace_append hprefix tailTrace_324197
  have hstable : (prefixWord ++ tailWord_324197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324197).length < 2 ^ (prefixWord ++ tailWord_324197).sum := by decide
  have hdescent : baseEnd_324197 < baseStart_324197 := by decide
  rcases family_descends (prefixWord ++ tailWord_324197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324207 : List Nat := [1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 3]
def baseStart_324207 : Nat := 118140960795 + 324207 * 2 ^ 59
def prefixEnd_324207 : Nat := 4983230072969 + 3 ^ 40 * 324207 * 2
def baseEnd_324207 : Nat := 166474022552318272321505

theorem tailTrace_324207 : CollatzResearch.WordTrace tailWord_324207 prefixEnd_324207 166474022552318272321505 := by
  unfold tailWord_324207
  simp only [CollatzResearch.WordTrace]
  refine ⟨11824800736460883992466875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7883200490973922661644583 11824800736460883992466875)
  ·
    refine ⟨17737201104691325988700313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11824800736460883992466875 17737201104691325988700313)
    ·
      refine ⟨13302900828518494491525235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17737201104691325988700313 13302900828518494491525235)
      ·
        refine ⟨19954351242777741737287853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13302900828518494491525235 19954351242777741737287853)
        ·
          refine ⟨7482881716041653151482945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19954351242777741737287853 7482881716041653151482945)
          ·
            refine ⟨5612161287031239863612209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7482881716041653151482945 5612161287031239863612209)
            ·
              refine ⟨4209120965273429897709157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5612161287031239863612209 4209120965273429897709157)
              ·
                refine ⟨789210180988768105820467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4209120965273429897709157 789210180988768105820467)
                ·
                  refine ⟨1183815271483152158730701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 789210180988768105820467 1183815271483152158730701)
                  ·
                    refine ⟨443930726806182059524013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1183815271483152158730701 443930726806182059524013)
                    ·
                      refine ⟨166474022552318272321505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 443930726806182059524013 166474022552318272321505)
                      ·
                        rfl

theorem cell23_324207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 3].length) (baseStart_324207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324207 prefixEnd_324207 := by exact prefixLift 324207
  have htrace : WordTrace (prefixWord ++ tailWord_324207) baseStart_324207 baseEnd_324207 := by
    simpa [prefixWord, tailWord_324207, baseEnd_324207] using wordTrace_append hprefix tailTrace_324207
  have hstable : (prefixWord ++ tailWord_324207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324207).length < 2 ^ (prefixWord ++ tailWord_324207).sum := by decide
  have hdescent : baseEnd_324207 < baseStart_324207 := by decide
  rcases family_descends (prefixWord ++ tailWord_324207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324214 : List Nat := [5, 1, 1, 2, 3, 2, 9]
def baseStart_324214 : Nat := 118140960795 + 324214 * 2 ^ 59
def prefixEnd_324214 : Nat := 4983230072969 + 3 ^ 40 * 324214 * 2
def baseEnd_324214 : Nat := 2055279221196293147333

theorem tailTrace_324214 : CollatzResearch.WordTrace tailWord_324214 prefixEnd_324214 2055279221196293147333 := by
  unfold tailWord_324214
  simp only [CollatzResearch.WordTrace]
  refine ⟨739066002964720261748231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7883370698290349458647797 739066002964720261748231)
  ·
    refine ⟨1108599004447080392622347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 739066002964720261748231 1108599004447080392622347)
    ·
      refine ⟨1662898506670620588933521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1108599004447080392622347 1662898506670620588933521)
      ·
        refine ⟨1247173880002965441700141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1662898506670620588933521 1247173880002965441700141)
        ·
          refine ⟨467690205001112040637553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1247173880002965441700141 467690205001112040637553)
          ·
            refine ⟨350767653750834030478165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 467690205001112040637553 350767653750834030478165)
            ·
              refine ⟨2055279221196293147333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 350767653750834030478165 2055279221196293147333)
              ·
                rfl

theorem cell23_324214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 9].length) (baseStart_324214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324214 prefixEnd_324214 := by exact prefixLift 324214
  have htrace : WordTrace (prefixWord ++ tailWord_324214) baseStart_324214 baseEnd_324214 := by
    simpa [prefixWord, tailWord_324214, baseEnd_324214] using wordTrace_append hprefix tailTrace_324214
  have hstable : (prefixWord ++ tailWord_324214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324214).length < 2 ^ (prefixWord ++ tailWord_324214).sum := by decide
  have hdescent : baseEnd_324214 < baseStart_324214 := by decide
  rcases family_descends (prefixWord ++ tailWord_324214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324224 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 4, 1, 3]
def baseStart_324224 : Nat := 118140960795 + 324224 * 2 ^ 59
def prefixEnd_324224 : Nat := 4983230072969 + 3 ^ 40 * 324224 * 2
def baseEnd_324224 : Nat := 166482751723444705808927

theorem tailTrace_324224 : CollatzResearch.WordTrace tailWord_324224 prefixEnd_324224 166482751723444705808927 := by
  unfold tailWord_324224
  simp only [CollatzResearch.WordTrace]
  refine ⟨5912710388699647947917863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7883613851599530597223817 5912710388699647947917863)
  ·
    refine ⟨8869065583049471921876795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5912710388699647947917863 8869065583049471921876795)
    ·
      refine ⟨13303598374574207882815193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8869065583049471921876795 13303598374574207882815193)
      ·
        refine ⟨9977698780930655912111395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13303598374574207882815193 9977698780930655912111395)
        ·
          refine ⟨14966548171395983868167093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9977698780930655912111395 14966548171395983868167093)
          ·
            refine ⟨1403113891068373487640665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14966548171395983868167093 1403113891068373487640665)
            ·
              refine ⟨1052335418301280115730499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1403113891068373487640665 1052335418301280115730499)
              ·
                refine ⟨1578503127451920173595749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052335418301280115730499 1578503127451920173595749)
                ·
                  refine ⟨295969336397235032549203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1578503127451920173595749 295969336397235032549203)
                  ·
                    refine ⟨443954004595852548823805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 295969336397235032549203 443954004595852548823805)
                    ·
                      refine ⟨166482751723444705808927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 443954004595852548823805 166482751723444705808927)
                      ·
                        rfl

theorem cell23_324224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 4, 1, 3].length) (baseStart_324224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324224 prefixEnd_324224 := by exact prefixLift 324224
  have htrace : WordTrace (prefixWord ++ tailWord_324224) baseStart_324224 baseEnd_324224 := by
    simpa [prefixWord, tailWord_324224, baseEnd_324224] using wordTrace_append hprefix tailTrace_324224
  have hstable : (prefixWord ++ tailWord_324224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324224).length < 2 ^ (prefixWord ++ tailWord_324224).sum := by decide
  have hdescent : baseEnd_324224 < baseStart_324224 := by decide
  rcases family_descends (prefixWord ++ tailWord_324224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324225 : List Nat := [1, 2, 4, 2, 1, 1, 5, 2, 1, 2, 2]
def baseStart_324225 : Nat := 118140960795 + 324225 * 2 ^ 59
def prefixEnd_324225 : Nat := 4983230072969 + 3 ^ 40 * 324225 * 2
def baseEnd_324225 : Nat := 166483265204099201896423

theorem tailTrace_324225 : CollatzResearch.WordTrace tailWord_324225 prefixEnd_324225 166483265204099201896423 := by
  unfold tailWord_324225
  simp only [CollatzResearch.WordTrace]
  refine ⟨11825457250395673066622129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7883638166930448711081419 11825457250395673066622129)
  ·
    refine ⟨8869092937796754799966597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11825457250395673066622129 8869092937796754799966597)
    ·
      refine ⟨1662954925836891524993737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8869092937796754799966597 1662954925836891524993737)
      ·
        refine ⟨1247216194377668643745303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1662954925836891524993737 1247216194377668643745303)
        ·
          refine ⟨1870824291566502965617955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1247216194377668643745303 1870824291566502965617955)
          ·
            refine ⟨2806236437349754448426933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870824291566502965617955 2806236437349754448426933)
            ·
              refine ⟨263084666001539479540025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2806236437349754448426933 263084666001539479540025)
              ·
                refine ⟨197313499501154609655019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263084666001539479540025 197313499501154609655019)
                ·
                  refine ⟨295970249251731914482529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197313499501154609655019 295970249251731914482529)
                  ·
                    refine ⟨221977686938798935861897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 295970249251731914482529 221977686938798935861897)
                    ·
                      refine ⟨166483265204099201896423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 221977686938798935861897 166483265204099201896423)
                      ·
                        rfl

theorem cell23_324225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_324225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324225 prefixEnd_324225 := by exact prefixLift 324225
  have htrace : WordTrace (prefixWord ++ tailWord_324225) baseStart_324225 baseEnd_324225 := by
    simpa [prefixWord, tailWord_324225, baseEnd_324225] using wordTrace_append hprefix tailTrace_324225
  have hstable : (prefixWord ++ tailWord_324225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324225).length < 2 ^ (prefixWord ++ tailWord_324225).sum := by decide
  have hdescent : baseEnd_324225 < baseStart_324225 := by decide
  rcases family_descends (prefixWord ++ tailWord_324225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324298 : List Nat := [3, 1, 2, 1, 4, 1, 2, 3, 2, 2, 2]
def baseStart_324298 : Nat := 118140960795 + 324298 * 2 ^ 59
def prefixEnd_324298 : Nat := 4983230072969 + 3 ^ 40 * 324298 * 2
def baseEnd_324298 : Nat := 166520749291877416283587

theorem tailTrace_324298 : CollatzResearch.WordTrace tailWord_324298 prefixEnd_324298 166520749291877416283587 := by
  unfold tailWord_324298
  simp only [CollatzResearch.WordTrace]
  refine ⟨2957029944782801633507387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7885413186087471022686365 2957029944782801633507387)
  ·
    refine ⟨4435544917174202450261081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2957029944782801633507387 4435544917174202450261081)
    ·
      refine ⟨3326658687880651837695811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4435544917174202450261081 3326658687880651837695811)
      ·
        refine ⟨4989988031820977756543717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3326658687880651837695811 4989988031820977756543717)
        ·
          refine ⟨935622755966433329351947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4989988031820977756543717 935622755966433329351947)
          ·
            refine ⟨1403434133949649994027921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935622755966433329351947 1403434133949649994027921)
            ·
              refine ⟨1052575600462237495520941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1403434133949649994027921 1052575600462237495520941)
              ·
                refine ⟨394715850173339060820353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1052575600462237495520941 394715850173339060820353)
                ·
                  refine ⟨296036887630004295615265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394715850173339060820353 296036887630004295615265)
                  ·
                    refine ⟨222027665722503221711449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 296036887630004295615265 222027665722503221711449)
                    ·
                      refine ⟨166520749291877416283587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 222027665722503221711449 166520749291877416283587)
                      ·
                        rfl

theorem cell23_324298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_324298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324298 prefixEnd_324298 := by exact prefixLift 324298
  have htrace : WordTrace (prefixWord ++ tailWord_324298) baseStart_324298 baseEnd_324298 := by
    simpa [prefixWord, tailWord_324298, baseEnd_324298] using wordTrace_append hprefix tailTrace_324298
  have hstable : (prefixWord ++ tailWord_324298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324298).length < 2 ^ (prefixWord ++ tailWord_324298).sum := by decide
  have hdescent : baseEnd_324298 < baseStart_324298 := by decide
  rcases family_descends (prefixWord ++ tailWord_324298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324321 : List Nat := [1, 2, 3, 1, 4, 2, 2, 3, 5]
def baseStart_324321 : Nat := 118140960795 + 324321 * 2 ^ 59
def prefixEnd_324321 : Nat := 4983230072969 + 3 ^ 40 * 324321 * 2
def baseEnd_324321 : Nat := 18503617705214536255109

theorem tailTrace_324321 : CollatzResearch.WordTrace tailWord_324321 prefixEnd_324321 18503617705214536255109 := by
  unfold tailWord_324321
  simp only [CollatzResearch.WordTrace]
  refine ⟨11828958658047881462116817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7885972438698587641411211 11828958658047881462116817)
  ·
    refine ⟨8871718993535911096587613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11828958658047881462116817 8871718993535911096587613)
    ·
      refine ⟨3326894622575966661220355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8871718993535911096587613 3326894622575966661220355)
      ·
        refine ⟨4990341933863949991830533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3326894622575966661220355 4990341933863949991830533)
        ·
          refine ⟨935689112599490623468225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4990341933863949991830533 935689112599490623468225)
          ·
            refine ⟨701766834449617967601169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 935689112599490623468225 701766834449617967601169)
            ·
              refine ⟨526325125837213475700877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 701766834449617967601169 526325125837213475700877)
              ·
                refine ⟨197371922188955053387829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 526325125837213475700877 197371922188955053387829)
                ·
                  refine ⟨18503617705214536255109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 197371922188955053387829 18503617705214536255109)
                  ·
                    rfl

theorem cell23_324321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 5].length) (baseStart_324321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324321 prefixEnd_324321 := by exact prefixLift 324321
  have htrace : WordTrace (prefixWord ++ tailWord_324321) baseStart_324321 baseEnd_324321 := by
    simpa [prefixWord, tailWord_324321, baseEnd_324321] using wordTrace_append hprefix tailTrace_324321
  have hstable : (prefixWord ++ tailWord_324321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324321).length < 2 ^ (prefixWord ++ tailWord_324321).sum := by decide
  have hdescent : baseEnd_324321 < baseStart_324321 := by decide
  rcases family_descends (prefixWord ++ tailWord_324321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324367 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 4]
def baseStart_324367 : Nat := 118140960795 + 324367 * 2 ^ 59
def prefixEnd_324367 : Nat := 4983230072969 + 3 ^ 40 * 324367 * 2
def baseEnd_324367 : Nat := 166556179457037646320769

theorem tailTrace_324367 : CollatzResearch.WordTrace tailWord_324367 prefixEnd_324367 166556179457037646320769 := by
  unfold tailWord_324367
  simp only [CollatzResearch.WordTrace]
  refine ⟨11830636415881231318291355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7887090943920820878860903 11830636415881231318291355)
  ·
    refine ⟨17745954623821846977437033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11830636415881231318291355 17745954623821846977437033)
    ·
      refine ⟨13309465967866385233077775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17745954623821846977437033 13309465967866385233077775)
      ·
        refine ⟨19964198951799577849616663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13309465967866385233077775 19964198951799577849616663)
        ·
          refine ⟨29946298427699366774424995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19964198951799577849616663 29946298427699366774424995)
          ·
            refine ⟨44919447641549050161637493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29946298427699366774424995 44919447641549050161637493)
            ·
              refine ⟨4211198216395223452653515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44919447641549050161637493 4211198216395223452653515)
              ·
                refine ⟨6316797324592835178980273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4211198216395223452653515 6316797324592835178980273)
                ·
                  refine ⟨4737597993444626384235205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6316797324592835178980273 4737597993444626384235205)
                  ·
                    refine ⟨888299623770867447044101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4737597993444626384235205 888299623770867447044101)
                    ·
                      refine ⟨166556179457037646320769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 888299623770867447044101 166556179457037646320769)
                      ·
                        rfl

theorem cell23_324367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_324367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324367 prefixEnd_324367 := by exact prefixLift 324367
  have htrace : WordTrace (prefixWord ++ tailWord_324367) baseStart_324367 baseEnd_324367 := by
    simpa [prefixWord, tailWord_324367, baseEnd_324367] using wordTrace_append hprefix tailTrace_324367
  have hstable : (prefixWord ++ tailWord_324367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324367).length < 2 ^ (prefixWord ++ tailWord_324367).sum := by decide
  have hdescent : baseEnd_324367 < baseStart_324367 := by decide
  rcases family_descends (prefixWord ++ tailWord_324367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324398 : List Nat := [4, 1, 3, 2, 1, 1, 3, 1, 3, 4]
def baseStart_324398 : Nat := 118140960795 + 324398 * 2 ^ 59
def prefixEnd_324398 : Nat := 4983230072969 + 3 ^ 40 * 324398 * 2
def baseEnd_324398 : Nat := 55524032452442341677709

theorem tailTrace_324398 : CollatzResearch.WordTrace tailWord_324398 prefixEnd_324398 55524032452442341677709 := by
  unfold tailWord_324398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1478970884846115451583731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7887844719179282408446565 1478970884846115451583731)
  ·
    refine ⟨2218456327269173177375597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1478970884846115451583731 2218456327269173177375597)
    ·
      refine ⟨831921122725939941515849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2218456327269173177375597 831921122725939941515849)
      ·
        refine ⟨623940842044454956136887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 831921122725939941515849 623940842044454956136887)
        ·
          refine ⟨935911263066682434205331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623940842044454956136887 935911263066682434205331)
          ·
            refine ⟨1403866894600023651307997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935911263066682434205331 1403866894600023651307997)
            ·
              refine ⟨526450085475008869240499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1403866894600023651307997 526450085475008869240499)
              ·
                refine ⟨789675128212513303860749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526450085475008869240499 789675128212513303860749)
                ·
                  refine ⟨296128173079692488947781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 789675128212513303860749 296128173079692488947781)
                  ·
                    refine ⟨55524032452442341677709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 296128173079692488947781 55524032452442341677709)
                    ·
                      rfl

theorem cell23_324398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_324398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324398 prefixEnd_324398 := by exact prefixLift 324398
  have htrace : WordTrace (prefixWord ++ tailWord_324398) baseStart_324398 baseEnd_324398 := by
    simpa [prefixWord, tailWord_324398, baseEnd_324398] using wordTrace_append hprefix tailTrace_324398
  have hstable : (prefixWord ++ tailWord_324398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324398).length < 2 ^ (prefixWord ++ tailWord_324398).sum := by decide
  have hdescent : baseEnd_324398 < baseStart_324398 := by decide
  rcases family_descends (prefixWord ++ tailWord_324398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324424 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 3, 5]
def baseStart_324424 : Nat := 118140960795 + 324424 * 2 ^ 59
def prefixEnd_324424 : Nat := 4983230072969 + 3 ^ 40 * 324424 * 2
def baseEnd_324424 : Nat := 55528482618114641102669

theorem tailTrace_324424 : CollatzResearch.WordTrace tailWord_324424 prefixEnd_324424 55528482618114641102669 := by
  unfold tailWord_324424
  simp only [CollatzResearch.WordTrace]
  refine ⟨5916357688337365026558163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7888476917783153368744217 5916357688337365026558163)
  ·
    refine ⟨8874536532506047539837245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5916357688337365026558163 8874536532506047539837245)
    ·
      refine ⟨3327951199689767827438967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8874536532506047539837245 3327951199689767827438967)
      ·
        refine ⟨4991926799534651741158451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3327951199689767827438967 4991926799534651741158451)
        ·
          refine ⟨7487890199301977611737677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4991926799534651741158451 7487890199301977611737677)
          ·
            refine ⟨2807958824738241604401629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7487890199301977611737677 2807958824738241604401629)
            ·
              refine ⟨1052984559276840601650611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2807958824738241604401629 1052984559276840601650611)
              ·
                refine ⟨1579476838915260902475917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052984559276840601650611 1579476838915260902475917)
                ·
                  refine ⟨592303814593222838428469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1579476838915260902475917 592303814593222838428469)
                  ·
                    refine ⟨55528482618114641102669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 592303814593222838428469 55528482618114641102669)
                    ·
                      rfl

theorem cell23_324424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_324424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324424 prefixEnd_324424 := by exact prefixLift 324424
  have htrace : WordTrace (prefixWord ++ tailWord_324424) baseStart_324424 baseEnd_324424 := by
    simpa [prefixWord, tailWord_324424, baseEnd_324424] using wordTrace_append hprefix tailTrace_324424
  have hstable : (prefixWord ++ tailWord_324424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324424).length < 2 ^ (prefixWord ++ tailWord_324424).sum := by decide
  have hdescent : baseEnd_324424 < baseStart_324424 := by decide
  rcases family_descends (prefixWord ++ tailWord_324424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324455 : List Nat := [1, 1, 5, 1, 2, 3, 1, 4, 1, 1, 3]
def baseStart_324455 : Nat := 118140960795 + 324455 * 2 ^ 59
def prefixEnd_324455 : Nat := 4983230072969 + 3 ^ 40 * 324455 * 2
def baseEnd_324455 : Nat := 166601365754633302020365

theorem tailTrace_324455 : CollatzResearch.WordTrace tailWord_324455 prefixEnd_324455 166601365754633302020365 := by
  unfold tailWord_324455
  simp only [CollatzResearch.WordTrace]
  refine ⟨11833846039562422347494819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7889230693041614898329879 11833846039562422347494819)
  ·
    refine ⟨17750769059343633521242229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11833846039562422347494819 17750769059343633521242229)
    ·
      refine ⟨1664134599313465642616459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17750769059343633521242229 1664134599313465642616459)
      ·
        refine ⟨2496201898970198463924689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1664134599313465642616459 2496201898970198463924689)
        ·
          refine ⟨1872151424227648847943517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2496201898970198463924689 1872151424227648847943517)
          ·
            refine ⟨702056784085368317978819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1872151424227648847943517 702056784085368317978819)
            ·
              refine ⟨1053085176128052476968229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702056784085368317978819 1053085176128052476968229)
              ·
                refine ⟨197453470524009839431543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1053085176128052476968229 197453470524009839431543)
                ·
                  refine ⟨296180205786014759147315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197453470524009839431543 296180205786014759147315)
                  ·
                    refine ⟨444270308679022138720973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 296180205786014759147315 444270308679022138720973)
                    ·
                      refine ⟨166601365754633302020365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 444270308679022138720973 166601365754633302020365)
                      ·
                        rfl

theorem cell23_324455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_324455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324455 prefixEnd_324455 := by exact prefixLift 324455
  have htrace : WordTrace (prefixWord ++ tailWord_324455) baseStart_324455 baseEnd_324455 := by
    simpa [prefixWord, tailWord_324455, baseEnd_324455] using wordTrace_append hprefix tailTrace_324455
  have hstable : (prefixWord ++ tailWord_324455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324455).length < 2 ^ (prefixWord ++ tailWord_324455).sum := by decide
  have hdescent : baseEnd_324455 < baseStart_324455 := by decide
  rcases family_descends (prefixWord ++ tailWord_324455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324461 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 2, 6, 2]
def baseStart_324461 : Nat := 118140960795 + 324461 * 2 ^ 59
def prefixEnd_324461 : Nat := 4983230072969 + 3 ^ 40 * 324461 * 2
def baseEnd_324461 : Nat := 166604446638560278545337

theorem tailTrace_324461 : CollatzResearch.WordTrace tailWord_324461 prefixEnd_324461 166604446638560278545337 := by
  unfold tailWord_324461
  simp only [CollatzResearch.WordTrace]
  refine ⟨11834064877540685372213237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7889376585027123581475491 11834064877540685372213237)
  ·
    refine ⟨1109443582269439253644991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11834064877540685372213237 1109443582269439253644991)
    ·
      refine ⟨1664165373404158880467487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1109443582269439253644991 1664165373404158880467487)
      ·
        refine ⟨2496248060106238320701231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1664165373404158880467487 2496248060106238320701231)
        ·
          refine ⟨3744372090159357481051847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2496248060106238320701231 3744372090159357481051847)
          ·
            refine ⟨5616558135239036221577771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3744372090159357481051847 5616558135239036221577771)
            ·
              refine ⟨8424837202858554332366657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5616558135239036221577771 8424837202858554332366657)
              ·
                refine ⟨6318627902143915749274993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8424837202858554332366657 6318627902143915749274993)
                ·
                  refine ⟨4738970926607936811956245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6318627902143915749274993 4738970926607936811956245)
                  ·
                    refine ⟨222139262184747038060449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4738970926607936811956245 222139262184747038060449)
                    ·
                      refine ⟨166604446638560278545337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 222139262184747038060449 166604446638560278545337)
                      ·
                        rfl

theorem cell23_324461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_324461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324461 prefixEnd_324461 := by exact prefixLift 324461
  have htrace : WordTrace (prefixWord ++ tailWord_324461) baseStart_324461 baseEnd_324461 := by
    simpa [prefixWord, tailWord_324461, baseEnd_324461] using wordTrace_append hprefix tailTrace_324461
  have hstable : (prefixWord ++ tailWord_324461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324461).length < 2 ^ (prefixWord ++ tailWord_324461).sum := by decide
  have hdescent : baseEnd_324461 < baseStart_324461 := by decide
  rcases family_descends (prefixWord ++ tailWord_324461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324464 : List Nat := [2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 5]
def baseStart_324464 : Nat := 118140960795 + 324464 * 2 ^ 59
def prefixEnd_324464 : Nat := 4983230072969 + 3 ^ 40 * 324464 * 2
def baseEnd_324464 : Nat := 166605987080523766807823

theorem tailTrace_324464 : CollatzResearch.WordTrace tailWord_324464 prefixEnd_324464 166605987080523766807823 := by
  unfold tailWord_324464
  simp only [CollatzResearch.WordTrace]
  refine ⟨5917087148264908442286223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7889449531019877923048297 5917087148264908442286223)
  ·
    refine ⟨8875630722397362663429335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5917087148264908442286223 8875630722397362663429335)
    ·
      refine ⟨13313446083596043995144003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8875630722397362663429335 13313446083596043995144003)
      ·
        refine ⟨19970169125394065992716005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13313446083596043995144003 19970169125394065992716005)
        ·
          refine ⟨3744406711011387373634251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19970169125394065992716005 3744406711011387373634251)
          ·
            refine ⟨5616610066517081060451377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3744406711011387373634251 5616610066517081060451377)
            ·
              refine ⟨4212457549887810795338533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5616610066517081060451377 4212457549887810795338533)
              ·
                refine ⟨789835790603964524125975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4212457549887810795338533 789835790603964524125975)
                ·
                  refine ⟨1184753685905946786188963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 789835790603964524125975 1184753685905946786188963)
                  ·
                    refine ⟨1777130528858920179283445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1184753685905946786188963 1777130528858920179283445)
                    ·
                      refine ⟨166605987080523766807823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1777130528858920179283445 166605987080523766807823)
                      ·
                        rfl

theorem cell23_324464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 5].length) (baseStart_324464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324464 prefixEnd_324464 := by exact prefixLift 324464
  have htrace : WordTrace (prefixWord ++ tailWord_324464) baseStart_324464 baseEnd_324464 := by
    simpa [prefixWord, tailWord_324464, baseEnd_324464] using wordTrace_append hprefix tailTrace_324464
  have hstable : (prefixWord ++ tailWord_324464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324464).length < 2 ^ (prefixWord ++ tailWord_324464).sum := by decide
  have hdescent : baseEnd_324464 < baseStart_324464 := by decide
  rcases family_descends (prefixWord ++ tailWord_324464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324482 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_324482 : Nat := 118140960795 + 324482 * 2 ^ 59
def prefixEnd_324482 : Nat := 4983230072969 + 3 ^ 40 * 324482 * 2
def baseEnd_324482 : Nat := 166615229732304696382741

theorem tailTrace_324482 : CollatzResearch.WordTrace tailWord_324482 prefixEnd_324482 166615229732304696382741 := by
  unfold tailWord_324482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2958707702616151489681925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7889887206976403972485133 2958707702616151489681925)
  ·
    refine ⟨554757694240528404315361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2958707702616151489681925 554757694240528404315361)
    ·
      refine ⟨416068270680396303236521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 554757694240528404315361 416068270680396303236521)
      ·
        refine ⟨312051203010297227427391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 416068270680396303236521 312051203010297227427391)
        ·
          refine ⟨468076804515445841141087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312051203010297227427391 468076804515445841141087)
          ·
            refine ⟨702115206773168761711631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468076804515445841141087 702115206773168761711631)
            ·
              refine ⟨1053172810159753142567447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702115206773168761711631 1053172810159753142567447)
              ·
                refine ⟨1579759215239629713851171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1053172810159753142567447 1579759215239629713851171)
                ·
                  refine ⟨2369638822859444570776757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1579759215239629713851171 2369638822859444570776757)
                  ·
                    refine ⟨222153639643072928510321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2369638822859444570776757 222153639643072928510321)
                    ·
                      refine ⟨166615229732304696382741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 222153639643072928510321 166615229732304696382741)
                      ·
                        rfl

theorem cell23_324482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_324482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324482 prefixEnd_324482 := by exact prefixLift 324482
  have htrace : WordTrace (prefixWord ++ tailWord_324482) baseStart_324482 baseEnd_324482 := by
    simpa [prefixWord, tailWord_324482, baseEnd_324482] using wordTrace_append hprefix tailTrace_324482
  have hstable : (prefixWord ++ tailWord_324482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324482).length < 2 ^ (prefixWord ++ tailWord_324482).sum := by decide
  have hdescent : baseEnd_324482 < baseStart_324482 := by decide
  rcases family_descends (prefixWord ++ tailWord_324482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324532 : List Nat := [2, 5, 2, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_324532 : Nat := 118140960795 + 324532 * 2 ^ 59
def prefixEnd_324532 : Nat := 4983230072969 + 3 ^ 40 * 324532 * 2
def baseEnd_324532 : Nat := 166640903765029500757511

theorem tailTrace_324532 : CollatzResearch.WordTrace tailWord_324532 prefixEnd_324532 166640903765029500757511 := by
  unfold tailWord_324532
  simp only [CollatzResearch.WordTrace]
  refine ⟨5918327230141732249023925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7891102973522309665365233 5918327230141732249023925)
  ·
    refine ⟨554843177825787398345993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5918327230141732249023925 554843177825787398345993)
    ·
      refine ⟨416132383369340548759495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 554843177825787398345993 416132383369340548759495)
      ·
        refine ⟨624198575054010823139243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416132383369340548759495 624198575054010823139243)
        ·
          refine ⟨936297862581016234708865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624198575054010823139243 936297862581016234708865)
          ·
            refine ⟨702223396935762176031649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 936297862581016234708865 702223396935762176031649)
            ·
              refine ⟨526667547701821632023737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 702223396935762176031649 526667547701821632023737)
              ·
                refine ⟨395000660776366224017803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 526667547701821632023737 395000660776366224017803)
                ·
                  refine ⟨592500991164549336026705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 395000660776366224017803 592500991164549336026705)
                  ·
                    refine ⟨444375743373412002020029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 592500991164549336026705 444375743373412002020029)
                    ·
                      refine ⟨166640903765029500757511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 444375743373412002020029 166640903765029500757511)
                      ·
                        rfl

theorem cell23_324532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_324532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324532 prefixEnd_324532 := by exact prefixLift 324532
  have htrace : WordTrace (prefixWord ++ tailWord_324532) baseStart_324532 baseEnd_324532 := by
    simpa [prefixWord, tailWord_324532, baseEnd_324532] using wordTrace_append hprefix tailTrace_324532
  have hstable : (prefixWord ++ tailWord_324532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324532).length < 2 ^ (prefixWord ++ tailWord_324532).sum := by decide
  have hdescent : baseEnd_324532 < baseStart_324532 := by decide
  rcases family_descends (prefixWord ++ tailWord_324532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
