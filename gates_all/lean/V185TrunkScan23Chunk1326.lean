import V185TrunkScan23Chunk1325

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7853814 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2]
def baseStart_7853814 : Nat := 118140960795 + 7853814 * 2 ^ 59
def prefixEnd_7853814 : Nat := 4983230072969 + 3 ^ 40 * 7853814 * 2
def baseEnd_7853814 : Nat := 4032781553010640150305973

theorem tailTrace_7853814 : CollatzResearch.WordTrace tailWord_7853814 prefixEnd_7853814 4032781553010640150305973 := by
  unfold tailWord_7853814
  simp only [CollatzResearch.WordTrace]
  refine ⟨17903258098061292343000031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190968086379320451658666997 17903258098061292343000031)
  ·
    refine ⟨26854887147091938514500047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17903258098061292343000031 26854887147091938514500047)
    ·
      refine ⟨40282330720637907771750071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26854887147091938514500047 40282330720637907771750071)
      ·
        refine ⟨60423496080956861657625107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40282330720637907771750071 60423496080956861657625107)
        ·
          refine ⟨90635244121435292486437661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60423496080956861657625107 90635244121435292486437661)
          ·
            refine ⟨33988216545538234682414123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90635244121435292486437661 33988216545538234682414123)
            ·
              refine ⟨50982324818307352023621185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33988216545538234682414123 50982324818307352023621185)
              ·
                refine ⟨38236743613730514017715889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50982324818307352023621185 38236743613730514017715889)
                ·
                  refine ⟨28677557710297885513286917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38236743613730514017715889 28677557710297885513286917)
                  ·
                    refine ⟨5377042070680853533741297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28677557710297885513286917 5377042070680853533741297)
                    ·
                      refine ⟨4032781553010640150305973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5377042070680853533741297 4032781553010640150305973)
                      ·
                        rfl

theorem cell23_7853814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_7853814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853814 prefixEnd_7853814 := by exact prefixLift 7853814
  have htrace : WordTrace (prefixWord ++ tailWord_7853814) baseStart_7853814 baseEnd_7853814 := by
    simpa [prefixWord, tailWord_7853814, baseEnd_7853814] using wordTrace_append hprefix tailTrace_7853814
  have hstable : (prefixWord ++ tailWord_7853814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853814).length < 2 ^ (prefixWord ++ tailWord_7853814).sum := by decide
  have hdescent : baseEnd_7853814 < baseStart_7853814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853820 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 8]
def baseStart_7853820 : Nat := 118140960795 + 7853820 * 2 ^ 59
def prefixEnd_7853820 : Nat := 4983230072969 + 3 ^ 40 * 7853820 * 2
def baseEnd_7853820 : Nat := 448087181543840791870105

theorem tailTrace_7853820 : CollatzResearch.WordTrace tailWord_7853820 prefixEnd_7853820 448087181543840791870105 := by
  unfold tailWord_7853820
  simp only [CollatzResearch.WordTrace]
  refine ⟨143226174203479470256359457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190968232271305960341812609 143226174203479470256359457)
  ·
    refine ⟨107419630652609602692269593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143226174203479470256359457 107419630652609602692269593)
    ·
      refine ⟨80564722989457202019202195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107419630652609602692269593 80564722989457202019202195)
      ·
        refine ⟨120847084484185803028803293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80564722989457202019202195 120847084484185803028803293)
        ·
          refine ⟨45317656681569676135801235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120847084484185803028803293 45317656681569676135801235)
          ·
            refine ⟨67976485022354514203701853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45317656681569676135801235 67976485022354514203701853)
            ·
              refine ⟨25491181883382942826388195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67976485022354514203701853 25491181883382942826388195)
              ·
                refine ⟨38236772825074414239582293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25491181883382942826388195 38236772825074414239582293)
                ·
                  refine ⟨448087181543840791870105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38236772825074414239582293 448087181543840791870105)
                  ·
                    rfl

theorem cell23_7853820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 8].length) (baseStart_7853820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853820 prefixEnd_7853820 := by exact prefixLift 7853820
  have htrace : WordTrace (prefixWord ++ tailWord_7853820) baseStart_7853820 baseEnd_7853820 := by
    simpa [prefixWord, tailWord_7853820, baseEnd_7853820] using wordTrace_append hprefix tailTrace_7853820
  have hstable : (prefixWord ++ tailWord_7853820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853820).length < 2 ^ (prefixWord ++ tailWord_7853820).sum := by decide
  have hdescent : baseEnd_7853820 < baseStart_7853820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853874 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2]
def baseStart_7853874 : Nat := 118140960795 + 7853874 * 2 ^ 59
def prefixEnd_7853874 : Nat := 4983230072969 + 3 ^ 40 * 7853874 * 2
def baseEnd_7853874 : Nat := 4032812361849909915555697

theorem tailTrace_7853874 : CollatzResearch.WordTrace tailWord_7853874 prefixEnd_7853874 4032812361849909915555697 := by
  unfold tailWord_7853874
  simp only [CollatzResearch.WordTrace]
  refine ⟨71613579487190826933796169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190969545299175538490123117 71613579487190826933796169)
  ·
    refine ⟨53710184615393120200347127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71613579487190826933796169 53710184615393120200347127)
    ·
      refine ⟨80565276923089680300520691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53710184615393120200347127 80565276923089680300520691)
      ·
        refine ⟨120847915384634520450781037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80565276923089680300520691 120847915384634520450781037)
        ·
          refine ⟨45317968269237945169042889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120847915384634520450781037 45317968269237945169042889)
          ·
            refine ⟨33988476201928458876782167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45317968269237945169042889 33988476201928458876782167)
            ·
              refine ⟨50982714302892688315173251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33988476201928458876782167 50982714302892688315173251)
              ·
                refine ⟨76474071454339032472759877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50982714302892688315173251 76474071454339032472759877)
                ·
                  refine ⟨14338888397688568588642477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76474071454339032472759877 14338888397688568588642477)
                  ·
                    refine ⟨5377083149133213220740929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14338888397688568588642477 5377083149133213220740929)
                    ·
                      refine ⟨4032812361849909915555697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5377083149133213220740929 4032812361849909915555697)
                      ·
                        rfl

theorem cell23_7853874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_7853874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853874 prefixEnd_7853874 := by exact prefixLift 7853874
  have htrace : WordTrace (prefixWord ++ tailWord_7853874) baseStart_7853874 baseEnd_7853874 := by
    simpa [prefixWord, tailWord_7853874, baseEnd_7853874] using wordTrace_append hprefix tailTrace_7853874
  have hstable : (prefixWord ++ tailWord_7853874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853874).length < 2 ^ (prefixWord ++ tailWord_7853874).sum := by decide
  have hdescent : baseEnd_7853874 < baseStart_7853874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853901 : List Nat := [1, 6, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_7853901 : Nat := 118140960795 + 7853901 * 2 ^ 59
def prefixEnd_7853901 : Nat := 4983230072969 + 3 ^ 40 * 7853901 * 2
def baseEnd_7853901 : Nat := 1344275408609193769972691

theorem tailTrace_7853901 : CollatzResearch.WordTrace tailWord_7853901 prefixEnd_7853901 1344275408609193769972691 := by
  unfold tailWord_7853901
  simp only [CollatzResearch.WordTrace]
  refine ⟨286455302719665491346417557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190970201813110327564278371 286455302719665491346417557)
  ·
    refine ⟨13427592314984319906863323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 286455302719665491346417557 13427592314984319906863323)
    ·
      refine ⟨20141388472476479860294985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13427592314984319906863323 20141388472476479860294985)
      ·
        refine ⟨15106041354357359895221239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20141388472476479860294985 15106041354357359895221239)
        ·
          refine ⟨22659062031536039842831859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15106041354357359895221239 22659062031536039842831859)
          ·
            refine ⟨33988593047304059764247789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22659062031536039842831859 33988593047304059764247789)
            ·
              refine ⟨12745722392739022411592921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33988593047304059764247789 12745722392739022411592921)
              ·
                refine ⟨9559291794554266808694691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12745722392739022411592921 9559291794554266808694691)
                ·
                  refine ⟨14338937691831400213042037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9559291794554266808694691 14338937691831400213042037)
                  ·
                    refine ⟨1344275408609193769972691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14338937691831400213042037 1344275408609193769972691)
                    ·
                      rfl

theorem cell23_7853901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_7853901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853901 prefixEnd_7853901 := by exact prefixLift 7853901
  have htrace : WordTrace (prefixWord ++ tailWord_7853901) baseStart_7853901 baseEnd_7853901 := by
    simpa [prefixWord, tailWord_7853901, baseEnd_7853901] using wordTrace_append hprefix tailTrace_7853901
  have hstable : (prefixWord ++ tailWord_7853901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853901).length < 2 ^ (prefixWord ++ tailWord_7853901).sum := by decide
  have hdescent : baseEnd_7853901 < baseStart_7853901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853904 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 5, 2, 2]
def baseStart_7853904 : Nat := 118140960795 + 7853904 * 2 ^ 59
def prefixEnd_7853904 : Nat := 4983230072969 + 3 ^ 40 * 7853904 * 2
def baseEnd_7853904 : Nat := 4032827766269544798180559

theorem tailTrace_7853904 : CollatzResearch.WordTrace tailWord_7853904 prefixEnd_7853904 4032827766269544798180559 := by
  unfold tailWord_7853904
  simp only [CollatzResearch.WordTrace]
  refine ⟨143227706069327311429388383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190970274759103081905851177 143227706069327311429388383)
  ·
    refine ⟨214841559103990967144082575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143227706069327311429388383 214841559103990967144082575)
    ·
      refine ⟨322262338655986450716123863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214841559103990967144082575 322262338655986450716123863)
      ·
        refine ⟨483393507983979676074185795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322262338655986450716123863 483393507983979676074185795)
        ·
          refine ⟨725090261975969514111278693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483393507983979676074185795 725090261975969514111278693)
          ·
            refine ⟨135954424120494283895864755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 725090261975969514111278693 135954424120494283895864755)
            ·
              refine ⟨203931636180741425843797133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135954424120494283895864755 203931636180741425843797133)
              ·
                refine ⟨76474363567778034691423925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203931636180741425843797133 76474363567778034691423925)
                ·
                  refine ⟨7169471584479190752320993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76474363567778034691423925 7169471584479190752320993)
                  ·
                    refine ⟨5377103688359393064240745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7169471584479190752320993 5377103688359393064240745)
                    ·
                      refine ⟨4032827766269544798180559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5377103688359393064240745 4032827766269544798180559)
                      ·
                        rfl

theorem cell23_7853904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 5, 2, 2].length) (baseStart_7853904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853904 prefixEnd_7853904 := by exact prefixLift 7853904
  have htrace : WordTrace (prefixWord ++ tailWord_7853904) baseStart_7853904 baseEnd_7853904 := by
    simpa [prefixWord, tailWord_7853904, baseEnd_7853904] using wordTrace_append hprefix tailTrace_7853904
  have hstable : (prefixWord ++ tailWord_7853904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853904).length < 2 ^ (prefixWord ++ tailWord_7853904).sum := by decide
  have hdescent : baseEnd_7853904 < baseStart_7853904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853937 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 3, 3, 3]
def baseStart_7853937 : Nat := 118140960795 + 7853937 * 2 ^ 59
def prefixEnd_7853937 : Nat := 4983230072969 + 3 ^ 40 * 7853937 * 2
def baseEnd_7853937 : Nat := 4032844711131143169067907

theorem tailTrace_7853937 : CollatzResearch.WordTrace tailWord_7853937 prefixEnd_7853937 4032844711131143169067907 := by
  unfold tailWord_7853937
  simp only [CollatzResearch.WordTrace]
  refine ⟨286456615747535069494728065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190971077165023379663152043 286456615747535069494728065)
  ·
    refine ⟨214842461810651302121046049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286456615747535069494728065 214842461810651302121046049)
    ·
      refine ⟨161131846357988476590784537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214842461810651302121046049 161131846357988476590784537)
      ·
        refine ⟨120848884768491357443088403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161131846357988476590784537 120848884768491357443088403)
        ·
          refine ⟨181273327152737036164632605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120848884768491357443088403 181273327152737036164632605)
          ·
            refine ⟨67977497682276388561737227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181273327152737036164632605 67977497682276388561737227)
            ·
              refine ⟨101966246523414582842605841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67977497682276388561737227 101966246523414582842605841)
              ·
                refine ⟨76474684892560937131954381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101966246523414582842605841 76474684892560937131954381)
                ·
                  refine ⟨28678006834710351424482893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76474684892560937131954381 28678006834710351424482893)
                  ·
                    refine ⟨10754252563016381784181085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28678006834710351424482893 10754252563016381784181085)
                    ·
                      refine ⟨4032844711131143169067907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10754252563016381784181085 4032844711131143169067907)
                      ·
                        rfl

theorem cell23_7853937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_7853937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853937 prefixEnd_7853937 := by exact prefixLift 7853937
  have htrace : WordTrace (prefixWord ++ tailWord_7853937) baseStart_7853937 baseEnd_7853937 := by
    simpa [prefixWord, tailWord_7853937, baseEnd_7853937] using wordTrace_append hprefix tailTrace_7853937
  have hstable : (prefixWord ++ tailWord_7853937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853937).length < 2 ^ (prefixWord ++ tailWord_7853937).sum := by decide
  have hdescent : baseEnd_7853937 < baseStart_7853937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853982 : List Nat := [4, 3, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_7853982 : Nat := 118140960795 + 7853982 * 2 ^ 59
def prefixEnd_7853982 : Nat := 4983230072969 + 3 ^ 40 * 7853982 * 2
def baseEnd_7853982 : Nat := 1344289272586865164335067

theorem tailTrace_7853982 : CollatzResearch.WordTrace tailWord_7853982 prefixEnd_7853982 1344289272586865164335067 := by
  unfold tailWord_7853982
  simp only [CollatzResearch.WordTrace]
  refine ⟨35807282129046505272514525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190972171354914694786744133 35807282129046505272514525)
  ·
    refine ⟨13427730798392439477192947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35807282129046505272514525 13427730798392439477192947)
    ·
      refine ⟨20141596197588659215789421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13427730798392439477192947 20141596197588659215789421)
      ·
        refine ⟨7553098574095747205921033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20141596197588659215789421 7553098574095747205921033)
        ·
          refine ⟨5664823930571810404440775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7553098574095747205921033 5664823930571810404440775)
          ·
            refine ⟨8497235895857715606661163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5664823930571810404440775 8497235895857715606661163)
            ·
              refine ⟨12745853843786573409991745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8497235895857715606661163 12745853843786573409991745)
              ·
                refine ⟨9559390382839930057493809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12745853843786573409991745 9559390382839930057493809)
                ·
                  refine ⟨7169542787129947543120357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9559390382839930057493809 7169542787129947543120357)
                  ·
                    refine ⟨1344289272586865164335067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7169542787129947543120357 1344289272586865164335067)
                    ·
                      rfl

theorem cell23_7853982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_7853982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853982 prefixEnd_7853982 := by exact prefixLift 7853982
  have htrace : WordTrace (prefixWord ++ tailWord_7853982) baseStart_7853982 baseEnd_7853982 := by
    simpa [prefixWord, tailWord_7853982, baseEnd_7853982] using wordTrace_append hprefix tailTrace_7853982
  have hstable : (prefixWord ++ tailWord_7853982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853982).length < 2 ^ (prefixWord ++ tailWord_7853982).sum := by decide
  have hdescent : baseEnd_7853982 < baseStart_7853982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853988 : List Nat := [2, 3, 1, 2, 1, 5, 1, 2, 2, 1, 3]
def baseStart_7853988 : Nat := 118140960795 + 7853988 * 2 ^ 59
def prefixEnd_7853988 : Nat := 4983230072969 + 3 ^ 40 * 7853988 * 2
def baseEnd_7853988 : Nat := 4032870898644522469530173

theorem tailTrace_7853988 : CollatzResearch.WordTrace tailWord_7853988 prefixEnd_7853988 4032870898644522469530173 := by
  unfold tailWord_7853988
  simp only [CollatzResearch.WordTrace]
  refine ⟨143229237935175152602417309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190972317246900203469889745 143229237935175152602417309)
  ·
    refine ⟨53710964225690682225906491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143229237935175152602417309 53710964225690682225906491)
    ·
      refine ⟨80566446338536023338859737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53710964225690682225906491 80566446338536023338859737)
      ·
        refine ⟨60424834753902017504144803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80566446338536023338859737 60424834753902017504144803)
        ·
          refine ⟨90637252130853026256217205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60424834753902017504144803 90637252130853026256217205)
          ·
            refine ⟨8497242387267471211520363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90637252130853026256217205 8497242387267471211520363)
            ·
              refine ⟨12745863580901206817280545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8497242387267471211520363 12745863580901206817280545)
              ·
                refine ⟨9559397685675905112960409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12745863580901206817280545 9559397685675905112960409)
                ·
                  refine ⟨7169548264256928834720307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9559397685675905112960409 7169548264256928834720307)
                  ·
                    refine ⟨10754322396385393252080461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7169548264256928834720307 10754322396385393252080461)
                    ·
                      refine ⟨4032870898644522469530173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10754322396385393252080461 4032870898644522469530173)
                      ·
                        rfl

theorem cell23_7853988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_7853988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853988 prefixEnd_7853988 := by exact prefixLift 7853988
  have htrace : WordTrace (prefixWord ++ tailWord_7853988) baseStart_7853988 baseEnd_7853988 := by
    simpa [prefixWord, tailWord_7853988, baseEnd_7853988] using wordTrace_append hprefix tailTrace_7853988
  have hstable : (prefixWord ++ tailWord_7853988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853988).length < 2 ^ (prefixWord ++ tailWord_7853988).sum := by decide
  have hdescent : baseEnd_7853988 < baseStart_7853988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854062 : List Nat := [4, 1, 2, 1, 3, 3, 2, 1, 2, 2, 2]
def baseStart_7854062 : Nat := 118140960795 + 7854062 * 2 ^ 59
def prefixEnd_7854062 : Nat := 4983230072969 + 3 ^ 40 * 7854062 * 2
def baseEnd_7854062 : Nat := 4032908896212955180004833

theorem tailTrace_7854062 : CollatzResearch.WordTrace tailWord_7854062 prefixEnd_7854062 4032908896212955180004833 := by
  unfold tailWord_7854062
  simp only [CollatzResearch.WordTrace]
  refine ⟨35807646859010276980378555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190974116581388143895352293 35807646859010276980378555)
  ·
    refine ⟨53711470288515415470567833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35807646859010276980378555 53711470288515415470567833)
    ·
      refine ⟨40283602716386561602925875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53711470288515415470567833 40283602716386561602925875)
      ·
        refine ⟨60425404074579842404388813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40283602716386561602925875 60425404074579842404388813)
        ·
          refine ⟨22659526527967440901645805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60425404074579842404388813 22659526527967440901645805)
          ·
            refine ⟨8497322447987790338117177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22659526527967440901645805 8497322447987790338117177)
            ·
              refine ⟨6372991835990842753587883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8497322447987790338117177 6372991835990842753587883)
              ·
                refine ⟨9559487753986264130381825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6372991835990842753587883 9559487753986264130381825)
                ·
                  refine ⟨7169615815489698097786369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9559487753986264130381825 7169615815489698097786369)
                  ·
                    refine ⟨5377211861617273573339777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7169615815489698097786369 5377211861617273573339777)
                    ·
                      refine ⟨4032908896212955180004833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5377211861617273573339777 4032908896212955180004833)
                      ·
                        rfl

theorem cell23_7854062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_7854062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854062 prefixEnd_7854062 := by exact prefixLift 7854062
  have htrace : WordTrace (prefixWord ++ tailWord_7854062) baseStart_7854062 baseEnd_7854062 := by
    simpa [prefixWord, tailWord_7854062, baseEnd_7854062] using wordTrace_append hprefix tailTrace_7854062
  have hstable : (prefixWord ++ tailWord_7854062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854062).length < 2 ^ (prefixWord ++ tailWord_7854062).sum := by decide
  have hdescent : baseEnd_7854062 < baseStart_7854062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854067 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 4]
def baseStart_7854067 : Nat := 118140960795 + 7854067 * 2 ^ 59
def prefixEnd_7854067 : Nat := 4983230072969 + 3 ^ 40 * 7854067 * 2
def baseEnd_7854067 : Nat := 4032911463616227660442309

theorem tailTrace_7854067 : CollatzResearch.WordTrace tailWord_7854067 prefixEnd_7854067 4032911463616227660442309 := by
  unfold tailWord_7854067
  simp only [CollatzResearch.WordTrace]
  refine ⟨286461357237064101696960455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190974238158042734464640303 286461357237064101696960455)
  ·
    refine ⟨429692035855596152545440683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286461357237064101696960455 429692035855596152545440683)
    ·
      refine ⟨644538053783394228818161025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429692035855596152545440683 644538053783394228818161025)
      ·
        refine ⟨483403540337545671613620769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 644538053783394228818161025 483403540337545671613620769)
        ·
          refine ⟨362552655253159253710215577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483403540337545671613620769 362552655253159253710215577)
          ·
            refine ⟨271914491439869440282661683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362552655253159253710215577 271914491439869440282661683)
            ·
              refine ⟨407871737159804160423992525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271914491439869440282661683 407871737159804160423992525)
              ·
                refine ⟨152951901434926560158997197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407871737159804160423992525 152951901434926560158997197)
                ·
                  refine ⟨57356963038097460059623949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152951901434926560158997197 57356963038097460059623949)
                  ·
                    refine ⟨21508861139286547522358981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57356963038097460059623949 21508861139286547522358981)
                    ·
                      refine ⟨4032911463616227660442309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21508861139286547522358981 4032911463616227660442309)
                      ·
                        rfl

theorem cell23_7854067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_7854067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854067 prefixEnd_7854067 := by exact prefixLift 7854067
  have htrace : WordTrace (prefixWord ++ tailWord_7854067) baseStart_7854067 baseEnd_7854067 := by
    simpa [prefixWord, tailWord_7854067, baseEnd_7854067] using wordTrace_append hprefix tailTrace_7854067
  have hstable : (prefixWord ++ tailWord_7854067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854067).length < 2 ^ (prefixWord ++ tailWord_7854067).sum := by decide
  have hdescent : baseEnd_7854067 < baseStart_7854067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854077 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 2, 8]
def baseStart_7854077 : Nat := 118140960795 + 7854077 * 2 ^ 59
def prefixEnd_7854077 : Nat := 4983230072969 + 3 ^ 40 * 7854077 * 2
def baseEnd_7854077 : Nat := 1344305532807590873772421

theorem tailTrace_7854077 : CollatzResearch.WordTrace tailWord_7854077 prefixEnd_7854077 1344305532807590873772421 := by
  unfold tailWord_7854077
  simp only [CollatzResearch.WordTrace]
  refine ⟨286461721967027873404824485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190974481311351915603216323 286461721967027873404824485)
  ·
    refine ⟨53711572868817726263404591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286461721967027873404824485 53711572868817726263404591)
    ·
      refine ⟨80567359303226589395106887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53711572868817726263404591 80567359303226589395106887)
      ·
        refine ⟨120851038954839884092660331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80567359303226589395106887 120851038954839884092660331)
        ·
          refine ⟨181276558432259826138990497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120851038954839884092660331 181276558432259826138990497)
          ·
            refine ⟨135957418824194869604242873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181276558432259826138990497 135957418824194869604242873)
            ·
              refine ⟨101968064118146152203182155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135957418824194869604242873 101968064118146152203182155)
              ·
                refine ⟨152952096177219228304773233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101968064118146152203182155 152952096177219228304773233)
                ·
                  refine ⟨114714072132914421228579925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152952096177219228304773233 114714072132914421228579925)
                  ·
                    refine ⟨1344305532807590873772421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114714072132914421228579925 1344305532807590873772421)
                    ·
                      rfl

theorem cell23_7854077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_7854077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854077 prefixEnd_7854077 := by exact prefixLift 7854077
  have htrace : WordTrace (prefixWord ++ tailWord_7854077) baseStart_7854077 baseEnd_7854077 := by
    simpa [prefixWord, tailWord_7854077, baseEnd_7854077] using wordTrace_append hprefix tailTrace_7854077
  have hstable : (prefixWord ++ tailWord_7854077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854077).length < 2 ^ (prefixWord ++ tailWord_7854077).sum := by decide
  have hdescent : baseEnd_7854077 < baseStart_7854077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854127 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 6]
def baseStart_7854127 : Nat := 118140960795 + 7854127 * 2 ^ 59
def prefixEnd_7854127 : Nat := 4983230072969 + 3 ^ 40 * 7854127 * 2
def baseEnd_7854127 : Nat := 4032942272455497425692033

theorem tailTrace_7854127 : CollatzResearch.WordTrace tailWord_7854127 prefixEnd_7854127 4032942272455497425692033 := by
  unfold tailWord_7854127
  simp only [CollatzResearch.WordTrace]
  refine ⟨286463545616846731944144635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190975697077897821296096423 286463545616846731944144635)
  ·
    refine ⟨429695318425270097916216953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286463545616846731944144635 429695318425270097916216953)
    ·
      refine ⟨322271488818952573437162715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429695318425270097916216953 322271488818952573437162715)
      ·
        refine ⟨483407233228428860155744073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322271488818952573437162715 483407233228428860155744073)
        ·
          refine ⟨362555424921321645116808055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483407233228428860155744073 362555424921321645116808055)
          ·
            refine ⟨543833137381982467675212083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362555424921321645116808055 543833137381982467675212083)
            ·
              refine ⟨815749706072973701512818125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543833137381982467675212083 815749706072973701512818125)
              ·
                refine ⟨305906139777365138067306797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 815749706072973701512818125 305906139777365138067306797)
                ·
                  refine ⟨114714802416511926775240049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305906139777365138067306797 114714802416511926775240049)
                  ·
                    refine ⟨86036101812383945081430037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114714802416511926775240049 86036101812383945081430037)
                    ·
                      refine ⟨4032942272455497425692033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86036101812383945081430037 4032942272455497425692033)
                      ·
                        rfl

theorem cell23_7854127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_7854127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854127 prefixEnd_7854127 := by exact prefixLift 7854127
  have htrace : WordTrace (prefixWord ++ tailWord_7854127) baseStart_7854127 baseEnd_7854127 := by
    simpa [prefixWord, tailWord_7854127, baseEnd_7854127] using wordTrace_append hprefix tailTrace_7854127
  have hstable : (prefixWord ++ tailWord_7854127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854127).length < 2 ^ (prefixWord ++ tailWord_7854127).sum := by decide
  have hdescent : baseEnd_7854127 < baseStart_7854127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854145 : List Nat := [1, 2, 5, 1, 2, 2, 2, 3, 1, 4]
def baseStart_7854145 : Nat := 118140960795 + 7854145 * 2 ^ 59
def prefixEnd_7854145 : Nat := 4983230072969 + 3 ^ 40 * 7854145 * 2
def baseEnd_7854145 : Nat := 1344317171702426118422317

theorem tailTrace_7854145 : CollatzResearch.WordTrace tailWord_7854145 prefixEnd_7854145 1344317171702426118422317 := by
  unfold tailWord_7854145
  simp only [CollatzResearch.WordTrace]
  refine ⟨286464202130781521018299889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190976134753854347345533259 286464202130781521018299889)
  ·
    refine ⟨214848151598086140763724917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286464202130781521018299889 214848151598086140763724917)
    ·
      refine ⟨20142014212320575696599211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214848151598086140763724917 20142014212320575696599211)
      ·
        refine ⟨30213021318480863544898817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20142014212320575696599211 30213021318480863544898817)
        ·
          refine ⟨22659765988860647658674113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30213021318480863544898817 22659765988860647658674113)
          ·
            refine ⟨16994824491645485744005585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22659765988860647658674113 16994824491645485744005585)
            ·
              refine ⟨12746118368734114308004189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16994824491645485744005585 12746118368734114308004189)
              ·
                refine ⟨4779794388275292865501571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12746118368734114308004189 4779794388275292865501571)
                ·
                  refine ⟨7169691582412939298252357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4779794388275292865501571 7169691582412939298252357)
                  ·
                    refine ⟨1344317171702426118422317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7169691582412939298252357 1344317171702426118422317)
                    ·
                      rfl

theorem cell23_7854145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_7854145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854145 prefixEnd_7854145 := by exact prefixLift 7854145
  have htrace : WordTrace (prefixWord ++ tailWord_7854145) baseStart_7854145 baseEnd_7854145 := by
    simpa [prefixWord, tailWord_7854145, baseEnd_7854145] using wordTrace_append hprefix tailTrace_7854145
  have hstable : (prefixWord ++ tailWord_7854145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854145).length < 2 ^ (prefixWord ++ tailWord_7854145).sum := by decide
  have hdescent : baseEnd_7854145 < baseStart_7854145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854151 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 5, 1, 3]
def baseStart_7854151 : Nat := 118140960795 + 7854151 * 2 ^ 59
def prefixEnd_7854151 : Nat := 4983230072969 + 3 ^ 40 * 7854151 * 2
def baseEnd_7854151 : Nat := 4032954595991205331791923

theorem tailTrace_7854151 : CollatzResearch.WordTrace tailWord_7854151 prefixEnd_7854151 4032954595991205331791923 := by
  unfold tailWord_7854151
  simp only [CollatzResearch.WordTrace]
  refine ⟨286464420968759784043018307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190976280645839856028678871 286464420968759784043018307)
  ·
    refine ⟨429696631453139676064527461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286464420968759784043018307 429696631453139676064527461)
    ·
      refine ⟨80568118397463689262098899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 429696631453139676064527461 80568118397463689262098899)
      ·
        refine ⟨120852177596195533893148349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80568118397463689262098899 120852177596195533893148349)
        ·
          refine ⟨45319566598573325209930631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120852177596195533893148349 45319566598573325209930631)
          ·
            refine ⟨67979349897859987814895947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45319566598573325209930631 67979349897859987814895947)
            ·
              refine ⟨101969024846789981722343921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67979349897859987814895947 101969024846789981722343921)
              ·
                refine ⟨76476768635092486291757941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101969024846789981722343921 76476768635092486291757941)
                ·
                  refine ⟨7169697059539920589852307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76476768635092486291757941 7169697059539920589852307)
                  ·
                    refine ⟨10754545589309880884778461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7169697059539920589852307 10754545589309880884778461)
                    ·
                      refine ⟨4032954595991205331791923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10754545589309880884778461 4032954595991205331791923)
                      ·
                        rfl

theorem cell23_7854151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_7854151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854151 prefixEnd_7854151 := by exact prefixLift 7854151
  have htrace : WordTrace (prefixWord ++ tailWord_7854151) baseStart_7854151 baseEnd_7854151 := by
    simpa [prefixWord, tailWord_7854151, baseEnd_7854151] using wordTrace_append hprefix tailTrace_7854151
  have hstable : (prefixWord ++ tailWord_7854151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854151).length < 2 ^ (prefixWord ++ tailWord_7854151).sum := by decide
  have hdescent : baseEnd_7854151 < baseStart_7854151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854161 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 4, 3, 2]
def baseStart_7854161 : Nat := 118140960795 + 7854161 * 2 ^ 59
def prefixEnd_7854161 : Nat := 4983230072969 + 3 ^ 40 * 7854161 * 2
def baseEnd_7854161 : Nat := 4032959730797750292666877

theorem tailTrace_7854161 : CollatzResearch.WordTrace tailWord_7854161 prefixEnd_7854161 4032959730797750292666877 := by
  unfold tailWord_7854161
  simp only [CollatzResearch.WordTrace]
  refine ⟨286464785698723555750882337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190976523799149037167254891 286464785698723555750882337)
  ·
    refine ⟨214848589274042666813161753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286464785698723555750882337 214848589274042666813161753)
    ·
      refine ⟨161136441955532000109871315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214848589274042666813161753 161136441955532000109871315)
      ·
        refine ⟨241704662933298000164806973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161136441955532000109871315 241704662933298000164806973)
        ·
          refine ⟨90639248599986750061802615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241704662933298000164806973 90639248599986750061802615)
          ·
            refine ⟨135958872899980125092703923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90639248599986750061802615 135958872899980125092703923)
            ·
              refine ⟨203938309349970187639055885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135958872899980125092703923 203938309349970187639055885)
              ·
                refine ⟨76476866006238820364645957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203938309349970187639055885 76476866006238820364645957)
                ·
                  refine ⟨14339412376169778818371117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76476866006238820364645957 14339412376169778818371117)
                  ·
                    refine ⟨5377279641063667056889169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14339412376169778818371117 5377279641063667056889169)
                    ·
                      refine ⟨4032959730797750292666877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5377279641063667056889169 4032959730797750292666877)
                      ·
                        rfl

theorem cell23_7854161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 3, 2].length) (baseStart_7854161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854161 prefixEnd_7854161 := by exact prefixLift 7854161
  have htrace : WordTrace (prefixWord ++ tailWord_7854161) baseStart_7854161 baseEnd_7854161 := by
    simpa [prefixWord, tailWord_7854161, baseEnd_7854161] using wordTrace_append hprefix tailTrace_7854161
  have hstable : (prefixWord ++ tailWord_7854161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854161).length < 2 ^ (prefixWord ++ tailWord_7854161).sum := by decide
  have hdescent : baseEnd_7854161 < baseStart_7854161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854168 : List Nat := [2, 1, 2, 2, 1, 5, 2, 1, 3, 1, 3]
def baseStart_7854168 : Nat := 118140960795 + 7854168 * 2 ^ 59
def prefixEnd_7854168 : Nat := 4983230072969 + 3 ^ 40 * 7854168 * 2
def baseEnd_7854168 : Nat := 4032963325162331765279345

theorem tailTrace_7854168 : CollatzResearch.WordTrace tailWord_7854168 prefixEnd_7854168 4032963325162331765279345 := by
  unfold tailWord_7854168
  simp only [CollatzResearch.WordTrace]
  refine ⟨143232520504849097973193579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190976694006465463964258105 143232520504849097973193579)
  ·
    refine ⟨214848780757273646959790369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143232520504849097973193579 214848780757273646959790369)
    ·
      refine ⟨161136585567955235219842777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214848780757273646959790369 161136585567955235219842777)
      ·
        refine ⟨120852439175966426414882083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161136585567955235219842777 120852439175966426414882083)
        ·
          refine ⟨181278658763949639622323125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120852439175966426414882083 181278658763949639622323125)
          ·
            refine ⟨16994874259120278714592793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181278658763949639622323125 16994874259120278714592793)
            ·
              refine ⟨12746155694340209035944595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16994874259120278714592793 12746155694340209035944595)
              ·
                refine ⟨19119233541510313553916893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12746155694340209035944595 19119233541510313553916893)
                ·
                  refine ⟨7169712578066367582718835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19119233541510313553916893 7169712578066367582718835)
                  ·
                    refine ⟨10754568867099551374078253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7169712578066367582718835 10754568867099551374078253)
                    ·
                      refine ⟨4032963325162331765279345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10754568867099551374078253 4032963325162331765279345)
                      ·
                        rfl

theorem cell23_7854168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_7854168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854168 prefixEnd_7854168 := by exact prefixLift 7854168
  have htrace : WordTrace (prefixWord ++ tailWord_7854168) baseStart_7854168 baseEnd_7854168 := by
    simpa [prefixWord, tailWord_7854168, baseEnd_7854168] using wordTrace_append hprefix tailTrace_7854168
  have hstable : (prefixWord ++ tailWord_7854168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854168).length < 2 ^ (prefixWord ++ tailWord_7854168).sum := by decide
  have hdescent : baseEnd_7854168 < baseStart_7854168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854191 : List Nat := [1, 1, 2, 1, 3, 4, 1, 4, 1, 1, 4]
def baseStart_7854191 : Nat := 118140960795 + 7854191 * 2 ^ 59
def prefixEnd_7854191 : Nat := 4983230072969 + 3 ^ 40 * 7854191 * 2
def baseEnd_7854191 : Nat := 4032975135217385175291739

theorem tailTrace_7854191 : CollatzResearch.WordTrace tailWord_7854191 prefixEnd_7854191 4032975135217385175291739 := by
  unfold tailWord_7854191
  simp only [CollatzResearch.WordTrace]
  refine ⟨286465879888614870874474427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190977253259076580582982951 286465879888614870874474427)
  ·
    refine ⟨429698819832922306311711641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286465879888614870874474427 429698819832922306311711641)
    ·
      refine ⟨322274114874691729733783731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429698819832922306311711641 322274114874691729733783731)
      ·
        refine ⟨483411172312037594600675597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322274114874691729733783731 483411172312037594600675597)
        ·
          refine ⟨181279189617014097975253349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 483411172312037594600675597 181279189617014097975253349)
          ·
            refine ⟨33989848053190143370360003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181279189617014097975253349 33989848053190143370360003)
            ·
              refine ⟨50984772079785215055540005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33989848053190143370360003 50984772079785215055540005)
              ·
                refine ⟨9559644764959727822913751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50984772079785215055540005 9559644764959727822913751)
                ·
                  refine ⟨14339467147439591734370627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9559644764959727822913751 14339467147439591734370627)
                  ·
                    refine ⟨21509200721159387601555941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14339467147439591734370627 21509200721159387601555941)
                    ·
                      refine ⟨4032975135217385175291739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21509200721159387601555941 4032975135217385175291739)
                      ·
                        rfl

theorem cell23_7854191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 1, 4].length) (baseStart_7854191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854191 prefixEnd_7854191 := by exact prefixLift 7854191
  have htrace : WordTrace (prefixWord ++ tailWord_7854191) baseStart_7854191 baseEnd_7854191 := by
    simpa [prefixWord, tailWord_7854191, baseEnd_7854191] using wordTrace_append hprefix tailTrace_7854191
  have hstable : (prefixWord ++ tailWord_7854191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854191).length < 2 ^ (prefixWord ++ tailWord_7854191).sum := by decide
  have hdescent : baseEnd_7854191 < baseStart_7854191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854201 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 4, 4]
def baseStart_7854201 : Nat := 118140960795 + 7854201 * 2 ^ 59
def prefixEnd_7854201 : Nat := 4983230072969 + 3 ^ 40 * 7854201 * 2
def baseEnd_7854201 : Nat := 1344326756674643378722231

theorem tailTrace_7854201 : CollatzResearch.WordTrace tailWord_7854201 prefixEnd_7854201 1344326756674643378722231 := by
  unfold tailWord_7854201
  simp only [CollatzResearch.WordTrace]
  refine ⟨286466244618578642582338457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190977496412385761721558971 286466244618578642582338457)
  ·
    refine ⟨214849683463933981936753843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286466244618578642582338457 214849683463933981936753843)
    ·
      refine ⟨322274525195900972905130765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214849683463933981936753843 322274525195900972905130765)
      ·
        refine ⟨120852946948462864839424037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322274525195900972905130765 120852946948462864839424037)
        ·
          refine ⟨22659927552836787157392007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120852946948462864839424037 22659927552836787157392007)
          ·
            refine ⟨33989891329255180736088011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22659927552836787157392007 33989891329255180736088011)
            ·
              refine ⟨50984836993882771104132017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33989891329255180736088011 50984836993882771104132017)
              ·
                refine ⟨38238627745412078328099013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50984836993882771104132017 38238627745412078328099013)
                ·
                  refine ⟨7169742702264764686518565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38238627745412078328099013 7169742702264764686518565)
                  ·
                    refine ⟨1344326756674643378722231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7169742702264764686518565 1344326756674643378722231)
                    ·
                      rfl

theorem cell23_7854201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 4].length) (baseStart_7854201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854201 prefixEnd_7854201 := by exact prefixLift 7854201
  have htrace : WordTrace (prefixWord ++ tailWord_7854201) baseStart_7854201 baseEnd_7854201 := by
    simpa [prefixWord, tailWord_7854201, baseEnd_7854201] using wordTrace_append hprefix tailTrace_7854201
  have hstable : (prefixWord ++ tailWord_7854201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854201).length < 2 ^ (prefixWord ++ tailWord_7854201).sum := by decide
  have hdescent : baseEnd_7854201 < baseStart_7854201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854211 : List Nat := [1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 5]
def baseStart_7854211 : Nat := 118140960795 + 7854211 * 2 ^ 59
def prefixEnd_7854211 : Nat := 4983230072969 + 3 ^ 40 * 7854211 * 2
def baseEnd_7854211 : Nat := 4032985404830475097041647

theorem tailTrace_7854211 : CollatzResearch.WordTrace tailWord_7854211 prefixEnd_7854211 4032985404830475097041647 := by
  unfold tailWord_7854211
  simp only [CollatzResearch.WordTrace]
  refine ⟨286466609348542414290202487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190977739565694942860134991 286466609348542414290202487)
  ·
    refine ⟨429699914022813621435303731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286466609348542414290202487 429699914022813621435303731)
    ·
      refine ⟨644549871034220432152955597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429699914022813621435303731 644549871034220432152955597)
      ·
        refine ⟨241706201637832662057358349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 644549871034220432152955597 241706201637832662057358349)
        ·
          refine ⟨90639825614187248271509381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241706201637832662057358349 90639825614187248271509381)
          ·
            refine ⟨16994967302660109050908009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90639825614187248271509381 16994967302660109050908009)
            ·
              refine ⟨12746225476995081788181007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16994967302660109050908009 12746225476995081788181007)
              ·
                refine ⟨19119338215492622682271511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12746225476995081788181007 19119338215492622682271511)
                ·
                  refine ⟨28679007323238934023407267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19119338215492622682271511 28679007323238934023407267)
                  ·
                    refine ⟨43018510984858401035110901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28679007323238934023407267 43018510984858401035110901)
                    ·
                      refine ⟨4032985404830475097041647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43018510984858401035110901 4032985404830475097041647)
                      ·
                        rfl

theorem cell23_7854211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_7854211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854211 prefixEnd_7854211 := by exact prefixLift 7854211
  have htrace : WordTrace (prefixWord ++ tailWord_7854211) baseStart_7854211 baseEnd_7854211 := by
    simpa [prefixWord, tailWord_7854211, baseEnd_7854211] using wordTrace_append hprefix tailTrace_7854211
  have hstable : (prefixWord ++ tailWord_7854211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854211).length < 2 ^ (prefixWord ++ tailWord_7854211).sum := by decide
  have hdescent : baseEnd_7854211 < baseStart_7854211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854231 : List Nat := [1, 1, 3, 3, 4, 1, 2, 8]
def baseStart_7854231 : Nat := 118140960795 + 7854231 * 2 ^ 59
def prefixEnd_7854231 : Nat := 4983230072969 + 3 ^ 40 * 7854231 * 2
def baseEnd_7854231 : Nat := 149370210164576482177465

theorem tailTrace_7854231 : CollatzResearch.WordTrace tailWord_7854231 prefixEnd_7854231 149370210164576482177465 := by
  unfold tailWord_7854231
  simp only [CollatzResearch.WordTrace]
  refine ⟨286467338808469957705930547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190978225872313305137287031 286467338808469957705930547)
  ·
    refine ⟨429701008212704936558895821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286467338808469957705930547 429701008212704936558895821)
    ·
      refine ⟨161137878079764351209585933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429701008212704936558895821 161137878079764351209585933)
      ·
        refine ⟨60426704279911631703594725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161137878079764351209585933 60426704279911631703594725)
        ·
          refine ⟨11330007052483430944424011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60426704279911631703594725 11330007052483430944424011)
          ·
            refine ⟨16995010578725146416636017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11330007052483430944424011 16995010578725146416636017)
            ·
              refine ⟨12746257934043859812477013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16995010578725146416636017 12746257934043859812477013)
              ·
                refine ⟨149370210164576482177465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12746257934043859812477013 149370210164576482177465)
                ·
                  rfl

theorem cell23_7854231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 8].length) (baseStart_7854231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854231 prefixEnd_7854231 := by exact prefixLift 7854231
  have htrace : WordTrace (prefixWord ++ tailWord_7854231) baseStart_7854231 baseEnd_7854231 := by
    simpa [prefixWord, tailWord_7854231, baseEnd_7854231] using wordTrace_append hprefix tailTrace_7854231
  have hstable : (prefixWord ++ tailWord_7854231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854231).length < 2 ^ (prefixWord ++ tailWord_7854231).sum := by decide
  have hdescent : baseEnd_7854231 < baseStart_7854231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854276 : List Nat := [2, 3, 3, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_7854276 : Nat := 118140960795 + 7854276 * 2 ^ 59
def prefixEnd_7854276 : Nat := 4983230072969 + 3 ^ 40 * 7854276 * 2
def baseEnd_7854276 : Nat := 4033018781073017342728849

theorem tailTrace_7854276 : CollatzResearch.WordTrace tailWord_7854276 prefixEnd_7854276 4033018781073017342728849 := by
  unfold tailWord_7854276
  simp only [CollatzResearch.WordTrace]
  refine ⟨143234490046653465195659341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190979320062204620260879121 143234490046653465195659341)
  ·
    refine ⟨53712933767495049448372253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143234490046653465195659341 53712933767495049448372253)
    ·
      refine ⟨20142350162810643543139595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53712933767495049448372253 20142350162810643543139595)
      ·
        refine ⟨30213525244215965314709393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20142350162810643543139595 30213525244215965314709393)
        ·
          refine ⟨22660143933161973986032045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30213525244215965314709393 22660143933161973986032045)
          ·
            refine ⟨8497553974935740244762017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22660143933161973986032045 8497553974935740244762017)
            ·
              refine ⟨6373165481201805183571513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8497553974935740244762017 6373165481201805183571513)
              ·
                refine ⟨4779874110901353887678635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6373165481201805183571513 4779874110901353887678635)
                ·
                  refine ⟨7169811166352030831517953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4779874110901353887678635 7169811166352030831517953)
                  ·
                    refine ⟨5377358374764023123638465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7169811166352030831517953 5377358374764023123638465)
                    ·
                      refine ⟨4033018781073017342728849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5377358374764023123638465 4033018781073017342728849)
                      ·
                        rfl

theorem cell23_7854276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_7854276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854276 prefixEnd_7854276 := by exact prefixLift 7854276
  have htrace : WordTrace (prefixWord ++ tailWord_7854276) baseStart_7854276 baseEnd_7854276 := by
    simpa [prefixWord, tailWord_7854276, baseEnd_7854276] using wordTrace_append hprefix tailTrace_7854276
  have hstable : (prefixWord ++ tailWord_7854276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854276).length < 2 ^ (prefixWord ++ tailWord_7854276).sum := by decide
  have hdescent : baseEnd_7854276 < baseStart_7854276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854298 : List Nat := [3, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2]
def baseStart_7854298 : Nat := 118140960795 + 7854298 * 2 ^ 59
def prefixEnd_7854298 : Nat := 4983230072969 + 3 ^ 40 * 7854298 * 2
def baseEnd_7854298 : Nat := 4033030077647416256653747

theorem tailTrace_7854298 : CollatzResearch.WordTrace tailWord_7854298 prefixEnd_7854298 4033030077647416256653747 := by
  unfold tailWord_7854298
  simp only [CollatzResearch.WordTrace]
  refine ⟨71617445624806807037154887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190979854999484818765746365 71617445624806807037154887)
  ·
    refine ⟨107426168437210210555732331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71617445624806807037154887 107426168437210210555732331)
    ·
      refine ⟨161139252655815315833598497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107426168437210210555732331 161139252655815315833598497)
      ·
        refine ⟨120854439491861486875198873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161139252655815315833598497 120854439491861486875198873)
        ·
          refine ⟨90640829618896115156399155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120854439491861486875198873 90640829618896115156399155)
          ·
            refine ⟨135961244428344172734598733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90640829618896115156399155 135961244428344172734598733)
            ·
              refine ⟨50985466660629064775474525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135961244428344172734598733 50985466660629064775474525)
              ·
                refine ⟨19119549997735899290802947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50985466660629064775474525 19119549997735899290802947)
                ·
                  refine ⟨28679324996603848936204421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19119549997735899290802947 28679324996603848936204421)
                  ·
                    refine ⟨5377373436863221675538329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28679324996603848936204421 5377373436863221675538329)
                    ·
                      refine ⟨4033030077647416256653747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5377373436863221675538329 4033030077647416256653747)
                      ·
                        rfl

theorem cell23_7854298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_7854298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854298 prefixEnd_7854298 := by exact prefixLift 7854298
  have htrace : WordTrace (prefixWord ++ tailWord_7854298) baseStart_7854298 baseEnd_7854298 := by
    simpa [prefixWord, tailWord_7854298, baseEnd_7854298] using wordTrace_append hprefix tailTrace_7854298
  have hstable : (prefixWord ++ tailWord_7854298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854298).length < 2 ^ (prefixWord ++ tailWord_7854298).sum := by decide
  have hdescent : baseEnd_7854298 < baseStart_7854298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854332 : List Nat := [2, 2, 2, 1, 4, 1, 3, 2, 2, 2, 2]
def baseStart_7854332 : Nat := 118140960795 + 7854332 * 2 ^ 59
def prefixEnd_7854332 : Nat := 4983230072969 + 3 ^ 40 * 7854332 * 2
def baseEnd_7854332 : Nat := 4033047535989669123628591

theorem tailTrace_7854332 : CollatzResearch.WordTrace tailWord_7854332 prefixEnd_7854332 4033047535989669123628591 := by
  unfold tailWord_7854332
  simp only [CollatzResearch.WordTrace]
  refine ⟨143235511290552025977678625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190980681720736034636904833 143235511290552025977678625)
  ·
    refine ⟨107426633467914019483258969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143235511290552025977678625 107426633467914019483258969)
    ·
      refine ⟨80569975100935514612444227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107426633467914019483258969 80569975100935514612444227)
      ·
        refine ⟨120854962651403271918666341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80569975100935514612444227 120854962651403271918666341)
        ·
          refine ⟨22660305497138113484749939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120854962651403271918666341 22660305497138113484749939)
          ·
            refine ⟨33990458245707170227124909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22660305497138113484749939 33990458245707170227124909)
            ·
              refine ⟨12746421842140188835171841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33990458245707170227124909 12746421842140188835171841)
              ·
                refine ⟨9559816381605141626378881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12746421842140188835171841 9559816381605141626378881)
                ·
                  refine ⟨7169862286203856219784161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9559816381605141626378881 7169862286203856219784161)
                  ·
                    refine ⟨5377396714652892164838121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7169862286203856219784161 5377396714652892164838121)
                    ·
                      refine ⟨4033047535989669123628591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5377396714652892164838121 4033047535989669123628591)
                      ·
                        rfl

theorem cell23_7854332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_7854332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854332 prefixEnd_7854332 := by exact prefixLift 7854332
  have htrace : WordTrace (prefixWord ++ tailWord_7854332) baseStart_7854332 baseEnd_7854332 := by
    simpa [prefixWord, tailWord_7854332, baseEnd_7854332] using wordTrace_append hprefix tailTrace_7854332
  have hstable : (prefixWord ++ tailWord_7854332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854332).length < 2 ^ (prefixWord ++ tailWord_7854332).sum := by decide
  have hdescent : baseEnd_7854332 < baseStart_7854332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854338 : List Nat := [3, 4, 1, 1, 2, 1, 1, 3, 7]
def baseStart_7854338 : Nat := 118140960795 + 7854338 * 2 ^ 59
def prefixEnd_7854338 : Nat := 4983230072969 + 3 ^ 40 * 7854338 * 2
def baseEnd_7854338 : Nat := 448116735208177344461507

theorem tailTrace_7854338 : CollatzResearch.WordTrace tailWord_7854338 prefixEnd_7854338 448116735208177344461507 := by
  unfold tailWord_7854338
  simp only [CollatzResearch.WordTrace]
  refine ⟨71617810354770578745018917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190980827612721543320050445 71617810354770578745018917)
  ·
    refine ⟨13428339441519483514691047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71617810354770578745018917 13428339441519483514691047)
    ·
      refine ⟨20142509162279225272036571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13428339441519483514691047 20142509162279225272036571)
      ·
        refine ⟨30213763743418837908054857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20142509162279225272036571 30213763743418837908054857)
        ·
          refine ⟨22660322807564128431041143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30213763743418837908054857 22660322807564128431041143)
          ·
            refine ⟨33990484211346192646561715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22660322807564128431041143 33990484211346192646561715)
            ·
              refine ⟨50985726317019288969842573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33990484211346192646561715 50985726317019288969842573)
              ·
                refine ⟨19119647368882233363690965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50985726317019288969842573 19119647368882233363690965)
                ·
                  refine ⟨448116735208177344461507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19119647368882233363690965 448116735208177344461507)
                  ·
                    rfl

theorem cell23_7854338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_7854338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854338 prefixEnd_7854338 := by exact prefixLift 7854338
  have htrace : WordTrace (prefixWord ++ tailWord_7854338) baseStart_7854338 baseEnd_7854338 := by
    simpa [prefixWord, tailWord_7854338, baseEnd_7854338] using wordTrace_append hprefix tailTrace_7854338
  have hstable : (prefixWord ++ tailWord_7854338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854338).length < 2 ^ (prefixWord ++ tailWord_7854338).sum := by decide
  have hdescent : baseEnd_7854338 < baseStart_7854338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854371 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 4]
def baseStart_7854371 : Nat := 118140960795 + 7854371 * 2 ^ 59
def prefixEnd_7854371 : Nat := 4983230072969 + 3 ^ 40 * 7854371 * 2
def baseEnd_7854371 : Nat := 4033067561735194471040911

theorem tailTrace_7854371 : CollatzResearch.WordTrace tailWord_7854371 prefixEnd_7854371 4033067561735194471040911 := by
  unfold tailWord_7854371
  simp only [CollatzResearch.WordTrace]
  refine ⟨286472445027962761616026967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190981630018641841077351311 286472445027962761616026967)
  ·
    refine ⟨429708667541944142424040451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286472445027962761616026967 429708667541944142424040451)
    ·
      refine ⟨644563001312916213636060677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429708667541944142424040451 644563001312916213636060677)
      ·
        refine ⟨120855562746171790056761377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 644563001312916213636060677 120855562746171790056761377)
        ·
          refine ⟨90641672059628842542571033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120855562746171790056761377 90641672059628842542571033)
          ·
            refine ⟨67981254044721631906928275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90641672059628842542571033 67981254044721631906928275)
            ·
              refine ⟨101971881067082447860392413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67981254044721631906928275 101971881067082447860392413)
              ·
                refine ⟨38239455400155917947647155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101971881067082447860392413 38239455400155917947647155)
                ·
                  refine ⟨57359183100233876921470733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38239455400155917947647155 57359183100233876921470733)
                  ·
                    refine ⟨21509693662587703845551525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57359183100233876921470733 21509693662587703845551525)
                    ·
                      refine ⟨4033067561735194471040911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21509693662587703845551525 4033067561735194471040911)
                      ·
                        rfl

theorem cell23_7854371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_7854371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854371 prefixEnd_7854371 := by exact prefixLift 7854371
  have htrace : WordTrace (prefixWord ++ tailWord_7854371) baseStart_7854371 baseEnd_7854371 := by
    simpa [prefixWord, tailWord_7854371, baseEnd_7854371] using wordTrace_append hprefix tailTrace_7854371
  have hstable : (prefixWord ++ tailWord_7854371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854371).length < 2 ^ (prefixWord ++ tailWord_7854371).sum := by decide
  have hdescent : baseEnd_7854371 < baseStart_7854371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854481 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 5]
def baseStart_7854481 : Nat := 118140960795 + 7854481 * 2 ^ 59
def prefixEnd_7854481 : Nat := 4983230072969 + 3 ^ 40 * 7854481 * 2
def baseEnd_7854481 : Nat := 4033124044607189040665405

theorem tailTrace_7854481 : CollatzResearch.WordTrace tailWord_7854481 prefixEnd_7854481 4033124044607189040665405 := by
  unfold tailWord_7854481
  simp only [CollatzResearch.WordTrace]
  refine ⟨286476457057564250402531297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190984304705042833601687531 286476457057564250402531297)
  ·
    refine ⟨214857342793173187801898473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286476457057564250402531297 214857342793173187801898473)
    ·
      refine ⟨161143007094879890851423855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214857342793173187801898473 161143007094879890851423855)
      ·
        refine ⟨241714510642319836277135783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161143007094879890851423855 241714510642319836277135783)
        ·
          refine ⟨362571765963479754415703675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241714510642319836277135783 362571765963479754415703675)
          ·
            refine ⟨543857648945219631623555513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362571765963479754415703675 543857648945219631623555513)
            ·
              refine ⟨407893236708914723717666635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543857648945219631623555513 407893236708914723717666635)
              ·
                refine ⟨611839855063372085576499953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407893236708914723717666635 611839855063372085576499953)
                ·
                  refine ⟨458879891297529064182374965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 611839855063372085576499953 458879891297529064182374965)
                  ·
                    refine ⟨43019989809143349767097653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 458879891297529064182374965 43019989809143349767097653)
                    ·
                      refine ⟨4033124044607189040665405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43019989809143349767097653 4033124044607189040665405)
                      ·
                        rfl

theorem cell23_7854481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_7854481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854481 prefixEnd_7854481 := by exact prefixLift 7854481
  have htrace : WordTrace (prefixWord ++ tailWord_7854481) baseStart_7854481 baseEnd_7854481 := by
    simpa [prefixWord, tailWord_7854481, baseEnd_7854481] using wordTrace_append hprefix tailTrace_7854481
  have hstable : (prefixWord ++ tailWord_7854481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854481).length < 2 ^ (prefixWord ++ tailWord_7854481).sum := by decide
  have hdescent : baseEnd_7854481 < baseStart_7854481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854495 : List Nat := [1, 1, 2, 5, 1, 1, 3, 3, 1, 1, 4]
def baseStart_7854495 : Nat := 118140960795 + 7854495 * 2 ^ 59
def prefixEnd_7854495 : Nat := 4983230072969 + 3 ^ 40 * 7854495 * 2
def baseEnd_7854495 : Nat := 4033131233336351985890341

theorem tailTrace_7854495 : CollatzResearch.WordTrace tailWord_7854495 prefixEnd_7854495 4033131233336351985890341 := by
  unfold tailWord_7854495
  simp only [CollatzResearch.WordTrace]
  refine ⟨286476967679513530793540939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190984645119675687195693959 286476967679513530793540939)
  ·
    refine ⟨429715451519270296190311409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286476967679513530793540939 429715451519270296190311409)
    ·
      refine ⟨322286588639452722142733557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429715451519270296190311409 322286588639452722142733557)
      ·
        refine ⟨30214367684948692700881271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 322286588639452722142733557 30214367684948692700881271)
        ·
          refine ⟨45321551527423039051321907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30214367684948692700881271 45321551527423039051321907)
          ·
            refine ⟨67982327291134558576982861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45321551527423039051321907 67982327291134558576982861)
            ·
              refine ⟨25493372734175459466368573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67982327291134558576982861 25493372734175459466368573)
              ·
                refine ⟨9560014775315797299888215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25493372734175459466368573 9560014775315797299888215)
                ·
                  refine ⟨14340022162973695949832323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9560014775315797299888215 14340022162973695949832323)
                  ·
                    refine ⟨21510033244460543924748485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14340022162973695949832323 21510033244460543924748485)
                    ·
                      refine ⟨4033131233336351985890341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21510033244460543924748485 4033131233336351985890341)
                      ·
                        rfl

theorem cell23_7854495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_7854495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854495 prefixEnd_7854495 := by exact prefixLift 7854495
  have htrace : WordTrace (prefixWord ++ tailWord_7854495) baseStart_7854495 baseEnd_7854495 := by
    simpa [prefixWord, tailWord_7854495, baseEnd_7854495] using wordTrace_append hprefix tailTrace_7854495
  have hstable : (prefixWord ++ tailWord_7854495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854495).length < 2 ^ (prefixWord ++ tailWord_7854495).sum := by decide
  have hdescent : baseEnd_7854495 < baseStart_7854495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854501 : List Nat := [1, 3, 1, 2, 1, 1, 14]
def baseStart_7854501 : Nat := 118140960795 + 7854501 * 2 ^ 59
def prefixEnd_7854501 : Nat := 4983230072969 + 3 ^ 40 * 7854501 * 2
def baseEnd_7854501 : Nat := 49791781657040481017473

theorem tailTrace_7854501 : CollatzResearch.WordTrace tailWord_7854501 prefixEnd_7854501 49791781657040481017473 := by
  unfold tailWord_7854501
  simp only [CollatzResearch.WordTrace]
  refine ⟨286477186517491793818259357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190984791011661195878839571 286477186517491793818259357)
  ·
    refine ⟨107428944944059422681847259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286477186517491793818259357 107428944944059422681847259)
    ·
      refine ⟨161143417416089134022770889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107428944944059422681847259 161143417416089134022770889)
      ·
        refine ⟨120857563062066850517078167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161143417416089134022770889 120857563062066850517078167)
        ·
          refine ⟨181286344593100275775617251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120857563062066850517078167 181286344593100275775617251)
          ·
            refine ⟨271929516889650413663425877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181286344593100275775617251 271929516889650413663425877)
            ·
              refine ⟨49791781657040481017473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 271929516889650413663425877 49791781657040481017473)
              ·
                rfl

theorem cell23_7854501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 14].length) (baseStart_7854501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854501 prefixEnd_7854501 := by exact prefixLift 7854501
  have htrace : WordTrace (prefixWord ++ tailWord_7854501) baseStart_7854501 baseEnd_7854501 := by
    simpa [prefixWord, tailWord_7854501, baseEnd_7854501] using wordTrace_append hprefix tailTrace_7854501
  have hstable : (prefixWord ++ tailWord_7854501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854501).length < 2 ^ (prefixWord ++ tailWord_7854501).sum := by decide
  have hdescent : baseEnd_7854501 < baseStart_7854501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854511 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 7]
def baseStart_7854511 : Nat := 118140960795 + 7854511 * 2 ^ 59
def prefixEnd_7854511 : Nat := 4983230072969 + 3 ^ 40 * 7854511 * 2
def baseEnd_7854511 : Nat := 4033139449026823923290267

theorem tailTrace_7854511 : CollatzResearch.WordTrace tailWord_7854511 prefixEnd_7854511 4033139449026823923290267 := by
  unfold tailWord_7854511
  simp only [CollatzResearch.WordTrace]
  refine ⟨286477551247455565526123387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190985034164970377017415591 286477551247455565526123387)
  ·
    refine ⟨429716326871183348289185081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286477551247455565526123387 429716326871183348289185081)
    ·
      refine ⟨322287245153387511216888811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429716326871183348289185081 322287245153387511216888811)
      ·
        refine ⟨483430867730081266825333217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322287245153387511216888811 483430867730081266825333217)
        ·
          refine ⟨362573150797560950118999913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483430867730081266825333217 362573150797560950118999913)
          ·
            refine ⟨271929863098170712589249935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362573150797560950118999913 271929863098170712589249935)
            ·
              refine ⟨407894794647256068883874903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271929863098170712589249935 407894794647256068883874903)
              ·
                refine ⟨611842191970884103325812355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407894794647256068883874903 611842191970884103325812355)
                ·
                  refine ⟨917763287956326154988718533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 611842191970884103325812355 917763287956326154988718533)
                  ·
                    refine ⟨172080616491811154060384725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 917763287956326154988718533 172080616491811154060384725)
                    ·
                      refine ⟨4033139449026823923290267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172080616491811154060384725 4033139449026823923290267)
                      ·
                        rfl

theorem cell23_7854511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_7854511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854511 prefixEnd_7854511 := by exact prefixLift 7854511
  have htrace : WordTrace (prefixWord ++ tailWord_7854511) baseStart_7854511 baseEnd_7854511 := by
    simpa [prefixWord, tailWord_7854511, baseEnd_7854511] using wordTrace_append hprefix tailTrace_7854511
  have hstable : (prefixWord ++ tailWord_7854511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854511).length < 2 ^ (prefixWord ++ tailWord_7854511).sum := by decide
  have hdescent : baseEnd_7854511 < baseStart_7854511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854525 : List Nat := [1, 4, 1, 2, 2, 2, 3, 1, 1, 2, 4]
def baseStart_7854525 : Nat := 118140960795 + 7854525 * 2 ^ 59
def prefixEnd_7854525 : Nat := 4983230072969 + 3 ^ 40 * 7854525 * 2
def baseEnd_7854525 : Nat := 4033146637755986868515203

theorem tailTrace_7854525 : CollatzResearch.WordTrace tailWord_7854525 prefixEnd_7854525 4033146637755986868515203 := by
  unfold tailWord_7854525
  simp only [CollatzResearch.WordTrace]
  refine ⟨286478061869404845917133029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190985374579603230611422019 286478061869404845917133029)
  ·
    refine ⟨53714636600513408609462443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286478061869404845917133029 53714636600513408609462443)
    ·
      refine ⟨80571954900770112914193665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53714636600513408609462443 80571954900770112914193665)
      ·
        refine ⟨60428966175577584685645249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80571954900770112914193665 60428966175577584685645249)
        ·
          refine ⟨45321724631683188514233937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60428966175577584685645249 45321724631683188514233937)
          ·
            refine ⟨33991293473762391385675453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45321724631683188514233937 33991293473762391385675453)
            ·
              refine ⟨12746735052660896769628295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33991293473762391385675453 12746735052660896769628295)
              ·
                refine ⟨19120102578991345154442443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12746735052660896769628295 19120102578991345154442443)
                ·
                  refine ⟨28680153868487017731663665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19120102578991345154442443 28680153868487017731663665)
                  ·
                    refine ⟨21510115401365263298747749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28680153868487017731663665 21510115401365263298747749)
                    ·
                      refine ⟨4033146637755986868515203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21510115401365263298747749 4033146637755986868515203)
                      ·
                        rfl

theorem cell23_7854525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_7854525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854525 prefixEnd_7854525 := by exact prefixLift 7854525
  have htrace : WordTrace (prefixWord ++ tailWord_7854525) baseStart_7854525 baseEnd_7854525 := by
    simpa [prefixWord, tailWord_7854525, baseEnd_7854525] using wordTrace_append hprefix tailTrace_7854525
  have hstable : (prefixWord ++ tailWord_7854525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854525).length < 2 ^ (prefixWord ++ tailWord_7854525).sum := by decide
  have hdescent : baseEnd_7854525 < baseStart_7854525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854535 : List Nat := [1, 1, 4, 1, 1, 6, 2, 7]
def baseStart_7854535 : Nat := 118140960795 + 7854535 * 2 ^ 59
def prefixEnd_7854535 : Nat := 4983230072969 + 3 ^ 40 * 7854535 * 2
def baseEnd_7854535 : Nat := 149375991576390067755191

theorem tailTrace_7854535 : CollatzResearch.WordTrace tailWord_7854535 prefixEnd_7854535 149375991576390067755191 := by
  unfold tailWord_7854535
  simp only [CollatzResearch.WordTrace]
  refine ⟨286478426599368617624997059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190985617732912411749998039 286478426599368617624997059)
  ·
    refine ⟨429717639899052926437495589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286478426599368617624997059 429717639899052926437495589)
    ·
      refine ⟨80572057481072423707030423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 429717639899052926437495589 80572057481072423707030423)
      ·
        refine ⟨120858086221608635560545635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80572057481072423707030423 120858086221608635560545635)
        ·
          refine ⟨181287129332412953340818453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120858086221608635560545635 181287129332412953340818453)
          ·
            refine ⟨8497834187456857187850865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 181287129332412953340818453 8497834187456857187850865)
            ·
              refine ⟨6373375640592642890888149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8497834187456857187850865 6373375640592642890888149)
              ·
                refine ⟨149375991576390067755191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6373375640592642890888149 149375991576390067755191)
                ·
                  rfl

theorem cell23_7854535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 7].length) (baseStart_7854535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854535 prefixEnd_7854535 := by exact prefixLift 7854535
  have htrace : WordTrace (prefixWord ++ tailWord_7854535) baseStart_7854535 baseEnd_7854535 := by
    simpa [prefixWord, tailWord_7854535, baseEnd_7854535] using wordTrace_append hprefix tailTrace_7854535
  have hstable : (prefixWord ++ tailWord_7854535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854535).length < 2 ^ (prefixWord ++ tailWord_7854535).sum := by decide
  have hdescent : baseEnd_7854535 < baseStart_7854535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854563 : List Nat := [1, 1, 1, 6, 3, 1, 3, 2, 1, 2, 2]
def baseStart_7854563 : Nat := 118140960795 + 7854563 * 2 ^ 59
def prefixEnd_7854563 : Nat := 4983230072969 + 3 ^ 40 * 7854563 * 2
def baseEnd_7854563 : Nat := 4033166150020857719840029

theorem tailTrace_7854563 : CollatzResearch.WordTrace tailWord_7854563 prefixEnd_7854563 4033166150020857719840029 := by
  unfold tailWord_7854563
  simp only [CollatzResearch.WordTrace]
  refine ⟨286479447843267178407016343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190986298562178118938010895 286479447843267178407016343)
  ·
    refine ⟨429719171764900767610524515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286479447843267178407016343 429719171764900767610524515)
    ·
      refine ⟨644578757647351151415786773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429719171764900767610524515 644578757647351151415786773)
      ·
        refine ⟨30214629264719585222615005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 644578757647351151415786773 30214629264719585222615005)
        ·
          refine ⟨11330485974269844458480627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30214629264719585222615005 11330485974269844458480627)
          ·
            refine ⟨16995728961404766687720941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11330485974269844458480627 16995728961404766687720941)
            ·
              refine ⟨6373398360526787507895353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16995728961404766687720941 6373398360526787507895353)
              ·
                refine ⟨4780048770395090630921515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6373398360526787507895353 4780048770395090630921515)
                ·
                  refine ⟨7170073155592635946382273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4780048770395090630921515 7170073155592635946382273)
                  ·
                    refine ⟨5377554866694476959786705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7170073155592635946382273 5377554866694476959786705)
                    ·
                      refine ⟨4033166150020857719840029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5377554866694476959786705 4033166150020857719840029)
                      ·
                        rfl

theorem cell23_7854563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_7854563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854563 prefixEnd_7854563 := by exact prefixLift 7854563
  have htrace : WordTrace (prefixWord ++ tailWord_7854563) baseStart_7854563 baseEnd_7854563 := by
    simpa [prefixWord, tailWord_7854563, baseEnd_7854563] using wordTrace_append hprefix tailTrace_7854563
  have hstable : (prefixWord ++ tailWord_7854563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854563).length < 2 ^ (prefixWord ++ tailWord_7854563).sum := by decide
  have hdescent : baseEnd_7854563 < baseStart_7854563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854602 : List Nat := [3, 1, 2, 2, 2, 1, 3, 2, 1, 4, 2]
def baseStart_7854602 : Nat := 118140960795 + 7854602 * 2 ^ 59
def prefixEnd_7854602 : Nat := 4983230072969 + 3 ^ 40 * 7854602 * 2
def baseEnd_7854602 : Nat := 4033186175766383067252349

theorem tailTrace_7854602 : CollatzResearch.WordTrace tailWord_7854602 prefixEnd_7854602 4033186175766383067252349 := by
  unfold tailWord_7854602
  simp only [CollatzResearch.WordTrace]
  refine ⟨71620217572531472016921515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190987246860083925378457373 71620217572531472016921515)
  ·
    refine ⟨107430326358797208025382273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71620217572531472016921515 107430326358797208025382273)
    ·
      refine ⟨80572744769097906019036705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107430326358797208025382273 80572744769097906019036705)
      ·
        refine ⟨60429558576823429514277529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80572744769097906019036705 60429558576823429514277529)
        ·
          refine ⟨45322168932617572135708147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60429558576823429514277529 45322168932617572135708147)
          ·
            refine ⟨67983253398926358203562221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45322168932617572135708147 67983253398926358203562221)
            ·
              refine ⟨25493720024597384326335833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67983253398926358203562221 25493720024597384326335833)
              ·
                refine ⟨19120290018448038244751875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25493720024597384326335833 19120290018448038244751875)
                ·
                  refine ⟨28680435027672057367127813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19120290018448038244751875 28680435027672057367127813)
                  ·
                    refine ⟨5377581567688510756336465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28680435027672057367127813 5377581567688510756336465)
                    ·
                      refine ⟨4033186175766383067252349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5377581567688510756336465 4033186175766383067252349)
                      ·
                        rfl

theorem cell23_7854602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_7854602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854602 prefixEnd_7854602 := by exact prefixLift 7854602
  have htrace : WordTrace (prefixWord ++ tailWord_7854602) baseStart_7854602 baseEnd_7854602 := by
    simpa [prefixWord, tailWord_7854602, baseEnd_7854602] using wordTrace_append hprefix tailTrace_7854602
  have hstable : (prefixWord ++ tailWord_7854602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854602).length < 2 ^ (prefixWord ++ tailWord_7854602).sum := by decide
  have hdescent : baseEnd_7854602 < baseStart_7854602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854606 : List Nat := [4, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2]
def baseStart_7854606 : Nat := 118140960795 + 7854606 * 2 ^ 59
def prefixEnd_7854606 : Nat := 4983230072969 + 3 ^ 40 * 7854606 * 2
def baseEnd_7854606 : Nat := 4033188229689001051602331

theorem tailTrace_7854606 : CollatzResearch.WordTrace tailWord_7854606 prefixEnd_7854606 4033188229689001051602331 := by
  unfold tailWord_7854606
  simp only [CollatzResearch.WordTrace]
  refine ⟨35810127022763924593853959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190987344121407597833887781 35810127022763924593853959)
  ·
    refine ⟨53715190534145886890780939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35810127022763924593853959 53715190534145886890780939)
    ·
      refine ⟨80572785801218830336171409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53715190534145886890780939 80572785801218830336171409)
      ·
        refine ⟨60429589350914122752128557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80572785801218830336171409 60429589350914122752128557)
        ·
          refine ⟨22661096006592796032048209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60429589350914122752128557 22661096006592796032048209)
          ·
            refine ⟨16995822004944597024036157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22661096006592796032048209 16995822004944597024036157)
            ·
              refine ⟨6373433251854223884013559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16995822004944597024036157 6373433251854223884013559)
              ·
                refine ⟨9560149877781335826020339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6373433251854223884013559 9560149877781335826020339)
                ·
                  refine ⟨14340224816672003739030509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9560149877781335826020339 14340224816672003739030509)
                  ·
                    refine ⟨5377584306252001402136441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14340224816672003739030509 5377584306252001402136441)
                    ·
                      refine ⟨4033188229689001051602331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5377584306252001402136441 4033188229689001051602331)
                      ·
                        rfl

theorem cell23_7854606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_7854606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854606 prefixEnd_7854606 := by exact prefixLift 7854606
  have htrace : WordTrace (prefixWord ++ tailWord_7854606) baseStart_7854606 baseEnd_7854606 := by
    simpa [prefixWord, tailWord_7854606, baseEnd_7854606] using wordTrace_append hprefix tailTrace_7854606
  have hstable : (prefixWord ++ tailWord_7854606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854606).length < 2 ^ (prefixWord ++ tailWord_7854606).sum := by decide
  have hdescent : baseEnd_7854606 < baseStart_7854606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854618 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7]
def baseStart_7854618 : Nat := 118140960795 + 7854618 * 2 ^ 59
def prefixEnd_7854618 : Nat := 4983230072969 + 3 ^ 40 * 7854618 * 2
def baseEnd_7854618 : Nat := 4033194391456855004652275

theorem tailTrace_7854618 : CollatzResearch.WordTrace tailWord_7854618 prefixEnd_7854618 4033194391456855004652275 := by
  unfold tailWord_7854618
  simp only [CollatzResearch.WordTrace]
  refine ⟨71620363464516980700067127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190987635905378615200179005 71620363464516980700067127)
  ·
    refine ⟨107430545196775471050100691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71620363464516980700067127 107430545196775471050100691)
    ·
      refine ⟨161145817795163206575151037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107430545196775471050100691 161145817795163206575151037)
      ·
        refine ⟨60429681673186202465681639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161145817795163206575151037 60429681673186202465681639)
        ·
          refine ⟨90644522509779303698522459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60429681673186202465681639 90644522509779303698522459)
          ·
            refine ⟨135966783764668955547783689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90644522509779303698522459 135966783764668955547783689)
            ·
              refine ⟨101975087823501716660837767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135966783764668955547783689 101975087823501716660837767)
              ·
                refine ⟨152962631735252574991256651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101975087823501716660837767 152962631735252574991256651)
                ·
                  refine ⟨229443947602878862486884977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152962631735252574991256651 229443947602878862486884977)
                  ·
                    refine ⟨172082960702159146865163733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 229443947602878862486884977 172082960702159146865163733)
                    ·
                      refine ⟨4033194391456855004652275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172082960702159146865163733 4033194391456855004652275)
                      ·
                        rfl

theorem cell23_7854618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_7854618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854618 prefixEnd_7854618 := by exact prefixLift 7854618
  have htrace : WordTrace (prefixWord ++ tailWord_7854618) baseStart_7854618 baseEnd_7854618 := by
    simpa [prefixWord, tailWord_7854618, baseEnd_7854618] using wordTrace_append hprefix tailTrace_7854618
  have hstable : (prefixWord ++ tailWord_7854618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854618).length < 2 ^ (prefixWord ++ tailWord_7854618).sum := by decide
  have hdescent : baseEnd_7854618 < baseStart_7854618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854632 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_7854632 : Nat := 118140960795 + 7854632 * 2 ^ 59
def prefixEnd_7854632 : Nat := 4983230072969 + 3 ^ 40 * 7854632 * 2
def baseEnd_7854632 : Nat := 4033201580186017949877211

theorem tailTrace_7854632 : CollatzResearch.WordTrace tailWord_7854632 prefixEnd_7854632 4033201580186017949877211 := by
  unfold tailWord_7854632
  simp only [CollatzResearch.WordTrace]
  refine ⟨143240982240008601595639075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190987976320011468794185433 143240982240008601595639075)
  ·
    refine ⟨214861473360012902393458613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143240982240008601595639075 214861473360012902393458613)
    ·
      refine ⟨20143263127501209599386745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214861473360012902393458613 20143263127501209599386745)
      ·
        refine ⟨15107447345625907199540059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20143263127501209599386745 15107447345625907199540059)
        ·
          refine ⟨22661171018438860799310089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15107447345625907199540059 22661171018438860799310089)
          ·
            refine ⟨16995878263829145599482567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22661171018438860799310089 16995878263829145599482567)
            ·
              refine ⟨25493817395743718399223851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16995878263829145599482567 25493817395743718399223851)
              ·
                refine ⟨38240726093615577598835777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25493817395743718399223851 38240726093615577598835777)
                ·
                  refine ⟨28680544570211683199126833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38240726093615577598835777 28680544570211683199126833)
                  ·
                    refine ⟨21510408427658762399345125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28680544570211683199126833 21510408427658762399345125)
                    ·
                      refine ⟨4033201580186017949877211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21510408427658762399345125 4033201580186017949877211)
                      ·
                        rfl

theorem cell23_7854632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_7854632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854632 prefixEnd_7854632 := by exact prefixLift 7854632
  have htrace : WordTrace (prefixWord ++ tailWord_7854632) baseStart_7854632 baseEnd_7854632 := by
    simpa [prefixWord, tailWord_7854632, baseEnd_7854632] using wordTrace_append hprefix tailTrace_7854632
  have hstable : (prefixWord ++ tailWord_7854632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854632).length < 2 ^ (prefixWord ++ tailWord_7854632).sum := by decide
  have hdescent : baseEnd_7854632 < baseStart_7854632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854692 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 2, 4, 2]
def baseStart_7854692 : Nat := 118140960795 + 7854692 * 2 ^ 59
def prefixEnd_7854692 : Nat := 4983230072969 + 3 ^ 40 * 7854692 * 2
def baseEnd_7854692 : Nat := 4033232389025287715126935

theorem tailTrace_7854692 : CollatzResearch.WordTrace tailWord_7854692 prefixEnd_7854692 4033232389025287715126935 := by
  unfold tailWord_7854692
  simp only [CollatzResearch.WordTrace]
  refine ⟨143242076429899916719231165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190989435239866555625641553 143242076429899916719231165)
  ·
    refine ⟨53715778661212468769711687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143242076429899916719231165 53715778661212468769711687)
    ·
      refine ⟨80573667991818703154567531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53715778661212468769711687 80573667991818703154567531)
      ·
        refine ⟨120860501987728054731851297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80573667991818703154567531 120860501987728054731851297)
        ·
          refine ⟨90645376490796041048888473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120860501987728054731851297 90645376490796041048888473)
          ·
            refine ⟨67984032368097030786666355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90645376490796041048888473 67984032368097030786666355)
            ·
              refine ⟨101976048552145546179999533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67984032368097030786666355 101976048552145546179999533)
              ·
                refine ⟨38241018207054579817499825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101976048552145546179999533 38241018207054579817499825)
                ·
                  refine ⟨28680763655290934863124869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38241018207054579817499825 28680763655290934863124869)
                  ·
                    refine ⟨5377643185367050286835913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28680763655290934863124869 5377643185367050286835913)
                    ·
                      refine ⟨4033232389025287715126935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5377643185367050286835913 4033232389025287715126935)
                      ·
                        rfl

theorem cell23_7854692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_7854692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854692 prefixEnd_7854692 := by exact prefixLift 7854692
  have htrace : WordTrace (prefixWord ++ tailWord_7854692) baseStart_7854692 baseEnd_7854692 := by
    simpa [prefixWord, tailWord_7854692, baseEnd_7854692] using wordTrace_append hprefix tailTrace_7854692
  have hstable : (prefixWord ++ tailWord_7854692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854692).length < 2 ^ (prefixWord ++ tailWord_7854692).sum := by decide
  have hdescent : baseEnd_7854692 < baseStart_7854692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854745 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 3, 5]
def baseStart_7854745 : Nat := 118140960795 + 7854745 * 2 ^ 59
def prefixEnd_7854745 : Nat := 4983230072969 + 3 ^ 40 * 7854745 * 2
def baseEnd_7854745 : Nat := 1344419867833325335921397

theorem tailTrace_7854745 : CollatzResearch.WordTrace tailWord_7854745 prefixEnd_7854745 1344419867833325335921397 := by
  unfold tailWord_7854745
  simp only [CollatzResearch.WordTrace]
  refine ⟨286486085928607823490141689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190990723952405215660094459 286486085928607823490141689)
  ·
    refine ⟨214864564446455867617606267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286486085928607823490141689 214864564446455867617606267)
    ·
      refine ⟨322296846669683801426409401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214864564446455867617606267 322296846669683801426409401)
      ·
        refine ⟨241722635002262851069807051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322296846669683801426409401 241722635002262851069807051)
        ·
          refine ⟨362583952503394276604710577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241722635002262851069807051 362583952503394276604710577)
          ·
            refine ⟨271937964377545707453532933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362583952503394276604710577 271937964377545707453532933)
            ·
              refine ⟨50988368320789820147537425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 271937964377545707453532933 50988368320789820147537425)
              ·
                refine ⟨38241276240592365110653069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50988368320789820147537425 38241276240592365110653069)
                ·
                  refine ⟨14340478590222136916494901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38241276240592365110653069 14340478590222136916494901)
                  ·
                    refine ⟨1344419867833325335921397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14340478590222136916494901 1344419867833325335921397)
                    ·
                      rfl

theorem cell23_7854745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 5].length) (baseStart_7854745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854745 prefixEnd_7854745 := by exact prefixLift 7854745
  have htrace : WordTrace (prefixWord ++ tailWord_7854745) baseStart_7854745 baseEnd_7854745 := by
    simpa [prefixWord, tailWord_7854745, baseEnd_7854745] using wordTrace_append hprefix tailTrace_7854745
  have hstable : (prefixWord ++ tailWord_7854745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854745).length < 2 ^ (prefixWord ++ tailWord_7854745).sum := by decide
  have hdescent : baseEnd_7854745 < baseStart_7854745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854819 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 3]
def baseStart_7854819 : Nat := 118140960795 + 7854819 * 2 ^ 59
def prefixEnd_7854819 : Nat := 4983230072969 + 3 ^ 40 * 7854819 * 2
def baseEnd_7854819 : Nat := 4033297601068408718238851

theorem tailTrace_7854819 : CollatzResearch.WordTrace tailWord_7854819 prefixEnd_7854819 4033297601068408718238851 := by
  unfold tailWord_7854819
  simp only [CollatzResearch.WordTrace]
  refine ⟨286488784930339734128335511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190992523286893156085557007 286488784930339734128335511)
  ·
    refine ⟨429733177395509601192503267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286488784930339734128335511 429733177395509601192503267)
    ·
      refine ⟨644599766093264401788754901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429733177395509601192503267 644599766093264401788754901)
      ·
        refine ⟨15107807017810884416923943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 644599766093264401788754901 15107807017810884416923943)
        ·
          refine ⟨22661710526716326625385915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15107807017810884416923943 22661710526716326625385915)
          ·
            refine ⟨33992565790074489938078873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22661710526716326625385915 33992565790074489938078873)
            ·
              refine ⟨25494424342555867453559155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33992565790074489938078873 25494424342555867453559155)
              ·
                refine ⟨38241636513833801180338733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25494424342555867453559155 38241636513833801180338733)
                ·
                  refine ⟨14340613692687675442627025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38241636513833801180338733 14340613692687675442627025)
                  ·
                    refine ⟨10755460269515756581970269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14340613692687675442627025 10755460269515756581970269)
                    ·
                      refine ⟨4033297601068408718238851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10755460269515756581970269 4033297601068408718238851)
                      ·
                        rfl

theorem cell23_7854819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_7854819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854819 prefixEnd_7854819 := by exact prefixLift 7854819
  have htrace : WordTrace (prefixWord ++ tailWord_7854819) baseStart_7854819 baseEnd_7854819 := by
    simpa [prefixWord, tailWord_7854819, baseEnd_7854819] using wordTrace_append hprefix tailTrace_7854819
  have hstable : (prefixWord ++ tailWord_7854819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854819).length < 2 ^ (prefixWord ++ tailWord_7854819).sum := by decide
  have hdescent : baseEnd_7854819 < baseStart_7854819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854832 : List Nat := [2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 3]
def baseStart_7854832 : Nat := 118140960795 + 7854832 * 2 ^ 59
def prefixEnd_7854832 : Nat := 4983230072969 + 3 ^ 40 * 7854832 * 2
def baseEnd_7854832 : Nat := 4033304276316917167376291

theorem tailTrace_7854832 : CollatzResearch.WordTrace tailWord_7854832 prefixEnd_7854832 4033304276316917167376291 := by
  unfold tailWord_7854832
  simp only [CollatzResearch.WordTrace]
  refine ⟨143244629539646318674279375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190992839386195091565705833 143244629539646318674279375)
  ·
    refine ⟨214866944309469478011419063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143244629539646318674279375 214866944309469478011419063)
    ·
      refine ⟨322300416464204217017128595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214866944309469478011419063 322300416464204217017128595)
      ·
        refine ⟨483450624696306325525692893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322300416464204217017128595 483450624696306325525692893)
        ·
          refine ⟨181293984261114872072134835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 483450624696306325525692893 181293984261114872072134835)
          ·
            refine ⟨271940976391672308108202253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181293984261114872072134835 271940976391672308108202253)
            ·
              refine ⟨101977866146877115540575845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271940976391672308108202253 101977866146877115540575845)
              ·
                refine ⟨19120849902539459163857971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101977866146877115540575845 19120849902539459163857971)
                ·
                  refine ⟨28681274853809188745786957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19120849902539459163857971 28681274853809188745786957)
                  ·
                    refine ⟨10755478070178445779670109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28681274853809188745786957 10755478070178445779670109)
                    ·
                      refine ⟨4033304276316917167376291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10755478070178445779670109 4033304276316917167376291)
                      ·
                        rfl

theorem cell23_7854832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 3].length) (baseStart_7854832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854832 prefixEnd_7854832 := by exact prefixLift 7854832
  have htrace : WordTrace (prefixWord ++ tailWord_7854832) baseStart_7854832 baseEnd_7854832 := by
    simpa [prefixWord, tailWord_7854832, baseEnd_7854832] using wordTrace_append hprefix tailTrace_7854832
  have hstable : (prefixWord ++ tailWord_7854832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854832).length < 2 ^ (prefixWord ++ tailWord_7854832).sum := by decide
  have hdescent : baseEnd_7854832 < baseStart_7854832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854833 : List Nat := [1, 2, 2, 2, 2, 2, 4, 3, 1, 2, 2]
def baseStart_7854833 : Nat := 118140960795 + 7854833 * 2 ^ 59
def prefixEnd_7854833 : Nat := 4983230072969 + 3 ^ 40 * 7854833 * 2
def baseEnd_7854833 : Nat := 4033304789797571663463787

theorem tailTrace_7854833 : CollatzResearch.WordTrace tailWord_7854833 prefixEnd_7854833 4033304789797571663463787 := by
  unfold tailWord_7854833
  simp only [CollatzResearch.WordTrace]
  refine ⟨286489295552289014519345153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190992863701526009679563435 286489295552289014519345153)
  ·
    refine ⟨214866971664216760889508865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286489295552289014519345153 214866971664216760889508865)
    ·
      refine ⟨161150228748162570667131649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214866971664216760889508865 161150228748162570667131649)
      ·
        refine ⟨120862671561121928000348737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161150228748162570667131649 120862671561121928000348737)
        ·
          refine ⟨90647003670841446000261553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120862671561121928000348737 90647003670841446000261553)
          ·
            refine ⟨67985252753131084500196165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90647003670841446000261553 67985252753131084500196165)
            ·
              refine ⟨12747234891212078343786781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67985252753131084500196165 12747234891212078343786781)
              ·
                refine ⟨4780213084204529378920043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12747234891212078343786781 4780213084204529378920043)
                ·
                  refine ⟨7170319626306794068380065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4780213084204529378920043 7170319626306794068380065)
                  ·
                    refine ⟨5377739719730095551285049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7170319626306794068380065 5377739719730095551285049)
                    ·
                      refine ⟨4033304789797571663463787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5377739719730095551285049 4033304789797571663463787)
                      ·
                        rfl

theorem cell23_7854833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 1, 2, 2].length) (baseStart_7854833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854833 prefixEnd_7854833 := by exact prefixLift 7854833
  have htrace : WordTrace (prefixWord ++ tailWord_7854833) baseStart_7854833 baseEnd_7854833 := by
    simpa [prefixWord, tailWord_7854833, baseEnd_7854833] using wordTrace_append hprefix tailTrace_7854833
  have hstable : (prefixWord ++ tailWord_7854833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854833).length < 2 ^ (prefixWord ++ tailWord_7854833).sum := by decide
  have hdescent : baseEnd_7854833 < baseStart_7854833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854850 : List Nat := [3, 4, 1, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_7854850 : Nat := 118140960795 + 7854850 * 2 ^ 59
def prefixEnd_7854850 : Nat := 4983230072969 + 3 ^ 40 * 7854850 * 2
def baseEnd_7854850 : Nat := 4033313518968698096951209

theorem tailTrace_7854850 : CollatzResearch.WordTrace tailWord_7854850 prefixEnd_7854850 4033313518968698096951209 := by
  unfold tailWord_7854850
  simp only [CollatzResearch.WordTrace]
  refine ⟨71622478898306856605678501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190993277062151617615142669 71622478898306856605678501)
  ·
    refine ⟨13429214793432535613564719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71622478898306856605678501 13429214793432535613564719)
    ·
      refine ⟨20143822190148803420347079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13429214793432535613564719 20143822190148803420347079)
      ·
        refine ⟨30215733285223205130520619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20143822190148803420347079 30215733285223205130520619)
        ·
          refine ⟨45323599927834807695780929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30215733285223205130520619 45323599927834807695780929)
          ·
            refine ⟨33992699945876105771835697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45323599927834807695780929 33992699945876105771835697)
            ·
              refine ⟨25494524959407079328876773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33992699945876105771835697 25494524959407079328876773)
              ·
                refine ⟨4780223429888827374164395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25494524959407079328876773 4780223429888827374164395)
                ·
                  refine ⟨7170335144833241061246593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4780223429888827374164395 7170335144833241061246593)
                  ·
                    refine ⟨5377751358624930795934945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7170335144833241061246593 5377751358624930795934945)
                    ·
                      refine ⟨4033313518968698096951209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5377751358624930795934945 4033313518968698096951209)
                      ·
                        rfl

theorem cell23_7854850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_7854850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854850 prefixEnd_7854850 := by exact prefixLift 7854850
  have htrace : WordTrace (prefixWord ++ tailWord_7854850) baseStart_7854850 baseEnd_7854850 := by
    simpa [prefixWord, tailWord_7854850, baseEnd_7854850] using wordTrace_append hprefix tailTrace_7854850
  have hstable : (prefixWord ++ tailWord_7854850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854850).length < 2 ^ (prefixWord ++ tailWord_7854850).sum := by decide
  have hdescent : baseEnd_7854850 < baseStart_7854850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854876 : List Nat := [2, 2, 3, 1, 1, 3, 1, 4, 1, 3, 2]
def baseStart_7854876 : Nat := 118140960795 + 7854876 * 2 ^ 59
def prefixEnd_7854876 : Nat := 4983230072969 + 3 ^ 40 * 7854876 * 2
def baseEnd_7854876 : Nat := 4033326869465714995226089

theorem tailTrace_7854876 : CollatzResearch.WordTrace tailWord_7854876 prefixEnd_7854876 4033326869465714995226089 := by
  unfold tailWord_7854876
  simp only [CollatzResearch.WordTrace]
  refine ⟨143245431945566616431580241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190993909260755488575440321 143245431945566616431580241)
  ·
    refine ⟨107434073959174962323685181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143245431945566616431580241 107434073959174962323685181)
    ·
      refine ⟨40287777734690610871381943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107434073959174962323685181 40287777734690610871381943)
      ·
        refine ⟨60431666602035916307072915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40287777734690610871381943 60431666602035916307072915)
        ·
          refine ⟨90647499903053874460609373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60431666602035916307072915 90647499903053874460609373)
          ·
            refine ⟨33992812463645202922728515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90647499903053874460609373 33992812463645202922728515)
            ·
              refine ⟨50989218695467804384092773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33992812463645202922728515 50989218695467804384092773)
              ·
                refine ⟨9560478505400213322017395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50989218695467804384092773 9560478505400213322017395)
                ·
                  refine ⟨14340717758100319983026093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9560478505400213322017395 14340717758100319983026093)
                  ·
                    refine ⟨5377769159287619993634785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14340717758100319983026093 5377769159287619993634785)
                    ·
                      refine ⟨4033326869465714995226089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5377769159287619993634785 4033326869465714995226089)
                      ·
                        rfl

theorem cell23_7854876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_7854876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854876 prefixEnd_7854876 := by exact prefixLift 7854876
  have htrace : WordTrace (prefixWord ++ tailWord_7854876) baseStart_7854876 baseEnd_7854876 := by
    simpa [prefixWord, tailWord_7854876, baseEnd_7854876] using wordTrace_append hprefix tailTrace_7854876
  have hstable : (prefixWord ++ tailWord_7854876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854876).length < 2 ^ (prefixWord ++ tailWord_7854876).sum := by decide
  have hdescent : baseEnd_7854876 < baseStart_7854876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854892 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 5]
def baseStart_7854892 : Nat := 118140960795 + 7854892 * 2 ^ 59
def prefixEnd_7854892 : Nat := 4983230072969 + 3 ^ 40 * 7854892 * 2
def baseEnd_7854892 : Nat := 4033335085156186932626015

theorem tailTrace_7854892 : CollatzResearch.WordTrace tailWord_7854892 prefixEnd_7854892 4033335085156186932626015 := by
  unfold tailWord_7854892
  simp only [CollatzResearch.WordTrace]
  refine ⟨143245723729537633797871465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190994298306050178397161953 143245723729537633797871465)
  ·
    refine ⟨107434292797153225348403599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143245723729537633797871465 107434292797153225348403599)
    ·
      refine ⟨161151439195729838022605399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107434292797153225348403599 161151439195729838022605399)
      ·
        refine ⟨241727158793594757033908099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161151439195729838022605399 241727158793594757033908099)
        ·
          refine ⟨362590738190392135550862149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241727158793594757033908099 362590738190392135550862149)
          ·
            refine ⟨67985763410698525415786653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 362590738190392135550862149 67985763410698525415786653)
            ·
              refine ⟨25494661279011947030919995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67985763410698525415786653 25494661279011947030919995)
              ·
                refine ⟨38241991918517920546379993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25494661279011947030919995 38241991918517920546379993)
                ·
                  refine ⟨28681493938888440409784995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38241991918517920546379993 28681493938888440409784995)
                  ·
                    refine ⟨43022240908332660614677493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28681493938888440409784995 43022240908332660614677493)
                    ·
                      refine ⟨4033335085156186932626015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43022240908332660614677493 4033335085156186932626015)
                      ·
                        rfl

theorem cell23_7854892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_7854892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854892 prefixEnd_7854892 := by exact prefixLift 7854892
  have htrace : WordTrace (prefixWord ++ tailWord_7854892) baseStart_7854892 baseEnd_7854892 := by
    simpa [prefixWord, tailWord_7854892, baseEnd_7854892] using wordTrace_append hprefix tailTrace_7854892
  have hstable : (prefixWord ++ tailWord_7854892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854892).length < 2 ^ (prefixWord ++ tailWord_7854892).sum := by decide
  have hdescent : baseEnd_7854892 < baseStart_7854892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854996 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_7854996 : Nat := 118140960795 + 7854996 * 2 ^ 59
def prefixEnd_7854996 : Nat := 4983230072969 + 3 ^ 40 * 7854996 * 2
def baseEnd_7854996 : Nat := 4033388487144254525725537

theorem tailTrace_7854996 : CollatzResearch.WordTrace tailWord_7854996 prefixEnd_7854996 4033388487144254525725537 := by
  unfold tailWord_7854996
  simp only [CollatzResearch.WordTrace]
  refine ⟨143247620325349246678764421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190996827100465662238352561 143247620325349246678764421)
  ·
    refine ⟨26858928811002983752268329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143247620325349246678764421 26858928811002983752268329)
    ·
      refine ⟨20144196608252237814201247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26858928811002983752268329 20144196608252237814201247)
      ·
        refine ⟨30216294912378356721301871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20144196608252237814201247 30216294912378356721301871)
        ·
          refine ⟨45324442368567535081952807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30216294912378356721301871 45324442368567535081952807)
          ·
            refine ⟨67986663552851302622929211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45324442368567535081952807 67986663552851302622929211)
            ·
              refine ⟨101979995329276953934393817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67986663552851302622929211 101979995329276953934393817)
              ·
                refine ⟨76484996496957715450795363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101979995329276953934393817 76484996496957715450795363)
                ·
                  refine ⟨114727494745436573176193045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76484996496957715450795363 114727494745436573176193045)
                  ·
                    refine ⟨5377851316192339367634049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114727494745436573176193045 5377851316192339367634049)
                    ·
                      refine ⟨4033388487144254525725537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5377851316192339367634049 4033388487144254525725537)
                      ·
                        rfl

theorem cell23_7854996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_7854996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854996 prefixEnd_7854996 := by exact prefixLift 7854996
  have htrace : WordTrace (prefixWord ++ tailWord_7854996) baseStart_7854996 baseEnd_7854996 := by
    simpa [prefixWord, tailWord_7854996, baseEnd_7854996] using wordTrace_append hprefix tailTrace_7854996
  have hstable : (prefixWord ++ tailWord_7854996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854996).length < 2 ^ (prefixWord ++ tailWord_7854996).sum := by decide
  have hdescent : baseEnd_7854996 < baseStart_7854996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7854999 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 3]
def baseStart_7854999 : Nat := 118140960795 + 7854999 * 2 ^ 59
def prefixEnd_7854999 : Nat := 4983230072969 + 3 ^ 40 * 7854999 * 2
def baseEnd_7854999 : Nat := 4033390027586218013988023

theorem tailTrace_7854999 : CollatzResearch.WordTrace tailWord_7854999 prefixEnd_7854999 4033390027586218013988023 := by
  unfold tailWord_7854999
  simp only [CollatzResearch.WordTrace]
  refine ⟨286495350069687624869888051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190996900046458416579925367 286495350069687624869888051)
  ·
    refine ⟨429743025104531437304832077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286495350069687624869888051 429743025104531437304832077)
    ·
      refine ⟨161153634414199288989312029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429743025104531437304832077 161153634414199288989312029)
      ·
        refine ⟨60432612905324733370992011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161153634414199288989312029 60432612905324733370992011)
        ·
          refine ⟨90648919357987100056488017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60432612905324733370992011 90648919357987100056488017)
          ·
            refine ⟨67986689518490325042366013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90648919357987100056488017 67986689518490325042366013)
            ·
              refine ⟨25495008569433871890887255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67986689518490325042366013 25495008569433871890887255)
              ·
                refine ⟨38242512854150807836330883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25495008569433871890887255 38242512854150807836330883)
                ·
                  refine ⟨57363769281226211754496325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38242512854150807836330883 57363769281226211754496325)
                  ·
                    refine ⟨10755706740229914703968061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57363769281226211754496325 10755706740229914703968061)
                    ·
                      refine ⟨4033390027586218013988023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10755706740229914703968061 4033390027586218013988023)
                      ·
                        rfl

theorem cell23_7854999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_7854999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7854999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7854999 prefixEnd_7854999 := by exact prefixLift 7854999
  have htrace : WordTrace (prefixWord ++ tailWord_7854999) baseStart_7854999 baseEnd_7854999 := by
    simpa [prefixWord, tailWord_7854999, baseEnd_7854999] using wordTrace_append hprefix tailTrace_7854999
  have hstable : (prefixWord ++ tailWord_7854999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7854999).length < 2 ^ (prefixWord ++ tailWord_7854999).sum := by decide
  have hdescent : baseEnd_7854999 < baseStart_7854999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7854999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855009 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_7855009 : Nat := 118140960795 + 7855009 * 2 ^ 59
def prefixEnd_7855009 : Nat := 4983230072969 + 3 ^ 40 * 7855009 * 2
def baseEnd_7855009 : Nat := 4033395162392762974862977

theorem tailTrace_7855009 : CollatzResearch.WordTrace tailWord_7855009 prefixEnd_7855009 4033395162392762974862977 := by
  unfold tailWord_7855009
  simp only [CollatzResearch.WordTrace]
  refine ⟨286495714799651396577752081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190997143199767597718501387 286495714799651396577752081)
  ·
    refine ⟨214871786099738547433314061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286495714799651396577752081 214871786099738547433314061)
    ·
      refine ⟨80576919787401955287492773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214871786099738547433314061 80576919787401955287492773)
      ·
        refine ⟨15108172460137866616404895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80576919787401955287492773 15108172460137866616404895)
        ·
          refine ⟨22662258690206799924607343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15108172460137866616404895 22662258690206799924607343)
          ·
            refine ⟨33993388035310199886911015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22662258690206799924607343 33993388035310199886911015)
            ·
              refine ⟨50990082052965299830366523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33993388035310199886911015 50990082052965299830366523)
              ·
                refine ⟨76485123079447949745549785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50990082052965299830366523 76485123079447949745549785)
                ·
                  refine ⟨57363842309585962309162339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76485123079447949745549785 57363842309585962309162339)
                  ·
                    refine ⟨86045763464378943463743509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57363842309585962309162339 86045763464378943463743509)
                    ·
                      refine ⟨4033395162392762974862977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86045763464378943463743509 4033395162392762974862977)
                      ·
                        rfl

theorem cell23_7855009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_7855009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855009 prefixEnd_7855009 := by exact prefixLift 7855009
  have htrace : WordTrace (prefixWord ++ tailWord_7855009) baseStart_7855009 baseEnd_7855009 := by
    simpa [prefixWord, tailWord_7855009, baseEnd_7855009] using wordTrace_append hprefix tailTrace_7855009
  have hstable : (prefixWord ++ tailWord_7855009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855009).length < 2 ^ (prefixWord ++ tailWord_7855009).sum := by decide
  have hdescent : baseEnd_7855009 < baseStart_7855009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855056 : List Nat := [2, 1, 1, 1, 1, 2, 3, 5, 2, 3, 2]
def baseStart_7855056 : Nat := 118140960795 + 7855056 * 2 ^ 59
def prefixEnd_7855056 : Nat := 4983230072969 + 3 ^ 40 * 7855056 * 2
def baseEnd_7855056 : Nat := 4033419295983524290975261

theorem tailTrace_7855056 : CollatzResearch.WordTrace tailWord_7855056 prefixEnd_7855056 4033419295983524290975261 := by
  unfold tailWord_7855056
  simp only [CollatzResearch.WordTrace]
  refine ⟨143248714515240561802356511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190998286020320749069808681 143248714515240561802356511)
  ·
    refine ⟨214873071772860842703534767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143248714515240561802356511 214873071772860842703534767)
    ·
      refine ⟨322309607659291264055302151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214873071772860842703534767 322309607659291264055302151)
      ·
        refine ⟨483464411488936896082953227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322309607659291264055302151 483464411488936896082953227)
        ·
          refine ⟨725196617233405344124429841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483464411488936896082953227 725196617233405344124429841)
          ·
            refine ⟨543897462925054008093322381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 725196617233405344124429841 543897462925054008093322381)
            ·
              refine ⟨203961548596895253034995893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 543897462925054008093322381 203961548596895253034995893)
              ·
                refine ⟨19121395180958929972030865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203961548596895253034995893 19121395180958929972030865)
                ·
                  refine ⟨14341046385719197479023149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19121395180958929972030865 14341046385719197479023149)
                  ·
                    refine ⟨5377892394644699054633681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14341046385719197479023149 5377892394644699054633681)
                    ·
                      refine ⟨4033419295983524290975261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5377892394644699054633681 4033419295983524290975261)
                      ·
                        rfl

theorem cell23_7855056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 2, 3, 2].length) (baseStart_7855056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855056 prefixEnd_7855056 := by exact prefixLift 7855056
  have htrace : WordTrace (prefixWord ++ tailWord_7855056) baseStart_7855056 baseEnd_7855056 := by
    simpa [prefixWord, tailWord_7855056, baseEnd_7855056] using wordTrace_append hprefix tailTrace_7855056
  have hstable : (prefixWord ++ tailWord_7855056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855056).length < 2 ^ (prefixWord ++ tailWord_7855056).sum := by decide
  have hdescent : baseEnd_7855056 < baseStart_7855056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855063 : List Nat := [1, 1, 3, 2, 1, 1, 2, 7, 1, 1, 3]
def baseStart_7855063 : Nat := 118140960795 + 7855063 * 2 ^ 59
def prefixEnd_7855063 : Nat := 4983230072969 + 3 ^ 40 * 7855063 * 2
def baseEnd_7855063 : Nat := 4033422890348105763587729

theorem tailTrace_7855063 : CollatzResearch.WordTrace tailWord_7855063 prefixEnd_7855063 4033422890348105763587729 := by
  unfold tailWord_7855063
  simp only [CollatzResearch.WordTrace]
  refine ⟨286497684341455763800217843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190998456227637175866811895 286497684341455763800217843)
  ·
    refine ⟨429746526512183645700326765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286497684341455763800217843 429746526512183645700326765)
    ·
      refine ⟨161154947442068867137622537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429746526512183645700326765 161154947442068867137622537)
      ·
        refine ⟨120866210581551650353216903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161154947442068867137622537 120866210581551650353216903)
        ·
          refine ⟨181299315872327475529825355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120866210581551650353216903 181299315872327475529825355)
          ·
            refine ⟨271948973808491213294738033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181299315872327475529825355 271948973808491213294738033)
            ·
              refine ⟨203961730356368409971053525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271948973808491213294738033 203961730356368409971053525)
              ·
                refine ⟨4780353055227384608696567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 203961730356368409971053525 4780353055227384608696567)
                ·
                  refine ⟨7170529582841076913044851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4780353055227384608696567 7170529582841076913044851)
                  ·
                    refine ⟨10755794374261615369567277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7170529582841076913044851 10755794374261615369567277)
                    ·
                      refine ⟨4033422890348105763587729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10755794374261615369567277 4033422890348105763587729)
                      ·
                        rfl

theorem cell23_7855063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 1, 1, 3].length) (baseStart_7855063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855063 prefixEnd_7855063 := by exact prefixLift 7855063
  have htrace : WordTrace (prefixWord ++ tailWord_7855063) baseStart_7855063 baseEnd_7855063 := by
    simpa [prefixWord, tailWord_7855063, baseEnd_7855063] using wordTrace_append hprefix tailTrace_7855063
  have hstable : (prefixWord ++ tailWord_7855063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855063).length < 2 ^ (prefixWord ++ tailWord_7855063).sum := by decide
  have hdescent : baseEnd_7855063 < baseStart_7855063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855066 : List Nat := [3, 1, 1, 2, 4, 1, 2, 3, 1, 5]
def baseStart_7855066 : Nat := 118140960795 + 7855066 * 2 ^ 59
def prefixEnd_7855066 : Nat := 4983230072969 + 3 ^ 40 * 7855066 * 2
def baseEnd_7855066 : Nat := 1344474810263356417283405

theorem tailTrace_7855066 : CollatzResearch.WordTrace tailWord_7855066 prefixEnd_7855066 1344474810263356417283405 := by
  unfold tailWord_7855066
  simp only [CollatzResearch.WordTrace]
  refine ⟨71624448440111223828144263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190998529173629930208384701 71624448440111223828144263)
  ·
    refine ⟨107436672660166835742216395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71624448440111223828144263 107436672660166835742216395)
    ·
      refine ⟨161155008990250253613324593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107436672660166835742216395 161155008990250253613324593)
      ·
        refine ⟨120866256742687690209993445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161155008990250253613324593 120866256742687690209993445)
        ·
          refine ⟨22662423139253941914373771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120866256742687690209993445 22662423139253941914373771)
          ·
            refine ⟨33993634708880912871560657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22662423139253941914373771 33993634708880912871560657)
            ·
              refine ⟨25495226031660684653670493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33993634708880912871560657 25495226031660684653670493)
              ·
                refine ⟨9560709761872756745126435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25495226031660684653670493 9560709761872756745126435)
                ·
                  refine ⟨14341064642809135117689653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9560709761872756745126435 14341064642809135117689653)
                  ·
                    refine ⟨1344474810263356417283405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14341064642809135117689653 1344474810263356417283405)
                    ·
                      rfl

theorem cell23_7855066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_7855066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855066 prefixEnd_7855066 := by exact prefixLift 7855066
  have htrace : WordTrace (prefixWord ++ tailWord_7855066) baseStart_7855066 baseEnd_7855066 := by
    simpa [prefixWord, tailWord_7855066, baseEnd_7855066] using wordTrace_append hprefix tailTrace_7855066
  have hstable : (prefixWord ++ tailWord_7855066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855066).length < 2 ^ (prefixWord ++ tailWord_7855066).sum := by decide
  have hdescent : baseEnd_7855066 < baseStart_7855066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855099 : List Nat := [1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 4]
def baseStart_7855099 : Nat := 118140960795 + 7855099 * 2 ^ 59
def prefixEnd_7855099 : Nat := 4983230072969 + 3 ^ 40 * 7855099 * 2
def baseEnd_7855099 : Nat := 4033441375651667622737563

theorem tailTrace_7855099 : CollatzResearch.WordTrace tailWord_7855099 prefixEnd_7855099 4033441375651667622737563 := by
  unfold tailWord_7855099
  simp only [CollatzResearch.WordTrace]
  refine ⟨286498997369325341948528351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190999331579550227965685567 286498997369325341948528351)
  ·
    refine ⟨429748496053988012922792527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286498997369325341948528351 429748496053988012922792527)
    ·
      refine ⟨644622744080982019384188791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429748496053988012922792527 644622744080982019384188791)
      ·
        refine ⟨966934116121473029076283187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644622744080982019384188791 966934116121473029076283187)
        ·
          refine ⟨1450401174182209543614424781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966934116121473029076283187 1450401174182209543614424781)
          ·
            refine ⟨543900440318328578855409293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1450401174182209543614424781 543900440318328578855409293)
            ·
              refine ⟨203962665119373217070778485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 543900440318328578855409293 203962665119373217070778485)
              ·
                refine ⟨19121499854941239100385483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203962665119373217070778485 19121499854941239100385483)
                ·
                  refine ⟨28682249782411858650578225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19121499854941239100385483 28682249782411858650578225)
                  ·
                    refine ⟨21511687336808893987933669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28682249782411858650578225 21511687336808893987933669)
                    ·
                      refine ⟨4033441375651667622737563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21511687336808893987933669 4033441375651667622737563)
                      ·
                        rfl

theorem cell23_7855099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 4].length) (baseStart_7855099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855099 prefixEnd_7855099 := by exact prefixLift 7855099
  have htrace : WordTrace (prefixWord ++ tailWord_7855099) baseStart_7855099 baseEnd_7855099 := by
    simpa [prefixWord, tailWord_7855099, baseEnd_7855099] using wordTrace_append hprefix tailTrace_7855099
  have hstable : (prefixWord ++ tailWord_7855099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855099).length < 2 ^ (prefixWord ++ tailWord_7855099).sum := by decide
  have hdescent : baseEnd_7855099 < baseStart_7855099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855116 : List Nat := [2, 2, 1, 2, 3, 3, 1, 2, 1, 2, 4]
def baseStart_7855116 : Nat := 118140960795 + 7855116 * 2 ^ 59
def prefixEnd_7855116 : Nat := 4983230072969 + 3 ^ 40 * 7855116 * 2
def baseEnd_7855116 : Nat := 4033450104822794056224985

theorem tailTrace_7855116 : CollatzResearch.WordTrace tailWord_7855116 prefixEnd_7855116 4033450104822794056224985 := by
  unfold tailWord_7855116
  simp only [CollatzResearch.WordTrace]
  refine ⟨143249808705131876925948601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190999744940175835901264801 143249808705131876925948601)
  ·
    refine ⟨107437356528848907694461451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143249808705131876925948601 107437356528848907694461451)
    ·
      refine ⟨161156034793273361541692177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107437356528848907694461451 161156034793273361541692177)
      ·
        refine ⟨120867026094955021156269133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161156034793273361541692177 120867026094955021156269133)
        ·
          refine ⟨45325134785608132933600925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120867026094955021156269133 45325134785608132933600925)
          ·
            refine ⟨16996925544603049850100347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45325134785608132933600925 16996925544603049850100347)
            ·
              refine ⟨25495388316904574775150521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16996925544603049850100347 25495388316904574775150521)
              ·
                refine ⟨19121541237678431081362891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25495388316904574775150521 19121541237678431081362891)
                ·
                  refine ⟨28682311856517646622044337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19121541237678431081362891 28682311856517646622044337)
                  ·
                    refine ⟨21511733892388234966533253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28682311856517646622044337 21511733892388234966533253)
                    ·
                      refine ⟨4033450104822794056224985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21511733892388234966533253 4033450104822794056224985)
                      ·
                        rfl

theorem cell23_7855116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_7855116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855116 prefixEnd_7855116 := by exact prefixLift 7855116
  have htrace : WordTrace (prefixWord ++ tailWord_7855116) baseStart_7855116 baseEnd_7855116 := by
    simpa [prefixWord, tailWord_7855116, baseEnd_7855116] using wordTrace_append hprefix tailTrace_7855116
  have hstable : (prefixWord ++ tailWord_7855116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855116).length < 2 ^ (prefixWord ++ tailWord_7855116).sum := by decide
  have hdescent : baseEnd_7855116 < baseStart_7855116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855137 : List Nat := [1, 2, 3, 2, 3, 2, 1, 4, 1, 2, 2]
def baseStart_7855137 : Nat := 118140960795 + 7855137 * 2 ^ 59
def prefixEnd_7855137 : Nat := 4983230072969 + 3 ^ 40 * 7855137 * 2
def baseEnd_7855137 : Nat := 4033460887916538474062389

theorem tailTrace_7855137 : CollatzResearch.WordTrace tailWord_7855137 prefixEnd_7855137 4033460887916538474062389 := by
  unfold tailWord_7855137
  simp only [CollatzResearch.WordTrace]
  refine ⟨286500383343187674438411665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191000255562125116292274443 286500383343187674438411665)
  ·
    refine ⟨214875287507390755828808749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286500383343187674438411665 214875287507390755828808749)
    ·
      refine ⟨80578232815271533435803281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214875287507390755828808749 80578232815271533435803281)
      ·
        refine ⟨60433674611453650076852461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80578232815271533435803281 60433674611453650076852461)
        ·
          refine ⟨22662627979295118778819673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60433674611453650076852461 22662627979295118778819673)
          ·
            refine ⟨16996970984471339084114755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22662627979295118778819673 16996970984471339084114755)
            ·
              refine ⟨25495456476707008626172133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16996970984471339084114755 25495456476707008626172133)
              ·
                refine ⟨4780398089382564117407275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25495456476707008626172133 4780398089382564117407275)
                ·
                  refine ⟨7170597134073846176110913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4780398089382564117407275 7170597134073846176110913)
                  ·
                    refine ⟨5377947850555384632083185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7170597134073846176110913 5377947850555384632083185)
                    ·
                      refine ⟨4033460887916538474062389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5377947850555384632083185 4033460887916538474062389)
                      ·
                        rfl

theorem cell23_7855137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_7855137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855137 prefixEnd_7855137 := by exact prefixLift 7855137
  have htrace : WordTrace (prefixWord ++ tailWord_7855137) baseStart_7855137 baseEnd_7855137 := by
    simpa [prefixWord, tailWord_7855137, baseEnd_7855137] using wordTrace_append hprefix tailTrace_7855137
  have hstable : (prefixWord ++ tailWord_7855137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855137).length < 2 ^ (prefixWord ++ tailWord_7855137).sum := by decide
  have hdescent : baseEnd_7855137 < baseStart_7855137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855139 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 2, 7]
def baseStart_7855139 : Nat := 118140960795 + 7855139 * 2 ^ 59
def prefixEnd_7855139 : Nat := 4983230072969 + 3 ^ 40 * 7855139 * 2
def baseEnd_7855139 : Nat := 1344487304959282488745793

theorem tailTrace_7855139 : CollatzResearch.WordTrace tailWord_7855139 prefixEnd_7855139 1344487304959282488745793 := by
  unfold tailWord_7855139
  simp only [CollatzResearch.WordTrace]
  refine ⟨286500456289180428779984471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191000304192786952519989647 286500456289180428779984471)
  ·
    refine ⟨429750684433770643169976707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286500456289180428779984471 429750684433770643169976707)
    ·
      refine ⟨644626026650655964754965061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429750684433770643169976707 644626026650655964754965061)
      ·
        refine ⟨120867379996997993391555949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 644626026650655964754965061 120867379996997993391555949)
        ·
          refine ⟨45325267498874247521833481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120867379996997993391555949 45325267498874247521833481)
          ·
            refine ⟨33993950624155685641375111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45325267498874247521833481 33993950624155685641375111)
            ·
              refine ⟨50990925936233528462062667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33993950624155685641375111 50990925936233528462062667)
              ·
                refine ⟨76486388904350292693094001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50990925936233528462062667 76486388904350292693094001)
                ·
                  refine ⟨57364791678262719519820501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76486388904350292693094001 57364791678262719519820501)
                  ·
                    refine ⟨1344487304959282488745793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57364791678262719519820501 1344487304959282488745793)
                    ·
                      rfl

theorem cell23_7855139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 7].length) (baseStart_7855139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855139 prefixEnd_7855139 := by exact prefixLift 7855139
  have htrace : WordTrace (prefixWord ++ tailWord_7855139) baseStart_7855139 baseEnd_7855139 := by
    simpa [prefixWord, tailWord_7855139, baseEnd_7855139] using wordTrace_append hprefix tailTrace_7855139
  have hstable : (prefixWord ++ tailWord_7855139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855139).length < 2 ^ (prefixWord ++ tailWord_7855139).sum := by decide
  have hdescent : baseEnd_7855139 < baseStart_7855139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855143 : List Nat := [1, 1, 7, 1, 1, 3, 1, 8]
def baseStart_7855143 : Nat := 118140960795 + 7855143 * 2 ^ 59
def prefixEnd_7855143 : Nat := 4983230072969 + 3 ^ 40 * 7855143 * 2
def baseEnd_7855143 : Nat := 149387554400017238910643

theorem tailTrace_7855143 : CollatzResearch.WordTrace tailWord_7855143 prefixEnd_7855143 149387554400017238910643 := by
  unfold tailWord_7855143
  simp only [CollatzResearch.WordTrace]
  refine ⟨286500602181165937463130083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191000401454110624975420055 286500602181165937463130083)
  ·
    refine ⟨429750903271748906194695125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286500602181165937463130083 429750903271748906194695125)
    ·
      refine ⟨10072286795431614988938167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 429750903271748906194695125 10072286795431614988938167)
      ·
        refine ⟨15108430193147422483407251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10072286795431614988938167 15108430193147422483407251)
        ·
          refine ⟨22662645289721133725110877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15108430193147422483407251 22662645289721133725110877)
          ·
            refine ⟨8498491983645425146916579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22662645289721133725110877 8498491983645425146916579)
            ·
              refine ⟨12747737975468137720374869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8498491983645425146916579 12747737975468137720374869)
              ·
                refine ⟨149387554400017238910643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12747737975468137720374869 149387554400017238910643)
                ·
                  rfl

theorem cell23_7855143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 8].length) (baseStart_7855143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855143 prefixEnd_7855143 := by exact prefixLift 7855143
  have htrace : WordTrace (prefixWord ++ tailWord_7855143) baseStart_7855143 baseEnd_7855143 := by
    simpa [prefixWord, tailWord_7855143, baseEnd_7855143] using wordTrace_append hprefix tailTrace_7855143
  have hstable : (prefixWord ++ tailWord_7855143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855143).length < 2 ^ (prefixWord ++ tailWord_7855143).sum := by decide
  have hdescent : baseEnd_7855143 < baseStart_7855143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855153 : List Nat := [1, 2, 2, 3, 1, 2, 1, 5, 2, 1, 3]
def baseStart_7855153 : Nat := 118140960795 + 7855153 * 2 ^ 59
def prefixEnd_7855153 : Nat := 4983230072969 + 3 ^ 40 * 7855153 * 2
def baseEnd_7855153 : Nat := 4033469103607010411462315

theorem tailTrace_7855153 : CollatzResearch.WordTrace tailWord_7855153 prefixEnd_7855153 4033469103607010411462315 := by
  unfold tailWord_7855153
  simp only [CollatzResearch.WordTrace]
  refine ⟨286500966911129709170994113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191000644607419806113996075 286500966911129709170994113)
  ·
    refine ⟨214875725183347281878245585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286500966911129709170994113 214875725183347281878245585)
    ·
      refine ⟨161156793887510461408684189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214875725183347281878245585 161156793887510461408684189)
      ·
        refine ⟨60433797707816423028256571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161156793887510461408684189 60433797707816423028256571)
        ·
          refine ⟨90650696561724634542384857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60433797707816423028256571 90650696561724634542384857)
          ·
            refine ⟨67988022421293475906788643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90650696561724634542384857 67988022421293475906788643)
            ·
              refine ⟨101982033631940213860182965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67988022421293475906788643 101982033631940213860182965)
              ·
                refine ⟨9560815652994395049392153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101982033631940213860182965 9560815652994395049392153)
                ·
                  refine ⟨7170611739745796287044115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9560815652994395049392153 7170611739745796287044115)
                  ·
                    refine ⟨10755917609618694430566173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7170611739745796287044115 10755917609618694430566173)
                    ·
                      refine ⟨4033469103607010411462315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10755917609618694430566173 4033469103607010411462315)
                      ·
                        rfl

theorem cell23_7855153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_7855153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855153 prefixEnd_7855153 := by exact prefixLift 7855153
  have htrace : WordTrace (prefixWord ++ tailWord_7855153) baseStart_7855153 baseEnd_7855153 := by
    simpa [prefixWord, tailWord_7855153, baseEnd_7855153] using wordTrace_append hprefix tailTrace_7855153
  have hstable : (prefixWord ++ tailWord_7855153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855153).length < 2 ^ (prefixWord ++ tailWord_7855153).sum := by decide
  have hdescent : baseEnd_7855153 < baseStart_7855153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855159 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 4]
def baseStart_7855159 : Nat := 118140960795 + 7855159 * 2 ^ 59
def prefixEnd_7855159 : Nat := 4983230072969 + 3 ^ 40 * 7855159 * 2
def baseEnd_7855159 : Nat := 4033472184490937387987287

theorem tailTrace_7855159 : CollatzResearch.WordTrace tailWord_7855159 prefixEnd_7855159 4033472184490937387987287 := by
  unfold tailWord_7855159
  simp only [CollatzResearch.WordTrace]
  refine ⟨286501185749107972195712531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191000790499405314797141687 286501185749107972195712531)
  ·
    refine ⟨429751778623661958293568797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286501185749107972195712531 429751778623661958293568797)
    ·
      refine ⟨161156916983873234360088299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429751778623661958293568797 161156916983873234360088299)
      ·
        refine ⟨241735375475809851540132449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161156916983873234360088299 241735375475809851540132449)
        ·
          refine ⟨181301531606857388655099337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241735375475809851540132449 181301531606857388655099337)
          ·
            refine ⟨135976148705143041491324503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181301531606857388655099337 135976148705143041491324503)
            ·
              refine ⟨203964223057714562236986755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135976148705143041491324503 203964223057714562236986755)
              ·
                refine ⟨305946334586571843355480133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203964223057714562236986755 305946334586571843355480133)
                ·
                  refine ⟨57364937734982220629152525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 305946334586571843355480133 57364937734982220629152525)
                  ·
                    refine ⟨21511851650618332735932197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57364937734982220629152525 21511851650618332735932197)
                    ·
                      refine ⟨4033472184490937387987287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21511851650618332735932197 4033472184490937387987287)
                      ·
                        rfl

theorem cell23_7855159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_7855159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855159 prefixEnd_7855159 := by exact prefixLift 7855159
  have htrace : WordTrace (prefixWord ++ tailWord_7855159) baseStart_7855159 baseEnd_7855159 := by
    simpa [prefixWord, tailWord_7855159, baseEnd_7855159] using wordTrace_append hprefix tailTrace_7855159
  have hstable : (prefixWord ++ tailWord_7855159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855159).length < 2 ^ (prefixWord ++ tailWord_7855159).sum := by decide
  have hdescent : baseEnd_7855159 < baseStart_7855159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855174 : List Nat := [6, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_7855174 : Nat := 118140960795 + 7855174 * 2 ^ 59
def prefixEnd_7855174 : Nat := 4983230072969 + 3 ^ 40 * 7855174 * 2
def baseEnd_7855174 : Nat := 4033479886700754829299719

theorem tailTrace_7855174 : CollatzResearch.WordTrace tailWord_7855174 prefixEnd_7855174 4033479886700754829299719 := by
  unfold tailWord_7855174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8953179151376675929922143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 191001155229369086505005717 8953179151376675929922143)
  ·
    refine ⟨13429768727065013894883215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8953179151376675929922143 13429768727065013894883215)
    ·
      refine ⟨20144653090597520842324823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13429768727065013894883215 20144653090597520842324823)
      ·
        refine ⟨30216979635896281263487235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20144653090597520842324823 30216979635896281263487235)
        ·
          refine ⟨45325469453844421895230853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30216979635896281263487235 45325469453844421895230853)
          ·
            refine ⟨8498525522595829105355785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45325469453844421895230853 8498525522595829105355785)
            ·
              refine ⟨6373894141946871829016839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8498525522595829105355785 6373894141946871829016839)
              ·
                refine ⟨9560841212920307743525259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6373894141946871829016839 9560841212920307743525259)
                ·
                  refine ⟨14341261819380461615287889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9560841212920307743525259 14341261819380461615287889)
                  ·
                    refine ⟨10755946364535346211465917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14341261819380461615287889 10755946364535346211465917)
                    ·
                      refine ⟨4033479886700754829299719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10755946364535346211465917 4033479886700754829299719)
                      ·
                        rfl

theorem cell23_7855174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_7855174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855174 prefixEnd_7855174 := by exact prefixLift 7855174
  have htrace : WordTrace (prefixWord ++ tailWord_7855174) baseStart_7855174 baseEnd_7855174 := by
    simpa [prefixWord, tailWord_7855174, baseEnd_7855174] using wordTrace_append hprefix tailTrace_7855174
  have hstable : (prefixWord ++ tailWord_7855174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855174).length < 2 ^ (prefixWord ++ tailWord_7855174).sum := by decide
  have hdescent : baseEnd_7855174 < baseStart_7855174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855186 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 2, 6]
def baseStart_7855186 : Nat := 118140960795 + 7855186 * 2 ^ 59
def prefixEnd_7855186 : Nat := 4983230072969 + 3 ^ 40 * 7855186 * 2
def baseEnd_7855186 : Nat := 1344495349489536260783221

theorem tailTrace_7855186 : CollatzResearch.WordTrace tailWord_7855186 prefixEnd_7855186 1344495349489536260783221 := by
  unfold tailWord_7855186
  simp only [CollatzResearch.WordTrace]
  refine ⟨71625542630002538951736353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191001447013340103871296941 71625542630002538951736353)
  ·
    refine ⟨53719156972501904213802265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71625542630002538951736353 53719156972501904213802265)
    ·
      refine ⟨40289367729376428160351699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53719156972501904213802265 40289367729376428160351699)
      ·
        refine ⟨60434051594064642240527549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40289367729376428160351699 60434051594064642240527549)
        ·
          refine ⟨22662769347774240840197831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60434051594064642240527549 22662769347774240840197831)
          ·
            refine ⟨33994154021661361260296747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22662769347774240840197831 33994154021661361260296747)
            ·
              refine ⟨50991231032492041890445121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33994154021661361260296747 50991231032492041890445121)
              ·
                refine ⟨38243423274369031417833841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50991231032492041890445121 38243423274369031417833841)
                ·
                  refine ⟨28682567455776773563375381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38243423274369031417833841 28682567455776773563375381)
                  ·
                    refine ⟨1344495349489536260783221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28682567455776773563375381 1344495349489536260783221)
                    ·
                      rfl

theorem cell23_7855186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_7855186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855186 prefixEnd_7855186 := by exact prefixLift 7855186
  have htrace : WordTrace (prefixWord ++ tailWord_7855186) baseStart_7855186 baseEnd_7855186 := by
    simpa [prefixWord, tailWord_7855186, baseEnd_7855186] using wordTrace_append hprefix tailTrace_7855186
  have hstable : (prefixWord ++ tailWord_7855186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855186).length < 2 ^ (prefixWord ++ tailWord_7855186).sum := by decide
  have hdescent : baseEnd_7855186 < baseStart_7855186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855210 : List Nat := [3, 1, 3, 2, 2, 1, 3, 1, 1, 4, 2]
def baseStart_7855210 : Nat := 118140960795 + 7855210 * 2 ^ 59
def prefixEnd_7855210 : Nat := 4983230072969 + 3 ^ 40 * 7855210 * 2
def baseEnd_7855210 : Nat := 4033498372004316688449553

theorem tailTrace_7855210 : CollatzResearch.WordTrace tailWord_7855210 prefixEnd_7855210 4033498372004316688449553 := by
  unfold tailWord_7855210
  simp only [CollatzResearch.WordTrace]
  refine ⟨71625761467980801976454771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191002030581282138603879389 71625761467980801976454771)
  ·
    refine ⟨107438642201971202964682157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71625761467980801976454771 107438642201971202964682157)
    ·
      refine ⟨40289490825739201111755809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107438642201971202964682157 40289490825739201111755809)
      ·
        refine ⟨30217118119304400833816857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40289490825739201111755809 30217118119304400833816857)
        ·
          refine ⟨22662838589478300625362643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30217118119304400833816857 22662838589478300625362643)
          ·
            refine ⟨33994257884217450938043965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22662838589478300625362643 33994257884217450938043965)
            ·
              refine ⟨12747846706581544101766487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33994257884217450938043965 12747846706581544101766487)
              ·
                refine ⟨19121770059872316152649731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12747846706581544101766487 19121770059872316152649731)
                ·
                  refine ⟨28682655089808474228974597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19121770059872316152649731 28682655089808474228974597)
                  ·
                    refine ⟨5377997829339088917932737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28682655089808474228974597 5377997829339088917932737)
                    ·
                      refine ⟨4033498372004316688449553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5377997829339088917932737 4033498372004316688449553)
                      ·
                        rfl

theorem cell23_7855210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_7855210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855210 prefixEnd_7855210 := by exact prefixLift 7855210
  have htrace : WordTrace (prefixWord ++ tailWord_7855210) baseStart_7855210 baseEnd_7855210 := by
    simpa [prefixWord, tailWord_7855210, baseEnd_7855210] using wordTrace_append hprefix tailTrace_7855210
  have hstable : (prefixWord ++ tailWord_7855210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855210).length < 2 ^ (prefixWord ++ tailWord_7855210).sum := by decide
  have hdescent : baseEnd_7855210 < baseStart_7855210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855249 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 8]
def baseStart_7855249 : Nat := 118140960795 + 7855249 * 2 ^ 59
def prefixEnd_7855249 : Nat := 4983230072969 + 3 ^ 40 * 7855249 * 2
def baseEnd_7855249 : Nat := 4033518397749842035861873

theorem tailTrace_7855249 : CollatzResearch.WordTrace tailWord_7855249 prefixEnd_7855249 4033518397749842035861873 := by
  unfold tailWord_7855249
  simp only [CollatzResearch.WordTrace]
  refine ⟨286504468318781917566488801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191002978879187945044325867 286504468318781917566488801)
  ·
    refine ⟨214878351239086438174866601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286504468318781917566488801 214878351239086438174866601)
    ·
      refine ⟨161158763429314828631149951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214878351239086438174866601 161158763429314828631149951)
      ·
        refine ⟨241738145143972242946724927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161158763429314828631149951 241738145143972242946724927)
        ·
          refine ⟨362607217715958364420087391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241738145143972242946724927 362607217715958364420087391)
          ·
            refine ⟨543910826573937546630131087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362607217715958364420087391 543910826573937546630131087)
            ·
              refine ⟨815866239860906319945196631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543910826573937546630131087 815866239860906319945196631)
              ·
                refine ⟨1223799359791359479917794947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815866239860906319945196631 1223799359791359479917794947)
                ·
                  refine ⟨1835699039687039219876692421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223799359791359479917794947 1835699039687039219876692421)
                  ·
                    refine ⟨344193569941319853726879829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1835699039687039219876692421 344193569941319853726879829)
                    ·
                      refine ⟨4033518397749842035861873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 344193569941319853726879829 4033518397749842035861873)
                      ·
                        rfl

theorem cell23_7855249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_7855249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855249 prefixEnd_7855249 := by exact prefixLift 7855249
  have htrace : WordTrace (prefixWord ++ tailWord_7855249) baseStart_7855249 baseEnd_7855249 := by
    simpa [prefixWord, tailWord_7855249, baseEnd_7855249] using wordTrace_append hprefix tailTrace_7855249
  have hstable : (prefixWord ++ tailWord_7855249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855249).length < 2 ^ (prefixWord ++ tailWord_7855249).sum := by decide
  have hdescent : baseEnd_7855249 < baseStart_7855249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855256 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 1, 1, 7]
def baseStart_7855256 : Nat := 118140960795 + 7855256 * 2 ^ 59
def prefixEnd_7855256 : Nat := 4983230072969 + 3 ^ 40 * 7855256 * 2
def baseEnd_7855256 : Nat := 4033521992114423508474341

theorem tailTrace_7855256 : CollatzResearch.WordTrace tailWord_7855256 prefixEnd_7855256 4033521992114423508474341 := by
  unfold tailWord_7855256
  simp only [CollatzResearch.WordTrace]
  refine ⟨143252361814878278880996811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191003149086504371841329081 143252361814878278880996811)
  ·
    refine ⟨214878542722317418321495217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143252361814878278880996811 214878542722317418321495217)
    ·
      refine ⟨161158907041738063741121413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214878542722317418321495217 161158907041738063741121413)
      ·
        refine ⟨30217295070325886951460265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161158907041738063741121413 30217295070325886951460265)
        ·
          refine ⟨22662971302744415213595199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30217295070325886951460265 22662971302744415213595199)
          ·
            refine ⟨33994456954116622820392799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22662971302744415213595199 33994456954116622820392799)
            ·
              refine ⟨50991685431174934230589199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33994456954116622820392799 50991685431174934230589199)
              ·
                refine ⟨76487528146762401345883799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50991685431174934230589199 76487528146762401345883799)
                ·
                  refine ⟨114731292220143602018825699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76487528146762401345883799 114731292220143602018825699)
                  ·
                    refine ⟨172096938330215403028238549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114731292220143602018825699 172096938330215403028238549)
                    ·
                      refine ⟨4033521992114423508474341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172096938330215403028238549 4033521992114423508474341)
                      ·
                        rfl

theorem cell23_7855256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_7855256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855256 prefixEnd_7855256 := by exact prefixLift 7855256
  have htrace : WordTrace (prefixWord ++ tailWord_7855256) baseStart_7855256 baseEnd_7855256 := by
    simpa [prefixWord, tailWord_7855256, baseEnd_7855256] using wordTrace_append hprefix tailTrace_7855256
  have hstable : (prefixWord ++ tailWord_7855256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855256).length < 2 ^ (prefixWord ++ tailWord_7855256).sum := by decide
  have hdescent : baseEnd_7855256 < baseStart_7855256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855259 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 4, 8]
def baseStart_7855259 : Nat := 118140960795 + 7855259 * 2 ^ 59
def prefixEnd_7855259 : Nat := 4983230072969 + 3 ^ 40 * 7855259 * 2
def baseEnd_7855259 : Nat := 1344507844185462332245609

theorem tailTrace_7855259 : CollatzResearch.WordTrace tailWord_7855259 prefixEnd_7855259 1344507844185462332245609 := by
  unfold tailWord_7855259
  simp only [CollatzResearch.WordTrace]
  refine ⟨286504833048745689274352831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191003222032497126182901887 286504833048745689274352831)
  ·
    refine ⟨429757249573118533911529247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286504833048745689274352831 429757249573118533911529247)
    ·
      refine ⟨644635874359677800867293871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429757249573118533911529247 644635874359677800867293871)
      ·
        refine ⟨966953811539516701300940807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644635874359677800867293871 966953811539516701300940807)
        ·
          refine ⟨1450430717309275051951411211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966953811539516701300940807 1450430717309275051951411211)
          ·
            refine ⟨2175646075963912577927116817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450430717309275051951411211 2175646075963912577927116817)
            ·
              refine ⟨1631734556972934433445337613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2175646075963912577927116817 1631734556972934433445337613)
              ·
                refine ⟨611900458864850412542001605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1631734556972934433445337613 611900458864850412542001605)
                ·
                  refine ⟨114731336037159452351625301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 611900458864850412542001605 114731336037159452351625301)
                  ·
                    refine ⟨1344507844185462332245609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114731336037159452351625301 1344507844185462332245609)
                    ·
                      rfl

theorem cell23_7855259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 8].length) (baseStart_7855259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855259 prefixEnd_7855259 := by exact prefixLift 7855259
  have htrace : WordTrace (prefixWord ++ tailWord_7855259) baseStart_7855259 baseEnd_7855259 := by
    simpa [prefixWord, tailWord_7855259, baseEnd_7855259] using wordTrace_append hprefix tailTrace_7855259
  have hstable : (prefixWord ++ tailWord_7855259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855259).length < 2 ^ (prefixWord ++ tailWord_7855259).sum := by decide
  have hdescent : baseEnd_7855259 < baseStart_7855259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855350 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_7855350 : Nat := 118140960795 + 7855350 * 2 ^ 59
def prefixEnd_7855350 : Nat := 4983230072969 + 3 ^ 40 * 7855350 * 2
def baseEnd_7855350 : Nat := 4033570259295946140698909

theorem tailTrace_7855350 : CollatzResearch.WordTrace tailWord_7855350 prefixEnd_7855350 4033570259295946140698909 := by
  unfold tailWord_7855350
  simp only [CollatzResearch.WordTrace]
  refine ⟨17906759505713500738494719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191005434727610674543943669 17906759505713500738494719)
  ·
    refine ⟨26860139258570251107742079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17906759505713500738494719 26860139258570251107742079)
    ·
      refine ⟨40290208887855376661613119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26860139258570251107742079 40290208887855376661613119)
      ·
        refine ⟨60435313331783064992419679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40290208887855376661613119 60435313331783064992419679)
        ·
          refine ⟨90652969997674597488629519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60435313331783064992419679 90652969997674597488629519)
          ·
            refine ⟨135979454996511896232944279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90652969997674597488629519 135979454996511896232944279)
            ·
              refine ⟨203969182494767844349416419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135979454996511896232944279 203969182494767844349416419)
              ·
                refine ⟨305953773742151766524124629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203969182494767844349416419 305953773742151766524124629)
                ·
                  refine ⟨7170791572081682027909171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 305953773742151766524124629 7170791572081682027909171)
                  ·
                    refine ⟨10756187358122523041863757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7170791572081682027909171 10756187358122523041863757)
                    ·
                      refine ⟨4033570259295946140698909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10756187358122523041863757 4033570259295946140698909)
                      ·
                        rfl

theorem cell23_7855350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_7855350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855350 prefixEnd_7855350 := by exact prefixLift 7855350
  have htrace : WordTrace (prefixWord ++ tailWord_7855350) baseStart_7855350 baseEnd_7855350 := by
    simpa [prefixWord, tailWord_7855350, baseEnd_7855350] using wordTrace_append hprefix tailTrace_7855350
  have hstable : (prefixWord ++ tailWord_7855350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855350).length < 2 ^ (prefixWord ++ tailWord_7855350).sum := by decide
  have hdescent : baseEnd_7855350 < baseStart_7855350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855353 : List Nat := [1, 2, 1, 3, 1, 1, 5, 3, 1, 5]
def baseStart_7855353 : Nat := 118140960795 + 7855353 * 2 ^ 59
def prefixEnd_7855353 : Nat := 4983230072969 + 3 ^ 40 * 7855353 * 2
def baseEnd_7855353 : Nat := 1344523933245969876320465

theorem tailTrace_7855353 : CollatzResearch.WordTrace tailWord_7855353 prefixEnd_7855353 1344523933245969876320465 := by
  unfold tailWord_7855353
  simp only [CollatzResearch.WordTrace]
  refine ⟨286508261510405143328274713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191005507673603428885516475 286508261510405143328274713)
  ·
    refine ⟨214881196132803857496206035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286508261510405143328274713 214881196132803857496206035)
    ·
      refine ⟨322321794199205786244309053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214881196132803857496206035 322321794199205786244309053)
      ·
        refine ⟨120870672824702169841615895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322321794199205786244309053 120870672824702169841615895)
        ·
          refine ⟨181306009237053254762423843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120870672824702169841615895 181306009237053254762423843)
          ·
            refine ⟨271959013855579882143635765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181306009237053254762423843 271959013855579882143635765)
            ·
              refine ⟨25496157548960613950965853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 271959013855579882143635765 25496157548960613950965853)
              ·
                refine ⟨9561059080860230231612195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25496157548960613950965853 9561059080860230231612195)
                ·
                  refine ⟨14341588621290345347418293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9561059080860230231612195 14341588621290345347418293)
                  ·
                    refine ⟨1344523933245969876320465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14341588621290345347418293 1344523933245969876320465)
                    ·
                      rfl

theorem cell23_7855353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 5].length) (baseStart_7855353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855353 prefixEnd_7855353 := by exact prefixLift 7855353
  have htrace : WordTrace (prefixWord ++ tailWord_7855353) baseStart_7855353 baseEnd_7855353 := by
    simpa [prefixWord, tailWord_7855353, baseEnd_7855353] using wordTrace_append hprefix tailTrace_7855353
  have hstable : (prefixWord ++ tailWord_7855353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855353).length < 2 ^ (prefixWord ++ tailWord_7855353).sum := by decide
  have hdescent : baseEnd_7855353 < baseStart_7855353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855400 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 4, 4]
def baseStart_7855400 : Nat := 118140960795 + 7855400 * 2 ^ 59
def prefixEnd_7855400 : Nat := 4983230072969 + 3 ^ 40 * 7855400 * 2
def baseEnd_7855400 : Nat := 1344531977776223648357893

theorem tailTrace_7855400 : CollatzResearch.WordTrace tailWord_7855400 prefixEnd_7855400 1344531977776223648357893 := by
  unfold tailWord_7855400
  simp only [CollatzResearch.WordTrace]
  refine ⟨143254987870617435177617827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191006650494156580236823769 143254987870617435177617827)
  ·
    refine ⟨214882481805926152766426741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143254987870617435177617827 214882481805926152766426741)
    ·
      refine ⟨20145232669305576821852507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214882481805926152766426741 20145232669305576821852507)
      ·
        refine ⟨30217849003958365232778761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20145232669305576821852507 30217849003958365232778761)
        ·
          refine ⟨22663386752968773924584071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30217849003958365232778761 22663386752968773924584071)
          ·
            refine ⟨33995080129453160886876107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22663386752968773924584071 33995080129453160886876107)
            ·
              refine ⟨50992620194179741330314161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33995080129453160886876107 50992620194179741330314161)
              ·
                refine ⟨38244465145634805997735621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50992620194179741330314161 38244465145634805997735621)
                ·
                  refine ⟨7170837214806526124575429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38244465145634805997735621 7170837214806526124575429)
                  ·
                    refine ⟨1344531977776223648357893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7170837214806526124575429 1344531977776223648357893)
                    ·
                      rfl

theorem cell23_7855400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_7855400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855400 prefixEnd_7855400 := by exact prefixLift 7855400
  have htrace : WordTrace (prefixWord ++ tailWord_7855400) baseStart_7855400 baseEnd_7855400 := by
    simpa [prefixWord, tailWord_7855400, baseEnd_7855400] using wordTrace_append hprefix tailTrace_7855400
  have hstable : (prefixWord ++ tailWord_7855400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855400).length < 2 ^ (prefixWord ++ tailWord_7855400).sum := by decide
  have hdescent : baseEnd_7855400 < baseStart_7855400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855410 : List Nat := [3, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5]
def baseStart_7855410 : Nat := 118140960795 + 7855410 * 2 ^ 59
def prefixEnd_7855410 : Nat := 4983230072969 + 3 ^ 40 * 7855410 * 2
def baseEnd_7855410 : Nat := 4033601068135215905948633

theorem tailTrace_7855410 : CollatzResearch.WordTrace tailWord_7855410 prefixEnd_7855410 4033601068135215905948633 := by
  unfold tailWord_7855410
  simp only [CollatzResearch.WordTrace]
  refine ⟨71627585117799660515774921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191006893647465761375399789 71627585117799660515774921)
  ·
    refine ⟨53720688838349745386831191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71627585117799660515774921 53720688838349745386831191)
    ·
      refine ⟨80581033257524618080246787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53720688838349745386831191 80581033257524618080246787)
      ·
        refine ⟨120871549886286927120370181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80581033257524618080246787 120871549886286927120370181)
        ·
          refine ⟨22663415603678798835069409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120871549886286927120370181 22663415603678798835069409)
          ·
            refine ⟨16997561702759099126302057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22663415603678798835069409 16997561702759099126302057)
            ·
              refine ⟨12748171277069324344726543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16997561702759099126302057 12748171277069324344726543)
              ·
                refine ⟨19122256915603986517089815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12748171277069324344726543 19122256915603986517089815)
                ·
                  refine ⟨28683385373405979775634723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19122256915603986517089815 28683385373405979775634723)
                  ·
                    refine ⟨43025078060108969663452085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28683385373405979775634723 43025078060108969663452085)
                    ·
                      refine ⟨4033601068135215905948633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43025078060108969663452085 4033601068135215905948633)
                      ·
                        rfl

theorem cell23_7855410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_7855410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855410 prefixEnd_7855410 := by exact prefixLift 7855410
  have htrace : WordTrace (prefixWord ++ tailWord_7855410) baseStart_7855410 baseEnd_7855410 := by
    simpa [prefixWord, tailWord_7855410, baseEnd_7855410] using wordTrace_append hprefix tailTrace_7855410
  have hstable : (prefixWord ++ tailWord_7855410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855410).length < 2 ^ (prefixWord ++ tailWord_7855410).sum := by decide
  have hdescent : baseEnd_7855410 < baseStart_7855410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855413 : List Nat := [1, 3, 3, 1, 2, 4, 9]
def baseStart_7855413 : Nat := 118140960795 + 7855413 * 2 ^ 59
def prefixEnd_7855413 : Nat := 4983230072969 + 3 ^ 40 * 7855413 * 2
def baseEnd_7855413 : Nat := 49797563068854066595199

theorem tailTrace_7855413 : CollatzResearch.WordTrace tailWord_7855413 prefixEnd_7855413 49797563068854066595199 := by
  unfold tailWord_7855413
  simp only [CollatzResearch.WordTrace]
  refine ⟨286510449890187773575458893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191006966593458515716972595 286510449890187773575458893)
  ·
    refine ⟨107441418708820415090797085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286510449890187773575458893 107441418708820415090797085)
    ·
      refine ⟨40290532015807655659048907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107441418708820415090797085 40290532015807655659048907)
      ·
        refine ⟨60435798023711483488573361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40290532015807655659048907 60435798023711483488573361)
        ·
          refine ⟨45326848517783612616430021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60435798023711483488573361 45326848517783612616430021)
          ·
            refine ⟨8498784097084427365580629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45326848517783612616430021 8498784097084427365580629)
            ·
              refine ⟨49797563068854066595199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8498784097084427365580629 49797563068854066595199)
              ·
                rfl

theorem cell23_7855413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 9].length) (baseStart_7855413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855413 prefixEnd_7855413 := by exact prefixLift 7855413
  have htrace : WordTrace (prefixWord ++ tailWord_7855413) baseStart_7855413 baseEnd_7855413 := by
    simpa [prefixWord, tailWord_7855413, baseEnd_7855413] using wordTrace_append hprefix tailTrace_7855413
  have hstable : (prefixWord ++ tailWord_7855413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855413).length < 2 ^ (prefixWord ++ tailWord_7855413).sum := by decide
  have hdescent : baseEnd_7855413 < baseStart_7855413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855483 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 3]
def baseStart_7855483 : Nat := 118140960795 + 7855483 * 2 ^ 59
def prefixEnd_7855483 : Nat := 4983230072969 + 3 ^ 40 * 7855483 * 2
def baseEnd_7855483 : Nat := 4033638552222994120335797

theorem tailTrace_7855483 : CollatzResearch.WordTrace tailWord_7855483 prefixEnd_7855483 4033638552222994120335797 := by
  unfold tailWord_7855483
  simp only [CollatzResearch.WordTrace]
  refine ⟨286513002999934175530507103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191008668666622783687004735 286513002999934175530507103)
  ·
    refine ⟨429769504499901263295760655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286513002999934175530507103 429769504499901263295760655)
    ·
      refine ⟨644654256749851894943640983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429769504499901263295760655 644654256749851894943640983)
      ·
        refine ⟨966981385124777842415461475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644654256749851894943640983 966981385124777842415461475)
        ·
          refine ⟨1450472077687166763623192213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966981385124777842415461475 1450472077687166763623192213)
          ·
            refine ⟨67990878641585942044837135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1450472077687166763623192213 67990878641585942044837135)
            ·
              refine ⟨101986317962378913067255703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67990878641585942044837135 101986317962378913067255703)
              ·
                refine ⟨152979476943568369600883555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101986317962378913067255703 152979476943568369600883555)
                ·
                  refine ⟨229469215415352554401325333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152979476943568369600883555 229469215415352554401325333)
                  ·
                    refine ⟨10756369472594650987562125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 229469215415352554401325333 10756369472594650987562125)
                    ·
                      refine ⟨4033638552222994120335797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10756369472594650987562125 4033638552222994120335797)
                      ·
                        rfl

theorem cell23_7855483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 3].length) (baseStart_7855483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855483 prefixEnd_7855483 := by exact prefixLift 7855483
  have htrace : WordTrace (prefixWord ++ tailWord_7855483) baseStart_7855483 baseEnd_7855483 := by
    simpa [prefixWord, tailWord_7855483, baseEnd_7855483] using wordTrace_append hprefix tailTrace_7855483
  have hstable : (prefixWord ++ tailWord_7855483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855483).length < 2 ^ (prefixWord ++ tailWord_7855483).sum := by decide
  have hdescent : baseEnd_7855483 < baseStart_7855483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855493 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 1, 4, 4]
def baseStart_7855493 : Nat := 118140960795 + 7855493 * 2 ^ 59
def prefixEnd_7855493 : Nat := 4983230072969 + 3 ^ 40 * 7855493 * 2
def baseEnd_7855493 : Nat := 4033643687029539081210751

theorem tailTrace_7855493 : CollatzResearch.WordTrace tailWord_7855493 prefixEnd_7855493 4033643687029539081210751 := by
  unfold tailWord_7855493
  simp only [CollatzResearch.WordTrace]
  refine ⟨286513367729897947238371133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191008911819931964825580755 286513367729897947238371133)
  ·
    refine ⟨107442512898711730214389175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286513367729897947238371133 107442512898711730214389175)
    ·
      refine ⟨161163769348067595321583763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107442512898711730214389175 161163769348067595321583763)
      ·
        refine ⟨241745654022101392982375645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161163769348067595321583763 241745654022101392982375645)
        ·
          refine ⟨90654620258288022368390867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241745654022101392982375645 90654620258288022368390867)
          ·
            refine ⟨135981930387432033552586301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90654620258288022368390867 135981930387432033552586301)
            ·
              refine ⟨50993223895287012582219863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135981930387432033552586301 50993223895287012582219863)
              ·
                refine ⟨76489835842930518873329795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50993223895287012582219863 76489835842930518873329795)
                ·
                  refine ⟨114734753764395778309994693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76489835842930518873329795 114734753764395778309994693)
                  ·
                    refine ⟨21512766330824208433124005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114734753764395778309994693 21512766330824208433124005)
                    ·
                      refine ⟨4033643687029539081210751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21512766330824208433124005 4033643687029539081210751)
                      ·
                        rfl

theorem cell23_7855493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_7855493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855493 prefixEnd_7855493 := by exact prefixLift 7855493
  have htrace : WordTrace (prefixWord ++ tailWord_7855493) baseStart_7855493 baseEnd_7855493 := by
    simpa [prefixWord, tailWord_7855493, baseEnd_7855493] using wordTrace_append hprefix tailTrace_7855493
  have hstable : (prefixWord ++ tailWord_7855493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855493).length < 2 ^ (prefixWord ++ tailWord_7855493).sum := by decide
  have hdescent : baseEnd_7855493 < baseStart_7855493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855543 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 7]
def baseStart_7855543 : Nat := 118140960795 + 7855543 * 2 ^ 59
def prefixEnd_7855543 : Nat := 4983230072969 + 3 ^ 40 * 7855543 * 2
def baseEnd_7855543 : Nat := 4033669361062263885585521

theorem tailTrace_7855543 : CollatzResearch.WordTrace tailWord_7855543 prefixEnd_7855543 4033669361062263885585521 := by
  unfold tailWord_7855543
  simp only [CollatzResearch.WordTrace]
  refine ⟨286515191379716805777691283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191010127586477870518460855 286515191379716805777691283)
  ·
    refine ⟨429772787069575208666536925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286515191379716805777691283 429772787069575208666536925)
    ·
      refine ⟨161164795151090703249951347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429772787069575208666536925 161164795151090703249951347)
      ·
        refine ⟨241747192726636054874927021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161164795151090703249951347 241747192726636054874927021)
        ·
          refine ⟨90655197272488520578097633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241747192726636054874927021 90655197272488520578097633)
          ·
            refine ⟨67991397954366390433573225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90655197272488520578097633 67991397954366390433573225)
            ·
              refine ⟨50993548465774792825179919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67991397954366390433573225 50993548465774792825179919)
              ·
                refine ⟨76490322698662189237769879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50993548465774792825179919 76490322698662189237769879)
                ·
                  refine ⟨114735484047993283856654819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76490322698662189237769879 114735484047993283856654819)
                  ·
                    refine ⟨172103226071989925784982229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114735484047993283856654819 172103226071989925784982229)
                    ·
                      refine ⟨4033669361062263885585521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172103226071989925784982229 4033669361062263885585521)
                      ·
                        rfl

theorem cell23_7855543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_7855543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855543 prefixEnd_7855543 := by exact prefixLift 7855543
  have htrace : WordTrace (prefixWord ++ tailWord_7855543) baseStart_7855543 baseEnd_7855543 := by
    simpa [prefixWord, tailWord_7855543, baseEnd_7855543] using wordTrace_append hprefix tailTrace_7855543
  have hstable : (prefixWord ++ tailWord_7855543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855543).length < 2 ^ (prefixWord ++ tailWord_7855543).sum := by decide
  have hdescent : baseEnd_7855543 < baseStart_7855543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855548 : List Nat := [2, 2, 2, 4, 2, 1, 3, 1, 2, 2, 2]
def baseStart_7855548 : Nat := 118140960795 + 7855548 * 2 ^ 59
def prefixEnd_7855548 : Nat := 4983230072969 + 3 ^ 40 * 7855548 * 2
def baseEnd_7855548 : Nat := 4033671928465536366022999

theorem tailTrace_7855548 : CollatzResearch.WordTrace tailWord_7855548 prefixEnd_7855548 4033671928465536366022999 := by
  unfold tailWord_7855548
  simp only [CollatzResearch.WordTrace]
  refine ⟨143257686872349345815811649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191010249163132461087748865 143257686872349345815811649)
  ·
    refine ⟨107443265154262009361858737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143257686872349345815811649 107443265154262009361858737)
    ·
      refine ⟨80582448865696507021394053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107443265154262009361858737 80582448865696507021394053)
      ·
        refine ⟨15109209162318095066511385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80582448865696507021394053 15109209162318095066511385)
        ·
          refine ⟨11331906871738571299883539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15109209162318095066511385 11331906871738571299883539)
          ·
            refine ⟨16997860307607856949825309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11331906871738571299883539 16997860307607856949825309)
            ·
              refine ⟨6374197615352946356184491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16997860307607856949825309 6374197615352946356184491)
              ·
                refine ⟨9561296423029419534276737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6374197615352946356184491 9561296423029419534276737)
                ·
                  refine ⟨7170972317272064650707553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9561296423029419534276737 7170972317272064650707553)
                  ·
                    refine ⟨5378229237954048488030665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7170972317272064650707553 5378229237954048488030665)
                    ·
                      refine ⟨4033671928465536366022999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5378229237954048488030665 4033671928465536366022999)
                      ·
                        rfl

theorem cell23_7855548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_7855548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855548 prefixEnd_7855548 := by exact prefixLift 7855548
  have htrace : WordTrace (prefixWord ++ tailWord_7855548) baseStart_7855548 baseEnd_7855548 := by
    simpa [prefixWord, tailWord_7855548, baseEnd_7855548] using wordTrace_append hprefix tailTrace_7855548
  have hstable : (prefixWord ++ tailWord_7855548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855548).length < 2 ^ (prefixWord ++ tailWord_7855548).sum := by decide
  have hdescent : baseEnd_7855548 < baseStart_7855548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855587 : List Nat := [1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 4]
def baseStart_7855587 : Nat := 118140960795 + 7855587 * 2 ^ 59
def prefixEnd_7855587 : Nat := 4983230072969 + 3 ^ 40 * 7855587 * 2
def baseEnd_7855587 : Nat := 4033691954211061713435319

theorem tailTrace_7855587 : CollatzResearch.WordTrace tailWord_7855587 prefixEnd_7855587 4033691954211061713435319 := by
  unfold tailWord_7855587
  simp only [CollatzResearch.WordTrace]
  refine ⟨286516796191557401292293015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191011197461038267528195343 286516796191557401292293015)
  ·
    refine ⟨429775194287336101938439523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286516796191557401292293015 429775194287336101938439523)
    ·
      refine ⟨644662791431004152907659285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429775194287336101938439523 644662791431004152907659285)
      ·
        refine ⟨30218568348328319667546529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 644662791431004152907659285 30218568348328319667546529)
        ·
          refine ⟨22663926261246239750659897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30218568348328319667546529 22663926261246239750659897)
          ·
            refine ⟨16997944695934679812994923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22663926261246239750659897 16997944695934679812994923)
            ·
              refine ⟨25496917043902019719492385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16997944695934679812994923 25496917043902019719492385)
              ·
                refine ⟨19122687782926514789619289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25496917043902019719492385 19122687782926514789619289)
                ·
                  refine ⟨14342015837194886092214467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19122687782926514789619289 14342015837194886092214467)
                  ·
                    refine ⟨21513023755792329138321701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14342015837194886092214467 21513023755792329138321701)
                    ·
                      refine ⟨4033691954211061713435319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21513023755792329138321701 4033691954211061713435319)
                      ·
                        rfl

theorem cell23_7855587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_7855587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855587 prefixEnd_7855587 := by exact prefixLift 7855587
  have htrace : WordTrace (prefixWord ++ tailWord_7855587) baseStart_7855587 baseEnd_7855587 := by
    simpa [prefixWord, tailWord_7855587, baseEnd_7855587] using wordTrace_append hprefix tailTrace_7855587
  have hstable : (prefixWord ++ tailWord_7855587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855587).length < 2 ^ (prefixWord ++ tailWord_7855587).sum := by decide
  have hdescent : baseEnd_7855587 < baseStart_7855587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855610 : List Nat := [3, 1, 1, 1, 1, 2, 5, 3, 6]
def baseStart_7855610 : Nat := 118140960795 + 7855610 * 2 ^ 59
def prefixEnd_7855610 : Nat := 4983230072969 + 3 ^ 40 * 7855610 * 2
def baseEnd_7855610 : Nat := 448189307140679458160857

theorem tailTrace_7855610 : CollatzResearch.WordTrace tailWord_7855610 prefixEnd_7855610 448189307140679458160857 := by
  unfold tailWord_7855610
  simp only [CollatzResearch.WordTrace]
  refine ⟨71629408767618519055095071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191011756713649384146920189 71629408767618519055095071)
  ·
    refine ⟨107444113151427778582642607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71629408767618519055095071 107444113151427778582642607)
    ·
      refine ⟨161166169727141667873963911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107444113151427778582642607 161166169727141667873963911)
      ·
        refine ⟨241749254590712501810945867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161166169727141667873963911 241749254590712501810945867)
        ·
          refine ⟨362623881886068752716418801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241749254590712501810945867 362623881886068752716418801)
          ·
            refine ⟨271967911414551564537314101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362623881886068752716418801 271967911414551564537314101)
            ·
              refine ⟨25496991695114209175373197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 271967911414551564537314101 25496991695114209175373197)
              ·
                refine ⟨9561371885667828440764949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25496991695114209175373197 9561371885667828440764949)
                ·
                  refine ⟨448189307140679458160857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9561371885667828440764949 448189307140679458160857)
                  ·
                    rfl

theorem cell23_7855610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 6].length) (baseStart_7855610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855610 prefixEnd_7855610 := by exact prefixLift 7855610
  have htrace : WordTrace (prefixWord ++ tailWord_7855610) baseStart_7855610 baseEnd_7855610 := by
    simpa [prefixWord, tailWord_7855610, baseEnd_7855610] using wordTrace_append hprefix tailTrace_7855610
  have hstable : (prefixWord ++ tailWord_7855610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855610).length < 2 ^ (prefixWord ++ tailWord_7855610).sum := by decide
  have hdescent : baseEnd_7855610 < baseStart_7855610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855648 : List Nat := [2, 1, 1, 6, 1, 3, 2, 2, 1, 4]
def baseStart_7855648 : Nat := 118140960795 + 7855648 * 2 ^ 59
def prefixEnd_7855648 : Nat := 4983230072969 + 3 ^ 40 * 7855648 * 2
def baseEnd_7855648 : Nat := 1344574425510328658257513

theorem tailTrace_7855648 : CollatzResearch.WordTrace tailWord_7855648 prefixEnd_7855648 1344574425510328658257513 := by
  unfold tailWord_7855648
  simp only [CollatzResearch.WordTrace]
  refine ⟨143259510522168204355131799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191012680696224272473509065 143259510522168204355131799)
  ·
    refine ⟨214889265783252306532697699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143259510522168204355131799 214889265783252306532697699)
    ·
      refine ⟨322333898674878459799046549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214889265783252306532697699 322333898674878459799046549)
      ·
        refine ⟨15109401500384927803080307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 322333898674878459799046549 15109401500384927803080307)
        ·
          refine ⟨22664102250577391704620461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15109401500384927803080307 22664102250577391704620461)
          ·
            refine ⟨8499038343966521889232673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22664102250577391704620461 8499038343966521889232673)
            ·
              refine ⟨6374278757974891416924505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8499038343966521889232673 6374278757974891416924505)
              ·
                refine ⟨4780709068481168562693379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6374278757974891416924505 4780709068481168562693379)
                ·
                  refine ⟨7171063602721752844040069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4780709068481168562693379 7171063602721752844040069)
                  ·
                    refine ⟨1344574425510328658257513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7171063602721752844040069 1344574425510328658257513)
                    ·
                      rfl

theorem cell23_7855648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 1, 4].length) (baseStart_7855648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855648 prefixEnd_7855648 := by exact prefixLift 7855648
  have htrace : WordTrace (prefixWord ++ tailWord_7855648) baseStart_7855648 baseEnd_7855648 := by
    simpa [prefixWord, tailWord_7855648, baseEnd_7855648] using wordTrace_append hprefix tailTrace_7855648
  have hstable : (prefixWord ++ tailWord_7855648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855648).length < 2 ^ (prefixWord ++ tailWord_7855648).sum := by decide
  have hdescent : baseEnd_7855648 < baseStart_7855648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855694 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2]
def baseStart_7855694 : Nat := 118140960795 + 7855694 * 2 ^ 59
def prefixEnd_7855694 : Nat := 4983230072969 + 3 ^ 40 * 7855694 * 2
def baseEnd_7855694 : Nat := 4033746896641092794797327

theorem tailTrace_7855694 : CollatzResearch.WordTrace tailWord_7855694 prefixEnd_7855694 4033746896641092794797327 := by
  unfold tailWord_7855694
  simp only [CollatzResearch.WordTrace]
  refine ⟨35815087350271219820804767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191013799201446505710958757 35815087350271219820804767)
  ·
    refine ⟨53722631025406829731207151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35815087350271219820804767 53722631025406829731207151)
    ·
      refine ⟨80583946538110244596810727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53722631025406829731207151 80583946538110244596810727)
      ·
        refine ⟨120875919807165366895216091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80583946538110244596810727 120875919807165366895216091)
        ·
          refine ⟨181313879710748050342824137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120875919807165366895216091 181313879710748050342824137)
          ·
            refine ⟨135985409783061037757118103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181313879710748050342824137 135985409783061037757118103)
            ·
              refine ⟨203978114674591556635677155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135985409783061037757118103 203978114674591556635677155)
              ·
                refine ⟨305967172011887334953515733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203978114674591556635677155 305967172011887334953515733)
                ·
                  refine ⟨7171105594028609412973025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 305967172011887334953515733 7171105594028609412973025)
                  ·
                    refine ⟨5378329195521457059729769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7171105594028609412973025 5378329195521457059729769)
                    ·
                      refine ⟨4033746896641092794797327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5378329195521457059729769 4033746896641092794797327)
                      ·
                        rfl

theorem cell23_7855694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_7855694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855694 prefixEnd_7855694 := by exact prefixLift 7855694
  have htrace : WordTrace (prefixWord ++ tailWord_7855694) baseStart_7855694 baseEnd_7855694 := by
    simpa [prefixWord, tailWord_7855694, baseEnd_7855694] using wordTrace_append hprefix tailTrace_7855694
  have hstable : (prefixWord ++ tailWord_7855694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855694).length < 2 ^ (prefixWord ++ tailWord_7855694).sum := by decide
  have hdescent : baseEnd_7855694 < baseStart_7855694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855700 : List Nat := [2, 4, 1, 1, 1, 2, 12]
def baseStart_7855700 : Nat := 118140960795 + 7855700 * 2 ^ 59
def prefixEnd_7855700 : Nat := 4983230072969 + 3 ^ 40 * 7855700 * 2
def baseEnd_7855700 : Nat := 49799382438580491003979

theorem tailTrace_7855700 : CollatzResearch.WordTrace tailWord_7855700 prefixEnd_7855700 49799382438580491003979 := by
  unfold tailWord_7855700
  simp only [CollatzResearch.WordTrace]
  refine ⟨143260458820074010795578277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191013945093432014394104369 143260458820074010795578277)
  ·
    refine ⟨26861336028763877024170927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143260458820074010795578277 26861336028763877024170927)
    ·
      refine ⟨40292004043145815536256391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26861336028763877024170927 40292004043145815536256391)
      ·
        refine ⟨60438006064718723304384587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40292004043145815536256391 60438006064718723304384587)
        ·
          refine ⟨90657009097078084956576881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60438006064718723304384587 90657009097078084956576881)
          ·
            refine ⟨67992756822808563717432661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90657009097078084956576881 67992756822808563717432661)
            ·
              refine ⟨49799382438580491003979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 67992756822808563717432661 49799382438580491003979)
              ·
                rfl

theorem cell23_7855700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 12].length) (baseStart_7855700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855700 prefixEnd_7855700 := by exact prefixLift 7855700
  have htrace : WordTrace (prefixWord ++ tailWord_7855700) baseStart_7855700 baseEnd_7855700 := by
    simpa [prefixWord, tailWord_7855700, baseEnd_7855700] using wordTrace_append hprefix tailTrace_7855700
  have hstable : (prefixWord ++ tailWord_7855700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855700).length < 2 ^ (prefixWord ++ tailWord_7855700).sum := by decide
  have hdescent : baseEnd_7855700 < baseStart_7855700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855734 : List Nat := [5, 1, 1, 2, 2, 1, 4, 7]
def baseStart_7855734 : Nat := 118140960795 + 7855734 * 2 ^ 59
def prefixEnd_7855734 : Nat := 4983230072969 + 3 ^ 40 * 7855734 * 2
def baseEnd_7855734 : Nat := 149398793921010097714709

theorem tailTrace_7855734 : CollatzResearch.WordTrace tailWord_7855734 prefixEnd_7855734 149398793921010097714709 := by
  unfold tailWord_7855734
  simp only [CollatzResearch.WordTrace]
  refine ⟨17907634857626552837368391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191014771814683230265262837 17907634857626552837368391)
  ·
    refine ⟨26861452286439829256052587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17907634857626552837368391 26861452286439829256052587)
    ·
      refine ⟨40292178429659743884078881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26861452286439829256052587 40292178429659743884078881)
      ·
        refine ⟨30219133822244807913059161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40292178429659743884078881 30219133822244807913059161)
        ·
          refine ⟨22664350366683605934794371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30219133822244807913059161 22664350366683605934794371)
          ·
            refine ⟨33996525550025408902191557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22664350366683605934794371 33996525550025408902191557)
            ·
              refine ⟨6374348540629764169160917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33996525550025408902191557 6374348540629764169160917)
              ·
                refine ⟨149398793921010097714709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6374348540629764169160917 149398793921010097714709)
                ·
                  rfl

theorem cell23_7855734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_7855734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855734 prefixEnd_7855734 := by exact prefixLift 7855734
  have htrace : WordTrace (prefixWord ++ tailWord_7855734) baseStart_7855734 baseEnd_7855734 := by
    simpa [prefixWord, tailWord_7855734, baseEnd_7855734] using wordTrace_append hprefix tailTrace_7855734
  have hstable : (prefixWord ++ tailWord_7855734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855734).length < 2 ^ (prefixWord ++ tailWord_7855734).sum := by decide
  have hdescent : baseEnd_7855734 < baseStart_7855734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855745 : List Nat := [1, 2, 4, 2, 1, 4, 1, 3, 1, 2, 2]
def baseStart_7855745 : Nat := 118140960795 + 7855745 * 2 ^ 59
def prefixEnd_7855745 : Nat := 4983230072969 + 3 ^ 40 * 7855745 * 2
def baseEnd_7855745 : Nat := 4033773084154472095259593

theorem tailTrace_7855745 : CollatzResearch.WordTrace tailWord_7855745 prefixEnd_7855745 4033773084154472095259593 := by
  unfold tailWord_7855745
  simp only [CollatzResearch.WordTrace]
  refine ⟨286522558924984994276544689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191015039283323329517696459 286522558924984994276544689)
  ·
    refine ⟨214891919193738745707408517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286522558924984994276544689 214891919193738745707408517)
    ·
      refine ⟨40292234848826014820139097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214891919193738745707408517 40292234848826014820139097)
      ·
        refine ⟨30219176136619511115104323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40292234848826014820139097 30219176136619511115104323)
        ·
          refine ⟨45328764204929266672656485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30219176136619511115104323 45328764204929266672656485)
          ·
            refine ⟨8499143288424237501123091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45328764204929266672656485 8499143288424237501123091)
            ·
              refine ⟨12748714932636356251684637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8499143288424237501123091 12748714932636356251684637)
              ·
                refine ⟨4780768099738633594381739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12748714932636356251684637 4780768099738633594381739)
                ·
                  refine ⟨7171152149607950391572609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4780768099738633594381739 7171152149607950391572609)
                  ·
                    refine ⟨5378364112205962793679457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7171152149607950391572609 5378364112205962793679457)
                    ·
                      refine ⟨4033773084154472095259593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5378364112205962793679457 4033773084154472095259593)
                      ·
                        rfl

theorem cell23_7855745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_7855745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855745 prefixEnd_7855745 := by exact prefixLift 7855745
  have htrace : WordTrace (prefixWord ++ tailWord_7855745) baseStart_7855745 baseEnd_7855745 := by
    simpa [prefixWord, tailWord_7855745, baseEnd_7855745] using wordTrace_append hprefix tailTrace_7855745
  have hstable : (prefixWord ++ tailWord_7855745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855745).length < 2 ^ (prefixWord ++ tailWord_7855745).sum := by decide
  have hdescent : baseEnd_7855745 < baseStart_7855745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855760 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 4, 6]
def baseStart_7855760 : Nat := 118140960795 + 7855760 * 2 ^ 59
def prefixEnd_7855760 : Nat := 4983230072969 + 3 ^ 40 * 7855760 * 2
def baseEnd_7855760 : Nat := 1344593595454763178857341

theorem tailTrace_7855760 : CollatzResearch.WordTrace tailWord_7855760 prefixEnd_7855760 1344593595454763178857341 := by
  unfold tailWord_7855760
  simp only [CollatzResearch.WordTrace]
  refine ⟨143261553009965325919170367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191015404013287101225560489 143261553009965325919170367)
  ·
    refine ⟨214892329514947988878755551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143261553009965325919170367 214892329514947988878755551)
    ·
      refine ⟨322338494272421983318133327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214892329514947988878755551 322338494272421983318133327)
      ·
        refine ⟨483507741408632974977199991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322338494272421983318133327 483507741408632974977199991)
        ·
          refine ⟨725261612112949462465799987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483507741408632974977199991 725261612112949462465799987)
          ·
            refine ⟨1087892418169424193698699981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725261612112949462465799987 1087892418169424193698699981)
            ·
              refine ⟨407959656813534072637012493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1087892418169424193698699981 407959656813534072637012493)
              ·
                refine ⟨152984871305075277238879685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407959656813534072637012493 152984871305075277238879685)
                ·
                  refine ⟨28684663369701614482289941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152984871305075277238879685 28684663369701614482289941)
                  ·
                    refine ⟨1344593595454763178857341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28684663369701614482289941 1344593595454763178857341)
                    ·
                      rfl

theorem cell23_7855760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 4, 6].length) (baseStart_7855760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855760 prefixEnd_7855760 := by exact prefixLift 7855760
  have htrace : WordTrace (prefixWord ++ tailWord_7855760) baseStart_7855760 baseEnd_7855760 := by
    simpa [prefixWord, tailWord_7855760, baseEnd_7855760] using wordTrace_append hprefix tailTrace_7855760
  have hstable : (prefixWord ++ tailWord_7855760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855760).length < 2 ^ (prefixWord ++ tailWord_7855760).sum := by decide
  have hdescent : baseEnd_7855760 < baseStart_7855760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855762 : List Nat := [3, 2, 3, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_7855762 : Nat := 118140960795 + 7855762 * 2 ^ 59
def prefixEnd_7855762 : Nat := 4983230072969 + 3 ^ 40 * 7855762 * 2
def baseEnd_7855762 : Nat := 4033781813325598528747015

theorem tailTrace_7855762 : CollatzResearch.WordTrace tailWord_7855762 prefixEnd_7855762 4033781813325598528747015 := by
  unfold tailWord_7855762
  simp only [CollatzResearch.WordTrace]
  refine ⟨71630794741480851544978385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191015452643948937453275693 71630794741480851544978385)
  ·
    refine ⟨53723096056110638658733789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71630794741480851544978385 53723096056110638658733789)
    ·
      refine ⟨20146161021041489497025171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53723096056110638658733789 20146161021041489497025171)
      ·
        refine ⟨30219241531562234245537757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20146161021041489497025171 30219241531562234245537757)
        ·
          refine ⟨11332215574335837842076659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30219241531562234245537757 11332215574335837842076659)
          ·
            refine ⟨16998323361503756763114989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11332215574335837842076659 16998323361503756763114989)
            ·
              refine ⟨6374371260563908786168121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16998323361503756763114989 6374371260563908786168121)
              ·
                refine ⟨4780778445422931589626091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6374371260563908786168121 4780778445422931589626091)
                ·
                  refine ⟨7171167668134397384439137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4780778445422931589626091 7171167668134397384439137)
                  ·
                    refine ⟨5378375751100798038329353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7171167668134397384439137 5378375751100798038329353)
                    ·
                      refine ⟨4033781813325598528747015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5378375751100798038329353 4033781813325598528747015)
                      ·
                        rfl

theorem cell23_7855762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_7855762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855762 prefixEnd_7855762 := by exact prefixLift 7855762
  have htrace : WordTrace (prefixWord ++ tailWord_7855762) baseStart_7855762 baseEnd_7855762 := by
    simpa [prefixWord, tailWord_7855762, baseEnd_7855762] using wordTrace_append hprefix tailTrace_7855762
  have hstable : (prefixWord ++ tailWord_7855762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855762).length < 2 ^ (prefixWord ++ tailWord_7855762).sum := by decide
  have hdescent : baseEnd_7855762 < baseStart_7855762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855821 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_7855821 : Nat := 118140960795 + 7855821 * 2 ^ 59
def prefixEnd_7855821 : Nat := 4983230072969 + 3 ^ 40 * 7855821 * 2
def baseEnd_7855821 : Nat := 4033812108684213797909243

theorem tailTrace_7855821 : CollatzResearch.WordTrace tailWord_7855821 prefixEnd_7855821 4033812108684213797909243 := by
  unfold tailWord_7855821
  simp only [CollatzResearch.WordTrace]
  refine ⟨286525330872709659256311317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191016887248473106170874211 286525330872709659256311317)
  ·
    refine ⟨13430874884658265277639593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 286525330872709659256311317 13430874884658265277639593)
    ·
      refine ⟨10073156163493698958229695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13430874884658265277639593 10073156163493698958229695)
      ·
        refine ⟨15109734245240548437344543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10073156163493698958229695 15109734245240548437344543)
        ·
          refine ⟨22664601367860822656016815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15109734245240548437344543 22664601367860822656016815)
          ·
            refine ⟨33996902051791233984025223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22664601367860822656016815 33996902051791233984025223)
            ·
              refine ⟨50995353077686850976037835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33996902051791233984025223 50995353077686850976037835)
              ·
                refine ⟨76493029616530276464056753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50995353077686850976037835 76493029616530276464056753)
                ·
                  refine ⟨57369772212397707348042565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76493029616530276464056753 57369772212397707348042565)
                  ·
                    refine ⟨10756832289824570127757981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57369772212397707348042565 10756832289824570127757981)
                    ·
                      refine ⟨4033812108684213797909243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10756832289824570127757981 4033812108684213797909243)
                      ·
                        rfl

theorem cell23_7855821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_7855821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855821 prefixEnd_7855821 := by exact prefixLift 7855821
  have htrace : WordTrace (prefixWord ++ tailWord_7855821) baseStart_7855821 baseEnd_7855821 := by
    simpa [prefixWord, tailWord_7855821, baseEnd_7855821] using wordTrace_append hprefix tailTrace_7855821
  have hstable : (prefixWord ++ tailWord_7855821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855821).length < 2 ^ (prefixWord ++ tailWord_7855821).sum := by decide
  have hdescent : baseEnd_7855821 < baseStart_7855821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855834 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3]
def baseStart_7855834 : Nat := 118140960795 + 7855834 * 2 ^ 59
def prefixEnd_7855834 : Nat := 4983230072969 + 3 ^ 40 * 7855834 * 2
def baseEnd_7855834 : Nat := 4033818783932722247046683

theorem tailTrace_7855834 : CollatzResearch.WordTrace tailWord_7855834 prefixEnd_7855834 4033818783932722247046683 := by
  unfold tailWord_7855834
  simp only [CollatzResearch.WordTrace]
  refine ⟨71631451255415640619133639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191017203347775041651023037 71631451255415640619133639)
  ·
    refine ⟨107447176883123460928700459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71631451255415640619133639 107447176883123460928700459)
    ·
      refine ⟨161170765324685191393050689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107447176883123460928700459 161170765324685191393050689)
      ·
        refine ⟨120878073993513893544788017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161170765324685191393050689 120878073993513893544788017)
        ·
          refine ⟨90658555495135420158591013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120878073993513893544788017 90658555495135420158591013)
          ·
            refine ⟨16998479155337891279735815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90658555495135420158591013 16998479155337891279735815)
            ·
              refine ⟨25497718733006836919603723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16998479155337891279735815 25497718733006836919603723)
              ·
                refine ⟨38246578099510255379405585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25497718733006836919603723 38246578099510255379405585)
                ·
                  refine ⟨28684933574632691534554189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38246578099510255379405585 28684933574632691534554189)
                  ·
                    refine ⟨10756850090487259325457821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28684933574632691534554189 10756850090487259325457821)
                    ·
                      refine ⟨4033818783932722247046683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10756850090487259325457821 4033818783932722247046683)
                      ·
                        rfl

theorem cell23_7855834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_7855834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855834 prefixEnd_7855834 := by exact prefixLift 7855834
  have htrace : WordTrace (prefixWord ++ tailWord_7855834) baseStart_7855834 baseEnd_7855834 := by
    simpa [prefixWord, tailWord_7855834, baseEnd_7855834] using wordTrace_append hprefix tailTrace_7855834
  have hstable : (prefixWord ++ tailWord_7855834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855834).length < 2 ^ (prefixWord ++ tailWord_7855834).sum := by decide
  have hdescent : baseEnd_7855834 < baseStart_7855834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855844 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 2, 5, 2]
def baseStart_7855844 : Nat := 118140960795 + 7855844 * 2 ^ 59
def prefixEnd_7855844 : Nat := 4983230072969 + 3 ^ 40 * 7855844 * 2
def baseEnd_7855844 : Nat := 4033823918739267207921637

theorem tailTrace_7855844 : CollatzResearch.WordTrace tailWord_7855844 prefixEnd_7855844 4033823918739267207921637 := by
  unfold tailWord_7855844
  simp only [CollatzResearch.WordTrace]
  refine ⟨143263084875813167092199293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191017446501084222789599057 143263084875813167092199293)
  ·
    refine ⟨53723656828429937659574735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143263084875813167092199293 53723656828429937659574735)
    ·
      refine ⟨80585485242644906489362103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53723656828429937659574735 80585485242644906489362103)
      ·
        refine ⟨120878227863967359734043155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80585485242644906489362103 120878227863967359734043155)
        ·
          refine ⟨181317341795951039601064733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120878227863967359734043155 181317341795951039601064733)
          ·
            refine ⟨67994003173481639850399275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181317341795951039601064733 67994003173481639850399275)
            ·
              refine ⟨101991004760222459775598913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67994003173481639850399275 101991004760222459775598913)
              ·
                refine ⟨76493253570166844831699185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101991004760222459775598913 76493253570166844831699185)
                ·
                  refine ⟨57369940177625133623774389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76493253570166844831699185 57369940177625133623774389)
                  ·
                    refine ⟨5378431891652356277228849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57369940177625133623774389 5378431891652356277228849)
                    ·
                      refine ⟨4033823918739267207921637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5378431891652356277228849 4033823918739267207921637)
                      ·
                        rfl

theorem cell23_7855844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_7855844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855844 prefixEnd_7855844 := by exact prefixLift 7855844
  have htrace : WordTrace (prefixWord ++ tailWord_7855844) baseStart_7855844 baseEnd_7855844 := by
    simpa [prefixWord, tailWord_7855844, baseEnd_7855844] using wordTrace_append hprefix tailTrace_7855844
  have hstable : (prefixWord ++ tailWord_7855844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855844).length < 2 ^ (prefixWord ++ tailWord_7855844).sum := by decide
  have hdescent : baseEnd_7855844 < baseStart_7855844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855884 : List Nat := [2, 2, 1, 2, 2, 1, 3, 3, 3, 4]
def baseStart_7855884 : Nat := 118140960795 + 7855884 * 2 ^ 59
def prefixEnd_7855884 : Nat := 4983230072969 + 3 ^ 40 * 7855884 * 2
def baseEnd_7855884 : Nat := 1344614819321815683807151

theorem tailTrace_7855884 : CollatzResearch.WordTrace tailWord_7855884 prefixEnd_7855884 1344614819321815683807151 := by
  unfold tailWord_7855884
  simp only [CollatzResearch.WordTrace]
  refine ⟨143263814335740710507927353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191018419114320947343903137 143263814335740710507927353)
  ·
    refine ⟨107447860751805532880945515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143263814335740710507927353 107447860751805532880945515)
    ·
      refine ⟨161171791127708299321418273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107447860751805532880945515 161171791127708299321418273)
      ·
        refine ⟨120878843345781224491063705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161171791127708299321418273 120878843345781224491063705)
        ·
          refine ⟨90659132509335918368297779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120878843345781224491063705 90659132509335918368297779)
          ·
            refine ⟨135988698764003877552446669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90659132509335918368297779 135988698764003877552446669)
            ·
              refine ⟨50995762036501454082167501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135988698764003877552446669 50995762036501454082167501)
              ·
                refine ⟨19123410763688045280812813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50995762036501454082167501 19123410763688045280812813)
                ·
                  refine ⟨7171279036383016980304805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19123410763688045280812813 7171279036383016980304805)
                  ·
                    refine ⟨1344614819321815683807151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7171279036383016980304805 1344614819321815683807151)
                    ·
                      rfl

theorem cell23_7855884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_7855884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855884 prefixEnd_7855884 := by exact prefixLift 7855884
  have htrace : WordTrace (prefixWord ++ tailWord_7855884) baseStart_7855884 baseEnd_7855884 := by
    simpa [prefixWord, tailWord_7855884, baseEnd_7855884] using wordTrace_append hprefix tailTrace_7855884
  have hstable : (prefixWord ++ tailWord_7855884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855884).length < 2 ^ (prefixWord ++ tailWord_7855884).sum := by decide
  have hdescent : baseEnd_7855884 < baseStart_7855884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855935 : List Nat := [1, 1, 2, 2, 6, 1, 3, 2, 1, 4]
def baseStart_7855935 : Nat := 118140960795 + 7855935 * 2 ^ 59
def prefixEnd_7855935 : Nat := 4983230072969 + 3 ^ 40 * 7855935 * 2
def baseEnd_7855935 : Nat := 1344623548492942117294573

theorem tailTrace_7855935 : CollatzResearch.WordTrace tailWord_7855935 prefixEnd_7855935 1344623548492942117294573 := by
  unfold tailWord_7855935
  simp only [CollatzResearch.WordTrace]
  refine ⟨286529488794296656725961259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191019659196197771150640839 286529488794296656725961259)
  ·
    refine ⟨429794233191444985088941889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286529488794296656725961259 429794233191444985088941889)
    ·
      refine ⟨322345674893583738816706417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429794233191444985088941889 322345674893583738816706417)
      ·
        refine ⟨241759256170187804112529813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322345674893583738816706417 241759256170187804112529813)
        ·
          refine ⟨11332465132977553317774835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 241759256170187804112529813 11332465132977553317774835)
          ·
            refine ⟨16998697699466329976662253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11332465132977553317774835 16998697699466329976662253)
            ·
              refine ⟨6374511637299873741248345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16998697699466329976662253 6374511637299873741248345)
              ·
                refine ⟨4780883727974905305936259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6374511637299873741248345 4780883727974905305936259)
                ·
                  refine ⟨7171325591962357958904389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4780883727974905305936259 7171325591962357958904389)
                  ·
                    refine ⟨1344623548492942117294573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7171325591962357958904389 1344623548492942117294573)
                    ·
                      rfl

theorem cell23_7855935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 1, 4].length) (baseStart_7855935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855935 prefixEnd_7855935 := by exact prefixLift 7855935
  have htrace : WordTrace (prefixWord ++ tailWord_7855935) baseStart_7855935 baseEnd_7855935 := by
    simpa [prefixWord, tailWord_7855935, baseEnd_7855935] using wordTrace_append hprefix tailTrace_7855935
  have hstable : (prefixWord ++ tailWord_7855935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855935).length < 2 ^ (prefixWord ++ tailWord_7855935).sum := by decide
  have hdescent : baseEnd_7855935 < baseStart_7855935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855948 : List Nat := [2, 2, 1, 3, 4, 2, 2, 1, 6]
def baseStart_7855948 : Nat := 118140960795 + 7855948 * 2 ^ 59
def prefixEnd_7855948 : Nat := 4983230072969 + 3 ^ 40 * 7855948 * 2
def baseEnd_7855948 : Nat := 448208591191926089002351

theorem tailTrace_7855948 : CollatzResearch.WordTrace tailWord_7855948 prefixEnd_7855948 448208591191926089002351 := by
  unfold tailWord_7855948
  simp only [CollatzResearch.WordTrace]
  refine ⟨143264981471624779973092249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191019975295499706630789665 143264981471624779973092249)
  ·
    refine ⟨107448736103718584979819187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143264981471624779973092249 107448736103718584979819187)
    ·
      refine ⟨161173104155577877469728781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107448736103718584979819187 161173104155577877469728781)
      ·
        refine ⟨60439914058341704051148293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161173104155577877469728781 60439914058341704051148293)
        ·
          refine ⟨11332483885939069509590305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60439914058341704051148293 11332483885939069509590305)
          ·
            refine ⟨8499362914454302132192729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11332483885939069509590305 8499362914454302132192729)
            ·
              refine ⟨6374522185840726599144547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8499362914454302132192729 6374522185840726599144547)
              ·
                refine ⟨9561783278761089898716821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6374522185840726599144547 9561783278761089898716821)
                ·
                  refine ⟨448208591191926089002351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9561783278761089898716821 448208591191926089002351)
                  ·
                    rfl

theorem cell23_7855948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 6].length) (baseStart_7855948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855948 prefixEnd_7855948 := by exact prefixLift 7855948
  have htrace : WordTrace (prefixWord ++ tailWord_7855948) baseStart_7855948 baseEnd_7855948 := by
    simpa [prefixWord, tailWord_7855948, baseEnd_7855948] using wordTrace_append hprefix tailTrace_7855948
  have hstable : (prefixWord ++ tailWord_7855948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855948).length < 2 ^ (prefixWord ++ tailWord_7855948).sum := by decide
  have hdescent : baseEnd_7855948 < baseStart_7855948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855968 : List Nat := [2, 1, 1, 3, 3, 3, 2, 1, 2, 3, 2]
def baseStart_7855968 : Nat := 118140960795 + 7855968 * 2 ^ 59
def prefixEnd_7855968 : Nat := 4983230072969 + 3 ^ 40 * 7855968 * 2
def baseEnd_7855968 : Nat := 4033887590340424722771067

theorem tailTrace_7855968 : CollatzResearch.WordTrace tailWord_7855968 prefixEnd_7855968 4033887590340424722771067 := by
  unfold tailWord_7855968
  simp only [CollatzResearch.WordTrace]
  refine ⟨143265346201588551680956279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191020461602118068907941705 143265346201588551680956279)
  ·
    refine ⟨214898019302382827521434419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143265346201588551680956279 214898019302382827521434419)
    ·
      refine ⟨322347028953574241282151629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214898019302382827521434419 322347028953574241282151629)
      ·
        refine ⟨120880135857590340480806861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322347028953574241282151629 120880135857590340480806861)
        ·
          refine ⟨45330050946596377680302573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120880135857590340480806861 45330050946596377680302573)
          ·
            refine ⟨16998769104973641630113465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45330050946596377680302573 16998769104973641630113465)
            ·
              refine ⟨12749076828730231222585099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16998769104973641630113465 12749076828730231222585099)
              ·
                refine ⟨19123615243095346833877649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12749076828730231222585099 19123615243095346833877649)
                ·
                  refine ⟨14342711432321510125408237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19123615243095346833877649 14342711432321510125408237)
                  ·
                    refine ⟨5378516787120566297028089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14342711432321510125408237 5378516787120566297028089)
                    ·
                      refine ⟨4033887590340424722771067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5378516787120566297028089 4033887590340424722771067)
                      ·
                        rfl

theorem cell23_7855968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_7855968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855968 prefixEnd_7855968 := by exact prefixLift 7855968
  have htrace : WordTrace (prefixWord ++ tailWord_7855968) baseStart_7855968 baseEnd_7855968 := by
    simpa [prefixWord, tailWord_7855968, baseEnd_7855968] using wordTrace_append hprefix tailTrace_7855968
  have hstable : (prefixWord ++ tailWord_7855968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855968).length < 2 ^ (prefixWord ++ tailWord_7855968).sum := by decide
  have hdescent : baseEnd_7855968 < baseStart_7855968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855981 : List Nat := [1, 5, 1, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_7855981 : Nat := 118140960795 + 7855981 * 2 ^ 59
def prefixEnd_7855981 : Nat := 4983230072969 + 3 ^ 40 * 7855981 * 2
def baseEnd_7855981 : Nat := 4033894265588933171908507

theorem tailTrace_7855981 : CollatzResearch.WordTrace tailWord_7855981 prefixEnd_7855981 4033894265588933171908507 := by
  unfold tailWord_7855981
  simp only [CollatzResearch.WordTrace]
  refine ⟨286531166552130006582135797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191020777701420004388090531 286531166552130006582135797)
  ·
    refine ⟨26862296864262188117075231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286531166552130006582135797 26862296864262188117075231)
    ·
      refine ⟨40293445296393282175612847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26862296864262188117075231 40293445296393282175612847)
      ·
        refine ⟨60440167944589923263419271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40293445296393282175612847 60440167944589923263419271)
        ·
          refine ⟨90660251916884884895128907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60440167944589923263419271 90660251916884884895128907)
          ·
            refine ⟨135990377875327327342693361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90660251916884884895128907 135990377875327327342693361)
            ·
              refine ⟨101992783406495495507020021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135990377875327327342693361 101992783406495495507020021)
              ·
                refine ⟨9561823444358952703783127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101992783406495495507020021 9561823444358952703783127)
                ·
                  refine ⟨14342735166538429055674691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9561823444358952703783127 14342735166538429055674691)
                  ·
                    refine ⟨21514102749807643583512037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14342735166538429055674691 21514102749807643583512037)
                    ·
                      refine ⟨4033894265588933171908507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21514102749807643583512037 4033894265588933171908507)
                      ·
                        rfl

theorem cell23_7855981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_7855981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855981 prefixEnd_7855981 := by exact prefixLift 7855981
  have htrace : WordTrace (prefixWord ++ tailWord_7855981) baseStart_7855981 baseEnd_7855981 := by
    simpa [prefixWord, tailWord_7855981, baseEnd_7855981] using wordTrace_append hprefix tailTrace_7855981
  have hstable : (prefixWord ++ tailWord_7855981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855981).length < 2 ^ (prefixWord ++ tailWord_7855981).sum := by decide
  have hdescent : baseEnd_7855981 < baseStart_7855981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7855998 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_7855998 : Nat := 118140960795 + 7855998 * 2 ^ 59
def prefixEnd_7855998 : Nat := 4983230072969 + 3 ^ 40 * 7855998 * 2
def baseEnd_7855998 : Nat := 4033902994760059605395929

theorem tailTrace_7855998 : CollatzResearch.WordTrace tailWord_7855998 prefixEnd_7855998 4033902994760059605395929 := by
  unfold tailWord_7855998
  simp only [CollatzResearch.WordTrace]
  refine ⟨35816473324133552310688081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191021191062045612323669765 35816473324133552310688081)
  ·
    refine ⟨26862354993100164233016061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35816473324133552310688081 26862354993100164233016061)
    ·
      refine ⟨10073383122412561587381023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26862354993100164233016061 10073383122412561587381023)
      ·
        refine ⟨15110074683618842381071535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10073383122412561587381023 15110074683618842381071535)
        ·
          refine ⟨22665112025428263571607303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15110074683618842381071535 22665112025428263571607303)
          ·
            refine ⟨33997668038142395357410955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22665112025428263571607303 33997668038142395357410955)
            ·
              refine ⟨50996502057213593036116433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33997668038142395357410955 50996502057213593036116433)
              ·
                refine ⟨38247376542910194777087325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50996502057213593036116433 38247376542910194777087325)
                ·
                  refine ⟨14342766203591323041407747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38247376542910194777087325 14342766203591323041407747)
                  ·
                    refine ⟨21514149305386984562111621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14342766203591323041407747 21514149305386984562111621)
                    ·
                      refine ⟨4033902994760059605395929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21514149305386984562111621 4033902994760059605395929)
                      ·
                        rfl

theorem cell23_7855998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_7855998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7855998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7855998 prefixEnd_7855998 := by exact prefixLift 7855998
  have htrace : WordTrace (prefixWord ++ tailWord_7855998) baseStart_7855998 baseEnd_7855998 := by
    simpa [prefixWord, tailWord_7855998, baseEnd_7855998] using wordTrace_append hprefix tailTrace_7855998
  have hstable : (prefixWord ++ tailWord_7855998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7855998).length < 2 ^ (prefixWord ++ tailWord_7855998).sum := by decide
  have hdescent : baseEnd_7855998 < baseStart_7855998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7855998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856004 : List Nat := [2, 3, 2, 1, 1, 1, 5, 8]
def baseStart_7856004 : Nat := 118140960795 + 7856004 * 2 ^ 59
def prefixEnd_7856004 : Nat := 4983230072969 + 3 ^ 40 * 7856004 * 2
def baseEnd_7856004 : Nat := 149403928727555058589663

theorem tailTrace_7856004 : CollatzResearch.WordTrace tailWord_7856004 prefixEnd_7856004 149403928727555058589663 := by
  unfold tailWord_7856004
  simp only [CollatzResearch.WordTrace]
  refine ⟨143266002715523340755111533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191021336954031121006815377 143266002715523340755111533)
  ·
    refine ⟨53724751018321252783166825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143266002715523340755111533 53724751018321252783166825)
    ·
      refine ⟨40293563263740939587375119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53724751018321252783166825 40293563263740939587375119)
      ·
        refine ⟨60440344895611409381062679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40293563263740939587375119 60440344895611409381062679)
        ·
          refine ⟨90660517343417114071594019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60440344895611409381062679 90660517343417114071594019)
          ·
            refine ⟨135990776015125671107391029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90660517343417114071594019 135990776015125671107391029)
            ·
              refine ⟨12749135251418031666317909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135990776015125671107391029 12749135251418031666317909)
              ·
                refine ⟨149403928727555058589663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12749135251418031666317909 149403928727555058589663)
                ·
                  rfl

theorem cell23_7856004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 8].length) (baseStart_7856004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856004 prefixEnd_7856004 := by exact prefixLift 7856004
  have htrace : WordTrace (prefixWord ++ tailWord_7856004) baseStart_7856004 baseEnd_7856004 := by
    simpa [prefixWord, tailWord_7856004, baseEnd_7856004] using wordTrace_append hprefix tailTrace_7856004
  have hstable : (prefixWord ++ tailWord_7856004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856004).length < 2 ^ (prefixWord ++ tailWord_7856004).sum := by decide
  have hdescent : baseEnd_7856004 < baseStart_7856004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856018 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_7856018 : Nat := 118140960795 + 7856018 * 2 ^ 59
def prefixEnd_7856018 : Nat := 4983230072969 + 3 ^ 40 * 7856018 * 2
def baseEnd_7856018 : Nat := 4033913264373149527145837

theorem tailTrace_7856018 : CollatzResearch.WordTrace tailWord_7856018 prefixEnd_7856018 4033913264373149527145837 := by
  unfold tailWord_7856018
  simp only [CollatzResearch.WordTrace]
  refine ⟨71633129013248990475308177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191021677368663974600821805 71633129013248990475308177)
  ·
    refine ⟨53724846759936742856481133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71633129013248990475308177 53724846759936742856481133)
    ·
      refine ⟨20146817534976278571180425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53724846759936742856481133 20146817534976278571180425)
      ·
        refine ⟨15110113151232208928385319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20146817534976278571180425 15110113151232208928385319)
        ·
          refine ⟨22665169726848313392577979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15110113151232208928385319 22665169726848313392577979)
          ·
            refine ⟨33997754590272470088866969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22665169726848313392577979 33997754590272470088866969)
            ·
              refine ⟨25498315942704352566650227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33997754590272470088866969 25498315942704352566650227)
              ·
                refine ⟨38247473914056528849975341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25498315942704352566650227 38247473914056528849975341)
                ·
                  refine ⟨14342802717771198318740753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38247473914056528849975341 14342802717771198318740753)
                  ·
                    refine ⟨10757102038328398739055565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14342802717771198318740753 10757102038328398739055565)
                    ·
                      refine ⟨4033913264373149527145837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10757102038328398739055565 4033913264373149527145837)
                      ·
                        rfl

theorem cell23_7856018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_7856018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856018 prefixEnd_7856018 := by exact prefixLift 7856018
  have htrace : WordTrace (prefixWord ++ tailWord_7856018) baseStart_7856018 baseEnd_7856018 := by
    simpa [prefixWord, tailWord_7856018, baseEnd_7856018] using wordTrace_append hprefix tailTrace_7856018
  have hstable : (prefixWord ++ tailWord_7856018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856018).length < 2 ^ (prefixWord ++ tailWord_7856018).sum := by decide
  have hdescent : baseEnd_7856018 < baseStart_7856018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856041 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 5, 3, 2]
def baseStart_7856041 : Nat := 118140960795 + 7856041 * 2 ^ 59
def prefixEnd_7856041 : Nat := 4983230072969 + 3 ^ 40 * 7856041 * 2
def baseEnd_7856041 : Nat := 4033925074428202937158231

theorem tailTrace_7856041 : CollatzResearch.WordTrace tailWord_7856041 prefixEnd_7856041 4033925074428202937158231 := by
  unfold tailWord_7856041
  simp only [CollatzResearch.WordTrace]
  refine ⟨286533354931912636829319977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191022236621275091219546651 286533354931912636829319977)
  ·
    refine ⟨214900016198934477621989983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286533354931912636829319977 214900016198934477621989983)
    ·
      refine ⟨322350024298401716432984975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214900016198934477621989983 322350024298401716432984975)
      ·
        refine ⟨483525036447602574649477463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322350024298401716432984975 483525036447602574649477463)
        ·
          refine ⟨725287554671403861974216195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483525036447602574649477463 725287554671403861974216195)
          ·
            refine ⟨1087931332007105792961324293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725287554671403861974216195 1087931332007105792961324293)
            ·
              refine ⟨203987124751332336180248305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1087931332007105792961324293 203987124751332336180248305)
              ·
                refine ⟨152990343563499252135186229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203987124751332336180248305 152990343563499252135186229)
                ·
                  refine ⟨14342844709078054887673709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152990343563499252135186229 14342844709078054887673709)
                  ·
                    refine ⟨5378566765904270582877641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14342844709078054887673709 5378566765904270582877641)
                    ·
                      refine ⟨4033925074428202937158231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5378566765904270582877641 4033925074428202937158231)
                      ·
                        rfl

theorem cell23_7856041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 3, 2].length) (baseStart_7856041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856041 prefixEnd_7856041 := by exact prefixLift 7856041
  have htrace : WordTrace (prefixWord ++ tailWord_7856041) baseStart_7856041 baseEnd_7856041 := by
    simpa [prefixWord, tailWord_7856041, baseEnd_7856041] using wordTrace_append hprefix tailTrace_7856041
  have hstable : (prefixWord ++ tailWord_7856041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856041).length < 2 ^ (prefixWord ++ tailWord_7856041).sum := by decide
  have hdescent : baseEnd_7856041 < baseStart_7856041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856064 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 2, 6]
def baseStart_7856064 : Nat := 118140960795 + 7856064 * 2 ^ 59
def prefixEnd_7856064 : Nat := 4983230072969 + 3 ^ 40 * 7856064 * 2
def baseEnd_7856064 : Nat := 1344645628161085449056875

theorem tailTrace_7856064 : CollatzResearch.WordTrace tailWord_7856064 prefixEnd_7856064 1344645628161085449056875 := by
  unfold tailWord_7856064
  simp only [CollatzResearch.WordTrace]
  refine ⟨143267096905414655878703623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191022795873886207838271497 143267096905414655878703623)
  ·
    refine ⟨214900645358121983818055435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143267096905414655878703623 214900645358121983818055435)
    ·
      refine ⟨322350968037182975727083153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214900645358121983818055435 322350968037182975727083153)
      ·
        refine ⟨241763226027887231795312365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322350968037182975727083153 241763226027887231795312365)
        ·
          refine ⟨90661209760457711923242137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241763226027887231795312365 90661209760457711923242137)
          ·
            refine ⟨67995907320343283942431603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90661209760457711923242137 67995907320343283942431603)
            ·
              refine ⟨101993860980514925913647405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67995907320343283942431603 101993860980514925913647405)
              ·
                refine ⟨38247697867693097217617777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101993860980514925913647405 38247697867693097217617777)
                ·
                  refine ⟨28685773400769822913213333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38247697867693097217617777 28685773400769822913213333)
                  ·
                    refine ⟨1344645628161085449056875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28685773400769822913213333 1344645628161085449056875)
                    ·
                      rfl

theorem cell23_7856064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 2, 6].length) (baseStart_7856064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856064 prefixEnd_7856064 := by exact prefixLift 7856064
  have htrace : WordTrace (prefixWord ++ tailWord_7856064) baseStart_7856064 baseEnd_7856064 := by
    simpa [prefixWord, tailWord_7856064, baseEnd_7856064] using wordTrace_append hprefix tailTrace_7856064
  have hstable : (prefixWord ++ tailWord_7856064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856064).length < 2 ^ (prefixWord ++ tailWord_7856064).sum := by decide
  have hdescent : baseEnd_7856064 < baseStart_7856064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856088 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 6, 2, 2]
def baseStart_7856088 : Nat := 118140960795 + 7856088 * 2 ^ 59
def prefixEnd_7856088 : Nat := 4983230072969 + 3 ^ 40 * 7856088 * 2
def baseEnd_7856088 : Nat := 4033949208018964253270515

theorem tailTrace_7856088 : CollatzResearch.WordTrace tailWord_7856088 prefixEnd_7856088 4033949208018964253270515 := by
  unfold tailWord_7856088
  simp only [CollatzResearch.WordTrace]
  refine ⟨143267534581371181928140459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191023379441828242570853945 143267534581371181928140459)
  ·
    refine ⟨214901301872056772892210689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143267534581371181928140459 214901301872056772892210689)
    ·
      refine ⟨161175976404042579669158017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214901301872056772892210689 161175976404042579669158017)
      ·
        refine ⟨120881982303031934751868513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161175976404042579669158017 120881982303031934751868513)
        ·
          refine ⟨90661486727273951063901385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120881982303031934751868513 90661486727273951063901385)
          ·
            refine ⟨67996115045455463297926039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90661486727273951063901385 67996115045455463297926039)
            ·
              refine ⟨101994172568183194946889059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67996115045455463297926039 101994172568183194946889059)
              ·
                refine ⟨152991258852274792420333589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101994172568183194946889059 152991258852274792420333589)
                ·
                  refine ⟨7171465258700380894703137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152991258852274792420333589 7171465258700380894703137)
                  ·
                    refine ⟨5378598944025285671027353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7171465258700380894703137 5378598944025285671027353)
                    ·
                      refine ⟨4033949208018964253270515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5378598944025285671027353 4033949208018964253270515)
                      ·
                        rfl

theorem cell23_7856088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_7856088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856088 prefixEnd_7856088 := by exact prefixLift 7856088
  have htrace : WordTrace (prefixWord ++ tailWord_7856088) baseStart_7856088 baseEnd_7856088 := by
    simpa [prefixWord, tailWord_7856088, baseEnd_7856088] using wordTrace_append hprefix tailTrace_7856088
  have hstable : (prefixWord ++ tailWord_7856088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856088).length < 2 ^ (prefixWord ++ tailWord_7856088).sum := by decide
  have hdescent : baseEnd_7856088 < baseStart_7856088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856104 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_7856104 : Nat := 118140960795 + 7856104 * 2 ^ 59
def prefixEnd_7856104 : Nat := 4983230072969 + 3 ^ 40 * 7856104 * 2
def baseEnd_7856104 : Nat := 4033957423709436190670441

theorem tailTrace_7856104 : CollatzResearch.WordTrace tailWord_7856104 prefixEnd_7856104 4033957423709436190670441 := by
  unfold tailWord_7856104
  simp only [CollatzResearch.WordTrace]
  refine ⟨143267826365342199294431683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191023768487122932392575577 143267826365342199294431683)
  ·
    refine ⟨214901739548013298941647525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143267826365342199294431683 214901739548013298941647525)
    ·
      refine ⟨40294076165252493551558911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214901739548013298941647525 40294076165252493551558911)
      ·
        refine ⟨60441114247878740327338367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40294076165252493551558911 60441114247878740327338367)
        ·
          refine ⟨90661671371818110491007551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60441114247878740327338367 90661671371818110491007551)
          ·
            refine ⟨135992507057727165736511327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90661671371818110491007551 135992507057727165736511327)
            ·
              refine ⟨203988760586590748604766991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135992507057727165736511327 203988760586590748604766991)
              ·
                refine ⟨305983140879886122907150487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203988760586590748604766991 305983140879886122907150487)
                ·
                  refine ⟨458974711319829184360725731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305983140879886122907150487 458974711319829184360725731)
                  ·
                    refine ⟨688462066979743776541088597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 458974711319829184360725731 688462066979743776541088597)
                    ·
                      refine ⟨4033957423709436190670441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 688462066979743776541088597 4033957423709436190670441)
                      ·
                        rfl

theorem cell23_7856104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_7856104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856104 prefixEnd_7856104 := by exact prefixLift 7856104
  have htrace : WordTrace (prefixWord ++ tailWord_7856104) baseStart_7856104 baseEnd_7856104 := by
    simpa [prefixWord, tailWord_7856104, baseEnd_7856104] using wordTrace_append hprefix tailTrace_7856104
  have hstable : (prefixWord ++ tailWord_7856104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856104).length < 2 ^ (prefixWord ++ tailWord_7856104).sum := by decide
  have hdescent : baseEnd_7856104 < baseStart_7856104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856178 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2]
def baseStart_7856178 : Nat := 118140960795 + 7856178 * 2 ^ 59
def prefixEnd_7856178 : Nat := 4983230072969 + 3 ^ 40 * 7856178 * 2
def baseEnd_7856178 : Nat := 4033995421277868901145101

theorem tailTrace_7856178 : CollatzResearch.WordTrace tailWord_7856178 prefixEnd_7856178 4033995421277868901145101 := by
  unfold tailWord_7856178
  simp only [CollatzResearch.WordTrace]
  refine ⟨71634587933104077306764297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191025567821610872818038125 71634587933104077306764297)
  ·
    refine ⟨53725940949828057980073223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71634587933104077306764297 53725940949828057980073223)
    ·
      refine ⟨80588911424742086970109835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53725940949828057980073223 80588911424742086970109835)
      ·
        refine ⟨120883367137113130455164753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80588911424742086970109835 120883367137113130455164753)
        ·
          refine ⟨90662525352834847841373565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120883367137113130455164753 90662525352834847841373565)
          ·
            refine ⟨33998447007313067940515087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90662525352834847841373565 33998447007313067940515087)
            ·
              refine ⟨50997670510969601910772631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33998447007313067940515087 50997670510969601910772631)
              ·
                refine ⟨76496505766454402866158947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50997670510969601910772631 76496505766454402866158947)
                ·
                  refine ⟨114744758649681604299238421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76496505766454402866158947 114744758649681604299238421)
                  ·
                    refine ⟨5378660561703825201526801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114744758649681604299238421 5378660561703825201526801)
                    ·
                      refine ⟨4033995421277868901145101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5378660561703825201526801 4033995421277868901145101)
                      ·
                        rfl

theorem cell23_7856178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_7856178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856178 prefixEnd_7856178 := by exact prefixLift 7856178
  have htrace : WordTrace (prefixWord ++ tailWord_7856178) baseStart_7856178 baseEnd_7856178 := by
    simpa [prefixWord, tailWord_7856178, baseEnd_7856178] using wordTrace_append hprefix tailTrace_7856178
  have hstable : (prefixWord ++ tailWord_7856178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856178).length < 2 ^ (prefixWord ++ tailWord_7856178).sum := by decide
  have hdescent : baseEnd_7856178 < baseStart_7856178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856188 : List Nat := [2, 2, 2, 2, 2, 1, 3, 2, 3, 4]
def baseStart_7856188 : Nat := 118140960795 + 7856188 * 2 ^ 59
def prefixEnd_7856188 : Nat := 4983230072969 + 3 ^ 40 * 7856188 * 2
def baseEnd_7856188 : Nat := 1344666852028137954006685

theorem tailTrace_7856188 : CollatzResearch.WordTrace tailWord_7856188 prefixEnd_7856188 1344666852028137954006685 := by
  unfold tailWord_7856188
  simp only [CollatzResearch.WordTrace]
  refine ⟨143269358231190040467460609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191025810974920053956614145 143269358231190040467460609)
  ·
    refine ⟨107452018673392530350595457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143269358231190040467460609 107452018673392530350595457)
    ·
      refine ⟨80589014005044397762946593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107452018673392530350595457 80589014005044397762946593)
      ·
        refine ⟨60441760503783298322209945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80589014005044397762946593 60441760503783298322209945)
        ·
          refine ⟨45331320377837473741657459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60441760503783298322209945 45331320377837473741657459)
          ·
            refine ⟨67996980566756210612486189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45331320377837473741657459 67996980566756210612486189)
            ·
              refine ⟨25498867712533578979682321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67996980566756210612486189 25498867712533578979682321)
              ·
                refine ⟨19124150784400184234761741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25498867712533578979682321 19124150784400184234761741)
                ·
                  refine ⟨7171556544150069088035653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19124150784400184234761741 7171556544150069088035653)
                  ·
                    refine ⟨1344666852028137954006685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7171556544150069088035653 1344666852028137954006685)
                    ·
                      rfl

theorem cell23_7856188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_7856188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856188 prefixEnd_7856188 := by exact prefixLift 7856188
  have htrace : WordTrace (prefixWord ++ tailWord_7856188) baseStart_7856188 baseEnd_7856188 := by
    simpa [prefixWord, tailWord_7856188, baseEnd_7856188] using wordTrace_append hprefix tailTrace_7856188
  have hstable : (prefixWord ++ tailWord_7856188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856188).length < 2 ^ (prefixWord ++ tailWord_7856188).sum := by decide
  have hdescent : baseEnd_7856188 < baseStart_7856188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856279 : List Nat := [1, 1, 3, 3, 5, 1, 1, 1, 3, 1, 3]
def baseStart_7856279 : Nat := 118140960795 + 7856279 * 2 ^ 59
def prefixEnd_7856279 : Nat := 4983230072969 + 3 ^ 40 * 7856279 * 2
def baseEnd_7856279 : Nat := 4034047282823973005982137

theorem tailTrace_7856279 : CollatzResearch.WordTrace tailWord_7856279 prefixEnd_7856279 4034047282823973005982137 := by
  unfold tailWord_7856279
  simp only [CollatzResearch.WordTrace]
  refine ⟨286542035505050403476483891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191028023670033602317655927 286542035505050403476483891)
  ·
    refine ⟨429813053257575605214725837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286542035505050403476483891 429813053257575605214725837)
    ·
      refine ⟨161179894971590851955522189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429813053257575605214725837 161179894971590851955522189)
      ·
        refine ⟨60442460614346569483320821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161179894971590851955522189 60442460614346569483320821)
        ·
          refine ⟨5666480682594990889061327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60442460614346569483320821 5666480682594990889061327)
          ·
            refine ⟨8499721023892486333591991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5666480682594990889061327 8499721023892486333591991)
            ·
              refine ⟨12749581535838729500387987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8499721023892486333591991 12749581535838729500387987)
              ·
                refine ⟨19124372303758094250581981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12749581535838729500387987 19124372303758094250581981)
                ·
                  refine ⟨7171639613909285343968243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19124372303758094250581981 7171639613909285343968243)
                  ·
                    refine ⟨10757459420863928015952365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7171639613909285343968243 10757459420863928015952365)
                    ·
                      refine ⟨4034047282823973005982137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10757459420863928015952365 4034047282823973005982137)
                      ·
                        rfl

theorem cell23_7856279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_7856279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856279 prefixEnd_7856279 := by exact prefixLift 7856279
  have htrace : WordTrace (prefixWord ++ tailWord_7856279) baseStart_7856279 baseEnd_7856279 := by
    simpa [prefixWord, tailWord_7856279, baseEnd_7856279] using wordTrace_append hprefix tailTrace_7856279
  have hstable : (prefixWord ++ tailWord_7856279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856279).length < 2 ^ (prefixWord ++ tailWord_7856279).sum := by decide
  have hdescent : baseEnd_7856279 < baseStart_7856279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856288 : List Nat := [2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 5]
def baseStart_7856288 : Nat := 118140960795 + 7856288 * 2 ^ 59
def prefixEnd_7856288 : Nat := 4983230072969 + 3 ^ 40 * 7856288 * 2
def baseEnd_7856288 : Nat := 4034051904149863470769595

theorem tailTrace_7856288 : CollatzResearch.WordTrace tailWord_7856288 prefixEnd_7856288 4034051904149863470769595 := by
  unfold tailWord_7856288
  simp only [CollatzResearch.WordTrace]
  refine ⟨143271181881008899006780759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191028242508011865342374345 143271181881008899006780759)
  ·
    refine ⟨214906772821513348510171139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143271181881008899006780759 214906772821513348510171139)
    ·
      refine ⟨322360159232270022765256709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214906772821513348510171139 322360159232270022765256709)
      ·
        refine ⟨60442529856050629268485633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322360159232270022765256709 60442529856050629268485633)
        ·
          refine ⟨45331897392037971951364225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60442529856050629268485633 45331897392037971951364225)
          ·
            refine ⟨33998923044028478963523169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45331897392037971951364225 33998923044028478963523169)
            ·
              refine ⟨25499192283021359222642377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33998923044028478963523169 25499192283021359222642377)
              ·
                refine ⟨19124394212266019416981783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25499192283021359222642377 19124394212266019416981783)
                ·
                  refine ⟨28686591318399029125472675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19124394212266019416981783 28686591318399029125472675)
                  ·
                    refine ⟨43029886977598543688209013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28686591318399029125472675 43029886977598543688209013)
                    ·
                      refine ⟨4034051904149863470769595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43029886977598543688209013 4034051904149863470769595)
                      ·
                        rfl

theorem cell23_7856288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_7856288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856288 prefixEnd_7856288 := by exact prefixLift 7856288
  have htrace : WordTrace (prefixWord ++ tailWord_7856288) baseStart_7856288 baseEnd_7856288 := by
    simpa [prefixWord, tailWord_7856288, baseEnd_7856288] using wordTrace_append hprefix tailTrace_7856288
  have hstable : (prefixWord ++ tailWord_7856288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856288).length < 2 ^ (prefixWord ++ tailWord_7856288).sum := by decide
  have hdescent : baseEnd_7856288 < baseStart_7856288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856338 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 2, 7]
def baseStart_7856338 : Nat := 118140960795 + 7856338 * 2 ^ 59
def prefixEnd_7856338 : Nat := 4983230072969 + 3 ^ 40 * 7856338 * 2
def baseEnd_7856338 : Nat := 1344692526060862758381455

theorem tailTrace_7856338 : CollatzResearch.WordTrace tailWord_7856338 prefixEnd_7856338 1344692526060862758381455 := by
  unfold tailWord_7856338
  simp only [CollatzResearch.WordTrace]
  refine ⟨71636046852959164138220417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191029458274557771035254445 71636046852959164138220417)
  ·
    refine ⟨53727035139719373103665313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71636046852959164138220417 53727035139719373103665313)
    ·
      refine ⟨40295276354789529827748985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53727035139719373103665313 40295276354789529827748985)
      ·
        refine ⟨30221457266092147370811739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40295276354789529827748985 30221457266092147370811739)
        ·
          refine ⟨45332185899138221056217609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30221457266092147370811739 45332185899138221056217609)
          ·
            refine ⟨33999139424353665792163207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45332185899138221056217609 33999139424353665792163207)
            ·
              refine ⟨50998709136530498688244811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33999139424353665792163207 50998709136530498688244811)
              ·
                refine ⟨76498063704795748032367217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50998709136530498688244811 76498063704795748032367217)
                ·
                  refine ⟨57373547778596811024275413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76498063704795748032367217 57373547778596811024275413)
                  ·
                    refine ⟨1344692526060862758381455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57373547778596811024275413 1344692526060862758381455)
                    ·
                      rfl

theorem cell23_7856338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_7856338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856338 prefixEnd_7856338 := by exact prefixLift 7856338
  have htrace : WordTrace (prefixWord ++ tailWord_7856338) baseStart_7856338 baseEnd_7856338 := by
    simpa [prefixWord, tailWord_7856338, baseEnd_7856338] using wordTrace_append hprefix tailTrace_7856338
  have hstable : (prefixWord ++ tailWord_7856338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856338).length < 2 ^ (prefixWord ++ tailWord_7856338).sum := by decide
  have hdescent : baseEnd_7856338 < baseStart_7856338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856342 : List Nat := [5, 2, 1, 2, 1, 3, 1, 8]
def baseStart_7856342 : Nat := 118140960795 + 7856342 * 2 ^ 59
def prefixEnd_7856342 : Nat := 4983230072969 + 3 ^ 40 * 7856342 * 2
def baseEnd_7856342 : Nat := 149410356744637268870161

theorem tailTrace_7856342 : CollatzResearch.WordTrace tailWord_7856342 prefixEnd_7856342 149410356744637268870161 := by
  unfold tailWord_7856342
  simp only [CollatzResearch.WordTrace]
  refine ⟨17909020831488885327251705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191029555535881443490684853 17909020831488885327251705)
  ·
    refine ⟨13431765623616663995438779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17909020831488885327251705 13431765623616663995438779)
    ·
      refine ⟨20147648435424995993158169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13431765623616663995438779 20147648435424995993158169)
      ·
        refine ⟨15110736326568746994868627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20147648435424995993158169 15110736326568746994868627)
        ·
          refine ⟨22666104489853120492302941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15110736326568746994868627 22666104489853120492302941)
          ·
            refine ⟨8499789183694920184613603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22666104489853120492302941 8499789183694920184613603)
            ·
              refine ⟨12749683775542380276920405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8499789183694920184613603 12749683775542380276920405)
              ·
                refine ⟨149410356744637268870161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12749683775542380276920405 149410356744637268870161)
                ·
                  rfl

theorem cell23_7856342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_7856342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856342 prefixEnd_7856342 := by exact prefixLift 7856342
  have htrace : WordTrace (prefixWord ++ tailWord_7856342) baseStart_7856342 baseEnd_7856342 := by
    simpa [prefixWord, tailWord_7856342, baseEnd_7856342] using wordTrace_append hprefix tailTrace_7856342
  have hstable : (prefixWord ++ tailWord_7856342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856342).length < 2 ^ (prefixWord ++ tailWord_7856342).sum := by decide
  have hdescent : baseEnd_7856342 < baseStart_7856342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856345 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 3, 3, 2]
def baseStart_7856345 : Nat := 118140960795 + 7856345 * 2 ^ 59
def prefixEnd_7856345 : Nat := 4983230072969 + 3 ^ 40 * 7856345 * 2
def baseEnd_7856345 : Nat := 4034081172547169747756833

theorem tailTrace_7856345 : CollatzResearch.WordTrace tailWord_7856345 prefixEnd_7856345 4034081172547169747756833 := by
  unfold tailWord_7856345
  simp only [CollatzResearch.WordTrace]
  refine ⟨286544442722811296748386489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191029628481874197832257659 286544442722811296748386489)
  ·
    refine ⟨214908332042108472561289867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286544442722811296748386489 214908332042108472561289867)
    ·
      refine ⟨322362498063162708841934801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214908332042108472561289867 322362498063162708841934801)
      ·
        refine ⟨241771873547372031631451101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322362498063162708841934801 241771873547372031631451101)
        ·
          refine ⟨90664452580264511861794163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241771873547372031631451101 90664452580264511861794163)
          ·
            refine ⟨135996678870396767792691245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90664452580264511861794163 135996678870396767792691245)
            ·
              refine ⟨50998754576398787922259217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135996678870396767792691245 50998754576398787922259217)
              ·
                refine ⟨38249065932299090941694413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50998754576398787922259217 38249065932299090941694413)
                ·
                  refine ⟨14343399724612159103135405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38249065932299090941694413 14343399724612159103135405)
                  ·
                    refine ⟨5378774896729559663675777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14343399724612159103135405 5378774896729559663675777)
                    ·
                      refine ⟨4034081172547169747756833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5378774896729559663675777 4034081172547169747756833)
                      ·
                        rfl

theorem cell23_7856345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 3, 2].length) (baseStart_7856345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856345 prefixEnd_7856345 := by exact prefixLift 7856345
  have htrace : WordTrace (prefixWord ++ tailWord_7856345) baseStart_7856345 baseEnd_7856345 := by
    simpa [prefixWord, tailWord_7856345, baseEnd_7856345] using wordTrace_append hprefix tailTrace_7856345
  have hstable : (prefixWord ++ tailWord_7856345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856345).length < 2 ^ (prefixWord ++ tailWord_7856345).sum := by decide
  have hdescent : baseEnd_7856345 < baseStart_7856345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856362 : List Nat := [3, 1, 3, 1, 1, 2, 2, 4, 1, 3, 2]
def baseStart_7856362 : Nat := 118140960795 + 7856362 * 2 ^ 59
def prefixEnd_7856362 : Nat := 4983230072969 + 3 ^ 40 * 7856362 * 2
def baseEnd_7856362 : Nat := 4034089901718296181244255

theorem tailTrace_7856362 : CollatzResearch.WordTrace tailWord_7856362 prefixEnd_7856362 4034089901718296181244255 := by
  unfold tailWord_7856362
  simp only [CollatzResearch.WordTrace]
  refine ⟨71636265690937427162938835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191030041842499805767836893 71636265690937427162938835)
  ·
    refine ⟨107454398536406140744408253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71636265690937427162938835 107454398536406140744408253)
    ·
      refine ⟨40295399451152302779153095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107454398536406140744408253 40295399451152302779153095)
      ·
        refine ⟨60443099176728454168729643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40295399451152302779153095 60443099176728454168729643)
        ·
          refine ⟨90664648765092681253094465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60443099176728454168729643 90664648765092681253094465)
          ·
            refine ⟨67998486573819510939820849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90664648765092681253094465 67998486573819510939820849)
            ·
              refine ⟨50998864930364633204865637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67998486573819510939820849 50998864930364633204865637)
              ·
                refine ⟨9562287174443368725912307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50998864930364633204865637 9562287174443368725912307)
                ·
                  refine ⟨14343430761665053088868461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9562287174443368725912307 14343430761665053088868461)
                  ·
                    refine ⟨5378786535624394908325673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14343430761665053088868461 5378786535624394908325673)
                    ·
                      refine ⟨4034089901718296181244255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5378786535624394908325673 4034089901718296181244255)
                      ·
                        rfl

theorem cell23_7856362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_7856362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856362 prefixEnd_7856362 := by exact prefixLift 7856362
  have htrace : WordTrace (prefixWord ++ tailWord_7856362) baseStart_7856362 baseEnd_7856362 := by
    simpa [prefixWord, tailWord_7856362, baseEnd_7856362] using wordTrace_append hprefix tailTrace_7856362
  have hstable : (prefixWord ++ tailWord_7856362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856362).length < 2 ^ (prefixWord ++ tailWord_7856362).sum := by decide
  have hdescent : baseEnd_7856362 < baseStart_7856362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856386 : List Nat := [3, 4, 1, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_7856386 : Nat := 118140960795 + 7856386 * 2 ^ 59
def prefixEnd_7856386 : Nat := 4983230072969 + 3 ^ 40 * 7856386 * 2
def baseEnd_7856386 : Nat := 4034102225254004087344145

theorem tailTrace_7856386 : CollatzResearch.WordTrace tailWord_7856386 prefixEnd_7856386 4034102225254004087344145 := by
  unfold tailWord_7856386
  simp only [CollatzResearch.WordTrace]
  refine ⟨71636484528915690187657253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191030625410441840500419341 71636484528915690187657253)
  ·
    refine ⟨13431840849171691910185735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71636484528915690187657253 13431840849171691910185735)
    ·
      refine ⟨20147761273757537865278603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13431840849171691910185735 20147761273757537865278603)
      ·
        refine ⟨30221641910636306797917905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20147761273757537865278603 30221641910636306797917905)
        ·
          refine ⟨22666231432977230098438429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30221641910636306797917905 22666231432977230098438429)
          ·
            refine ⟨8499836787366461286914411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22666231432977230098438429 8499836787366461286914411)
            ·
              refine ⟨12749755181049691930371617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8499836787366461286914411 12749755181049691930371617)
              ·
                refine ⟨9562316385787268947778713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12749755181049691930371617 9562316385787268947778713)
                ·
                  refine ⟨7171737289340451710834035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9562316385787268947778713 7171737289340451710834035)
                  ·
                    refine ⟨10757605934010677566251053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7171737289340451710834035 10757605934010677566251053)
                    ·
                      refine ⟨4034102225254004087344145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10757605934010677566251053 4034102225254004087344145)
                      ·
                        rfl

theorem cell23_7856386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_7856386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856386 prefixEnd_7856386 := by exact prefixLift 7856386
  have htrace : WordTrace (prefixWord ++ tailWord_7856386) baseStart_7856386 baseEnd_7856386 := by
    simpa [prefixWord, tailWord_7856386, baseEnd_7856386] using wordTrace_append hprefix tailTrace_7856386
  have hstable : (prefixWord ++ tailWord_7856386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856386).length < 2 ^ (prefixWord ++ tailWord_7856386).sum := by decide
  have hdescent : baseEnd_7856386 < baseStart_7856386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856428 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 1, 7]
def baseStart_7856428 : Nat := 118140960795 + 7856428 * 2 ^ 59
def prefixEnd_7856428 : Nat := 4983230072969 + 3 ^ 40 * 7856428 * 2
def baseEnd_7856428 : Nat := 1344707930480497641006317

theorem tailTrace_7856428 : CollatzResearch.WordTrace tailWord_7856428 prefixEnd_7856428 1344707930480497641006317 := by
  unfold tailWord_7856428
  simp only [CollatzResearch.WordTrace]
  refine ⟨143273734990755300961828969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191031646654340401282438625 143273734990755300961828969)
  ·
    refine ⟨107455301243066475721371727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143273734990755300961828969 107455301243066475721371727)
    ·
      refine ⟨161182951864599713582057591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107455301243066475721371727 161182951864599713582057591)
      ·
        refine ⟨241774427796899570373086387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161182951864599713582057591 241774427796899570373086387)
        ·
          refine ⟨362661641695349355559629581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241774427796899570373086387 362661641695349355559629581)
          ·
            refine ⟨135998115635756008334861093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 362661641695349355559629581 135998115635756008334861093)
            ·
              refine ⟨25499646681704251562786455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135998115635756008334861093 25499646681704251562786455)
              ·
                refine ⟨38249470022556377344179683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25499646681704251562786455 38249470022556377344179683)
                ·
                  refine ⟨57374205033834566016269525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38249470022556377344179683 57374205033834566016269525)
                  ·
                    refine ⟨1344707930480497641006317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57374205033834566016269525 1344707930480497641006317)
                    ·
                      rfl

theorem cell23_7856428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_7856428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856428 prefixEnd_7856428 := by exact prefixLift 7856428
  have htrace : WordTrace (prefixWord ++ tailWord_7856428) baseStart_7856428 baseEnd_7856428 := by
    simpa [prefixWord, tailWord_7856428, baseEnd_7856428] using wordTrace_append hprefix tailTrace_7856428
  have hstable : (prefixWord ++ tailWord_7856428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856428).length < 2 ^ (prefixWord ++ tailWord_7856428).sum := by decide
  have hdescent : baseEnd_7856428 < baseStart_7856428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856448 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 4]
def baseStart_7856448 : Nat := 118140960795 + 7856448 * 2 ^ 59
def prefixEnd_7856448 : Nat := 4983230072969 + 3 ^ 40 * 7856448 * 2
def baseEnd_7856448 : Nat := 4034134061054582844768859

theorem tailTrace_7856448 : CollatzResearch.WordTrace tailWord_7856448 prefixEnd_7856448 4034134061054582844768859 := by
  unfold tailWord_7856448
  simp only [CollatzResearch.WordTrace]
  refine ⟨143274099720719072669692999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191032132960958763559590665 143274099720719072669692999)
  ·
    refine ⟨214911149581078609004539499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143274099720719072669692999 214911149581078609004539499)
    ·
      refine ⟨322366724371617913506809249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214911149581078609004539499 322366724371617913506809249)
      ·
        refine ⟨241775043278713435130106937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322366724371617913506809249 241775043278713435130106937)
        ·
          refine ⟨181331282459035076347580203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241775043278713435130106937 181331282459035076347580203)
          ·
            refine ⟨271996923688552614521370305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181331282459035076347580203 271996923688552614521370305)
            ·
              refine ⟨203997692766414460891027729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271996923688552614521370305 203997692766414460891027729)
              ·
                refine ⟨152998269574810845668270797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203997692766414460891027729 152998269574810845668270797)
                ·
                  refine ⟨57374351090554067125601549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152998269574810845668270797 57374351090554067125601549)
                  ·
                    refine ⟨21515381658957775172100581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57374351090554067125601549 21515381658957775172100581)
                    ·
                      refine ⟨4034134061054582844768859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21515381658957775172100581 4034134061054582844768859)
                      ·
                        rfl

theorem cell23_7856448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_7856448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856448 prefixEnd_7856448 := by exact prefixLift 7856448
  have htrace : WordTrace (prefixWord ++ tailWord_7856448) baseStart_7856448 baseEnd_7856448 := by
    simpa [prefixWord, tailWord_7856448, baseEnd_7856448] using wordTrace_append hprefix tailTrace_7856448
  have hstable : (prefixWord ++ tailWord_7856448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856448).length < 2 ^ (prefixWord ++ tailWord_7856448).sum := by decide
  have hdescent : baseEnd_7856448 < baseStart_7856448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856449 : List Nat := [1, 2, 5, 2, 3, 1, 1, 1, 7]
def baseStart_7856449 : Nat := 118140960795 + 7856449 * 2 ^ 59
def prefixEnd_7856449 : Nat := 4983230072969 + 3 ^ 40 * 7856449 * 2
def baseEnd_7856449 : Nat := 448237174948359704539595

theorem tailTrace_7856449 : CollatzResearch.WordTrace tailWord_7856449 prefixEnd_7856449 448237174948359704539595 := by
  unfold tailWord_7856449
  simp only [CollatzResearch.WordTrace]
  refine ⟨286548235914434522510172401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191032157276289681673448267 286548235914434522510172401)
  ·
    refine ⟨214911176935825891882629301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286548235914434522510172401 214911176935825891882629301)
    ·
      refine ⟨20147922837733677363996497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214911176935825891882629301 20147922837733677363996497)
      ·
        refine ⟨15110942128300258022997373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20147922837733677363996497 15110942128300258022997373)
        ·
          refine ⟨5666603298112596758624015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15110942128300258022997373 5666603298112596758624015)
          ·
            refine ⟨8499904947168895137936023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5666603298112596758624015 8499904947168895137936023)
            ·
              refine ⟨12749857420753342706904035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8499904947168895137936023 12749857420753342706904035)
              ·
                refine ⟨19124786131130014060356053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12749857420753342706904035 19124786131130014060356053)
                ·
                  refine ⟨448237174948359704539595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19124786131130014060356053 448237174948359704539595)
                  ·
                    rfl

theorem cell23_7856449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 7].length) (baseStart_7856449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856449 prefixEnd_7856449 := by exact prefixLift 7856449
  have htrace : WordTrace (prefixWord ++ tailWord_7856449) baseStart_7856449 baseEnd_7856449 := by
    simpa [prefixWord, tailWord_7856449, baseEnd_7856449] using wordTrace_append hprefix tailTrace_7856449
  have hstable : (prefixWord ++ tailWord_7856449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856449).length < 2 ^ (prefixWord ++ tailWord_7856449).sum := by decide
  have hdescent : baseEnd_7856449 < baseStart_7856449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856482 : List Nat := [3, 3, 2, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_7856482 : Nat := 118140960795 + 7856482 * 2 ^ 59
def prefixEnd_7856482 : Nat := 4983230072969 + 3 ^ 40 * 7856482 * 2
def baseEnd_7856482 : Nat := 4034151519396835711743703

theorem tailTrace_7856482 : CollatzResearch.WordTrace tailWord_7856482 prefixEnd_7856482 4034151519396835711743703 := by
  unfold tailWord_7856482
  simp only [CollatzResearch.WordTrace]
  refine ⟨71637359880828742286530925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191032959682209979430749133 71637359880828742286530925)
  ·
    refine ⟨26864009955310778357449097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71637359880828742286530925 26864009955310778357449097)
    ·
      refine ⟨20148007466483083768086823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26864009955310778357449097 20148007466483083768086823)
      ·
        refine ⟨30222011199724625652130235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20148007466483083768086823 30222011199724625652130235)
        ·
          refine ⟨45333016799586938478195353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30222011199724625652130235 45333016799586938478195353)
          ·
            refine ⟨33999762599690203858646515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45333016799586938478195353 33999762599690203858646515)
            ·
              refine ⟨50999643899535305787969773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33999762599690203858646515 50999643899535305787969773)
              ·
                refine ⟨19124866462325739670488665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50999643899535305787969773 19124866462325739670488665)
                ·
                  refine ⟨14343649846744304752866499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19124866462325739670488665 14343649846744304752866499)
                  ·
                    refine ⟨21515474770116457129299749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14343649846744304752866499 21515474770116457129299749)
                    ·
                      refine ⟨4034151519396835711743703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21515474770116457129299749 4034151519396835711743703)
                      ·
                        rfl

theorem cell23_7856482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_7856482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856482 prefixEnd_7856482 := by exact prefixLift 7856482
  have htrace : WordTrace (prefixWord ++ tailWord_7856482) baseStart_7856482 baseEnd_7856482 := by
    simpa [prefixWord, tailWord_7856482, baseEnd_7856482] using wordTrace_append hprefix tailTrace_7856482
  have hstable : (prefixWord ++ tailWord_7856482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856482).length < 2 ^ (prefixWord ++ tailWord_7856482).sum := by decide
  have hdescent : baseEnd_7856482 < baseStart_7856482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856509 : List Nat := [1, 4, 1, 1, 2, 4, 1, 4, 1, 4]
def baseStart_7856509 : Nat := 118140960795 + 7856509 * 2 ^ 59
def prefixEnd_7856509 : Nat := 4983230072969 + 3 ^ 40 * 7856509 * 2
def baseEnd_7856509 : Nat := 1344721794458169035368693

theorem tailTrace_7856509 : CollatzResearch.WordTrace tailWord_7856509 prefixEnd_7856509 1344721794458169035368693 := by
  unfold tailWord_7856509
  simp only [CollatzResearch.WordTrace]
  refine ⟨286550424294217152757356581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191033616196144768504904387 286550424294217152757356581)
  ·
    refine ⟨53728204555165716142004359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286550424294217152757356581 53728204555165716142004359)
    ·
      refine ⟨80592306832748574213006539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53728204555165716142004359 80592306832748574213006539)
      ·
        refine ⟨120888460249122861319509809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80592306832748574213006539 120888460249122861319509809)
        ·
          refine ⟨90666345186842145989632357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120888460249122861319509809 90666345186842145989632357)
          ·
            refine ⟨16999939722532902373056067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90666345186842145989632357 16999939722532902373056067)
            ·
              refine ⟨25499909583799353559584101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16999939722532902373056067 25499909583799353559584101)
              ·
                refine ⟨4781233046962378792422019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25499909583799353559584101 4781233046962378792422019)
                ·
                  refine ⟨7171849570443568188633029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4781233046962378792422019 7171849570443568188633029)
                  ·
                    refine ⟨1344721794458169035368693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7171849570443568188633029 1344721794458169035368693)
                    ·
                      rfl

theorem cell23_7856509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_7856509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856509 prefixEnd_7856509 := by exact prefixLift 7856509
  have htrace : WordTrace (prefixWord ++ tailWord_7856509) baseStart_7856509 baseEnd_7856509 := by
    simpa [prefixWord, tailWord_7856509, baseEnd_7856509] using wordTrace_append hprefix tailTrace_7856509
  have hstable : (prefixWord ++ tailWord_7856509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856509).length < 2 ^ (prefixWord ++ tailWord_7856509).sum := by decide
  have hdescent : baseEnd_7856509 < baseStart_7856509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856535 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 3, 5]
def baseStart_7856535 : Nat := 118140960795 + 7856535 * 2 ^ 59
def prefixEnd_7856535 : Nat := 4983230072969 + 3 ^ 40 * 7856535 * 2
def baseEnd_7856535 : Nat := 1344726244623841334793653

theorem tailTrace_7856535 : CollatzResearch.WordTrace tailWord_7856535 prefixEnd_7856535 1344726244623841334793653 := by
  unfold tailWord_7856535
  simp only [CollatzResearch.WordTrace]
  refine ⟨286551372592122959197803059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191034248394748639465202039 286551372592122959197803059)
  ·
    refine ⟨429827058888184438796704589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286551372592122959197803059 429827058888184438796704589)
    ·
      refine ⟨161185147083069164548764221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429827058888184438796704589 161185147083069164548764221)
      ·
        refine ⟨60444430156150936705786583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161185147083069164548764221 60444430156150936705786583)
        ·
          refine ⟨90666645234226405058679875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60444430156150936705786583 90666645234226405058679875)
          ·
            refine ⟨135999967851339607588019813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90666645234226405058679875 135999967851339607588019813)
            ·
              refine ⟨25499993972126176422753715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135999967851339607588019813 25499993972126176422753715)
              ·
                refine ⟨38249990958189264634130573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25499993972126176422753715 38249990958189264634130573)
                ·
                  refine ⟨14343746609320974237798965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38249990958189264634130573 14343746609320974237798965)
                  ·
                    refine ⟨1344726244623841334793653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14343746609320974237798965 1344726244623841334793653)
                    ·
                      rfl

theorem cell23_7856535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_7856535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856535 prefixEnd_7856535 := by exact prefixLift 7856535
  have htrace : WordTrace (prefixWord ++ tailWord_7856535) baseStart_7856535 baseEnd_7856535 := by
    simpa [prefixWord, tailWord_7856535, baseEnd_7856535] using wordTrace_append hprefix tailTrace_7856535
  have hstable : (prefixWord ++ tailWord_7856535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856535).length < 2 ^ (prefixWord ++ tailWord_7856535).sum := by decide
  have hdescent : baseEnd_7856535 < baseStart_7856535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856625 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 2, 7]
def baseStart_7856625 : Nat := 118140960795 + 7856625 * 2 ^ 59
def prefixEnd_7856625 : Nat := 4983230072969 + 3 ^ 40 * 7856625 * 2
def baseEnd_7856625 : Nat := 1344741649043476217418515

theorem tailTrace_7856625 : CollatzResearch.WordTrace tailWord_7856625 prefixEnd_7856625 1344741649043476217418515 := by
  unfold tailWord_7856625
  simp only [CollatzResearch.WordTrace]
  refine ⟨286554655161796904568579329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191036436774531269712386219 286554655161796904568579329)
  ·
    refine ⟨214915991371347678426434497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286554655161796904568579329 214915991371347678426434497)
    ·
      refine ⟨161186993528510758819825873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214915991371347678426434497 161186993528510758819825873)
      ·
        refine ⟨120890245146383069114869405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161186993528510758819825873 120890245146383069114869405)
        ·
          refine ⟨45333841929893650918076027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120890245146383069114869405 45333841929893650918076027)
          ·
            refine ⟨68000762894840476377114041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45333841929893650918076027 68000762894840476377114041)
            ·
              refine ⟨51000572171130357282835531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68000762894840476377114041 51000572171130357282835531)
              ·
                refine ⟨76500858256695535924253297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51000572171130357282835531 76500858256695535924253297)
                ·
                  refine ⟨57375643692521651943189973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76500858256695535924253297 57375643692521651943189973)
                  ·
                    refine ⟨1344741649043476217418515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57375643692521651943189973 1344741649043476217418515)
                    ·
                      rfl

theorem cell23_7856625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_7856625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856625 prefixEnd_7856625 := by exact prefixLift 7856625
  have htrace : WordTrace (prefixWord ++ tailWord_7856625) baseStart_7856625 baseEnd_7856625 := by
    simpa [prefixWord, tailWord_7856625, baseEnd_7856625] using wordTrace_append hprefix tailTrace_7856625
  have hstable : (prefixWord ++ tailWord_7856625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856625).length < 2 ^ (prefixWord ++ tailWord_7856625).sum := by decide
  have hdescent : baseEnd_7856625 < baseStart_7856625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856629 : List Nat := [1, 3, 5, 1, 2, 1, 2, 8]
def baseStart_7856629 : Nat := 118140960795 + 7856629 * 2 ^ 59
def prefixEnd_7856629 : Nat := 4983230072969 + 3 ^ 40 * 7856629 * 2
def baseEnd_7856629 : Nat := 149415814853816542096501

theorem tailTrace_7856629 : CollatzResearch.WordTrace tailWord_7856629 prefixEnd_7856629 149415814853816542096501 := by
  unfold tailWord_7856629
  simp only [CollatzResearch.WordTrace]
  refine ⟨286554801053782413251724941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191036534035854942167816627 286554801053782413251724941)
  ·
    refine ⟨107458050395168404969396853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286554801053782413251724941 107458050395168404969396853)
    ·
      refine ⟨10074192224547037965880955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107458050395168404969396853 10074192224547037965880955)
      ·
        refine ⟨15111288336820556948821433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10074192224547037965880955 15111288336820556948821433)
        ·
          refine ⟨11333466252615417711616075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15111288336820556948821433 11333466252615417711616075)
          ·
            refine ⟨17000199378923126567424113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11333466252615417711616075 17000199378923126567424113)
            ·
              refine ⟨12750149534192344925568085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17000199378923126567424113 12750149534192344925568085)
              ·
                refine ⟨149415814853816542096501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12750149534192344925568085 149415814853816542096501)
                ·
                  rfl

theorem cell23_7856629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 8].length) (baseStart_7856629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856629 prefixEnd_7856629 := by exact prefixLift 7856629
  have htrace : WordTrace (prefixWord ++ tailWord_7856629) baseStart_7856629 baseEnd_7856629 := by
    simpa [prefixWord, tailWord_7856629, baseEnd_7856629] using wordTrace_append hprefix tailTrace_7856629
  have hstable : (prefixWord ++ tailWord_7856629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856629).length < 2 ^ (prefixWord ++ tailWord_7856629).sum := by decide
  have hdescent : baseEnd_7856629 < baseStart_7856629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856639 : List Nat := [1, 1, 2, 2, 1, 2, 5, 3, 2, 1, 3]
def baseStart_7856639 : Nat := 118140960795 + 7856639 * 2 ^ 59
def prefixEnd_7856639 : Nat := 4983230072969 + 3 ^ 40 * 7856639 * 2
def baseEnd_7856639 : Nat := 4034232135859591597480481

theorem tailTrace_7856639 : CollatzResearch.WordTrace tailWord_7856639 prefixEnd_7856639 4034232135859591597480481 := by
  unfold tailWord_7856639
  simp only [CollatzResearch.WordTrace]
  refine ⟨286555165783746184959588971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191036777189164123306392647 286555165783746184959588971)
  ·
    refine ⟨429832748675619277439383457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286555165783746184959588971 429832748675619277439383457)
    ·
      refine ⟨322374561506714458079537593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429832748675619277439383457 322374561506714458079537593)
      ·
        refine ⟨241780921130035843559653195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322374561506714458079537593 241780921130035843559653195)
        ·
          refine ⟨362671381695053765339479793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241780921130035843559653195 362671381695053765339479793)
          ·
            refine ⟨272003536271290324004609845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362671381695053765339479793 272003536271290324004609845)
            ·
              refine ⟨25500331525433467875432173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 272003536271290324004609845 25500331525433467875432173)
              ·
                refine ⟨9562624322037550453287065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25500331525433467875432173 9562624322037550453287065)
                ·
                  refine ⟨7171968241528162839965299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9562624322037550453287065 7171968241528162839965299)
                  ·
                    refine ⟨10757952362292244259947949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7171968241528162839965299 10757952362292244259947949)
                    ·
                      refine ⟨4034232135859591597480481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10757952362292244259947949 4034232135859591597480481)
                      ·
                        rfl

theorem cell23_7856639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 1, 3].length) (baseStart_7856639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856639 prefixEnd_7856639 := by exact prefixLift 7856639
  have htrace : WordTrace (prefixWord ++ tailWord_7856639) baseStart_7856639 baseEnd_7856639 := by
    simpa [prefixWord, tailWord_7856639, baseEnd_7856639] using wordTrace_append hprefix tailTrace_7856639
  have hstable : (prefixWord ++ tailWord_7856639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856639).length < 2 ^ (prefixWord ++ tailWord_7856639).sum := by decide
  have hdescent : baseEnd_7856639 < baseStart_7856639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856646 : List Nat := [6, 2, 1, 1, 1, 1, 2, 9]
def baseStart_7856646 : Nat := 118140960795 + 7856646 * 2 ^ 59
def prefixEnd_7856646 : Nat := 4983230072969 + 3 ^ 40 * 7856646 * 2
def baseEnd_7856646 : Nat := 149416138156450854447887

theorem tailTrace_7856646 : CollatzResearch.WordTrace tailWord_7856646 prefixEnd_7856646 149416138156450854447887 := by
  unfold tailWord_7856646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8954856909210025786096681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 191036947396480550103395861 8954856909210025786096681)
  ·
    refine ⟨6716142681907519339572511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8954856909210025786096681 6716142681907519339572511)
    ·
      refine ⟨10074214022861279009358767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6716142681907519339572511 10074214022861279009358767)
      ·
        refine ⟨15111321034291918514038151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10074214022861279009358767 15111321034291918514038151)
        ·
          refine ⟨22666981551437877771057227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15111321034291918514038151 22666981551437877771057227)
          ·
            refine ⟨34000472327156816656585841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22666981551437877771057227 34000472327156816656585841)
            ·
              refine ⟨25500354245367612492439381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34000472327156816656585841 25500354245367612492439381)
              ·
                refine ⟨149416138156450854447887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25500354245367612492439381 149416138156450854447887)
                ·
                  rfl

theorem cell23_7856646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_7856646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856646 prefixEnd_7856646 := by exact prefixLift 7856646
  have htrace : WordTrace (prefixWord ++ tailWord_7856646) baseStart_7856646 baseEnd_7856646 := by
    simpa [prefixWord, tailWord_7856646, baseEnd_7856646] using wordTrace_append hprefix tailTrace_7856646
  have hstable : (prefixWord ++ tailWord_7856646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856646).length < 2 ^ (prefixWord ++ tailWord_7856646).sum := by decide
  have hdescent : baseEnd_7856646 < baseStart_7856646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856649 : List Nat := [1, 2, 1, 1, 3, 1, 2, 6, 1, 3, 2]
def baseStart_7856649 : Nat := 118140960795 + 7856649 * 2 ^ 59
def prefixEnd_7856649 : Nat := 4983230072969 + 3 ^ 40 * 7856649 * 2
def baseEnd_7856649 : Nat := 4034237270666136558355435

theorem tailTrace_7856649 : CollatzResearch.WordTrace tailWord_7856649 prefixEnd_7856649 4034237270666136558355435 := by
  unfold tailWord_7856649
  simp only [CollatzResearch.WordTrace]
  refine ⟨286555530513709956667453001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191037020342473304444968667 286555530513709956667453001)
  ·
    refine ⟨214916647885282467500589751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286555530513709956667453001 214916647885282467500589751)
    ·
      refine ⟨322374971827923701250884627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214916647885282467500589751 322374971827923701250884627)
      ·
        refine ⟨483562457741885551876326941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322374971827923701250884627 483562457741885551876326941)
        ·
          refine ⟨181335921653207081953622603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 483562457741885551876326941 181335921653207081953622603)
          ·
            refine ⟨272003882479810622930433905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181335921653207081953622603 272003882479810622930433905)
            ·
              refine ⟨204002911859857967197825429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272003882479810622930433905 204002911859857967197825429)
              ·
                refine ⟨9562636493430842212398067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 204002911859857967197825429 9562636493430842212398067)
                ·
                  refine ⟨14343954740146263318597101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9562636493430842212398067 14343954740146263318597101)
                  ·
                    refine ⟨5378983027554848744473913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14343954740146263318597101 5378983027554848744473913)
                    ·
                      refine ⟨4034237270666136558355435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5378983027554848744473913 4034237270666136558355435)
                      ·
                        rfl

theorem cell23_7856649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 3, 2].length) (baseStart_7856649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856649 prefixEnd_7856649 := by exact prefixLift 7856649
  have htrace : WordTrace (prefixWord ++ tailWord_7856649) baseStart_7856649 baseEnd_7856649 := by
    simpa [prefixWord, tailWord_7856649, baseEnd_7856649] using wordTrace_append hprefix tailTrace_7856649
  have hstable : (prefixWord ++ tailWord_7856649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856649).length < 2 ^ (prefixWord ++ tailWord_7856649).sum := by decide
  have hdescent : baseEnd_7856649 < baseStart_7856649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856696 : List Nat := [2, 1, 2, 1, 4, 1, 1, 5, 2, 2, 2]
def baseStart_7856696 : Nat := 118140960795 + 7856696 * 2 ^ 59
def prefixEnd_7856696 : Nat := 4983230072969 + 3 ^ 40 * 7856696 * 2
def baseEnd_7856696 : Nat := 4034261404256897874467719

theorem tailTrace_7856696 : CollatzResearch.WordTrace tailWord_7856696 prefixEnd_7856696 4034261404256897874467719 := by
  unfold tailWord_7856696
  simp only [CollatzResearch.WordTrace]
  refine ⟨143278622372269841847206971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191038163163026455796275961 143278622372269841847206971)
  ·
    refine ⟨214917933558404762770810457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143278622372269841847206971 214917933558404762770810457)
    ·
      refine ⟨161188450168803572078107843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214917933558404762770810457 161188450168803572078107843)
      ·
        refine ⟨241782675253205358117161765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161188450168803572078107843 241782675253205358117161765)
        ·
          refine ⟨45334251609976004646967831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241782675253205358117161765 45334251609976004646967831)
          ·
            refine ⟨68001377414964006970451747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45334251609976004646967831 68001377414964006970451747)
            ·
              refine ⟨102002066122446010455677621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68001377414964006970451747 102002066122446010455677621)
              ·
                refine ⟨9562693698979313480219777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102002066122446010455677621 9562693698979313480219777)
                ·
                  refine ⟨7172020274234485110164833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9562693698979313480219777 7172020274234485110164833)
                  ·
                    refine ⟨5379015205675863832623625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7172020274234485110164833 5379015205675863832623625)
                    ·
                      refine ⟨4034261404256897874467719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5379015205675863832623625 4034261404256897874467719)
                      ·
                        rfl

theorem cell23_7856696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 2, 2, 2].length) (baseStart_7856696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856696 prefixEnd_7856696 := by exact prefixLift 7856696
  have htrace : WordTrace (prefixWord ++ tailWord_7856696) baseStart_7856696 baseEnd_7856696 := by
    simpa [prefixWord, tailWord_7856696, baseEnd_7856696] using wordTrace_append hprefix tailTrace_7856696
  have hstable : (prefixWord ++ tailWord_7856696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856696).length < 2 ^ (prefixWord ++ tailWord_7856696).sum := by decide
  have hdescent : baseEnd_7856696 < baseStart_7856696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856769 : List Nat := [1, 2, 4, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_7856769 : Nat := 118140960795 + 7856769 * 2 ^ 59
def prefixEnd_7856769 : Nat := 4983230072969 + 3 ^ 40 * 7856769 * 2
def baseEnd_7856769 : Nat := 4034298888344676088854883

theorem tailTrace_7856769 : CollatzResearch.WordTrace tailWord_7856769 prefixEnd_7856769 4034298888344676088854883 := by
  unfold tailWord_7856769
  simp only [CollatzResearch.WordTrace]
  refine ⟨286559907273275217161821361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191039938182183478107880907 286559907273275217161821361)
  ·
    refine ⟨214919930454956412871366021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286559907273275217161821361 214919930454956412871366021)
    ·
      refine ⟨40297486960304327413381129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214919930454956412871366021 40297486960304327413381129)
      ·
        refine ⟨30223115220228245560035847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40297486960304327413381129 30223115220228245560035847)
        ·
          refine ⟨45334672830342368340053771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30223115220228245560035847 45334672830342368340053771)
          ·
            refine ⟨68002009245513552510080657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45334672830342368340053771 68002009245513552510080657)
            ·
              refine ⟨51001506934135164382560493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68002009245513552510080657 51001506934135164382560493)
              ·
                refine ⟨19125565100300686643460185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51001506934135164382560493 19125565100300686643460185)
                ·
                  refine ⟨14344173825225514982595139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19125565100300686643460185 14344173825225514982595139)
                  ·
                    refine ⟨21516260737838272473892709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14344173825225514982595139 21516260737838272473892709)
                    ·
                      refine ⟨4034298888344676088854883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21516260737838272473892709 4034298888344676088854883)
                      ·
                        rfl

theorem cell23_7856769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_7856769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856769 prefixEnd_7856769 := by exact prefixLift 7856769
  have htrace : WordTrace (prefixWord ++ tailWord_7856769) baseStart_7856769 baseEnd_7856769 := by
    simpa [prefixWord, tailWord_7856769, baseEnd_7856769] using wordTrace_append hprefix tailTrace_7856769
  have hstable : (prefixWord ++ tailWord_7856769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856769).length < 2 ^ (prefixWord ++ tailWord_7856769).sum := by decide
  have hdescent : baseEnd_7856769 < baseStart_7856769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856786 : List Nat := [3, 2, 3, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_7856786 : Nat := 118140960795 + 7856786 * 2 ^ 59
def prefixEnd_7856786 : Nat := 4983230072969 + 3 ^ 40 * 7856786 * 2
def baseEnd_7856786 : Nat := 4034307617515802522342305

theorem tailTrace_7856786 : CollatzResearch.WordTrace tailWord_7856786 prefixEnd_7856786 4034307617515802522342305 := by
  unfold tailWord_7856786
  simp only [CollatzResearch.WordTrace]
  refine ⟨71640131828553407266297553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191040351542809086043460141 71640131828553407266297553)
  ·
    refine ⟨53730098871415055449723165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71640131828553407266297553 53730098871415055449723165)
    ·
      refine ⟨20148787076780645793646187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53730098871415055449723165 20148787076780645793646187)
      ·
        refine ⟨30223180615170968690469281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20148787076780645793646187 30223180615170968690469281)
        ·
          refine ⟨22667385461378226517851961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30223180615170968690469281 22667385461378226517851961)
          ·
            refine ⟨17000539096033669888388971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22667385461378226517851961 17000539096033669888388971)
            ·
              refine ⟨25500808644050504832583457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17000539096033669888388971 25500808644050504832583457)
              ·
                refine ⟨19125606483037878624437593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25500808644050504832583457 19125606483037878624437593)
                ·
                  refine ⟨14344204862278408968328195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19125606483037878624437593 14344204862278408968328195)
                  ·
                    refine ⟨21516307293417613452492293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14344204862278408968328195 21516307293417613452492293)
                    ·
                      refine ⟨4034307617515802522342305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21516307293417613452492293 4034307617515802522342305)
                      ·
                        rfl

theorem cell23_7856786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_7856786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856786 prefixEnd_7856786 := by exact prefixLift 7856786
  have htrace : WordTrace (prefixWord ++ tailWord_7856786) baseStart_7856786 baseEnd_7856786 := by
    simpa [prefixWord, tailWord_7856786, baseEnd_7856786] using wordTrace_append hprefix tailTrace_7856786
  have hstable : (prefixWord ++ tailWord_7856786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856786).length < 2 ^ (prefixWord ++ tailWord_7856786).sum := by decide
  have hdescent : baseEnd_7856786 < baseStart_7856786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856792 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 8]
def baseStart_7856792 : Nat := 118140960795 + 7856792 * 2 ^ 59
def prefixEnd_7856792 : Nat := 4983230072969 + 3 ^ 40 * 7856792 * 2
def baseEnd_7856792 : Nat := 448256744266636610985253

theorem tailTrace_7856792 : CollatzResearch.WordTrace tailWord_7856792 prefixEnd_7856792 448256744266636610985253 := by
  unfold tailWord_7856792
  simp only [CollatzResearch.WordTrace]
  refine ⟨143280373076095946044954315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191040497434794594726605753 143280373076095946044954315)
  ·
    refine ⟨214920559614143919067431473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143280373076095946044954315 214920559614143919067431473)
    ·
      refine ⟨161190419710607939300573605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214920559614143919067431473 161190419710607939300573605)
      ·
        refine ⟨30223203695738988618857551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161190419710607939300573605 30223203695738988618857551)
        ·
          refine ⟨45334805543608482928286327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30223203695738988618857551 45334805543608482928286327)
          ·
            refine ⟨68002208315412724392429491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45334805543608482928286327 68002208315412724392429491)
            ·
              refine ⟨102003312473119086588644237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68002208315412724392429491 102003312473119086588644237)
              ·
                refine ⟨38251242177419657470741589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102003312473119086588644237 38251242177419657470741589)
                ·
                  refine ⟨448256744266636610985253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38251242177419657470741589 448256744266636610985253)
                  ·
                    rfl

theorem cell23_7856792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 8].length) (baseStart_7856792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856792 prefixEnd_7856792 := by exact prefixLift 7856792
  have htrace : WordTrace (prefixWord ++ tailWord_7856792) baseStart_7856792 baseEnd_7856792 := by
    simpa [prefixWord, tailWord_7856792, baseEnd_7856792] using wordTrace_append hprefix tailTrace_7856792
  have hstable : (prefixWord ++ tailWord_7856792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856792).length < 2 ^ (prefixWord ++ tailWord_7856792).sum := by decide
  have hdescent : baseEnd_7856792 < baseStart_7856792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856796 : List Nat := [2, 2, 3, 2, 2, 1, 3, 1, 3, 4]
def baseStart_7856796 : Nat := 118140960795 + 7856796 * 2 ^ 59
def prefixEnd_7856796 : Nat := 4983230072969 + 3 ^ 40 * 7856796 * 2
def baseEnd_7856796 : Nat := 1344770917440782494405753

theorem tailTrace_7856796 : CollatzResearch.WordTrace tailWord_7856796 prefixEnd_7856796 1344770917440782494405753 := by
  unfold tailWord_7856796
  simp only [CollatzResearch.WordTrace]
  refine ⟨143280446022088700386527121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191040594696118267182036161 143280446022088700386527121)
  ·
    refine ⟨107460334516566525289895341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143280446022088700386527121 107460334516566525289895341)
    ·
      refine ⟨40297625443712446983710753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107460334516566525289895341 40297625443712446983710753)
      ·
        refine ⟨30223219082784335237783065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40297625443712446983710753 30223219082784335237783065)
        ·
          refine ⟨22667414312088251428337299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30223219082784335237783065 22667414312088251428337299)
          ·
            refine ⟨34001121468132377142505949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22667414312088251428337299 34001121468132377142505949)
            ·
              refine ⟨12750420550549641428439731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34001121468132377142505949 12750420550549641428439731)
              ·
                refine ⟨19125630825824462142659597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12750420550549641428439731 19125630825824462142659597)
                ·
                  refine ⟨7172111559684173303497349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19125630825824462142659597 7172111559684173303497349)
                  ·
                    refine ⟨1344770917440782494405753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7172111559684173303497349 1344770917440782494405753)
                    ·
                      rfl

theorem cell23_7856796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_7856796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856796 prefixEnd_7856796 := by exact prefixLift 7856796
  have htrace : WordTrace (prefixWord ++ tailWord_7856796) baseStart_7856796 baseEnd_7856796 := by
    simpa [prefixWord, tailWord_7856796, baseEnd_7856796] using wordTrace_append hprefix tailTrace_7856796
  have hstable : (prefixWord ++ tailWord_7856796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856796).length < 2 ^ (prefixWord ++ tailWord_7856796).sum := by decide
  have hdescent : baseEnd_7856796 < baseStart_7856796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856869 : List Nat := [1, 3, 1, 4, 1, 2, 1, 3, 1, 6]
def baseStart_7856869 : Nat := 118140960795 + 7856869 * 2 ^ 59
def prefixEnd_7856869 : Nat := 4983230072969 + 3 ^ 40 * 7856869 * 2
def baseEnd_7856869 : Nat := 1344783412136708565868141

theorem tailTrace_7856869 : CollatzResearch.WordTrace tailWord_7856869 prefixEnd_7856869 1344783412136708565868141 := by
  unfold tailWord_7856869
  simp only [CollatzResearch.WordTrace]
  refine ⟨286563554572912934240461661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191042369715275289493641107 286563554572912934240461661)
  ·
    refine ⟨107461332964842350340173123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286563554572912934240461661 107461332964842350340173123)
    ·
      refine ⟨161191999447263525510259685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107461332964842350340173123 161191999447263525510259685)
      ·
        refine ⟨30223499896361911033173691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161191999447263525510259685 30223499896361911033173691)
        ·
          refine ⟨45335249844542866549760537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30223499896361911033173691 45335249844542866549760537)
          ·
            refine ⟨34001437383407149912320403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45335249844542866549760537 34001437383407149912320403)
            ·
              refine ⟨51002156075110724868480605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34001437383407149912320403 51002156075110724868480605)
              ·
                refine ⟨19125808528166521825680227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51002156075110724868480605 19125808528166521825680227)
                ·
                  refine ⟨28688712792249782738520341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19125808528166521825680227 28688712792249782738520341)
                  ·
                    refine ⟨1344783412136708565868141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28688712792249782738520341 1344783412136708565868141)
                    ·
                      rfl

theorem cell23_7856869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_7856869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856869 prefixEnd_7856869 := by exact prefixLift 7856869
  have htrace : WordTrace (prefixWord ++ tailWord_7856869) baseStart_7856869 baseEnd_7856869 := by
    simpa [prefixWord, tailWord_7856869, baseEnd_7856869] using wordTrace_append hprefix tailTrace_7856869
  have hstable : (prefixWord ++ tailWord_7856869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856869).length < 2 ^ (prefixWord ++ tailWord_7856869).sum := by decide
  have hdescent : baseEnd_7856869 < baseStart_7856869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856886 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_7856886 : Nat := 118140960795 + 7856886 * 2 ^ 59
def prefixEnd_7856886 : Nat := 4983230072969 + 3 ^ 40 * 7856886 * 2
def baseEnd_7856886 : Nat := 1344786321860417377030615

theorem tailTrace_7856886 : CollatzResearch.WordTrace tailWord_7856886 prefixEnd_7856886 1344786321860417377030615 := by
  unfold tailWord_7856886
  simp only [CollatzResearch.WordTrace]
  refine ⟨17910260913365709133989407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191042783075900897429220341 17910260913365709133989407)
  ·
    refine ⟨26865391370048563700984111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17910260913365709133989407 26865391370048563700984111)
    ·
      refine ⟨40298087055072845551476167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26865391370048563700984111 40298087055072845551476167)
      ·
        refine ⟨60447130582609268327214251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40298087055072845551476167 60447130582609268327214251)
        ·
          refine ⟨90670695873913902490821377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60447130582609268327214251 90670695873913902490821377)
          ·
            refine ⟨68003021905435426868116033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90670695873913902490821377 68003021905435426868116033)
            ·
              refine ⟨51002266429076570151087025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68003021905435426868116033 51002266429076570151087025)
              ·
                refine ⟨38251699821807427613315269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51002266429076570151087025 38251699821807427613315269)
                ·
                  refine ⟨7172193716588892677496613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38251699821807427613315269 7172193716588892677496613)
                  ·
                    refine ⟨1344786321860417377030615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7172193716588892677496613 1344786321860417377030615)
                    ·
                      rfl

theorem cell23_7856886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_7856886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856886 prefixEnd_7856886 := by exact prefixLift 7856886
  have htrace : WordTrace (prefixWord ++ tailWord_7856886) baseStart_7856886 baseEnd_7856886 := by
    simpa [prefixWord, tailWord_7856886, baseEnd_7856886] using wordTrace_append hprefix tailTrace_7856886
  have hstable : (prefixWord ++ tailWord_7856886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856886).length < 2 ^ (prefixWord ++ tailWord_7856886).sum := by decide
  have hdescent : baseEnd_7856886 < baseStart_7856886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856903 : List Nat := [1, 1, 4, 4, 1, 1, 3, 2, 2, 4]
def baseStart_7856903 : Nat := 118140960795 + 7856903 * 2 ^ 59
def prefixEnd_7856903 : Nat := 4983230072969 + 3 ^ 40 * 7856903 * 2
def baseEnd_7856903 : Nat := 1344789231584126188193089

theorem tailTrace_7856903 : CollatzResearch.WordTrace tailWord_7856903 prefixEnd_7856903 1344789231584126188193089 := by
  unfold tailWord_7856903
  simp only [CollatzResearch.WordTrace]
  refine ⟨286564794654789758047199363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191043196436526505364799575 286564794654789758047199363)
  ·
    refine ⟨429847191982184637070799045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286564794654789758047199363 429847191982184637070799045)
    ·
      refine ⟨80596348496659619450774821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 429847191982184637070799045 80596348496659619450774821)
      ·
        refine ⟨15111815343123678647020279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80596348496659619450774821 15111815343123678647020279)
        ·
          refine ⟨22667723014685517970530419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15111815343123678647020279 22667723014685517970530419)
          ·
            refine ⟨34001584522028276955795629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22667723014685517970530419 34001584522028276955795629)
            ·
              refine ⟨12750594195760603858423361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34001584522028276955795629 12750594195760603858423361)
              ·
                refine ⟨9562945646820452893817521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12750594195760603858423361 9562945646820452893817521)
                ·
                  refine ⟨7172209235115339670363141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9562945646820452893817521 7172209235115339670363141)
                  ·
                    refine ⟨1344789231584126188193089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7172209235115339670363141 1344789231584126188193089)
                    ·
                      rfl

theorem cell23_7856903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_7856903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856903 prefixEnd_7856903 := by exact prefixLift 7856903
  have htrace : WordTrace (prefixWord ++ tailWord_7856903) baseStart_7856903 baseEnd_7856903 := by
    simpa [prefixWord, tailWord_7856903, baseEnd_7856903] using wordTrace_append hprefix tailTrace_7856903
  have hstable : (prefixWord ++ tailWord_7856903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856903).length < 2 ^ (prefixWord ++ tailWord_7856903).sum := by decide
  have hdescent : baseEnd_7856903 < baseStart_7856903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856961 : List Nat := [1, 2, 5, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_7856961 : Nat := 118140960795 + 7856961 * 2 ^ 59
def prefixEnd_7856961 : Nat := 4983230072969 + 3 ^ 40 * 7856961 * 2
def baseEnd_7856961 : Nat := 4034397476630339337654001

theorem tailTrace_7856961 : CollatzResearch.WordTrace tailWord_7856961 prefixEnd_7856961 4034397476630339337654001 := by
  unfold tailWord_7856961
  simp only [CollatzResearch.WordTrace]
  refine ⟨286566910088579633952810737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191044606725719755968540491 286566910088579633952810737)
  ·
    refine ⟨214925182566434725464608053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286566910088579633952810737 214925182566434725464608053)
    ·
      refine ⟨20149235865603255512307005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214925182566434725464608053 20149235865603255512307005)
      ·
        refine ⟨7555963449601220817115127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20149235865603255512307005 7555963449601220817115127)
        ·
          refine ⟨11333945174401831225672691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7555963449601220817115127 11333945174401831225672691)
          ·
            refine ⟨17000917761602746838509037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11333945174401831225672691 17000917761602746838509037)
            ·
              refine ⟨6375344160601030064440889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17000917761602746838509037 6375344160601030064440889)
              ·
                refine ⟨4781508120450772548330667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6375344160601030064440889 4781508120450772548330667)
                ·
                  refine ⟨7172262180676158822496001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4781508120450772548330667 7172262180676158822496001)
                  ·
                    refine ⟨5379196635507119116872001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7172262180676158822496001 5379196635507119116872001)
                    ·
                      refine ⟨4034397476630339337654001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5379196635507119116872001 4034397476630339337654001)
                      ·
                        rfl

theorem cell23_7856961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_7856961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856961 prefixEnd_7856961 := by exact prefixLift 7856961
  have htrace : WordTrace (prefixWord ++ tailWord_7856961) baseStart_7856961 baseEnd_7856961 := by
    simpa [prefixWord, tailWord_7856961, baseEnd_7856961] using wordTrace_append hprefix tailTrace_7856961
  have hstable : (prefixWord ++ tailWord_7856961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856961).length < 2 ^ (prefixWord ++ tailWord_7856961).sum := by decide
  have hdescent : baseEnd_7856961 < baseStart_7856961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856977 : List Nat := [1, 2, 2, 1, 6, 2, 2, 1, 2, 1, 3]
def baseStart_7856977 : Nat := 118140960795 + 7856977 * 2 ^ 59
def prefixEnd_7856977 : Nat := 4983230072969 + 3 ^ 40 * 7856977 * 2
def baseEnd_7856977 : Nat := 4034405692320811275053927

theorem tailTrace_7856977 : CollatzResearch.WordTrace tailWord_7856977 prefixEnd_7856977 4034405692320811275053927 := by
  unfold tailWord_7856977
  simp only [CollatzResearch.WordTrace]
  refine ⟨286567493656521668685393185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191044995771014445790262123 286567493656521668685393185)
  ·
    refine ⟨214925620242391251514044889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286567493656521668685393185 214925620242391251514044889)
    ·
      refine ⟨161194215181793438635533667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214925620242391251514044889 161194215181793438635533667)
      ·
        refine ⟨241791322772690157953300501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161194215181793438635533667 241791322772690157953300501)
        ·
          refine ⟨11333968254969851154060961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 241791322772690157953300501 11333968254969851154060961)
          ·
            refine ⟨8500476191227388365545721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11333968254969851154060961 8500476191227388365545721)
            ·
              refine ⟨6375357143420541274159291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8500476191227388365545721 6375357143420541274159291)
              ·
                refine ⟨9563035715130811911238937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6375357143420541274159291 9563035715130811911238937)
                ·
                  refine ⟨7172276786348108933429203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9563035715130811911238937 7172276786348108933429203)
                  ·
                    refine ⟨10758415179522163400143805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7172276786348108933429203 10758415179522163400143805)
                    ·
                      refine ⟨4034405692320811275053927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10758415179522163400143805 4034405692320811275053927)
                      ·
                        rfl

theorem cell23_7856977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 2, 1, 3].length) (baseStart_7856977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856977 prefixEnd_7856977 := by exact prefixLift 7856977
  have htrace : WordTrace (prefixWord ++ tailWord_7856977) baseStart_7856977 baseEnd_7856977 := by
    simpa [prefixWord, tailWord_7856977, baseEnd_7856977] using wordTrace_append hprefix tailTrace_7856977
  have hstable : (prefixWord ++ tailWord_7856977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856977).length < 2 ^ (prefixWord ++ tailWord_7856977).sum := by decide
  have hdescent : baseEnd_7856977 < baseStart_7856977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7856979 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 4]
def baseStart_7856979 : Nat := 118140960795 + 7856979 * 2 ^ 59
def prefixEnd_7856979 : Nat := 4983230072969 + 3 ^ 40 * 7856979 * 2
def baseEnd_7856979 : Nat := 4034406719282120267228917

theorem tailTrace_7856979 : CollatzResearch.WordTrace tailWord_7856979 prefixEnd_7856979 4034406719282120267228917 := by
  unfold tailWord_7856979
  simp only [CollatzResearch.WordTrace]
  refine ⟨286567566602514423026965991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191045044401676282017977327 286567566602514423026965991)
  ·
    refine ⟨429851349903771634540448987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286567566602514423026965991 429851349903771634540448987)
    ·
      refine ⟨644777024855657451810673481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429851349903771634540448987 644777024855657451810673481)
      ·
        refine ⟨483582768641743088858005111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 644777024855657451810673481 483582768641743088858005111)
        ·
          refine ⟨725374152962614633287007667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483582768641743088858005111 725374152962614633287007667)
          ·
            refine ⟨1088061229443921949930511501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725374152962614633287007667 1088061229443921949930511501)
            ·
              refine ⟨408022961041470731223941813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1088061229443921949930511501 408022961041470731223941813)
              ·
                refine ⟨38252152597637881052244545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 408022961041470731223941813 38252152597637881052244545)
                ·
                  refine ⟨28689114448228410789183409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38252152597637881052244545 28689114448228410789183409)
                  ·
                    refine ⟨21516835836171308091887557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28689114448228410789183409 21516835836171308091887557)
                    ·
                      refine ⟨4034406719282120267228917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21516835836171308091887557 4034406719282120267228917)
                      ·
                        rfl

theorem cell23_7856979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_7856979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7856979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7856979 prefixEnd_7856979 := by exact prefixLift 7856979
  have htrace : WordTrace (prefixWord ++ tailWord_7856979) baseStart_7856979 baseEnd_7856979 := by
    simpa [prefixWord, tailWord_7856979, baseEnd_7856979] using wordTrace_append hprefix tailTrace_7856979
  have hstable : (prefixWord ++ tailWord_7856979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7856979).length < 2 ^ (prefixWord ++ tailWord_7856979).sum := by decide
  have hdescent : baseEnd_7856979 < baseStart_7856979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7856979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857023 : List Nat := [1, 1, 2, 2, 1, 1, 8, 2, 5]
def baseStart_7857023 : Nat := 118140960795 + 7857023 * 2 ^ 59
def prefixEnd_7857023 : Nat := 4983230072969 + 3 ^ 40 * 7857023 * 2
def baseEnd_7857023 : Nat := 448269923603435343897635

theorem tailTrace_7857023 : CollatzResearch.WordTrace tailWord_7857023 prefixEnd_7857023 448269923603435343897635 := by
  unfold tailWord_7857023
  simp only [CollatzResearch.WordTrace]
  refine ⟨286569171414355018541567723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191046114276236679027711815 286569171414355018541567723)
  ·
    refine ⟨429853757121532527812351585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286569171414355018541567723 429853757121532527812351585)
    ·
      refine ⟨322390317841149395859263689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429853757121532527812351585 322390317841149395859263689)
      ·
        refine ⟨241792738380862046894447767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322390317841149395859263689 241792738380862046894447767)
        ·
          refine ⟨362689107571293070341671651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241792738380862046894447767 362689107571293070341671651)
          ·
            refine ⟨544033661356939605512507477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362689107571293070341671651 544033661356939605512507477)
            ·
              refine ⟨6375394469026636002099697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 544033661356939605512507477 6375394469026636002099697)
              ·
                refine ⟨4781545851769977001574773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6375394469026636002099697 4781545851769977001574773)
                ·
                  refine ⟨448269923603435343897635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4781545851769977001574773 448269923603435343897635)
                  ·
                    rfl

theorem cell23_7857023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 5].length) (baseStart_7857023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857023 prefixEnd_7857023 := by exact prefixLift 7857023
  have htrace : WordTrace (prefixWord ++ tailWord_7857023) baseStart_7857023 baseEnd_7857023 := by
    simpa [prefixWord, tailWord_7857023, baseEnd_7857023] using wordTrace_append hprefix tailTrace_7857023
  have hstable : (prefixWord ++ tailWord_7857023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857023).length < 2 ^ (prefixWord ++ tailWord_7857023).sum := by decide
  have hdescent : baseEnd_7857023 < baseStart_7857023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857086 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_7857086 : Nat := 118140960795 + 7857086 * 2 ^ 59
def prefixEnd_7857086 : Nat := 4983230072969 + 3 ^ 40 * 7857086 * 2
def baseEnd_7857086 : Nat := 4034461661712151348590925

theorem tailTrace_7857086 : CollatzResearch.WordTrace tailWord_7857086 prefixEnd_7857086 4034461661712151348590925 := by
  unfold tailWord_7857086
  simp only [CollatzResearch.WordTrace]
  refine ⟨35821433651640847537638889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191047646142084520200740741 35821433651640847537638889)
  ·
    refine ⟨26866075238730635653229167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35821433651640847537638889 26866075238730635653229167)
    ·
      refine ⟨40299112858095953479843751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26866075238730635653229167 40299112858095953479843751)
      ·
        refine ⟨60448669287143930219765627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40299112858095953479843751 60448669287143930219765627)
        ·
          refine ⟨90673003930715895329648441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60448669287143930219765627 90673003930715895329648441)
          ·
            refine ⟨68004752948036921497236331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90673003930715895329648441 68004752948036921497236331)
            ·
              refine ⟨102007129422055382245854497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68004752948036921497236331 102007129422055382245854497)
              ·
                refine ⟨76505347066541536684390873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102007129422055382245854497 76505347066541536684390873)
                ·
                  refine ⟨57379010299906152513293155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76505347066541536684390873 57379010299906152513293155)
                  ·
                    refine ⟨86068515449859228769939733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57379010299906152513293155 86068515449859228769939733)
                    ·
                      refine ⟨4034461661712151348590925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86068515449859228769939733 4034461661712151348590925)
                      ·
                        rfl

theorem cell23_7857086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_7857086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857086 prefixEnd_7857086 := by exact prefixLift 7857086
  have htrace : WordTrace (prefixWord ++ tailWord_7857086) baseStart_7857086 baseEnd_7857086 := by
    simpa [prefixWord, tailWord_7857086, baseEnd_7857086] using wordTrace_append hprefix tailTrace_7857086
  have hstable : (prefixWord ++ tailWord_7857086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857086).length < 2 ^ (prefixWord ++ tailWord_7857086).sum := by decide
  have hdescent : baseEnd_7857086 < baseStart_7857086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857110 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_7857110 : Nat := 118140960795 + 7857110 * 2 ^ 59
def prefixEnd_7857110 : Nat := 4983230072969 + 3 ^ 40 * 7857110 * 2
def baseEnd_7857110 : Nat := 4034473985247859254690815

theorem tailTrace_7857110 : CollatzResearch.WordTrace tailWord_7857110 prefixEnd_7857110 4034473985247859254690815 := by
  unfold tailWord_7857110
  simp only [CollatzResearch.WordTrace]
  refine ⟨17910771535314989524999049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191048229710026554933323189 17910771535314989524999049)
  ·
    refine ⟨13433078651486242143749287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17910771535314989524999049 13433078651486242143749287)
    ·
      refine ⟨20149617977229363215623931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13433078651486242143749287 20149617977229363215623931)
      ·
        refine ⟨30224426965844044823435897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20149617977229363215623931 30224426965844044823435897)
        ·
          refine ⟨22668320224383033617576923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30224426965844044823435897 22668320224383033617576923)
          ·
            refine ⟨34002480336574550426365385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22668320224383033617576923 34002480336574550426365385)
            ·
              refine ⟨25501860252430912819774039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34002480336574550426365385 25501860252430912819774039)
              ·
                refine ⟨38252790378646369229661059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25501860252430912819774039 38252790378646369229661059)
                ·
                  refine ⟨57379185567969553844491589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38252790378646369229661059 57379185567969553844491589)
                  ·
                    refine ⟨10758597293994291345842173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57379185567969553844491589 10758597293994291345842173)
                    ·
                      refine ⟨4034473985247859254690815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10758597293994291345842173 4034473985247859254690815)
                      ·
                        rfl

theorem cell23_7857110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_7857110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857110 prefixEnd_7857110 := by exact prefixLift 7857110
  have htrace : WordTrace (prefixWord ++ tailWord_7857110) baseStart_7857110 baseEnd_7857110 := by
    simpa [prefixWord, tailWord_7857110, baseEnd_7857110] using wordTrace_append hprefix tailTrace_7857110
  have hstable : (prefixWord ++ tailWord_7857110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857110).length < 2 ^ (prefixWord ++ tailWord_7857110).sum := by decide
  have hdescent : baseEnd_7857110 < baseStart_7857110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857117 : List Nat := [1, 4, 3, 1, 2, 1, 3, 3, 1, 4]
def baseStart_7857117 : Nat := 118140960795 + 7857117 * 2 ^ 59
def prefixEnd_7857117 : Nat := 4983230072969 + 3 ^ 40 * 7857117 * 2
def baseEnd_7857117 : Nat := 1344825859870813575767761

theorem tailTrace_7857117 : CollatzResearch.WordTrace tailWord_7857117 prefixEnd_7857117 1344825859870813575767761 := by
  unfold tailWord_7857117
  simp only [CollatzResearch.WordTrace]
  refine ⟨286572599876014472595489605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191048399917342981730326403 286572599876014472595489605)
  ·
    refine ⟨53732362476752713611654301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286572599876014472595489605 53732362476752713611654301)
    ·
      refine ⟨20149635928782267604370363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53732362476752713611654301 20149635928782267604370363)
      ·
        refine ⟨30224453893173401406555545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20149635928782267604370363 30224453893173401406555545)
        ·
          refine ⟨22668340419880051054916659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30224453893173401406555545 22668340419880051054916659)
          ·
            refine ⟨34002510629820076582374989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22668340419880051054916659 34002510629820076582374989)
            ·
              refine ⟨12750941486182528718390621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34002510629820076582374989 12750941486182528718390621)
              ·
                refine ⟨4781603057318448269396483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12750941486182528718390621 4781603057318448269396483)
                ·
                  refine ⟨7172404585977672404094725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4781603057318448269396483 7172404585977672404094725)
                  ·
                    refine ⟨1344825859870813575767761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7172404585977672404094725 1344825859870813575767761)
                    ·
                      rfl

theorem cell23_7857117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_7857117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857117 prefixEnd_7857117 := by exact prefixLift 7857117
  have htrace : WordTrace (prefixWord ++ tailWord_7857117) baseStart_7857117 baseEnd_7857117 := by
    simpa [prefixWord, tailWord_7857117, baseEnd_7857117] using wordTrace_append hprefix tailTrace_7857117
  have hstable : (prefixWord ++ tailWord_7857117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857117).length < 2 ^ (prefixWord ++ tailWord_7857117).sum := by decide
  have hdescent : baseEnd_7857117 < baseStart_7857117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857134 : List Nat := [4, 1, 2, 1, 4, 1, 3, 2, 1, 4]
def baseStart_7857134 : Nat := 118140960795 + 7857134 * 2 ^ 59
def prefixEnd_7857134 : Nat := 4983230072969 + 3 ^ 40 * 7857134 * 2
def baseEnd_7857134 : Nat := 1344828769594522386930235

theorem tailTrace_7857134 : CollatzResearch.WordTrace tailWord_7857134 prefixEnd_7857134 1344828769594522386930235 := by
  unfold tailWord_7857134
  simp only [CollatzResearch.WordTrace]
  refine ⟨35821652489619110562357307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191048813277968589665905637 35821652489619110562357307)
  ·
    refine ⟨53732478734428665843535961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35821652489619110562357307 53732478734428665843535961)
    ·
      refine ⟨40299359050821499382651971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53732478734428665843535961 40299359050821499382651971)
      ·
        refine ⟨60449038576232249073977957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40299359050821499382651971 60449038576232249073977957)
        ·
          refine ⟨11334194733043546701370867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60449038576232249073977957 11334194733043546701370867)
          ·
            refine ⟨17001292099565320052056301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11334194733043546701370867 17001292099565320052056301)
            ·
              refine ⟨6375484537336995019521113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17001292099565320052056301 6375484537336995019521113)
              ·
                refine ⟨4781613403002746264640835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6375484537336995019521113 4781613403002746264640835)
                ·
                  refine ⟨7172420104504119396961253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4781613403002746264640835 7172420104504119396961253)
                  ·
                    refine ⟨1344828769594522386930235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7172420104504119396961253 1344828769594522386930235)
                    ·
                      rfl

theorem cell23_7857134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_7857134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857134 prefixEnd_7857134 := by exact prefixLift 7857134
  have htrace : WordTrace (prefixWord ++ tailWord_7857134) baseStart_7857134 baseEnd_7857134 := by
    simpa [prefixWord, tailWord_7857134, baseEnd_7857134] using wordTrace_append hprefix tailTrace_7857134
  have hstable : (prefixWord ++ tailWord_7857134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857134).length < 2 ^ (prefixWord ++ tailWord_7857134).sum := by decide
  have hdescent : baseEnd_7857134 < baseStart_7857134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857160 : List Nat := [2, 1, 3, 2, 1, 5, 1, 2, 1, 5]
def baseStart_7857160 : Nat := 118140960795 + 7857160 * 2 ^ 59
def prefixEnd_7857160 : Nat := 4983230072969 + 3 ^ 40 * 7857160 * 2
def baseEnd_7857160 : Nat := 1344833219760194686355195

theorem tailTrace_7857160 : CollatzResearch.WordTrace tailWord_7857160 prefixEnd_7857160 1344833219760194686355195 := by
  unfold tailWord_7857160
  simp only [CollatzResearch.WordTrace]
  refine ⟨143287084107429345469652467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191049445476572460626203289 143287084107429345469652467)
  ·
    refine ⟨214930626161144018204478701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143287084107429345469652467 214930626161144018204478701)
    ·
      refine ⟨80598984810429006826679513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214930626161144018204478701 80598984810429006826679513)
      ·
        refine ⟨60449238607821755120009635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80598984810429006826679513 60449238607821755120009635)
        ·
          refine ⟨90673857911732632680014453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60449238607821755120009635 90673857911732632680014453)
          ·
            refine ⟨8500674179224934313751355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90673857911732632680014453 8500674179224934313751355)
            ·
              refine ⟨12751011268837401470627033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8500674179224934313751355 12751011268837401470627033)
              ·
                refine ⟨9563258451628051102970275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12751011268837401470627033 9563258451628051102970275)
                ·
                  refine ⟨14344887677442076654455413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9563258451628051102970275 14344887677442076654455413)
                  ·
                    refine ⟨1344833219760194686355195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14344887677442076654455413 1344833219760194686355195)
                    ·
                      rfl

theorem cell23_7857160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_7857160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857160 prefixEnd_7857160 := by exact prefixLift 7857160
  have htrace : WordTrace (prefixWord ++ tailWord_7857160) baseStart_7857160 baseEnd_7857160 := by
    simpa [prefixWord, tailWord_7857160, baseEnd_7857160] using wordTrace_append hprefix tailTrace_7857160
  have hstable : (prefixWord ++ tailWord_7857160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857160).length < 2 ^ (prefixWord ++ tailWord_7857160).sum := by decide
  have hdescent : baseEnd_7857160 < baseStart_7857160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857163 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 4]
def baseStart_7857163 : Nat := 118140960795 + 7857163 * 2 ^ 59
def prefixEnd_7857163 : Nat := 4983230072969 + 3 ^ 40 * 7857163 * 2
def baseEnd_7857163 : Nat := 4034501199722547547328071

theorem tailTrace_7857163 : CollatzResearch.WordTrace tailWord_7857163 prefixEnd_7857163 4034501199722547547328071 := by
  unfold tailWord_7857163
  simp only [CollatzResearch.WordTrace]
  refine ⟨286574277633847822451664143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191049518422565214967776095 286574277633847822451664143)
  ·
    refine ⟨429861416450771733677496215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286574277633847822451664143 429861416450771733677496215)
    ·
      refine ⟨644792124676157600516244323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429861416450771733677496215 644792124676157600516244323)
      ·
        refine ⟨967188187014236400774366485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644792124676157600516244323 967188187014236400774366485)
        ·
          refine ⟨45336946266292331286298429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 967188187014236400774366485 45336946266292331286298429)
          ·
            refine ⟨17001354849859624232361911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45336946266292331286298429 17001354849859624232361911)
            ·
              refine ⟨25502032274789436348542867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17001354849859624232361911 25502032274789436348542867)
              ·
                refine ⟨38253048412184154522814301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25502032274789436348542867 38253048412184154522814301)
                ·
                  refine ⟨14344893154569057946055363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38253048412184154522814301 14344893154569057946055363)
                  ·
                    refine ⟨21517339731853586919083045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14344893154569057946055363 21517339731853586919083045)
                    ·
                      refine ⟨4034501199722547547328071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21517339731853586919083045 4034501199722547547328071)
                      ·
                        rfl

theorem cell23_7857163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 4].length) (baseStart_7857163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857163 prefixEnd_7857163 := by exact prefixLift 7857163
  have htrace : WordTrace (prefixWord ++ tailWord_7857163) baseStart_7857163 baseEnd_7857163 := by
    simpa [prefixWord, tailWord_7857163, baseEnd_7857163] using wordTrace_append hprefix tailTrace_7857163
  have hstable : (prefixWord ++ tailWord_7857163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857163).length < 2 ^ (prefixWord ++ tailWord_7857163).sum := by decide
  have hdescent : baseEnd_7857163 < baseStart_7857163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857173 : List Nat := [1, 3, 2, 1, 4, 2, 1, 2, 1, 6]
def baseStart_7857173 : Nat := 118140960795 + 7857173 * 2 ^ 59
def prefixEnd_7857173 : Nat := 4983230072969 + 3 ^ 40 * 7857173 * 2
def baseEnd_7857173 : Nat := 1344835444843030836067675

theorem tailTrace_7857173 : CollatzResearch.WordTrace tailWord_7857173 prefixEnd_7857173 1344835444843030836067675 := by
  unfold tailWord_7857173
  simp only [CollatzResearch.WordTrace]
  refine ⟨286574642363811594159528173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191049761575874396106352115 286574642363811594159528173)
  ·
    refine ⟨107465490886429347809823065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286574642363811594159528173 107465490886429347809823065)
    ·
      refine ⟨80599118164822010857367299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107465490886429347809823065 80599118164822010857367299)
      ·
        refine ⟨120898677247233016286050949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80599118164822010857367299 120898677247233016286050949)
        ·
          refine ⟨22668501983856190553634553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120898677247233016286050949 22668501983856190553634553)
          ·
            refine ⟨17001376487892142915225915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22668501983856190553634553 17001376487892142915225915)
            ·
              refine ⟨25502064731838214372838873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17001376487892142915225915 25502064731838214372838873)
              ·
                refine ⟨19126548548878660779629155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25502064731838214372838873 19126548548878660779629155)
                ·
                  refine ⟨28689822823317991169443733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19126548548878660779629155 28689822823317991169443733)
                  ·
                    refine ⟨1344835444843030836067675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28689822823317991169443733 1344835444843030836067675)
                    ·
                      rfl

theorem cell23_7857173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_7857173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857173 prefixEnd_7857173 := by exact prefixLift 7857173
  have htrace : WordTrace (prefixWord ++ tailWord_7857173) baseStart_7857173 baseEnd_7857173 := by
    simpa [prefixWord, tailWord_7857173, baseEnd_7857173] using wordTrace_append hprefix tailTrace_7857173
  have hstable : (prefixWord ++ tailWord_7857173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857173).length < 2 ^ (prefixWord ++ tailWord_7857173).sum := by decide
  have hdescent : baseEnd_7857173 < baseStart_7857173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857183 : List Nat := [1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 5]
def baseStart_7857183 : Nat := 118140960795 + 7857183 * 2 ^ 59
def prefixEnd_7857183 : Nat := 4983230072969 + 3 ^ 40 * 7857183 * 2
def baseEnd_7857183 : Nat := 4034511469335637469077979

theorem tailTrace_7857183 : CollatzResearch.WordTrace tailWord_7857183 prefixEnd_7857183 4034511469335637469077979 := by
  unfold tailWord_7857183
  simp only [CollatzResearch.WordTrace]
  refine ⟨286575007093775365867392203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191050004729183577244928135 286575007093775365867392203)
  ·
    refine ⟨429862510640663048801088305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286575007093775365867392203 429862510640663048801088305)
    ·
      refine ⟨322396882980497286600816229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429862510640663048801088305 322396882980497286600816229)
      ·
        refine ⟨60449415558843241237653043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322396882980497286600816229 60449415558843241237653043)
        ·
          refine ⟨90674123338264861856479565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60449415558843241237653043 90674123338264861856479565)
          ·
            refine ⟨34002796251849323196179837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90674123338264861856479565 34002796251849323196179837)
            ·
              refine ⟨12751048594443496198567439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34002796251849323196179837 12751048594443496198567439)
              ·
                refine ⟨19126572891665244297851159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12751048594443496198567439 19126572891665244297851159)
                ·
                  refine ⟨28689859337497866446776739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19126572891665244297851159 28689859337497866446776739)
                  ·
                    refine ⟨43034789006246799670165109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28689859337497866446776739 43034789006246799670165109)
                    ·
                      refine ⟨4034511469335637469077979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43034789006246799670165109 4034511469335637469077979)
                      ·
                        rfl

theorem cell23_7857183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_7857183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857183 prefixEnd_7857183 := by exact prefixLift 7857183
  have htrace : WordTrace (prefixWord ++ tailWord_7857183) baseStart_7857183 baseEnd_7857183 := by
    simpa [prefixWord, tailWord_7857183, baseEnd_7857183] using wordTrace_append hprefix tailTrace_7857183
  have hstable : (prefixWord ++ tailWord_7857183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857183).length < 2 ^ (prefixWord ++ tailWord_7857183).sum := by decide
  have hdescent : baseEnd_7857183 < baseStart_7857183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857186 : List Nat := [3, 3, 1, 1, 1, 14]
def baseStart_7857186 : Nat := 118140960795 + 7857186 * 2 ^ 59
def prefixEnd_7857186 : Nat := 4983230072969 + 3 ^ 40 * 7857186 * 2
def baseEnd_7857186 : Nat := 16602934196615641799755

theorem tailTrace_7857186 : CollatzResearch.WordTrace tailWord_7857186 prefixEnd_7857186 16602934196615641799755 := by
  unfold tailWord_7857186
  simp only [CollatzResearch.WordTrace]
  refine ⟨71643779128191124344937853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191050077675176331586500941 71643779128191124344937853)
  ·
    refine ⟨26866417173071671629351695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71643779128191124344937853 26866417173071671629351695)
    ·
      refine ⟨40299625759607507444027543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26866417173071671629351695 40299625759607507444027543)
      ·
        refine ⟨60449438639411261166041315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40299625759607507444027543 60449438639411261166041315)
        ·
          refine ⟨90674157959116891749061973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60449438639411261166041315 90674157959116891749061973)
          ·
            refine ⟨16602934196615641799755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 90674157959116891749061973 16602934196615641799755)
            ·
              rfl

theorem cell23_7857186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 14].length) (baseStart_7857186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857186 prefixEnd_7857186 := by exact prefixLift 7857186
  have htrace : WordTrace (prefixWord ++ tailWord_7857186) baseStart_7857186 baseEnd_7857186 := by
    simpa [prefixWord, tailWord_7857186, baseEnd_7857186] using wordTrace_append hprefix tailTrace_7857186
  have hstable : (prefixWord ++ tailWord_7857186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857186).length < 2 ^ (prefixWord ++ tailWord_7857186).sum := by decide
  have hdescent : baseEnd_7857186 < baseStart_7857186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857191 : List Nat := [1, 1, 7, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_7857191 : Nat := 118140960795 + 7857191 * 2 ^ 59
def prefixEnd_7857191 : Nat := 4983230072969 + 3 ^ 40 * 7857191 * 2
def baseEnd_7857191 : Nat := 4034515577180873437777943

theorem tailTrace_7857191 : CollatzResearch.WordTrace tailWord_7857191 prefixEnd_7857191 4034515577180873437777943 := by
  unfold tailWord_7857191
  simp only [CollatzResearch.WordTrace]
  refine ⟨286575298877746383233683427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191050199251830922155788951 286575298877746383233683427)
  ·
    refine ⟨429862948316619574850525141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286575298877746383233683427 429862948316619574850525141)
    ·
      refine ⟨10074912851170771285559183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 429862948316619574850525141 10074912851170771285559183)
      ·
        refine ⟨15112369276756156928338775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10074912851170771285559183 15112369276756156928338775)
        ·
          refine ⟨22668553915134235392508163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15112369276756156928338775 22668553915134235392508163)
          ·
            refine ⟨34002830872701353088762245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22668553915134235392508163 34002830872701353088762245)
            ·
              refine ⟨6375530788631503704142921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34002830872701353088762245 6375530788631503704142921)
              ·
                refine ⟨4781648091473627778107191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6375530788631503704142921 4781648091473627778107191)
                ·
                  refine ⟨7172472137210441667160787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4781648091473627778107191 7172472137210441667160787)
                  ·
                    refine ⟨10758708205815662500741181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7172472137210441667160787 10758708205815662500741181)
                    ·
                      refine ⟨4034515577180873437777943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10758708205815662500741181 4034515577180873437777943)
                      ·
                        rfl

theorem cell23_7857191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_7857191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857191 prefixEnd_7857191 := by exact prefixLift 7857191
  have htrace : WordTrace (prefixWord ++ tailWord_7857191) baseStart_7857191 baseEnd_7857191 := by
    simpa [prefixWord, tailWord_7857191, baseEnd_7857191] using wordTrace_append hprefix tailTrace_7857191
  have hstable : (prefixWord ++ tailWord_7857191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857191).length < 2 ^ (prefixWord ++ tailWord_7857191).sum := by decide
  have hdescent : baseEnd_7857191 < baseStart_7857191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857214 : List Nat := [4, 2, 1, 3, 1, 2, 1, 2, 3, 2, 2]
def baseStart_7857214 : Nat := 118140960795 + 7857214 * 2 ^ 59
def prefixEnd_7857214 : Nat := 4983230072969 + 3 ^ 40 * 7857214 * 2
def baseEnd_7857214 : Nat := 4034527387235926847790337

theorem tailTrace_7857214 : CollatzResearch.WordTrace tailWord_7857214 prefixEnd_7857214 4034527387235926847790337 := by
  unfold tailWord_7857214
  simp only [CollatzResearch.WordTrace]
  refine ⟨35822017219582882270221337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191050758504442038774513797 35822017219582882270221337)
  ·
    refine ⟨26866512914687161702666003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35822017219582882270221337 26866512914687161702666003)
    ·
      refine ⟨40299769372030742553999005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26866512914687161702666003 40299769372030742553999005)
      ·
        refine ⟨15112413514511528457749627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40299769372030742553999005 15112413514511528457749627)
        ·
          refine ⟨22668620271767292686624441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15112413514511528457749627 22668620271767292686624441)
          ·
            refine ⟨17001465203825469514968331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22668620271767292686624441 17001465203825469514968331)
            ·
              refine ⟨25502197805738204272452497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17001465203825469514968331 25502197805738204272452497)
              ·
                refine ⟨19126648354303653204339373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25502197805738204272452497 19126648354303653204339373)
                ·
                  refine ⟨7172493132863869951627265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19126648354303653204339373 7172493132863869951627265)
                  ·
                    refine ⟨5379369849647902463720449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7172493132863869951627265 5379369849647902463720449)
                    ·
                      refine ⟨4034527387235926847790337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5379369849647902463720449 4034527387235926847790337)
                      ·
                        rfl

theorem cell23_7857214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_7857214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857214 prefixEnd_7857214 := by exact prefixLift 7857214
  have htrace : WordTrace (prefixWord ++ tailWord_7857214) baseStart_7857214 baseEnd_7857214 := by
    simpa [prefixWord, tailWord_7857214, baseEnd_7857214] using wordTrace_append hprefix tailTrace_7857214
  have hstable : (prefixWord ++ tailWord_7857214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857214).length < 2 ^ (prefixWord ++ tailWord_7857214).sum := by decide
  have hdescent : baseEnd_7857214 < baseStart_7857214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857216 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 2, 7]
def baseStart_7857216 : Nat := 118140960795 + 7857216 * 2 ^ 59
def prefixEnd_7857216 : Nat := 4983230072969 + 3 ^ 40 * 7857216 * 2
def baseEnd_7857216 : Nat := 1344842804732411946655109

theorem tailTrace_7857216 : CollatzResearch.WordTrace tailWord_7857216 prefixEnd_7857216 1344842804732411946655109 := by
  unfold tailWord_7857216
  simp only [CollatzResearch.WordTrace]
  refine ⟨143288105351327906251671751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191050807135103875002229001 143288105351327906251671751)
  ·
    refine ⟨214932158026991859377507627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143288105351327906251671751 214932158026991859377507627)
    ·
      refine ⟨322398237040487789066261441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214932158026991859377507627 322398237040487789066261441)
      ·
        refine ⟨241798677780365841799696081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322398237040487789066261441 241798677780365841799696081)
        ·
          refine ⟨181349008335274381349772061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241798677780365841799696081 181349008335274381349772061)
          ·
            refine ⟨68005878125727893006164523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181349008335274381349772061 68005878125727893006164523)
            ·
              refine ⟨102008817188591839509246785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68005878125727893006164523 102008817188591839509246785)
              ·
                refine ⟨76506612891443879631935089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102008817188591839509246785 76506612891443879631935089)
                ·
                  refine ⟨57379959668582909723951317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76506612891443879631935089 57379959668582909723951317)
                  ·
                    refine ⟨1344842804732411946655109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57379959668582909723951317 1344842804732411946655109)
                    ·
                      rfl

theorem cell23_7857216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2, 7].length) (baseStart_7857216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857216 prefixEnd_7857216 := by exact prefixLift 7857216
  have htrace : WordTrace (prefixWord ++ tailWord_7857216) baseStart_7857216 baseEnd_7857216 := by
    simpa [prefixWord, tailWord_7857216, baseEnd_7857216] using wordTrace_append hprefix tailTrace_7857216
  have hstable : (prefixWord ++ tailWord_7857216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857216).length < 2 ^ (prefixWord ++ tailWord_7857216).sum := by decide
  have hdescent : baseEnd_7857216 < baseStart_7857216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857230 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3]
def baseStart_7857230 : Nat := 118140960795 + 7857230 * 2 ^ 59
def prefixEnd_7857230 : Nat := 4983230072969 + 3 ^ 40 * 7857230 * 2
def baseEnd_7857230 : Nat := 4034535602926398785190263

theorem tailTrace_7857230 : CollatzResearch.WordTrace tailWord_7857230 prefixEnd_7857230 4034535602926398785190263 := by
  unfold tailWord_7857230
  simp only [CollatzResearch.WordTrace]
  refine ⟨35822090165575636611794143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191051147549736728596235429 35822090165575636611794143)
  ·
    refine ⟨53733135248363454917691215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35822090165575636611794143 53733135248363454917691215)
    ·
      refine ⟨80599702872545182376536823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53733135248363454917691215 80599702872545182376536823)
      ·
        refine ⟨120899554308817773564805235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80599702872545182376536823 120899554308817773564805235)
        ·
          refine ⟨181349331463226660347207853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120899554308817773564805235 181349331463226660347207853)
          ·
            refine ⟨68005999298709997630202945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181349331463226660347207853 68005999298709997630202945)
            ·
              refine ⟨51004499474032498222652209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68005999298709997630202945 51004499474032498222652209)
              ·
                refine ⟨38253374605524373666989157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51004499474032498222652209 38253374605524373666989157)
                ·
                  refine ⟨7172507738535820062560467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38253374605524373666989157 7172507738535820062560467)
                  ·
                    refine ⟨10758761607803730093840701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7172507738535820062560467 10758761607803730093840701)
                    ·
                      refine ⟨4034535602926398785190263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10758761607803730093840701 4034535602926398785190263)
                      ·
                        rfl

theorem cell23_7857230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_7857230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857230 prefixEnd_7857230 := by exact prefixLift 7857230
  have htrace : WordTrace (prefixWord ++ tailWord_7857230) baseStart_7857230 baseEnd_7857230 := by
    simpa [prefixWord, tailWord_7857230, baseEnd_7857230] using wordTrace_append hprefix tailTrace_7857230
  have hstable : (prefixWord ++ tailWord_7857230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857230).length < 2 ^ (prefixWord ++ tailWord_7857230).sum := by decide
  have hdescent : baseEnd_7857230 < baseStart_7857230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857234 : List Nat := [3, 2, 2, 1, 3, 3, 2, 1, 1, 2, 3]
def baseStart_7857234 : Nat := 118140960795 + 7857234 * 2 ^ 59
def prefixEnd_7857234 : Nat := 4983230072969 + 3 ^ 40 * 7857234 * 2
def baseEnd_7857234 : Nat := 4034537656849016769540245

theorem tailTrace_7857234 : CollatzResearch.WordTrace tailWord_7857234 prefixEnd_7857234 4034537656849016769540245 := by
  unfold tailWord_7857234
  simp only [CollatzResearch.WordTrace]
  refine ⟨71644216804147650394374689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191051244811060401051665837 71644216804147650394374689)
  ·
    refine ⟨53733162603110737795781017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71644216804147650394374689 53733162603110737795781017)
    ·
      refine ⟨40299871952333053346835763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53733162603110737795781017 40299871952333053346835763)
      ·
        refine ⟨60449807928499580020253645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40299871952333053346835763 60449807928499580020253645)
        ·
          refine ⟨22668677973187342507595117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60449807928499580020253645 22668677973187342507595117)
          ·
            refine ⟨8500754239945253440348169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22668677973187342507595117 8500754239945253440348169)
            ·
              refine ⟨6375565679958940080261127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8500754239945253440348169 6375565679958940080261127)
              ·
                refine ⟨9563348519938410120391691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6375565679958940080261127 9563348519938410120391691)
                ·
                  refine ⟨14345022779907615180587537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9563348519938410120391691 14345022779907615180587537)
                  ·
                    refine ⟨10758767084930711385440653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14345022779907615180587537 10758767084930711385440653)
                    ·
                      refine ⟨4034537656849016769540245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10758767084930711385440653 4034537656849016769540245)
                      ·
                        rfl

theorem cell23_7857234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_7857234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857234 prefixEnd_7857234 := by exact prefixLift 7857234
  have htrace : WordTrace (prefixWord ++ tailWord_7857234) baseStart_7857234 baseEnd_7857234 := by
    simpa [prefixWord, tailWord_7857234, baseEnd_7857234] using wordTrace_append hprefix tailTrace_7857234
  have hstable : (prefixWord ++ tailWord_7857234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857234).length < 2 ^ (prefixWord ++ tailWord_7857234).sum := by decide
  have hdescent : baseEnd_7857234 < baseStart_7857234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857340 : List Nat := [2, 2, 2, 3, 2, 1, 1, 3, 2, 5]
def baseStart_7857340 : Nat := 118140960795 + 7857340 * 2 ^ 59
def prefixEnd_7857340 : Nat := 4983230072969 + 3 ^ 40 * 7857340 * 2
def baseEnd_7857340 : Nat := 1344864028599464451604919

theorem tailTrace_7857340 : CollatzResearch.WordTrace tailWord_7857340 prefixEnd_7857340 1344864028599464451604919 := by
  unfold tailWord_7857340
  simp only [CollatzResearch.WordTrace]
  refine ⟨143290366677103290840428737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191053822236137721120571649 143290366677103290840428737)
  ·
    refine ⟨107467775007827468130321553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143290366677103290840428737 107467775007827468130321553)
    ·
      refine ⟨80600831255870601097741165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107467775007827468130321553 80600831255870601097741165)
      ·
        refine ⟨30225311720951475411652937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80600831255870601097741165 30225311720951475411652937)
        ·
          refine ⟨22668983790713606558739703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30225311720951475411652937 22668983790713606558739703)
          ·
            refine ⟨34003475686070409838109555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22668983790713606558739703 34003475686070409838109555)
            ·
              refine ⟨51005213529105614757164333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34003475686070409838109555 51005213529105614757164333)
              ·
                refine ⟨19126955073414605533936625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51005213529105614757164333 19126955073414605533936625)
                ·
                  refine ⟨14345216305060954150452469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19126955073414605533936625 14345216305060954150452469)
                  ·
                    refine ⟨1344864028599464451604919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14345216305060954150452469 1344864028599464451604919)
                    ·
                      rfl

theorem cell23_7857340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_7857340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857340 prefixEnd_7857340 := by exact prefixLift 7857340
  have htrace : WordTrace (prefixWord ++ tailWord_7857340) baseStart_7857340 baseEnd_7857340 := by
    simpa [prefixWord, tailWord_7857340, baseEnd_7857340] using wordTrace_append hprefix tailTrace_7857340
  have hstable : (prefixWord ++ tailWord_7857340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857340).length < 2 ^ (prefixWord ++ tailWord_7857340).sum := by decide
  have hdescent : baseEnd_7857340 < baseStart_7857340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857343 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 4]
def baseStart_7857343 : Nat := 118140960795 + 7857343 * 2 ^ 59
def prefixEnd_7857343 : Nat := 4983230072969 + 3 ^ 40 * 7857343 * 2
def baseEnd_7857343 : Nat := 4034593626240356843077243

theorem tailTrace_7857343 : CollatzResearch.WordTrace tailWord_7857343 prefixEnd_7857343 4034593626240356843077243 := by
  unfold tailWord_7857343
  simp only [CollatzResearch.WordTrace]
  refine ⟨286580842773195713193216683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191053895182130475462144455 286580842773195713193216683)
  ·
    refine ⟨429871264159793569789825025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286580842773195713193216683 429871264159793569789825025)
    ·
      refine ⟨322403448119845177342368769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429871264159793569789825025 322403448119845177342368769)
      ·
        refine ⟨241802586089883883006776577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322403448119845177342368769 241802586089883883006776577)
        ·
          refine ⟨181351939567412912255082433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241802586089883883006776577 181351939567412912255082433)
          ·
            refine ⟨136013954675559684191311825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181351939567412912255082433 136013954675559684191311825)
            ·
              refine ⟨102010466006669763143483869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136013954675559684191311825 102010466006669763143483869)
              ·
                refine ⟨38253924752501161178806451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102010466006669763143483869 38253924752501161178806451)
                ·
                  refine ⟨57380887128751741768209677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38253924752501161178806451 57380887128751741768209677)
                  ·
                    refine ⟨21517832673281903163078629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57380887128751741768209677 21517832673281903163078629)
                    ·
                      refine ⟨4034593626240356843077243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21517832673281903163078629 4034593626240356843077243)
                      ·
                        rfl

theorem cell23_7857343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_7857343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857343 prefixEnd_7857343 := by exact prefixLift 7857343
  have htrace : WordTrace (prefixWord ++ tailWord_7857343) baseStart_7857343 baseEnd_7857343 := by
    simpa [prefixWord, tailWord_7857343, baseEnd_7857343] using wordTrace_append hprefix tailTrace_7857343
  have hstable : (prefixWord ++ tailWord_7857343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857343).length < 2 ^ (prefixWord ++ tailWord_7857343).sum := by decide
  have hdescent : baseEnd_7857343 < baseStart_7857343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857370 : List Nat := [3, 1, 1, 2, 2, 1, 1, 5, 3, 4]
def baseStart_7857370 : Nat := 118140960795 + 7857370 * 2 ^ 59
def prefixEnd_7857370 : Nat := 4983230072969 + 3 ^ 40 * 7857370 * 2
def baseEnd_7857370 : Nat := 1344869163406009412479873

theorem tailTrace_7857370 : CollatzResearch.WordTrace tailWord_7857370 prefixEnd_7857370 1344869163406009412479873 := by
  unfold tailWord_7857370
  simp only [CollatzResearch.WordTrace]
  refine ⟨71645456886024474201112391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191054551696065264536299709 71645456886024474201112391)
  ·
    refine ⟨107468185329036711301668587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71645456886024474201112391 107468185329036711301668587)
    ·
      refine ⟨161202277993555066952502881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107468185329036711301668587 161202277993555066952502881)
      ·
        refine ⟨120901708495166300214377161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161202277993555066952502881 120901708495166300214377161)
        ·
          refine ⟨90676281371374725160782871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120901708495166300214377161 90676281371374725160782871)
          ·
            refine ⟨136014422057062087741174307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90676281371374725160782871 136014422057062087741174307)
            ·
              refine ⟨204021633085593131611761461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136014422057062087741174307 204021633085593131611761461)
              ·
                refine ⟨19127028101774356088602637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204021633085593131611761461 19127028101774356088602637)
                ·
                  refine ⟨7172635538165383533225989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19127028101774356088602637 7172635538165383533225989)
                  ·
                    refine ⟨1344869163406009412479873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7172635538165383533225989 1344869163406009412479873)
                    ·
                      rfl

theorem cell23_7857370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_7857370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857370 prefixEnd_7857370 := by exact prefixLift 7857370
  have htrace : WordTrace (prefixWord ++ tailWord_7857370) baseStart_7857370 baseEnd_7857370 := by
    simpa [prefixWord, tailWord_7857370, baseEnd_7857370] using wordTrace_append hprefix tailTrace_7857370
  have hstable : (prefixWord ++ tailWord_7857370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857370).length < 2 ^ (prefixWord ++ tailWord_7857370).sum := by decide
  have hdescent : baseEnd_7857370 < baseStart_7857370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857377 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 2, 4, 2]
def baseStart_7857377 : Nat := 118140960795 + 7857377 * 2 ^ 59
def prefixEnd_7857377 : Nat := 4983230072969 + 3 ^ 40 * 7857377 * 2
def baseEnd_7857377 : Nat := 4034611084582609710052087

theorem tailTrace_7857377 : CollatzResearch.WordTrace tailWord_7857377 prefixEnd_7857377 4034611084582609710052087 := by
  unfold tailWord_7857377
  simp only [CollatzResearch.WordTrace]
  refine ⟨286582082855072536999954385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191054721903381691333302923 286582082855072536999954385)
  ·
    refine ⟨214936562141304402749965789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286582082855072536999954385 214936562141304402749965789)
    ·
      refine ⟨80601210802989151031237171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214936562141304402749965789 80601210802989151031237171)
      ·
        refine ⟨120901816204483726546855757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80601210802989151031237171 120901816204483726546855757)
        ·
          refine ⟨45338181076681397455070909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120901816204483726546855757 45338181076681397455070909)
          ·
            refine ⟨17001817903755524045651591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45338181076681397455070909 17001817903755524045651591)
            ·
              refine ⟨25502726855633286068477387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17001817903755524045651591 25502726855633286068477387)
              ·
                refine ⟨38254090283449929102716081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25502726855633286068477387 38254090283449929102716081)
                ·
                  refine ⟨28690567712587446827037061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38254090283449929102716081 28690567712587446827037061)
                  ·
                    refine ⟨5379481446110146280069449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28690567712587446827037061 5379481446110146280069449)
                    ·
                      refine ⟨4034611084582609710052087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5379481446110146280069449 4034611084582609710052087)
                      ·
                        rfl

theorem cell23_7857377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_7857377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857377 prefixEnd_7857377 := by exact prefixLift 7857377
  have htrace : WordTrace (prefixWord ++ tailWord_7857377) baseStart_7857377 baseEnd_7857377 := by
    simpa [prefixWord, tailWord_7857377, baseEnd_7857377] using wordTrace_append hprefix tailTrace_7857377
  have hstable : (prefixWord ++ tailWord_7857377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857377).length < 2 ^ (prefixWord ++ tailWord_7857377).sum := by decide
  have hdescent : baseEnd_7857377 < baseStart_7857377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857380 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 4, 2, 3]
def baseStart_7857380 : Nat := 118140960795 + 7857380 * 2 ^ 59
def prefixEnd_7857380 : Nat := 4983230072969 + 3 ^ 40 * 7857380 * 2
def baseEnd_7857380 : Nat := 4034612625024573198314573

theorem tailTrace_7857380 : CollatzResearch.WordTrace tailWord_7857380 prefixEnd_7857380 4034612625024573198314573 := by
  unfold tailWord_7857380
  simp only [CollatzResearch.WordTrace]
  refine ⟨143291096137030834256156797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191054794849374445674875729 143291096137030834256156797)
  ·
    refine ⟨53734161051386562846058799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143291096137030834256156797 53734161051386562846058799)
    ·
      refine ⟨80601241577079844269088199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53734161051386562846058799 80601241577079844269088199)
      ·
        refine ⟨120901862365619766403632299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80601241577079844269088199 120901862365619766403632299)
        ·
          refine ⟨181352793548429649605448449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120901862365619766403632299 181352793548429649605448449)
          ·
            refine ⟨136014595161322237204086337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181352793548429649605448449 136014595161322237204086337)
            ·
              refine ⟨102010946370991677903064753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136014595161322237204086337 102010946370991677903064753)
              ·
                refine ⟨76508209778243758427298565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102010946370991677903064753 76508209778243758427298565)
                ·
                  refine ⟨14345289333420704705118481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76508209778243758427298565 14345289333420704705118481)
                  ·
                    refine ⟨10758967000065528528838861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14345289333420704705118481 10758967000065528528838861)
                    ·
                      refine ⟨4034612625024573198314573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10758967000065528528838861 4034612625024573198314573)
                      ·
                        rfl

theorem cell23_7857380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_7857380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857380 prefixEnd_7857380 := by exact prefixLift 7857380
  have htrace : WordTrace (prefixWord ++ tailWord_7857380) baseStart_7857380 baseEnd_7857380 := by
    simpa [prefixWord, tailWord_7857380, baseEnd_7857380] using wordTrace_append hprefix tailTrace_7857380
  have hstable : (prefixWord ++ tailWord_7857380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857380).length < 2 ^ (prefixWord ++ tailWord_7857380).sum := by decide
  have hdescent : baseEnd_7857380 < baseStart_7857380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857394 : List Nat := [3, 2, 1, 3, 3, 2, 1, 1, 2, 1, 4]
def baseStart_7857394 : Nat := 118140960795 + 7857394 * 2 ^ 59
def prefixEnd_7857394 : Nat := 4983230072969 + 3 ^ 40 * 7857394 * 2
def baseEnd_7857394 : Nat := 4034619813753736143539509

theorem tailTrace_7857394 : CollatzResearch.WordTrace tailWord_7857394 prefixEnd_7857394 4034619813753736143539509 := by
  unfold tailWord_7857394
  simp only [CollatzResearch.WordTrace]
  refine ⟨71645675724002737225830809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191055135264007299268882157 71645675724002737225830809)
  ·
    refine ⟨53734256793002052919373107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71645675724002737225830809 53734256793002052919373107)
    ·
      refine ⟨80601385189503079379059661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53734256793002052919373107 80601385189503079379059661)
      ·
        refine ⟨30225519446063654767147373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80601385189503079379059661 30225519446063654767147373)
        ·
          refine ⟨11334569792273870537680265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30225519446063654767147373 11334569792273870537680265)
          ·
            refine ⟨8500927344205402903260199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11334569792273870537680265 8500927344205402903260199)
            ·
              refine ⟨12751391016308104354890299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8500927344205402903260199 12751391016308104354890299)
              ·
                refine ⟨19127086524462156532335449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12751391016308104354890299 19127086524462156532335449)
                ·
                  refine ⟨14345314893346617399251587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19127086524462156532335449 14345314893346617399251587)
                  ·
                    refine ⟨21517972340019926098877381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14345314893346617399251587 21517972340019926098877381)
                    ·
                      refine ⟨4034619813753736143539509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21517972340019926098877381 4034619813753736143539509)
                      ·
                        rfl

theorem cell23_7857394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_7857394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857394 prefixEnd_7857394 := by exact prefixLift 7857394
  have htrace : WordTrace (prefixWord ++ tailWord_7857394) baseStart_7857394 baseEnd_7857394 := by
    simpa [prefixWord, tailWord_7857394, baseEnd_7857394] using wordTrace_append hprefix tailTrace_7857394
  have hstable : (prefixWord ++ tailWord_7857394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857394).length < 2 ^ (prefixWord ++ tailWord_7857394).sum := by decide
  have hdescent : baseEnd_7857394 < baseStart_7857394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857461 : List Nat := [1, 3, 3, 1, 2, 2, 3, 3, 1, 1, 3]
def baseStart_7857461 : Nat := 118140960795 + 7857461 * 2 ^ 59
def prefixEnd_7857461 : Nat := 4983230072969 + 3 ^ 40 * 7857461 * 2
def baseEnd_7857461 : Nat := 4034654216957587381401701

theorem tailTrace_7857461 : CollatzResearch.WordTrace tailWord_7857461 prefixEnd_7857461 4034654216957587381401701 := by
  unfold tailWord_7857461
  simp only [CollatzResearch.WordTrace]
  refine ⟨286585146586768219346012237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191056764391178812897341491 286585146586768219346012237)
  ·
    refine ⟨107469429970038082254754589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286585146586768219346012237 107469429970038082254754589)
    ·
      refine ⟨40301036238764280845532971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107469429970038082254754589 40301036238764280845532971)
      ·
        refine ⟨60451554358146421268299457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40301036238764280845532971 60451554358146421268299457)
        ·
          refine ⟨45338665768609815951224593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60451554358146421268299457 45338665768609815951224593)
          ·
            refine ⟨34003999326457361963418445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45338665768609815951224593 34003999326457361963418445)
            ·
              refine ⟨12751499747421510736281917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34003999326457361963418445 12751499747421510736281917)
              ·
                refine ⟨4781812405283066526105719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12751499747421510736281917 4781812405283066526105719)
                ·
                  refine ⟨7172718607924599789158579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4781812405283066526105719 7172718607924599789158579)
                  ·
                    refine ⟨10759077911886899683737869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7172718607924599789158579 10759077911886899683737869)
                    ·
                      refine ⟨4034654216957587381401701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10759077911886899683737869 4034654216957587381401701)
                      ·
                        rfl

theorem cell23_7857461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_7857461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857461 prefixEnd_7857461 := by exact prefixLift 7857461
  have htrace : WordTrace (prefixWord ++ tailWord_7857461) baseStart_7857461 baseEnd_7857461 := by
    simpa [prefixWord, tailWord_7857461, baseEnd_7857461] using wordTrace_append hprefix tailTrace_7857461
  have hstable : (prefixWord ++ tailWord_7857461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857461).length < 2 ^ (prefixWord ++ tailWord_7857461).sum := by decide
  have hdescent : baseEnd_7857461 < baseStart_7857461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857504 : List Nat := [2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 3]
def baseStart_7857504 : Nat := 118140960795 + 7857504 * 2 ^ 59
def prefixEnd_7857504 : Nat := 4983230072969 + 3 ^ 40 * 7857504 * 2
def baseEnd_7857504 : Nat := 4034676296625730713164003

theorem tailTrace_7857504 : CollatzResearch.WordTrace tailWord_7857504 prefixEnd_7857504 4034676296625730713164003 := by
  unfold tailWord_7857504
  simp only [CollatzResearch.WordTrace]
  refine ⟨143293357462806218844913783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191057809950408291793218377 143293357462806218844913783)
  ·
    refine ⟨214940036194209328267370675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143293357462806218844913783 214940036194209328267370675)
    ·
      refine ⟨322410054291313992401056013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214940036194209328267370675 322410054291313992401056013)
      ·
        refine ⟨120903770359242747150396005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322410054291313992401056013 120903770359242747150396005)
        ·
          refine ⟨22669456942358015090699251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120903770359242747150396005 22669456942358015090699251)
          ·
            refine ⟨34004185413537022636048877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22669456942358015090699251 34004185413537022636048877)
            ·
              refine ⟨12751569530076383488518329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34004185413537022636048877 12751569530076383488518329)
              ·
                refine ⟨9563677147557287616388747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12751569530076383488518329 9563677147557287616388747)
                ·
                  refine ⟨14345515721335931424583121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9563677147557287616388747 14345515721335931424583121)
                  ·
                    refine ⟨10759136791001948568437341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14345515721335931424583121 10759136791001948568437341)
                    ·
                      refine ⟨4034676296625730713164003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10759136791001948568437341 4034676296625730713164003)
                      ·
                        rfl

theorem cell23_7857504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_7857504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857504 prefixEnd_7857504 := by exact prefixLift 7857504
  have htrace : WordTrace (prefixWord ++ tailWord_7857504) baseStart_7857504 baseEnd_7857504 := by
    simpa [prefixWord, tailWord_7857504, baseEnd_7857504] using wordTrace_append hprefix tailTrace_7857504
  have hstable : (prefixWord ++ tailWord_7857504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857504).length < 2 ^ (prefixWord ++ tailWord_7857504).sum := by decide
  have hdescent : baseEnd_7857504 < baseStart_7857504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857514 : List Nat := [3, 1, 3, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_7857514 : Nat := 118140960795 + 7857514 * 2 ^ 59
def prefixEnd_7857514 : Nat := 4983230072969 + 3 ^ 40 * 7857514 * 2
def baseEnd_7857514 : Nat := 4034681431432275674038957

theorem tailTrace_7857514 : CollatzResearch.WordTrace tailWord_7857514 prefixEnd_7857514 4034681431432275674038957 := by
  unfold tailWord_7857514
  simp only [CollatzResearch.WordTrace]
  refine ⟨71646769913894052349422899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191058053103717472931794397 71646769913894052349422899)
  ·
    refine ⟨107470154870841078524134349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71646769913894052349422899 107470154870841078524134349)
    ·
      refine ⟨40301308076565404446550381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107470154870841078524134349 40301308076565404446550381)
      ·
        refine ⟨15112990528712026667456393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40301308076565404446550381 15112990528712026667456393)
        ·
          refine ⟨11334742896534020000592295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15112990528712026667456393 11334742896534020000592295)
          ·
            refine ⟨17002114344801030000888443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11334742896534020000592295 17002114344801030000888443)
            ·
              refine ⟨25503171517201545001332665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17002114344801030000888443 25503171517201545001332665)
              ·
                refine ⟨19127378637901158750999499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25503171517201545001332665 19127378637901158750999499)
                ·
                  refine ⟨28691067956851738126499249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19127378637901158750999499 28691067956851738126499249)
                  ·
                    refine ⟨21518300967638803594874437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28691067956851738126499249 21518300967638803594874437)
                    ·
                      refine ⟨4034681431432275674038957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21518300967638803594874437 4034681431432275674038957)
                      ·
                        rfl

theorem cell23_7857514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_7857514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857514 prefixEnd_7857514 := by exact prefixLift 7857514
  have htrace : WordTrace (prefixWord ++ tailWord_7857514) baseStart_7857514 baseEnd_7857514 := by
    simpa [prefixWord, tailWord_7857514, baseEnd_7857514] using wordTrace_append hprefix tailTrace_7857514
  have hstable : (prefixWord ++ tailWord_7857514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857514).length < 2 ^ (prefixWord ++ tailWord_7857514).sum := by decide
  have hdescent : baseEnd_7857514 < baseStart_7857514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857517 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_7857517 : Nat := 118140960795 + 7857517 * 2 ^ 59
def prefixEnd_7857517 : Nat := 4983230072969 + 3 ^ 40 * 7857517 * 2
def baseEnd_7857517 : Nat := 4034682971874239162301443

theorem tailTrace_7857517 : CollatzResearch.WordTrace tailWord_7857517 prefixEnd_7857517 4034682971874239162301443 := by
  unfold tailWord_7857517
  simp only [CollatzResearch.WordTrace]
  refine ⟨286587189074565340910050805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191058126049710227273367203 286587189074565340910050805)
  ·
    refine ⟨26867548975740500710317263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286587189074565340910050805 26867548975740500710317263)
    ·
      refine ⟨40301323463610751065475895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26867548975740500710317263 40301323463610751065475895)
      ·
        refine ⟨60451985195416126598213843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40301323463610751065475895 60451985195416126598213843)
        ·
          refine ⟨90677977793124189897320765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60451985195416126598213843 90677977793124189897320765)
          ·
            refine ⟨34004241672421571211495287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90677977793124189897320765 34004241672421571211495287)
            ·
              refine ⟨51006362508632356817242931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34004241672421571211495287 51006362508632356817242931)
              ·
                refine ⟨76509543762948535225864397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51006362508632356817242931 76509543762948535225864397)
                ·
                  refine ⟨28691078911105700709699149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76509543762948535225864397 28691078911105700709699149)
                  ·
                    refine ⟨10759154591664637766137181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28691078911105700709699149 10759154591664637766137181)
                    ·
                      refine ⟨4034682971874239162301443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10759154591664637766137181 4034682971874239162301443)
                      ·
                        rfl

theorem cell23_7857517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_7857517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857517 prefixEnd_7857517 := by exact prefixLift 7857517
  have htrace : WordTrace (prefixWord ++ tailWord_7857517) baseStart_7857517 baseEnd_7857517 := by
    simpa [prefixWord, tailWord_7857517, baseEnd_7857517] using wordTrace_append hprefix tailTrace_7857517
  have hstable : (prefixWord ++ tailWord_7857517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857517).length < 2 ^ (prefixWord ++ tailWord_7857517).sum := by decide
  have hdescent : baseEnd_7857517 < baseStart_7857517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857518 : List Nat := [4, 1, 2, 4, 1, 1, 3, 1, 1, 1, 4]
def baseStart_7857518 : Nat := 118140960795 + 7857518 * 2 ^ 59
def prefixEnd_7857518 : Nat := 4983230072969 + 3 ^ 40 * 7857518 * 2
def baseEnd_7857518 : Nat := 4034683485354893658388939

theorem tailTrace_7857518 : CollatzResearch.WordTrace tailWord_7857518 prefixEnd_7857518 4034683485354893658388939 := by
  unfold tailWord_7857518
  simp only [CollatzResearch.WordTrace]
  refine ⟨35823403193445214760104651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191058150365041145387224805 35823403193445214760104651)
  ·
    refine ⟨53735104790167822140156977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35823403193445214760104651 53735104790167822140156977)
    ·
      refine ⟨40301328592625866605117733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53735104790167822140156977 40301328592625866605117733)
      ·
        refine ⟨7556499111117349988459575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40301328592625866605117733 7556499111117349988459575)
        ·
          refine ⟨11334748666676024982689363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7556499111117349988459575 11334748666676024982689363)
          ·
            refine ⟨17002123000014037474034045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11334748666676024982689363 17002123000014037474034045)
            ·
              refine ⟨6375796125005264052762767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17002123000014037474034045 6375796125005264052762767)
              ·
                refine ⟨9563694187507896079144151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6375796125005264052762767 9563694187507896079144151)
                ·
                  refine ⟨14345541281261844118716227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9563694187507896079144151 14345541281261844118716227)
                  ·
                    refine ⟨21518311921892766178074341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14345541281261844118716227 21518311921892766178074341)
                    ·
                      refine ⟨4034683485354893658388939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21518311921892766178074341 4034683485354893658388939)
                      ·
                        rfl

theorem cell23_7857518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_7857518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857518 prefixEnd_7857518 := by exact prefixLift 7857518
  have htrace : WordTrace (prefixWord ++ tailWord_7857518) baseStart_7857518 baseEnd_7857518 := by
    simpa [prefixWord, tailWord_7857518, baseEnd_7857518] using wordTrace_append hprefix tailTrace_7857518
  have hstable : (prefixWord ++ tailWord_7857518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857518).length < 2 ^ (prefixWord ++ tailWord_7857518).sum := by decide
  have hdescent : baseEnd_7857518 < baseStart_7857518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857544 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 3, 3, 2]
def baseStart_7857544 : Nat := 118140960795 + 7857544 * 2 ^ 59
def prefixEnd_7857544 : Nat := 4983230072969 + 3 ^ 40 * 7857544 * 2
def baseEnd_7857544 : Nat := 4034696835851910556663819

theorem tailTrace_7857544 : CollatzResearch.WordTrace tailWord_7857544 prefixEnd_7857544 4034696835851910556663819 := by
  unfold tailWord_7857544
  simp only [CollatzResearch.WordTrace]
  refine ⟨143294086922733762260641843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191058782563645016347522457 143294086922733762260641843)
  ·
    refine ⟨214941130384100643390962765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143294086922733762260641843 214941130384100643390962765)
    ·
      refine ⟨80602923894037741271611037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214941130384100643390962765 80602923894037741271611037)
      ·
        refine ⟨30226096460264152976854139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80602923894037741271611037 30226096460264152976854139)
        ·
          refine ⟨45339144690396229465281209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30226096460264152976854139 45339144690396229465281209)
          ·
            refine ⟨34004358517797172098960907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45339144690396229465281209 34004358517797172098960907)
            ·
              refine ⟨51006537776695758148441361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34004358517797172098960907 51006537776695758148441361)
              ·
                refine ⟨38254903332521818611331021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51006537776695758148441361 38254903332521818611331021)
                ·
                  refine ⟨14345588749695681979249133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38254903332521818611331021 14345588749695681979249133)
                  ·
                    refine ⟨5379595781135880742218425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14345588749695681979249133 5379595781135880742218425)
                    ·
                      refine ⟨4034696835851910556663819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5379595781135880742218425 4034696835851910556663819)
                      ·
                        rfl

theorem cell23_7857544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_7857544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857544 prefixEnd_7857544 := by exact prefixLift 7857544
  have htrace : WordTrace (prefixWord ++ tailWord_7857544) baseStart_7857544 baseEnd_7857544 := by
    simpa [prefixWord, tailWord_7857544, baseEnd_7857544] using wordTrace_append hprefix tailTrace_7857544
  have hstable : (prefixWord ++ tailWord_7857544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857544).length < 2 ^ (prefixWord ++ tailWord_7857544).sum := by decide
  have hdescent : baseEnd_7857544 < baseStart_7857544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857597 : List Nat := [1, 4, 1, 2, 2, 1, 4, 1, 7]
def baseStart_7857597 : Nat := 118140960795 + 7857597 * 2 ^ 59
def prefixEnd_7857597 : Nat := 4983230072969 + 3 ^ 40 * 7857597 * 2
def baseEnd_7857597 : Nat := 448302672258510983255675

theorem tailTrace_7857597 : CollatzResearch.WordTrace tailWord_7857597 prefixEnd_7857597 448302672258510983255675 := by
  unfold tailWord_7857597
  simp only [CollatzResearch.WordTrace]
  refine ⟨286590106914275514572963045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191060071276183676381975363 286590106914275514572963045)
  ·
    refine ⟨53735645046426658982430571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286590106914275514572963045 53735645046426658982430571)
    ·
      refine ⟨80603467569639988473645857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53735645046426658982430571 80603467569639988473645857)
      ·
        refine ⟨60452600677229991355234393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80603467569639988473645857 60452600677229991355234393)
        ·
          refine ⟨45339450507922493516425795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60452600677229991355234393 45339450507922493516425795)
          ·
            refine ⟨68009175761883740274638693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45339450507922493516425795 68009175761883740274638693)
            ·
              refine ⟨12751720455353201301494755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68009175761883740274638693 12751720455353201301494755)
              ·
                refine ⟨19127580683029801952242133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12751720455353201301494755 19127580683029801952242133)
                ·
                  refine ⟨448302672258510983255675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19127580683029801952242133 448302672258510983255675)
                  ·
                    rfl

theorem cell23_7857597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_7857597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857597 prefixEnd_7857597 := by exact prefixLift 7857597
  have htrace : WordTrace (prefixWord ++ tailWord_7857597) baseStart_7857597 baseEnd_7857597 := by
    simpa [prefixWord, tailWord_7857597, baseEnd_7857597] using wordTrace_append hprefix tailTrace_7857597
  have hstable : (prefixWord ++ tailWord_7857597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857597).length < 2 ^ (prefixWord ++ tailWord_7857597).sum := by decide
  have hdescent : baseEnd_7857597 < baseStart_7857597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857602 : List Nat := [3, 5, 2, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_7857602 : Nat := 118140960795 + 7857602 * 2 ^ 59
def prefixEnd_7857602 : Nat := 4983230072969 + 3 ^ 40 * 7857602 * 2
def baseEnd_7857602 : Nat := 4034726617729871329738553

theorem tailTrace_7857602 : CollatzResearch.WordTrace tailWord_7857602 prefixEnd_7857602 4034726617729871329738553 := by
  unfold tailWord_7857602
  simp only [CollatzResearch.WordTrace]
  refine ⟨71647572319814350106723765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191060192852838266951263373 71647572319814350106723765)
  ·
    refine ⟨6716959904982595322505353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71647572319814350106723765 6716959904982595322505353)
    ·
      refine ⟨5037719928736946491879015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6716959904982595322505353 5037719928736946491879015)
      ·
        refine ⟨7556579893105419737818523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5037719928736946491879015 7556579893105419737818523)
        ·
          refine ⟨11334869839658129606727785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7556579893105419737818523 11334869839658129606727785)
          ·
            refine ⟨8501152379743597205045839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11334869839658129606727785 8501152379743597205045839)
            ·
              refine ⟨12751728569615395807568759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8501152379743597205045839 12751728569615395807568759)
              ·
                refine ⟨19127592854423093711353139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12751728569615395807568759 19127592854423093711353139)
                ·
                  refine ⟨28691389281634640567029709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19127592854423093711353139 28691389281634640567029709)
                  ·
                    refine ⟨10759270980612990212636141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28691389281634640567029709 10759270980612990212636141)
                    ·
                      refine ⟨4034726617729871329738553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10759270980612990212636141 4034726617729871329738553)
                      ·
                        rfl

theorem cell23_7857602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_7857602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857602 prefixEnd_7857602 := by exact prefixLift 7857602
  have htrace : WordTrace (prefixWord ++ tailWord_7857602) baseStart_7857602 baseEnd_7857602 := by
    simpa [prefixWord, tailWord_7857602, baseEnd_7857602] using wordTrace_append hprefix tailTrace_7857602
  have hstable : (prefixWord ++ tailWord_7857602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857602).length < 2 ^ (prefixWord ++ tailWord_7857602).sum := by decide
  have hdescent : baseEnd_7857602 < baseStart_7857602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857604 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_7857604 : Nat := 118140960795 + 7857604 * 2 ^ 59
def prefixEnd_7857604 : Nat := 4983230072969 + 3 ^ 40 * 7857604 * 2
def baseEnd_7857604 : Nat := 4034727644691180321913543

theorem tailTrace_7857604 : CollatzResearch.WordTrace tailWord_7857604 prefixEnd_7857604 4034727644691180321913543 := by
  unfold tailWord_7857604
  simp only [CollatzResearch.WordTrace]
  refine ⟨143295181112625077384233933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191060241483500103178978577 143295181112625077384233933)
  ·
    refine ⟨53735692917234404019087725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143295181112625077384233933 53735692917234404019087725)
    ·
      refine ⟨20150884843962901507157897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53735692917234404019087725 20150884843962901507157897)
      ·
        refine ⟨15113163632972176130368423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20150884843962901507157897 15113163632972176130368423)
        ·
          refine ⟨22669745449458264195552635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15113163632972176130368423 22669745449458264195552635)
          ·
            refine ⟨34004618174187396293328953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22669745449458264195552635 34004618174187396293328953)
            ·
              refine ⟨25503463630640547219996715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34004618174187396293328953 25503463630640547219996715)
              ·
                refine ⟨38255195445960820829995073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25503463630640547219996715 38255195445960820829995073)
                ·
                  refine ⟨28691396584470615622496305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38255195445960820829995073 28691396584470615622496305)
                  ·
                    refine ⟨21518547438352961716872229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28691396584470615622496305 21518547438352961716872229)
                    ·
                      refine ⟨4034727644691180321913543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21518547438352961716872229 4034727644691180321913543)
                      ·
                        rfl

theorem cell23_7857604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_7857604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857604 prefixEnd_7857604 := by exact prefixLift 7857604
  have htrace : WordTrace (prefixWord ++ tailWord_7857604) baseStart_7857604 baseEnd_7857604 := by
    simpa [prefixWord, tailWord_7857604, baseEnd_7857604] using wordTrace_append hprefix tailTrace_7857604
  have hstable : (prefixWord ++ tailWord_7857604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857604).length < 2 ^ (prefixWord ++ tailWord_7857604).sum := by decide
  have hdescent : baseEnd_7857604 < baseStart_7857604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857607 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 3]
def baseStart_7857607 : Nat := 118140960795 + 7857607 * 2 ^ 59
def prefixEnd_7857607 : Nat := 4983230072969 + 3 ^ 40 * 7857607 * 2
def baseEnd_7857607 : Nat := 4034729185133143810176029

theorem tailTrace_7857607 : CollatzResearch.WordTrace tailWord_7857607 prefixEnd_7857607 4034729185133143810176029 := by
  unfold tailWord_7857607
  simp only [CollatzResearch.WordTrace]
  refine ⟨286590471644239286280827075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191060314429492857520551383 286590471644239286280827075)
  ·
    refine ⟨429885707466358929421240613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286590471644239286280827075 429885707466358929421240613)
    ·
      refine ⟨80603570149942299266482615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 429885707466358929421240613 80603570149942299266482615)
      ·
        refine ⟨120905355224913448899723923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80603570149942299266482615 120905355224913448899723923)
        ·
          refine ⟨181358032837370173349585885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120905355224913448899723923 181358032837370173349585885)
          ·
            refine ⟨68009262314013815006094707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181358032837370173349585885 68009262314013815006094707)
            ·
              refine ⟨102013893471020722509142061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68009262314013815006094707 102013893471020722509142061)
              ·
                refine ⟨38255210051632770940928273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102013893471020722509142061 38255210051632770940928273)
                ·
                  refine ⟨28691407538724578205696205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38255210051632770940928273 28691407538724578205696205)
                  ·
                    refine ⟨10759277827021716827136077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28691407538724578205696205 10759277827021716827136077)
                    ·
                      refine ⟨4034729185133143810176029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10759277827021716827136077 4034729185133143810176029)
                      ·
                        rfl

theorem cell23_7857607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_7857607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857607 prefixEnd_7857607 := by exact prefixLift 7857607
  have htrace : WordTrace (prefixWord ++ tailWord_7857607) baseStart_7857607 baseEnd_7857607 := by
    simpa [prefixWord, tailWord_7857607, baseEnd_7857607] using wordTrace_append hprefix tailTrace_7857607
  have hstable : (prefixWord ++ tailWord_7857607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857607).length < 2 ^ (prefixWord ++ tailWord_7857607).sum := by decide
  have hdescent : baseEnd_7857607 < baseStart_7857607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857608 : List Nat := [2, 1, 3, 1, 3, 1, 5, 1, 2, 2, 2]
def baseStart_7857608 : Nat := 118140960795 + 7857608 * 2 ^ 59
def prefixEnd_7857608 : Nat := 4983230072969 + 3 ^ 40 * 7857608 * 2
def baseEnd_7857608 : Nat := 4034729698613798306263525

theorem tailTrace_7857608 : CollatzResearch.WordTrace tailWord_7857608 prefixEnd_7857608 4034729698613798306263525 := by
  unfold tailWord_7857608
  simp only [CollatzResearch.WordTrace]
  refine ⟨143295254058617831725806739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191060338744823775634408985 143295254058617831725806739)
  ·
    refine ⟨214942881087926747588710109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143295254058617831725806739 214942881087926747588710109)
    ·
      refine ⟨80603580407972530345766291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214942881087926747588710109 80603580407972530345766291)
      ·
        refine ⟨120905370611958795518649437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80603580407972530345766291 120905370611958795518649437)
        ·
          refine ⟨45339513979484548319493539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120905370611958795518649437 45339513979484548319493539)
          ·
            refine ⟨68009270969226822479240309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45339513979484548319493539 68009270969226822479240309)
            ·
              refine ⟨6375869153365014607428779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68009270969226822479240309 6375869153365014607428779)
              ·
                refine ⟨9563803730047521911143169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6375869153365014607428779 9563803730047521911143169)
                ·
                  refine ⟨7172852797535641433357377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9563803730047521911143169 7172852797535641433357377)
                  ·
                    refine ⟨5379639598151731075018033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7172852797535641433357377 5379639598151731075018033)
                    ·
                      refine ⟨4034729698613798306263525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5379639598151731075018033 4034729698613798306263525)
                      ·
                        rfl

theorem cell23_7857608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_7857608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857608 prefixEnd_7857608 := by exact prefixLift 7857608
  have htrace : WordTrace (prefixWord ++ tailWord_7857608) baseStart_7857608 baseEnd_7857608 := by
    simpa [prefixWord, tailWord_7857608, baseEnd_7857608] using wordTrace_append hprefix tailTrace_7857608
  have hstable : (prefixWord ++ tailWord_7857608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857608).length < 2 ^ (prefixWord ++ tailWord_7857608).sum := by decide
  have hdescent : baseEnd_7857608 < baseStart_7857608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857647 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 4]
def baseStart_7857647 : Nat := 118140960795 + 7857647 * 2 ^ 59
def prefixEnd_7857647 : Nat := 4983230072969 + 3 ^ 40 * 7857647 * 2
def baseEnd_7857647 : Nat := 4034749724359323653675845

theorem tailTrace_7857647 : CollatzResearch.WordTrace tailWord_7857647 prefixEnd_7857647 4034749724359323653675845 := by
  unfold tailWord_7857647
  simp only [CollatzResearch.WordTrace]
  refine ⟨286591930564094373112283195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191061287042729582074855463 286591930564094373112283195)
  ·
    refine ⟨429887895846141559668424793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286591930564094373112283195 429887895846141559668424793)
    ·
      refine ⟨322415921884606169751318595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429887895846141559668424793 322415921884606169751318595)
      ·
        refine ⟨483623882826909254626977893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322415921884606169751318595 483623882826909254626977893)
        ·
          refine ⟨90679478030045485242558355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 483623882826909254626977893 90679478030045485242558355)
          ·
            refine ⟨136019217045068227863837533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90679478030045485242558355 136019217045068227863837533)
            ·
              refine ⟨51007206391900585448939075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136019217045068227863837533 51007206391900585448939075)
              ·
                refine ⟨76510809587850878173408613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51007206391900585448939075 76510809587850878173408613)
                ·
                  refine ⟨14345776797722039657514115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76510809587850878173408613 14345776797722039657514115)
                  ·
                    refine ⟨21518665196583059486271173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14345776797722039657514115 21518665196583059486271173)
                    ·
                      refine ⟨4034749724359323653675845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21518665196583059486271173 4034749724359323653675845)
                      ·
                        rfl

theorem cell23_7857647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 4].length) (baseStart_7857647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857647 prefixEnd_7857647 := by exact prefixLift 7857647
  have htrace : WordTrace (prefixWord ++ tailWord_7857647) baseStart_7857647 baseEnd_7857647 := by
    simpa [prefixWord, tailWord_7857647, baseEnd_7857647] using wordTrace_append hprefix tailTrace_7857647
  have hstable : (prefixWord ++ tailWord_7857647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857647).length < 2 ^ (prefixWord ++ tailWord_7857647).sum := by decide
  have hdescent : baseEnd_7857647 < baseStart_7857647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857654 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_7857654 : Nat := 118140960795 + 7857654 * 2 ^ 59
def prefixEnd_7857654 : Nat := 4983230072969 + 3 ^ 40 * 7857654 * 2
def baseEnd_7857654 : Nat := 4034753318723905126288313

theorem tailTrace_7857654 : CollatzResearch.WordTrace tailWord_7857654 prefixEnd_7857654 4034753318723905126288313 := by
  unfold tailWord_7857654
  simp only [CollatzResearch.WordTrace]
  refine ⟨17912011617191813331736751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191061457250046008871858677 17912011617191813331736751)
  ·
    refine ⟨26868017425787719997605127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17912011617191813331736751 26868017425787719997605127)
    ·
      refine ⟨40302026138681579996407691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26868017425787719997605127 40302026138681579996407691)
      ·
        refine ⟨60453039208022369994611537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40302026138681579996407691 60453039208022369994611537)
        ·
          refine ⟨45339779406016777495958653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60453039208022369994611537 45339779406016777495958653)
          ·
            refine ⟨17002417277256291560984495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45339779406016777495958653 17002417277256291560984495)
            ·
              refine ⟨25503625915884437341476743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17002417277256291560984495 25503625915884437341476743)
              ·
                refine ⟨38255438873826656012215115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25503625915884437341476743 38255438873826656012215115)
                ·
                  refine ⟨57383158310739984018322673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38255438873826656012215115 57383158310739984018322673)
                  ·
                    refine ⟨43037368733054988013742005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57383158310739984018322673 43037368733054988013742005)
                    ·
                      refine ⟨4034753318723905126288313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43037368733054988013742005 4034753318723905126288313)
                      ·
                        rfl

theorem cell23_7857654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_7857654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857654 prefixEnd_7857654 := by exact prefixLift 7857654
  have htrace : WordTrace (prefixWord ++ tailWord_7857654) baseStart_7857654 baseEnd_7857654 := by
    simpa [prefixWord, tailWord_7857654, baseEnd_7857654] using wordTrace_append hprefix tailTrace_7857654
  have hstable : (prefixWord ++ tailWord_7857654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857654).length < 2 ^ (prefixWord ++ tailWord_7857654).sum := by decide
  have hdescent : baseEnd_7857654 < baseStart_7857654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857667 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 3]
def baseStart_7857667 : Nat := 118140960795 + 7857667 * 2 ^ 59
def prefixEnd_7857667 : Nat := 4983230072969 + 3 ^ 40 * 7857667 * 2
def baseEnd_7857667 : Nat := 4034759993972413575425753

theorem tailTrace_7857667 : CollatzResearch.WordTrace tailWord_7857667 prefixEnd_7857667 4034759993972413575425753 := by
  unfold tailWord_7857667
  simp only [CollatzResearch.WordTrace]
  refine ⟨286592660024021916528011255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191061773349347944352007503 286592660024021916528011255)
  ·
    refine ⟨429888990036032874792016883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286592660024021916528011255 429888990036032874792016883)
    ·
      refine ⟨644833485054049312188025325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429888990036032874792016883 644833485054049312188025325)
      ·
        refine ⟨241812556895268492070509497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 644833485054049312188025325 241812556895268492070509497)
        ·
          refine ⟨181359417671451369052882123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241812556895268492070509497 181359417671451369052882123)
          ·
            refine ⟨272039126507177053579323185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181359417671451369052882123 272039126507177053579323185)
            ·
              refine ⟨204029344880382790184492389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272039126507177053579323185 204029344880382790184492389)
              ·
                refine ⟨38255502165071773159592323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204029344880382790184492389 38255502165071773159592323)
                ·
                  refine ⟨57383253247607659739388485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38255502165071773159592323 57383253247607659739388485)
                  ·
                    refine ⟨10759359983926436201135341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57383253247607659739388485 10759359983926436201135341)
                    ·
                      refine ⟨4034759993972413575425753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10759359983926436201135341 4034759993972413575425753)
                      ·
                        rfl

theorem cell23_7857667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_7857667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857667 prefixEnd_7857667 := by exact prefixLift 7857667
  have htrace : WordTrace (prefixWord ++ tailWord_7857667) baseStart_7857667 baseEnd_7857667 := by
    simpa [prefixWord, tailWord_7857667, baseEnd_7857667] using wordTrace_append hprefix tailTrace_7857667
  have hstable : (prefixWord ++ tailWord_7857667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857667).length < 2 ^ (prefixWord ++ tailWord_7857667).sum := by decide
  have hdescent : baseEnd_7857667 < baseStart_7857667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857751 : List Nat := [1, 1, 3, 2, 2, 3, 4, 1, 1, 5]
def baseStart_7857751 : Nat := 118140960795 + 7857751 * 2 ^ 59
def prefixEnd_7857751 : Nat := 4983230072969 + 3 ^ 40 * 7857751 * 2
def baseEnd_7857751 : Nat := 1344934375449130415591789

theorem tailTrace_7857751 : CollatzResearch.WordTrace tailWord_7857751 prefixEnd_7857751 1344934375449130415591789 := by
  unfold tailWord_7857751
  simp only [CollatzResearch.WordTrace]
  refine ⟨286595723755717598874069107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191063815837145065916046071 286595723755717598874069107)
  ·
    refine ⟨429893585633576398311103661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286595723755717598874069107 429893585633576398311103661)
    ·
      refine ⟨161210094612591149366663873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429893585633576398311103661 161210094612591149366663873)
      ·
        refine ⟨120907570959443362024997905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161210094612591149366663873 120907570959443362024997905)
        ·
          refine ⟨90680678219582521518748429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120907570959443362024997905 90680678219582521518748429)
          ·
            refine ⟨34005254332343445569530661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90680678219582521518748429 34005254332343445569530661)
            ·
              refine ⟨6375985187314396044286999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34005254332343445569530661 6375985187314396044286999)
              ·
                refine ⟨9563977780971594066430499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6375985187314396044286999 9563977780971594066430499)
                ·
                  refine ⟨14345966671457391099645749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9563977780971594066430499 14345966671457391099645749)
                  ·
                    refine ⟨1344934375449130415591789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14345966671457391099645749 1344934375449130415591789)
                    ·
                      rfl

theorem cell23_7857751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 1, 5].length) (baseStart_7857751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857751 prefixEnd_7857751 := by exact prefixLift 7857751
  have htrace : WordTrace (prefixWord ++ tailWord_7857751) baseStart_7857751 baseEnd_7857751 := by
    simpa [prefixWord, tailWord_7857751, baseEnd_7857751] using wordTrace_append hprefix tailTrace_7857751
  have hstable : (prefixWord ++ tailWord_7857751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857751).length < 2 ^ (prefixWord ++ tailWord_7857751).sum := by decide
  have hdescent : baseEnd_7857751 < baseStart_7857751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857754 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2]
def baseStart_7857754 : Nat := 118140960795 + 7857754 * 2 ^ 59
def prefixEnd_7857754 : Nat := 4983230072969 + 3 ^ 40 * 7857754 * 2
def baseEnd_7857754 : Nat := 4034804666789354735037853

theorem tailTrace_7857754 : CollatzResearch.WordTrace tailWord_7857754 prefixEnd_7857754 4034804666789354735037853 := by
  unfold tailWord_7857754
  simp only [CollatzResearch.WordTrace]
  refine ⟨71648958293676682596607079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191063888783137820257618877 71648958293676682596607079)
  ·
    refine ⟨107473437440515023894910619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71648958293676682596607079 107473437440515023894910619)
    ·
      refine ⟨161210156160772535842365929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107473437440515023894910619 161210156160772535842365929)
      ·
        refine ⟨120907617120579401881774447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161210156160772535842365929 120907617120579401881774447)
        ·
          refine ⟨181361425680869102822661671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120907617120579401881774447 181361425680869102822661671)
          ·
            refine ⟨272042138521303654233992507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181361425680869102822661671 272042138521303654233992507)
            ·
              refine ⟨408063207781955481350988761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272042138521303654233992507 408063207781955481350988761)
              ·
                refine ⟨306047405836466611013241571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408063207781955481350988761 306047405836466611013241571)
                ·
                  refine ⟨459071108754699916519862357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306047405836466611013241571 459071108754699916519862357)
                  ·
                    refine ⟨5379739555719139646717137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 459071108754699916519862357 5379739555719139646717137)
                    ·
                      refine ⟨4034804666789354735037853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5379739555719139646717137 4034804666789354735037853)
                      ·
                        rfl

theorem cell23_7857754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_7857754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857754 prefixEnd_7857754 := by exact prefixLift 7857754
  have htrace : WordTrace (prefixWord ++ tailWord_7857754) baseStart_7857754 baseEnd_7857754 := by
    simpa [prefixWord, tailWord_7857754, baseEnd_7857754] using wordTrace_append hprefix tailTrace_7857754
  have hstable : (prefixWord ++ tailWord_7857754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857754).length < 2 ^ (prefixWord ++ tailWord_7857754).sum := by decide
  have hdescent : baseEnd_7857754 < baseStart_7857754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857781 : List Nat := [1, 3, 4, 2, 1, 1, 3, 1, 1, 6]
def baseStart_7857781 : Nat := 118140960795 + 7857781 * 2 ^ 59
def prefixEnd_7857781 : Nat := 4983230072969 + 3 ^ 40 * 7857781 * 2
def baseEnd_7857781 : Nat := 1344939510255675376466743

theorem tailTrace_7857781 : CollatzResearch.WordTrace tailWord_7857781 prefixEnd_7857781 1344939510255675376466743 := by
  unfold tailWord_7857781
  simp only [CollatzResearch.WordTrace]
  refine ⟨286596817945608913997661197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191064545297072609331774131 286596817945608913997661197)
  ·
    refine ⟨107473806729603342749122949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286596817945608913997661197 107473806729603342749122949)
    ·
      refine ⟨20151338761800626765460553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107473806729603342749122949 20151338761800626765460553)
      ·
        refine ⟨15113504071350470074095415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20151338761800626765460553 15113504071350470074095415)
        ·
          refine ⟨22670256107025705111143123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15113504071350470074095415 22670256107025705111143123)
          ·
            refine ⟨34005384160538557666714685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22670256107025705111143123 34005384160538557666714685)
            ·
              refine ⟨12752019060201959125018007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34005384160538557666714685 12752019060201959125018007)
              ·
                refine ⟨19128028590302938687527011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12752019060201959125018007 19128028590302938687527011)
                ·
                  refine ⟨28692042885454408031290517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19128028590302938687527011 28692042885454408031290517)
                  ·
                    refine ⟨1344939510255675376466743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28692042885454408031290517 1344939510255675376466743)
                    ·
                      rfl

theorem cell23_7857781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_7857781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857781 prefixEnd_7857781 := by exact prefixLift 7857781
  have htrace : WordTrace (prefixWord ++ tailWord_7857781) baseStart_7857781 baseEnd_7857781 := by
    simpa [prefixWord, tailWord_7857781, baseEnd_7857781] using wordTrace_append hprefix tailTrace_7857781
  have hstable : (prefixWord ++ tailWord_7857781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857781).length < 2 ^ (prefixWord ++ tailWord_7857781).sum := by decide
  have hdescent : baseEnd_7857781 < baseStart_7857781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857804 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 3, 3, 3]
def baseStart_7857804 : Nat := 118140960795 + 7857804 * 2 ^ 59
def prefixEnd_7857804 : Nat := 4983230072969 + 3 ^ 40 * 7857804 * 2
def baseEnd_7857804 : Nat := 4034830340822079539412623

theorem tailTrace_7857804 : CollatzResearch.WordTrace tailWord_7857804 prefixEnd_7857804 4034830340822079539412623 := by
  unfold tailWord_7857804
  simp only [CollatzResearch.WordTrace]
  refine ⟨143298828412262794462874233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191065104549683725950498977 143298828412262794462874233)
  ·
    refine ⟨107474121309197095847155675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143298828412262794462874233 107474121309197095847155675)
    ·
      refine ⟨161211181963795643770733513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107474121309197095847155675 161211181963795643770733513)
      ·
        refine ⟨120908386472846732828050135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161211181963795643770733513 120908386472846732828050135)
        ·
          refine ⟨181362579709270099242075203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120908386472846732828050135 181362579709270099242075203)
          ·
            refine ⟨272043869563905148863112805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181362579709270099242075203 272043869563905148863112805)
            ·
              refine ⟨51008225543232215411833651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272043869563905148863112805 51008225543232215411833651)
              ·
                refine ⟨76512338314848323117750477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51008225543232215411833651 76512338314848323117750477)
                ·
                  refine ⟨28692126868068121169156429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76512338314848323117750477 28692126868068121169156429)
                  ·
                    refine ⟨10759547575525545438433661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28692126868068121169156429 10759547575525545438433661)
                    ·
                      refine ⟨4034830340822079539412623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10759547575525545438433661 4034830340822079539412623)
                      ·
                        rfl

theorem cell23_7857804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_7857804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857804 prefixEnd_7857804 := by exact prefixLift 7857804
  have htrace : WordTrace (prefixWord ++ tailWord_7857804) baseStart_7857804 baseEnd_7857804 := by
    simpa [prefixWord, tailWord_7857804, baseEnd_7857804] using wordTrace_append hprefix tailTrace_7857804
  have hstable : (prefixWord ++ tailWord_7857804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857804).length < 2 ^ (prefixWord ++ tailWord_7857804).sum := by decide
  have hdescent : baseEnd_7857804 < baseStart_7857804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857822 : List Nat := [4, 3, 1, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_7857822 : Nat := 118140960795 + 7857822 * 2 ^ 59
def prefixEnd_7857822 : Nat := 4983230072969 + 3 ^ 40 * 7857822 * 2
def baseEnd_7857822 : Nat := 4034839583473860468987541

theorem tailTrace_7857822 : CollatzResearch.WordTrace tailWord_7857822 prefixEnd_7857822 4034839583473860468987541 := by
  unfold tailWord_7857822
  simp only [CollatzResearch.WordTrace]
  refine ⟨35824789167307547249987965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191065542225640251999935813 35824789167307547249987965)
  ·
    refine ⟨13434295937740330218745487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35824789167307547249987965 13434295937740330218745487)
    ·
      refine ⟨20151443906610495328118231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13434295937740330218745487 20151443906610495328118231)
      ·
        refine ⟨30227165859915742992177347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20151443906610495328118231 30227165859915742992177347)
        ·
          refine ⟨45340748789873614488266021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30227165859915742992177347 45340748789873614488266021)
          ·
            refine ⟨8501390398101302716549879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45340748789873614488266021 8501390398101302716549879)
            ·
              refine ⟨12752085597151954074824819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8501390398101302716549879 12752085597151954074824819)
              ·
                refine ⟨19128128395727931112237229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12752085597151954074824819 19128128395727931112237229)
                ·
                  refine ⟨7173048148397974167088961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19128128395727931112237229 7173048148397974167088961)
                  ·
                    refine ⟨5379786111298480625316721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7173048148397974167088961 5379786111298480625316721)
                    ·
                      refine ⟨4034839583473860468987541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5379786111298480625316721 4034839583473860468987541)
                      ·
                        rfl

theorem cell23_7857822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_7857822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857822 prefixEnd_7857822 := by exact prefixLift 7857822
  have htrace : WordTrace (prefixWord ++ tailWord_7857822) baseStart_7857822 baseEnd_7857822 := by
    simpa [prefixWord, tailWord_7857822, baseEnd_7857822] using wordTrace_append hprefix tailTrace_7857822
  have hstable : (prefixWord ++ tailWord_7857822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857822).length < 2 ^ (prefixWord ++ tailWord_7857822).sum := by decide
  have hdescent : baseEnd_7857822 < baseStart_7857822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857832 : List Nat := [2, 1, 7, 1, 1, 1, 1, 3, 2, 4]
def baseStart_7857832 : Nat := 118140960795 + 7857832 * 2 ^ 59
def prefixEnd_7857832 : Nat := 4983230072969 + 3 ^ 40 * 7857832 * 2
def baseEnd_7857832 : Nat := 1344948239426801809954165

theorem tailTrace_7857832 : CollatzResearch.WordTrace tailWord_7857832 prefixEnd_7857832 1344948239426801809954165 := by
  unfold tailWord_7857832
  simp only [CollatzResearch.WordTrace]
  refine ⟨143299339034212074853883875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191065785378949433138511833 143299339034212074853883875)
  ·
    refine ⟨214949008551318112280825813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143299339034212074853883875 214949008551318112280825813)
    ·
      refine ⟨5037867387921518256581855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 214949008551318112280825813 5037867387921518256581855)
      ·
        refine ⟨7556801081882277384872783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5037867387921518256581855 7556801081882277384872783)
        ·
          refine ⟨11335201622823416077309175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7556801081882277384872783 11335201622823416077309175)
          ·
            refine ⟨17002802434235124115963763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11335201622823416077309175 17002802434235124115963763)
            ·
              refine ⟨25504203651352686173945645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17002802434235124115963763 25504203651352686173945645)
              ·
                refine ⟨9564076369257257315229617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25504203651352686173945645 9564076369257257315229617)
                ·
                  refine ⟨7173057276942942986422213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9564076369257257315229617 7173057276942942986422213)
                  ·
                    refine ⟨1344948239426801809954165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7173057276942942986422213 1344948239426801809954165)
                    ·
                      rfl

theorem cell23_7857832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_7857832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857832 prefixEnd_7857832 := by exact prefixLift 7857832
  have htrace : WordTrace (prefixWord ++ tailWord_7857832) baseStart_7857832 baseEnd_7857832 := by
    simpa [prefixWord, tailWord_7857832, baseEnd_7857832] using wordTrace_append hprefix tailTrace_7857832
  have hstable : (prefixWord ++ tailWord_7857832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857832).length < 2 ^ (prefixWord ++ tailWord_7857832).sum := by decide
  have hdescent : baseEnd_7857832 < baseStart_7857832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857861 : List Nat := [1, 3, 1, 1, 1, 1, 2, 6, 1, 4, 2]
def baseStart_7857861 : Nat := 118140960795 + 7857861 * 2 ^ 59
def prefixEnd_7857861 : Nat := 4983230072969 + 3 ^ 40 * 7857861 * 2
def baseEnd_7857861 : Nat := 4034859609219385816399861

theorem tailTrace_7857861 : CollatzResearch.WordTrace tailWord_7857861 prefixEnd_7857861 4034859609219385816399861 := by
  unfold tailWord_7857861
  simp only [CollatzResearch.WordTrace]
  refine ⟨286599735785319087660573437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191066490523546058440382291 286599735785319087660573437)
  ·
    refine ⟨107474900919494657872715039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286599735785319087660573437 107474900919494657872715039)
    ·
      refine ⟨161212351379241986809072559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107474900919494657872715039 161212351379241986809072559)
      ·
        refine ⟨241818527068862980213608839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161212351379241986809072559 241818527068862980213608839)
        ·
          refine ⟨362727790603294470320413259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241818527068862980213608839 362727790603294470320413259)
          ·
            refine ⟨544091685904941705480619889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362727790603294470320413259 544091685904941705480619889)
            ·
              refine ⟨408068764428706279110464917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544091685904941705480619889 408068764428706279110464917)
              ·
                refine ⟨19128223332595606833303043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 408068764428706279110464917 19128223332595606833303043)
                ·
                  refine ⟨28692334998893410249954565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19128223332595606833303043 28692334998893410249954565)
                  ·
                    refine ⟨5379812812292514421866481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28692334998893410249954565 5379812812292514421866481)
                    ·
                      refine ⟨4034859609219385816399861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5379812812292514421866481 4034859609219385816399861)
                      ·
                        rfl

theorem cell23_7857861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 4, 2].length) (baseStart_7857861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857861 prefixEnd_7857861 := by exact prefixLift 7857861
  have htrace : WordTrace (prefixWord ++ tailWord_7857861) baseStart_7857861 baseEnd_7857861 := by
    simpa [prefixWord, tailWord_7857861, baseEnd_7857861] using wordTrace_append hprefix tailTrace_7857861
  have hstable : (prefixWord ++ tailWord_7857861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857861).length < 2 ^ (prefixWord ++ tailWord_7857861).sum := by decide
  have hdescent : baseEnd_7857861 < baseStart_7857861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857864 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_7857864 : Nat := 118140960795 + 7857864 * 2 ^ 59
def prefixEnd_7857864 : Nat := 4983230072969 + 3 ^ 40 * 7857864 * 2
def baseEnd_7857864 : Nat := 4034861149661349304662347

theorem tailTrace_7857864 : CollatzResearch.WordTrace tailWord_7857864 prefixEnd_7857864 4034861149661349304662347 := by
  unfold tailWord_7857864
  simp only [CollatzResearch.WordTrace]
  refine ⟨143299922602154109586466323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191066563469538812781955097 143299922602154109586466323)
  ·
    refine ⟨214949883903231164379699485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143299922602154109586466323 214949883903231164379699485)
    ·
      refine ⟨80606206463711686642387307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214949883903231164379699485 80606206463711686642387307)
      ·
        refine ⟨120909309695567529963580961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80606206463711686642387307 120909309695567529963580961)
        ·
          refine ⟨90681982271675647472685721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120909309695567529963580961 90681982271675647472685721)
          ·
            refine ⟨68011486703756735604514291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90681982271675647472685721 68011486703756735604514291)
            ·
              refine ⟨102017230055635103406771437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68011486703756735604514291 102017230055635103406771437)
              ·
                refine ⟨38256461270863163777539289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102017230055635103406771437 38256461270863163777539289)
                ·
                  refine ⟨28692345953147372833154467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38256461270863163777539289 28692345953147372833154467)
                  ·
                    refine ⟨43038518929721059249731701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28692345953147372833154467 43038518929721059249731701)
                    ·
                      refine ⟨4034861149661349304662347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43038518929721059249731701 4034861149661349304662347)
                      ·
                        rfl

theorem cell23_7857864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_7857864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857864 prefixEnd_7857864 := by exact prefixLift 7857864
  have htrace : WordTrace (prefixWord ++ tailWord_7857864) baseStart_7857864 baseEnd_7857864 := by
    simpa [prefixWord, tailWord_7857864, baseEnd_7857864] using wordTrace_append hprefix tailTrace_7857864
  have hstable : (prefixWord ++ tailWord_7857864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857864).length < 2 ^ (prefixWord ++ tailWord_7857864).sum := by decide
  have hdescent : baseEnd_7857864 < baseStart_7857864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7857901 : List Nat := [1, 5, 1, 2, 1, 3, 1, 2, 7]
def baseStart_7857901 : Nat := 118140960795 + 7857901 * 2 ^ 59
def prefixEnd_7857901 : Nat := 4983230072969 + 3 ^ 40 * 7857901 * 2
def baseEnd_7857901 : Nat := 448320016493951739988853

theorem tailTrace_7857901 : CollatzResearch.WordTrace tailWord_7857901 prefixEnd_7857901 448320016493951739988853 := by
  unfold tailWord_7857901
  simp only [CollatzResearch.WordTrace]
  refine ⟨286601194705174174492029557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191067463136782782994686371 286601194705174174492029557)
  ·
    refine ⟨26868862003610078858627771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286601194705174174492029557 26868862003610078858627771)
    ·
      refine ⟨40303293005415118287941657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26868862003610078858627771 40303293005415118287941657)
      ·
        refine ⟨30227469754061338715956243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40303293005415118287941657 30227469754061338715956243)
        ·
          refine ⟨45341204631092008073934365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30227469754061338715956243 45341204631092008073934365)
          ·
            refine ⟨17002951736659503027725387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45341204631092008073934365 17002951736659503027725387)
            ·
              refine ⟨25504427604989254541588081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17002951736659503027725387 25504427604989254541588081)
              ·
                refine ⟨19128320703741940906191061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25504427604989254541588081 19128320703741940906191061)
                ·
                  refine ⟨448320016493951739988853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19128320703741940906191061 448320016493951739988853)
                  ·
                    rfl

theorem cell23_7857901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_7857901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7857901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7857901 prefixEnd_7857901 := by exact prefixLift 7857901
  have htrace : WordTrace (prefixWord ++ tailWord_7857901) baseStart_7857901 baseEnd_7857901 := by
    simpa [prefixWord, tailWord_7857901, baseEnd_7857901] using wordTrace_append hprefix tailTrace_7857901
  have hstable : (prefixWord ++ tailWord_7857901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7857901).length < 2 ^ (prefixWord ++ tailWord_7857901).sum := by decide
  have hdescent : baseEnd_7857901 < baseStart_7857901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7857901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858035 : List Nat := [1, 1, 1, 2, 2, 1, 3, 7, 1, 1, 3]
def baseStart_7858035 : Nat := 118140960795 + 7858035 * 2 ^ 59
def prefixEnd_7858035 : Nat := 4983230072969 + 3 ^ 40 * 7858035 * 2
def baseEnd_7858035 : Nat := 4034948954853268135624061

theorem tailTrace_7858035 : CollatzResearch.WordTrace tailWord_7858035 prefixEnd_7858035 4034948954853268135624061 := by
  unfold tailWord_7858035
  simp only [CollatzResearch.WordTrace]
  refine ⟨286606082086688715377407559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191070721391125810251605039 286606082086688715377407559)
  ·
    refine ⟨429909123130033073066111339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286606082086688715377407559 429909123130033073066111339)
    ·
      refine ⟨644863684695049609599167009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429909123130033073066111339 644863684695049609599167009)
      ·
        refine ⟨483647763521287207199375257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 644863684695049609599167009 483647763521287207199375257)
        ·
          refine ⟨362735822640965405399531443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483647763521287207199375257 362735822640965405399531443)
          ·
            refine ⟨544103733961448108099297165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362735822640965405399531443 544103733961448108099297165)
            ·
              refine ⟨204038900235543040537236437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 544103733961448108099297165 204038900235543040537236437)
              ·
                refine ⟨4782161724270540012591479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 204038900235543040537236437 4782161724270540012591479)
                ·
                  refine ⟨7173242586405810018887219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4782161724270540012591479 7173242586405810018887219)
                  ·
                    refine ⟨10759863879608715028330829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7173242586405810018887219 10759863879608715028330829)
                    ·
                      refine ⟨4034948954853268135624061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10759863879608715028330829 4034948954853268135624061)
                      ·
                        rfl

theorem cell23_7858035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 1, 1, 3].length) (baseStart_7858035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858035 prefixEnd_7858035 := by exact prefixLift 7858035
  have htrace : WordTrace (prefixWord ++ tailWord_7858035) baseStart_7858035 baseEnd_7858035 := by
    simpa [prefixWord, tailWord_7858035, baseEnd_7858035] using wordTrace_append hprefix tailTrace_7858035
  have hstable : (prefixWord ++ tailWord_7858035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858035).length < 2 ^ (prefixWord ++ tailWord_7858035).sum := by decide
  have hdescent : baseEnd_7858035 < baseStart_7858035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858046 : List Nat := [4, 2, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_7858046 : Nat := 118140960795 + 7858046 * 2 ^ 59
def prefixEnd_7858046 : Nat := 4983230072969 + 3 ^ 40 * 7858046 * 2
def baseEnd_7858046 : Nat := 1344984867713489197528837

theorem tailTrace_7858046 : CollatzResearch.WordTrace tailWord_7858046 prefixEnd_7858046 1344984867713489197528837 := by
  unfold tailWord_7858046
  simp only [CollatzResearch.WordTrace]
  refine ⟨35825810411206108032007249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191070988859765909504038661 35825810411206108032007249)
  ·
    refine ⟨26869357808404581024005437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35825810411206108032007249 26869357808404581024005437)
    ·
      refine ⟨10076009178151717884002039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26869357808404581024005437 10076009178151717884002039)
      ·
        refine ⟨15114013767227576826003059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10076009178151717884002039 15114013767227576826003059)
        ·
          refine ⟨22671020650841365239004589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15114013767227576826003059 22671020650841365239004589)
          ·
            refine ⟨8501632744065511964626721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22671020650841365239004589 8501632744065511964626721)
            ·
              refine ⟨6376224558049133973470041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8501632744065511964626721 6376224558049133973470041)
              ·
                refine ⟨4782168418536850480102531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6376224558049133973470041 4782168418536850480102531)
                ·
                  refine ⟨7173252627805275720153797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4782168418536850480102531 7173252627805275720153797)
                  ·
                    refine ⟨1344984867713489197528837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7173252627805275720153797 1344984867713489197528837)
                    ·
                      rfl

theorem cell23_7858046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_7858046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858046 prefixEnd_7858046 := by exact prefixLift 7858046
  have htrace : WordTrace (prefixWord ++ tailWord_7858046) baseStart_7858046 baseEnd_7858046 := by
    simpa [prefixWord, tailWord_7858046, baseEnd_7858046] using wordTrace_append hprefix tailTrace_7858046
  have hstable : (prefixWord ++ tailWord_7858046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858046).length < 2 ^ (prefixWord ++ tailWord_7858046).sum := by decide
  have hdescent : baseEnd_7858046 < baseStart_7858046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858068 : List Nat := [2, 4, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_7858068 : Nat := 118140960795 + 7858068 * 2 ^ 59
def prefixEnd_7858068 : Nat := 4983230072969 + 3 ^ 40 * 7858068 * 2
def baseEnd_7858068 : Nat := 1344988633238288835503803

theorem tailTrace_7858068 : CollatzResearch.WordTrace tailWord_7858068 prefixEnd_7858068 1344988633238288835503803 := by
  unfold tailWord_7858068
  simp only [CollatzResearch.WordTrace]
  refine ⟨143303642847784581006679429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191071523797046108008905905 143303642847784581006679429)
  ·
    refine ⟨26869433033959608938752393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143303642847784581006679429 26869433033959608938752393)
    ·
      refine ⟨20152074775469706704064295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26869433033959608938752393 20152074775469706704064295)
      ·
        refine ⟨30228112163204560056096443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20152074775469706704064295 30228112163204560056096443)
        ·
          refine ⟨45342168244806840084144665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30228112163204560056096443 45342168244806840084144665)
          ·
            refine ⟨34006626183605130063108499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45342168244806840084144665 34006626183605130063108499)
            ·
              refine ⟨51009939275407695094662749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34006626183605130063108499 51009939275407695094662749)
              ·
                refine ⟨19128727228277885660498531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51009939275407695094662749 19128727228277885660498531)
                ·
                  refine ⟨28693090842416828490747797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19128727228277885660498531 28693090842416828490747797)
                  ·
                    refine ⟨1344988633238288835503803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28693090842416828490747797 1344988633238288835503803)
                    ·
                      rfl

theorem cell23_7858068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_7858068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858068 prefixEnd_7858068 := by exact prefixLift 7858068
  have htrace : WordTrace (prefixWord ++ tailWord_7858068) baseStart_7858068 baseEnd_7858068 := by
    simpa [prefixWord, tailWord_7858068, baseEnd_7858068] using wordTrace_append hprefix tailTrace_7858068
  have hstable : (prefixWord ++ tailWord_7858068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858068).length < 2 ^ (prefixWord ++ tailWord_7858068).sum := by decide
  have hdescent : baseEnd_7858068 < baseStart_7858068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858079 : List Nat := [1, 1, 2, 5, 4, 1, 1, 1, 2, 3, 2]
def baseStart_7858079 : Nat := 118140960795 + 7858079 * 2 ^ 59
def prefixEnd_7858079 : Nat := 4983230072969 + 3 ^ 40 * 7858079 * 2
def baseEnd_7858079 : Nat := 4034971548002065963473859

theorem tailTrace_7858079 : CollatzResearch.WordTrace tailWord_7858079 prefixEnd_7858079 4034971548002065963473859 := by
  unfold tailWord_7858079
  simp only [CollatzResearch.WordTrace]
  refine ⟨286607686898529310892009291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191071791265686207261339527 286607686898529310892009291)
  ·
    refine ⟨429911530347793966338013937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286607686898529310892009291 429911530347793966338013937)
    ·
      refine ⟨322433647760845474753510453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429911530347793966338013937 322433647760845474753510453)
      ·
        refine ⟨30228154477579263258141605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 322433647760845474753510453 30228154477579263258141605)
        ·
          refine ⟨5667778964546111860901551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30228154477579263258141605 5667778964546111860901551)
          ·
            refine ⟨8501668446819167791352327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5667778964546111860901551 8501668446819167791352327)
            ·
              refine ⟨12752502670228751687028491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8501668446819167791352327 12752502670228751687028491)
              ·
                refine ⟨19128754005343127530542737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12752502670228751687028491 19128754005343127530542737)
                ·
                  refine ⟨14346565504007345647907053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19128754005343127530542737 14346565504007345647907053)
                  ·
                    refine ⟨5379962064002754617965145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14346565504007345647907053 5379962064002754617965145)
                    ·
                      refine ⟨4034971548002065963473859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5379962064002754617965145 4034971548002065963473859)
                      ·
                        rfl

theorem cell23_7858079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_7858079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858079 prefixEnd_7858079 := by exact prefixLift 7858079
  have htrace : WordTrace (prefixWord ++ tailWord_7858079) baseStart_7858079 baseEnd_7858079 := by
    simpa [prefixWord, tailWord_7858079, baseEnd_7858079] using wordTrace_append hprefix tailTrace_7858079
  have hstable : (prefixWord ++ tailWord_7858079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858079).length < 2 ^ (prefixWord ++ tailWord_7858079).sum := by decide
  have hdescent : baseEnd_7858079 < baseStart_7858079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858109 : List Nat := [1, 4, 1, 2, 3, 1, 2, 4, 1, 2, 2]
def baseStart_7858109 : Nat := 118140960795 + 7858109 * 2 ^ 59
def prefixEnd_7858109 : Nat := 4983230072969 + 3 ^ 40 * 7858109 * 2
def baseEnd_7858109 : Nat := 4034986952421700846098721

theorem tailTrace_7858109 : CollatzResearch.WordTrace tailWord_7858109 prefixEnd_7858109 4034986952421700846098721 := by
  unfold tailWord_7858109
  simp only [CollatzResearch.WordTrace]
  refine ⟨286608781088420626015601381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191072520725613750677067587 286608781088420626015601381)
  ·
    refine ⟨53739146454078867377925259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286608781088420626015601381 53739146454078867377925259)
    ·
      refine ⟨80608719681118301066887889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53739146454078867377925259 80608719681118301066887889)
      ·
        refine ⟨60456539760838725800165917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80608719681118301066887889 60456539760838725800165917)
        ·
          refine ⟨22671202410314522175062219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60456539760838725800165917 22671202410314522175062219)
          ·
            refine ⟨34006803615471783262593329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22671202410314522175062219 34006803615471783262593329)
            ·
              refine ⟨25505102711603837446944997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34006803615471783262593329 25505102711603837446944997)
              ·
                refine ⟨4782206758425719521302187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25505102711603837446944997 4782206758425719521302187)
                ·
                  refine ⟨7173310137638579281953281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4782206758425719521302187 7173310137638579281953281)
                  ·
                    refine ⟨5379982603228934461464961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7173310137638579281953281 5379982603228934461464961)
                    ·
                      refine ⟨4034986952421700846098721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5379982603228934461464961 4034986952421700846098721)
                      ·
                        rfl

theorem cell23_7858109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_7858109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858109 prefixEnd_7858109 := by exact prefixLift 7858109
  have htrace : WordTrace (prefixWord ++ tailWord_7858109) baseStart_7858109 baseEnd_7858109 := by
    simpa [prefixWord, tailWord_7858109, baseEnd_7858109] using wordTrace_append hprefix tailTrace_7858109
  have hstable : (prefixWord ++ tailWord_7858109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858109).length < 2 ^ (prefixWord ++ tailWord_7858109).sum := by decide
  have hdescent : baseEnd_7858109 < baseStart_7858109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858186 : List Nat := [3, 1, 2, 2, 5, 1, 1, 2, 1, 3, 2]
def baseStart_7858186 : Nat := 118140960795 + 7858186 * 2 ^ 59
def prefixEnd_7858186 : Nat := 4983230072969 + 3 ^ 40 * 7858186 * 2
def baseEnd_7858186 : Nat := 4035026490432097044835867

theorem tailTrace_7858186 : CollatzResearch.WordTrace tailWord_7858186 prefixEnd_7858186 4035026490432097044835867 := by
  unfold tailWord_7858186
  simp only [CollatzResearch.WordTrace]
  refine ⟨71652897377285417041538603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191074393006094445444102941 71652897377285417041538603)
  ·
    refine ⟨107479346065928125562307905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71652897377285417041538603 107479346065928125562307905)
    ·
      refine ⟨80609509549446094171730929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107479346065928125562307905 80609509549446094171730929)
      ·
        refine ⟨60457132162084570628798197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80609509549446094171730929 60457132162084570628798197)
        ·
          refine ⟨5667856140195428496449831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60457132162084570628798197 5667856140195428496449831)
          ·
            refine ⟨8501784210293142744674747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5667856140195428496449831 8501784210293142744674747)
            ·
              refine ⟨12752676315439714117012121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8501784210293142744674747 12752676315439714117012121)
              ·
                refine ⟨9564507236579785587759091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12752676315439714117012121 9564507236579785587759091)
                ·
                  refine ⟨14346760854869678381638637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9564507236579785587759091 14346760854869678381638637)
                  ·
                    refine ⟨5380035320576129393114489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14346760854869678381638637 5380035320576129393114489)
                    ·
                      refine ⟨4035026490432097044835867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5380035320576129393114489 4035026490432097044835867)
                      ·
                        rfl

theorem cell23_7858186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_7858186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858186 prefixEnd_7858186 := by exact prefixLift 7858186
  have htrace : WordTrace (prefixWord ++ tailWord_7858186) baseStart_7858186 baseEnd_7858186 := by
    simpa [prefixWord, tailWord_7858186, baseEnd_7858186] using wordTrace_append hprefix tailTrace_7858186
  have hstable : (prefixWord ++ tailWord_7858186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858186).length < 2 ^ (prefixWord ++ tailWord_7858186).sum := by decide
  have hdescent : baseEnd_7858186 < baseStart_7858186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858222 : List Nat := [4, 1, 3, 1, 1, 3, 1, 4, 5]
def baseStart_7858222 : Nat := 118140960795 + 7858222 * 2 ^ 59
def prefixEnd_7858222 : Nat := 4983230072969 + 3 ^ 40 * 7858222 * 2
def baseEnd_7858222 : Nat := 448338330637295433776189

theorem tailTrace_7858222 : CollatzResearch.WordTrace tailWord_7858222 prefixEnd_7858222 448338330637295433776189 := by
  unfold tailWord_7858222
  simp only [CollatzResearch.WordTrace]
  refine ⟨35826612817126405789308115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191075268358007497542976613 35826612817126405789308115)
  ·
    refine ⟨53739919225689608683962173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35826612817126405789308115 53739919225689608683962173)
    ·
      refine ⟨20152469709633603256485815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53739919225689608683962173 20152469709633603256485815)
      ·
        refine ⟨30228704564450404884728723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20152469709633603256485815 30228704564450404884728723)
        ·
          refine ⟨45343056846675607327093085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30228704564450404884728723 45343056846675607327093085)
          ·
            refine ⟨17003646317503352747659907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45343056846675607327093085 17003646317503352747659907)
            ·
              refine ⟨25505469476255029121489861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17003646317503352747659907 25505469476255029121489861)
              ·
                refine ⟨4782275526797817960279349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25505469476255029121489861 4782275526797817960279349)
                ·
                  refine ⟨448338330637295433776189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4782275526797817960279349 448338330637295433776189)
                  ·
                    rfl

theorem cell23_7858222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_7858222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858222 prefixEnd_7858222 := by exact prefixLift 7858222
  have htrace : WordTrace (prefixWord ++ tailWord_7858222) baseStart_7858222 baseEnd_7858222 := by
    simpa [prefixWord, tailWord_7858222, baseEnd_7858222] using wordTrace_append hprefix tailTrace_7858222
  have hstable : (prefixWord ++ tailWord_7858222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858222).length < 2 ^ (prefixWord ++ tailWord_7858222).sum := by decide
  have hdescent : baseEnd_7858222 < baseStart_7858222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858225 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 2, 5, 2]
def baseStart_7858225 : Nat := 118140960795 + 7858225 * 2 ^ 59
def prefixEnd_7858225 : Nat := 4983230072969 + 3 ^ 40 * 7858225 * 2
def baseEnd_7858225 : Nat := 4035046516177622392248187

theorem tailTrace_7858225 : CollatzResearch.WordTrace tailWord_7858225 prefixEnd_7858225 4035046516177622392248187 := by
  unfold tailWord_7858225
  simp only [CollatzResearch.WordTrace]
  refine ⟨286613011956000377826824129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191075341304000251884549419 286613011956000377826824129)
  ·
    refine ⟨214959758967000283370118097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286613011956000377826824129 214959758967000283370118097)
    ·
      refine ⟨161219819225250212527588573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214959758967000283370118097 161219819225250212527588573)
      ·
        refine ⟨60457432209468829697845715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161219819225250212527588573 60457432209468829697845715)
        ·
          refine ⟨90686148314203244546768573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60457432209468829697845715 90686148314203244546768573)
          ·
            refine ⟨34007305617826216705038215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90686148314203244546768573 34007305617826216705038215)
            ·
              refine ⟨51010958426739325057557323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34007305617826216705038215 51010958426739325057557323)
              ·
                refine ⟨76516437640108987586335985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51010958426739325057557323 76516437640108987586335985)
                ·
                  refine ⟨57387328230081740689751989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76516437640108987586335985 57387328230081740689751989)
                  ·
                    refine ⟨5380062021570163189664249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57387328230081740689751989 5380062021570163189664249)
                    ·
                      refine ⟨4035046516177622392248187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5380062021570163189664249 4035046516177622392248187)
                      ·
                        rfl

theorem cell23_7858225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_7858225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858225 prefixEnd_7858225 := by exact prefixLift 7858225
  have htrace : WordTrace (prefixWord ++ tailWord_7858225) baseStart_7858225 baseEnd_7858225 := by
    simpa [prefixWord, tailWord_7858225, baseEnd_7858225] using wordTrace_append hprefix tailTrace_7858225
  have hstable : (prefixWord ++ tailWord_7858225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858225).length < 2 ^ (prefixWord ++ tailWord_7858225).sum := by decide
  have hdescent : baseEnd_7858225 < baseStart_7858225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858275 : List Nat := [1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 3]
def baseStart_7858275 : Nat := 118140960795 + 7858275 * 2 ^ 59
def prefixEnd_7858275 : Nat := 4983230072969 + 3 ^ 40 * 7858275 * 2
def baseEnd_7858275 : Nat := 4035072190210347196622957

theorem tailTrace_7858275 : CollatzResearch.WordTrace tailWord_7858275 prefixEnd_7858275 4035072190210347196622957 := by
  unfold tailWord_7858275
  simp only [CollatzResearch.WordTrace]
  refine ⟨286614835605819236366144279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191076557070546157577429519 286614835605819236366144279)
  ·
    refine ⟨429922253408728854549216419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286614835605819236366144279 429922253408728854549216419)
    ·
      refine ⟨644883380113093281823824629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429922253408728854549216419 644883380113093281823824629)
      ·
        refine ⟨60457816885602495170983559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 644883380113093281823824629 60457816885602495170983559)
        ·
          refine ⟨90686725328403742756475339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60457816885602495170983559 90686725328403742756475339)
          ·
            refine ⟨136030087992605614134713009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90686725328403742756475339 136030087992605614134713009)
            ·
              refine ⟨102022565994454210601034757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136030087992605614134713009 102022565994454210601034757)
              ·
                refine ⟨19129231123960164487694017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102022565994454210601034757 19129231123960164487694017)
                ·
                  refine ⟨14346923342970123365770513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19129231123960164487694017 14346923342970123365770513)
                  ·
                    refine ⟨10760192507227592524327885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14346923342970123365770513 10760192507227592524327885)
                    ·
                      refine ⟨4035072190210347196622957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10760192507227592524327885 4035072190210347196622957)
                      ·
                        rfl

theorem cell23_7858275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_7858275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858275 prefixEnd_7858275 := by exact prefixLift 7858275
  have htrace : WordTrace (prefixWord ++ tailWord_7858275) baseStart_7858275 baseEnd_7858275 := by
    simpa [prefixWord, tailWord_7858275, baseEnd_7858275] using wordTrace_append hprefix tailTrace_7858275
  have hstable : (prefixWord ++ tailWord_7858275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858275).length < 2 ^ (prefixWord ++ tailWord_7858275).sum := by decide
  have hdescent : baseEnd_7858275 < baseStart_7858275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858325 : List Nat := [1, 3, 2, 1, 1, 1, 3, 5, 1, 5]
def baseStart_7858325 : Nat := 118140960795 + 7858325 * 2 ^ 59
def prefixEnd_7858325 : Nat := 4983230072969 + 3 ^ 40 * 7858325 * 2
def baseEnd_7858325 : Nat := 1345032621414357333665909

theorem tailTrace_7858325 : CollatzResearch.WordTrace tailWord_7858325 prefixEnd_7858325 1345032621414357333665909 := by
  unfold tailWord_7858325
  simp only [CollatzResearch.WordTrace]
  refine ⟨286616659255638094905464429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191077772837092063270309619 286616659255638094905464429)
  ·
    refine ⟨107481247220864285589549161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286616659255638094905464429 107481247220864285589549161)
    ·
      refine ⟨80610935415648214192161871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107481247220864285589549161 80610935415648214192161871)
      ·
        refine ⟨120916403123472321288242807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80610935415648214192161871 120916403123472321288242807)
        ·
          refine ⟨181374604685208481932364211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120916403123472321288242807 181374604685208481932364211)
          ·
            refine ⟨272061907027812722898546317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181374604685208481932364211 272061907027812722898546317)
            ·
              refine ⟨102023215135429771086954869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272061907027812722898546317 102023215135429771086954869)
              ·
                refine ⟨9564676418946541039402019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102023215135429771086954869 9564676418946541039402019)
                ·
                  refine ⟨14347014628419811559103029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9564676418946541039402019 14347014628419811559103029)
                  ·
                    refine ⟨1345032621414357333665909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14347014628419811559103029 1345032621414357333665909)
                    ·
                      rfl

theorem cell23_7858325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_7858325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858325 prefixEnd_7858325 := by exact prefixLift 7858325
  have htrace : WordTrace (prefixWord ++ tailWord_7858325) baseStart_7858325 baseEnd_7858325 := by
    simpa [prefixWord, tailWord_7858325, baseEnd_7858325] using wordTrace_append hprefix tailTrace_7858325
  have hstable : (prefixWord ++ tailWord_7858325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858325).length < 2 ^ (prefixWord ++ tailWord_7858325).sum := by decide
  have hdescent : baseEnd_7858325 < baseStart_7858325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858346 : List Nat := [3, 1, 5, 1, 2, 2, 2, 1, 6]
def baseStart_7858346 : Nat := 118140960795 + 7858346 * 2 ^ 59
def prefixEnd_7858346 : Nat := 4983230072969 + 3 ^ 40 * 7858346 * 2
def baseEnd_7858346 : Nat := 448345405259646268759459

theorem tailTrace_7858346 : CollatzResearch.WordTrace tailWord_7858346 prefixEnd_7858346 448345405259646268759459 := by
  unfold tailWord_7858346
  simp only [CollatzResearch.WordTrace]
  refine ⟨71654356297140503872994723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191078283459041343661319261 71654356297140503872994723)
  ·
    refine ⟨107481534445710755809492085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71654356297140503872994723 107481534445710755809492085)
    ·
      refine ⟨10076393854285383357139883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107481534445710755809492085 10076393854285383357139883)
      ·
        refine ⟨15114590781428075035709825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10076393854285383357139883 15114590781428075035709825)
        ·
          refine ⟨11335943086071056276782369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15114590781428075035709825 11335943086071056276782369)
          ·
            refine ⟨8501957314553292207586777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11335943086071056276782369 8501957314553292207586777)
            ·
              refine ⟨6376467985914969155690083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8501957314553292207586777 6376467985914969155690083)
              ·
                refine ⟨9564701978872453733535125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6376467985914969155690083 9564701978872453733535125)
                ·
                  refine ⟨448345405259646268759459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9564701978872453733535125 448345405259646268759459)
                  ·
                    rfl

theorem cell23_7858346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 6].length) (baseStart_7858346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858346 prefixEnd_7858346 := by exact prefixLift 7858346
  have htrace : WordTrace (prefixWord ++ tailWord_7858346) baseStart_7858346 baseEnd_7858346 := by
    simpa [prefixWord, tailWord_7858346, baseEnd_7858346] using wordTrace_append hprefix tailTrace_7858346
  have hstable : (prefixWord ++ tailWord_7858346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858346).length < 2 ^ (prefixWord ++ tailWord_7858346).sum := by decide
  have hdescent : baseEnd_7858346 < baseStart_7858346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858348 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 5]
def baseStart_7858348 : Nat := 118140960795 + 7858348 * 2 ^ 59
def prefixEnd_7858348 : Nat := 4983230072969 + 3 ^ 40 * 7858348 * 2
def baseEnd_7858348 : Nat := 4035109674298125411010121

theorem tailTrace_7858348 : CollatzResearch.WordTrace tailWord_7858348 prefixEnd_7858348 4035109674298125411010121 := by
  unfold tailWord_7858348
  simp only [CollatzResearch.WordTrace]
  refine ⟨143308749067277384916775849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191078332089703179889034465 143308749067277384916775849)
  ·
    refine ⟨107481561800458038687581887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143308749067277384916775849 107481561800458038687581887)
    ·
      refine ⟨161222342700687058031372831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107481561800458038687581887 161222342700687058031372831)
      ·
        refine ⟨241833514051030587047059247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161222342700687058031372831 241833514051030587047059247)
        ·
          refine ⟨362750271076545880570588871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241833514051030587047059247 362750271076545880570588871)
          ·
            refine ⟨544125406614818820855883307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362750271076545880570588871 544125406614818820855883307)
            ·
              refine ⟨816188109922228231283824961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544125406614818820855883307 816188109922228231283824961)
              ·
                refine ⟨612141082441671173462868721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 816188109922228231283824961 612141082441671173462868721)
                ·
                  refine ⟨459105811831253380097151541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612141082441671173462868721 459105811831253380097151541)
                  ·
                    refine ⟨43041169859180004384107957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 459105811831253380097151541 43041169859180004384107957)
                    ·
                      refine ⟨4035109674298125411010121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43041169859180004384107957 4035109674298125411010121)
                      ·
                        rfl

theorem cell23_7858348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_7858348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858348 prefixEnd_7858348 := by exact prefixLift 7858348
  have htrace : WordTrace (prefixWord ++ tailWord_7858348) baseStart_7858348 baseEnd_7858348 := by
    simpa [prefixWord, tailWord_7858348, baseEnd_7858348] using wordTrace_append hprefix tailTrace_7858348
  have hstable : (prefixWord ++ tailWord_7858348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858348).length < 2 ^ (prefixWord ++ tailWord_7858348).sum := by decide
  have hdescent : baseEnd_7858348 < baseStart_7858348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858362 : List Nat := [3, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4]
def baseStart_7858362 : Nat := 118140960795 + 7858362 * 2 ^ 59
def prefixEnd_7858362 : Nat := 4983230072969 + 3 ^ 40 * 7858362 * 2
def baseEnd_7858362 : Nat := 4035116863027288356235057

theorem tailTrace_7858362 : CollatzResearch.WordTrace tailWord_7858362 prefixEnd_7858362 4035116863027288356235057 := by
  unfold tailWord_7858362
  simp only [CollatzResearch.WordTrace]
  refine ⟨71654502189126012556140335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191078672504336033483040893 71654502189126012556140335)
  ·
    refine ⟨107481753283689018834210503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71654502189126012556140335 107481753283689018834210503)
    ·
      refine ⟨161222629925533528251315755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107481753283689018834210503 161222629925533528251315755)
      ·
        refine ⟨241833944888300292376973633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161222629925533528251315755 241833944888300292376973633)
        ·
          refine ⟨181375458666225219282730225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241833944888300292376973633 181375458666225219282730225)
          ·
            refine ⟨136031593999668914462047669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181375458666225219282730225 136031593999668914462047669)
            ·
              refine ⟨12752961937468960730816969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136031593999668914462047669 12752961937468960730816969)
              ·
                refine ⟨9564721453101720548112727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12752961937468960730816969 9564721453101720548112727)
                ·
                  refine ⟨14347082179652580822169091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9564721453101720548112727 14347082179652580822169091)
                  ·
                    refine ⟨21520623269478871233253637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14347082179652580822169091 21520623269478871233253637)
                    ·
                      refine ⟨4035116863027288356235057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21520623269478871233253637 4035116863027288356235057)
                      ·
                        rfl

theorem cell23_7858362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4].length) (baseStart_7858362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858362 prefixEnd_7858362 := by exact prefixLift 7858362
  have htrace : WordTrace (prefixWord ++ tailWord_7858362) baseStart_7858362 baseEnd_7858362 := by
    simpa [prefixWord, tailWord_7858362, baseEnd_7858362] using wordTrace_append hprefix tailTrace_7858362
  have hstable : (prefixWord ++ tailWord_7858362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858362).length < 2 ^ (prefixWord ++ tailWord_7858362).sum := by decide
  have hdescent : baseEnd_7858362 < baseStart_7858362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858366 : List Nat := [4, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2]
def baseStart_7858366 : Nat := 118140960795 + 7858366 * 2 ^ 59
def prefixEnd_7858366 : Nat := 4983230072969 + 3 ^ 40 * 7858366 * 2
def baseEnd_7858366 : Nat := 4035118916949906340585039

theorem tailTrace_7858366 : CollatzResearch.WordTrace tailWord_7858366 prefixEnd_7858366 4035118916949906340585039 := by
  unfold tailWord_7858366
  simp only [CollatzResearch.WordTrace]
  refine ⟨35827269331061194863463369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191078769765659705938471301 35827269331061194863463369)
  ·
    refine ⟨26870451998295896147597527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35827269331061194863463369 26870451998295896147597527)
    ·
      refine ⟨40305677997443844221396291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26870451998295896147597527 40305677997443844221396291)
      ·
        refine ⟨60458516996165766332094437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40305677997443844221396291 60458516996165766332094437)
        ·
          refine ⟨11335971936781081187267707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60458516996165766332094437 11335971936781081187267707)
          ·
            refine ⟨17003957905171621780901561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11335971936781081187267707 17003957905171621780901561)
            ·
              refine ⟨12752968428878716335676171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17003957905171621780901561 12752968428878716335676171)
              ·
                refine ⟨19129452643318074503514257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12752968428878716335676171 19129452643318074503514257)
                ·
                  refine ⟨14347089482488555877635693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19129452643318074503514257 14347089482488555877635693)
                  ·
                    refine ⟨5380158555933208454113385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14347089482488555877635693 5380158555933208454113385)
                    ·
                      refine ⟨4035118916949906340585039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5380158555933208454113385 4035118916949906340585039)
                      ·
                        rfl

theorem cell23_7858366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_7858366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858366 prefixEnd_7858366 := by exact prefixLift 7858366
  have htrace : WordTrace (prefixWord ++ tailWord_7858366) baseStart_7858366 baseEnd_7858366 := by
    simpa [prefixWord, tailWord_7858366, baseEnd_7858366] using wordTrace_append hprefix tailTrace_7858366
  have hstable : (prefixWord ++ tailWord_7858366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858366).length < 2 ^ (prefixWord ++ tailWord_7858366).sum := by decide
  have hdescent : baseEnd_7858366 < baseStart_7858366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858372 : List Nat := [2, 3, 3, 1, 2, 2, 1, 2, 1, 6]
def baseStart_7858372 : Nat := 118140960795 + 7858372 * 2 ^ 59
def prefixEnd_7858372 : Nat := 4983230072969 + 3 ^ 40 * 7858372 * 2
def baseEnd_7858372 : Nat := 1345040665944611105703337

theorem tailTrace_7858372 : CollatzResearch.WordTrace tailWord_7858372 prefixEnd_7858372 1345040665944611105703337 := by
  unfold tailWord_7858372
  simp only [CollatzResearch.WordTrace]
  refine ⟨143309186743233910966212685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191078915657645214621616913 143309186743233910966212685)
  ·
    refine ⟨53740945028712716612329757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143309186743233910966212685 53740945028712716612329757)
    ·
      refine ⟨20152854385767268729623659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53740945028712716612329757 20152854385767268729623659)
      ·
        refine ⟨30229281578650903094435489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20152854385767268729623659 30229281578650903094435489)
        ·
          refine ⟨22671961183988177320826617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30229281578650903094435489 22671961183988177320826617)
          ·
            refine ⟨17003970887991132990619963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22671961183988177320826617 17003970887991132990619963)
            ·
              refine ⟨25505956331986699485929945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17003970887991132990619963 25505956331986699485929945)
              ·
                refine ⟨19129467248990024614447459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25505956331986699485929945 19129467248990024614447459)
                ·
                  refine ⟨28694200873485036921671189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19129467248990024614447459 28694200873485036921671189)
                  ·
                    refine ⟨1345040665944611105703337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28694200873485036921671189 1345040665944611105703337)
                    ·
                      rfl

theorem cell23_7858372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_7858372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858372 prefixEnd_7858372 := by exact prefixLift 7858372
  have htrace : WordTrace (prefixWord ++ tailWord_7858372) baseStart_7858372 baseEnd_7858372 := by
    simpa [prefixWord, tailWord_7858372, baseEnd_7858372] using wordTrace_append hprefix tailTrace_7858372
  have hstable : (prefixWord ++ tailWord_7858372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858372).length < 2 ^ (prefixWord ++ tailWord_7858372).sum := by decide
  have hdescent : baseEnd_7858372 < baseStart_7858372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858382 : List Nat := [4, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5]
def baseStart_7858382 : Nat := 118140960795 + 7858382 * 2 ^ 59
def prefixEnd_7858382 : Nat := 4983230072969 + 3 ^ 40 * 7858382 * 2
def baseEnd_7858382 : Nat := 4035127132640378277984965

theorem tailTrace_7858382 : CollatzResearch.WordTrace tailWord_7858382 prefixEnd_7858382 4035127132640378277984965 := by
  unfold tailWord_7858382
  simp only [CollatzResearch.WordTrace]
  refine ⟨35827342277053949205036175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191079158810954395760192933 35827342277053949205036175)
  ·
    refine ⟨53741013415580923807554263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35827342277053949205036175 53741013415580923807554263)
    ·
      refine ⟨80611520123371385711331395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53741013415580923807554263 80611520123371385711331395)
      ·
        refine ⟨120917280185057078566997093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80611520123371385711331395 120917280185057078566997093)
        ·
          refine ⟨22671990034698202231311955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120917280185057078566997093 22671990034698202231311955)
          ·
            refine ⟨34007985052047303346967933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22671990034698202231311955 34007985052047303346967933)
            ·
              refine ⟨12752994394517738755112975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34007985052047303346967933 12752994394517738755112975)
              ·
                refine ⟨19129491591776608132669463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12752994394517738755112975 19129491591776608132669463)
                ·
                  refine ⟨28694237387664912199004195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19129491591776608132669463 28694237387664912199004195)
                  ·
                    refine ⟨43041356081497368298506293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28694237387664912199004195 43041356081497368298506293)
                    ·
                      refine ⟨4035127132640378277984965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43041356081497368298506293 4035127132640378277984965)
                      ·
                        rfl

theorem cell23_7858382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_7858382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858382 prefixEnd_7858382 := by exact prefixLift 7858382
  have htrace : WordTrace (prefixWord ++ tailWord_7858382) baseStart_7858382 baseEnd_7858382 := by
    simpa [prefixWord, tailWord_7858382, baseEnd_7858382] using wordTrace_append hprefix tailTrace_7858382
  have hstable : (prefixWord ++ tailWord_7858382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858382).length < 2 ^ (prefixWord ++ tailWord_7858382).sum := by decide
  have hdescent : baseEnd_7858382 < baseStart_7858382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858390 : List Nat := [5, 2, 1, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_7858390 : Nat := 118140960795 + 7858390 * 2 ^ 59
def prefixEnd_7858390 : Nat := 4983230072969 + 3 ^ 40 * 7858390 * 2
def baseEnd_7858390 : Nat := 4035131240485614246684929

theorem tailTrace_7858390 : CollatzResearch.WordTrace tailWord_7858390 prefixEnd_7858390 4035131240485614246684929 := by
  unfold tailWord_7858390
  simp only [CollatzResearch.WordTrace]
  refine ⟨17913689375025163187911289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191079353333601740671053749 17913689375025163187911289)
  ·
    refine ⟨13435267031268872390933467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17913689375025163187911289 13435267031268872390933467)
    ·
      refine ⟨20152900546903308586400201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13435267031268872390933467 20152900546903308586400201)
      ·
        refine ⟨15114675410177481439800151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20152900546903308586400201 15114675410177481439800151)
        ·
          refine ⟨22672013115266222159700227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15114675410177481439800151 22672013115266222159700227)
          ·
            refine ⟨34008019672899333239550341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22672013115266222159700227 34008019672899333239550341)
            ·
              refine ⟨6376503688668624982415689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34008019672899333239550341 6376503688668624982415689)
              ·
                refine ⟨4782377766501468736811767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6376503688668624982415689 4782377766501468736811767)
                ·
                  refine ⟨7173566649752203105217651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4782377766501468736811767 7173566649752203105217651)
                  ·
                    refine ⟨10760349974628304657826477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7173566649752203105217651 10760349974628304657826477)
                    ·
                      refine ⟨4035131240485614246684929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10760349974628304657826477 4035131240485614246684929)
                      ·
                        rfl

theorem cell23_7858390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_7858390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858390 prefixEnd_7858390 := by exact prefixLift 7858390
  have htrace : WordTrace (prefixWord ++ tailWord_7858390) baseStart_7858390 baseEnd_7858390 := by
    simpa [prefixWord, tailWord_7858390, baseEnd_7858390] using wordTrace_append hprefix tailTrace_7858390
  have hstable : (prefixWord ++ tailWord_7858390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858390).length < 2 ^ (prefixWord ++ tailWord_7858390).sum := by decide
  have hdescent : baseEnd_7858390 < baseStart_7858390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858412 : List Nat := [2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 3]
def baseStart_7858412 : Nat := 118140960795 + 7858412 * 2 ^ 59
def prefixEnd_7858412 : Nat := 4983230072969 + 3 ^ 40 * 7858412 * 2
def baseEnd_7858412 : Nat := 4035142537060013160609827

theorem tailTrace_7858412 : CollatzResearch.WordTrace tailWord_7858412 prefixEnd_7858412 4035142537060013160609827 := by
  unfold tailWord_7858412
  simp only [CollatzResearch.WordTrace]
  refine ⟨143309916203161454381940745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191079888270881939175920993 143309916203161454381940745)
  ·
    refine ⟨107482437152371090786455559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143309916203161454381940745 107482437152371090786455559)
    ·
      refine ⟨161223655728556636179683339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107482437152371090786455559 161223655728556636179683339)
      ·
        refine ⟨241835483592834954269525009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161223655728556636179683339 241835483592834954269525009)
        ·
          refine ⟨181376612694626215702143757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241835483592834954269525009 181376612694626215702143757)
          ·
            refine ⟨68016229760484830888303909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181376612694626215702143757 68016229760484830888303909)
            ·
              refine ⟨12753043080090905791556983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68016229760484830888303909 12753043080090905791556983)
              ·
                refine ⟨19129564620136358687335475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12753043080090905791556983 19129564620136358687335475)
                ·
                  refine ⟨28694346930204538031003213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19129564620136358687335475 28694346930204538031003213)
                  ·
                    refine ⟨10760380098826701761626205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28694346930204538031003213 10760380098826701761626205)
                    ·
                      refine ⟨4035142537060013160609827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10760380098826701761626205 4035142537060013160609827)
                      ·
                        rfl

theorem cell23_7858412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_7858412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858412 prefixEnd_7858412 := by exact prefixLift 7858412
  have htrace : WordTrace (prefixWord ++ tailWord_7858412) baseStart_7858412 baseEnd_7858412 := by
    simpa [prefixWord, tailWord_7858412, baseEnd_7858412] using wordTrace_append hprefix tailTrace_7858412
  have hstable : (prefixWord ++ tailWord_7858412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858412).length < 2 ^ (prefixWord ++ tailWord_7858412).sum := by decide
  have hdescent : baseEnd_7858412 < baseStart_7858412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858593 : List Nat := [1, 2, 3, 5, 1, 2, 1, 1, 2, 1, 4]
def baseStart_7858593 : Nat := 118140960795 + 7858593 * 2 ^ 59
def prefixEnd_7858593 : Nat := 4983230072969 + 3 ^ 40 * 7858593 * 2
def baseEnd_7858593 : Nat := 4035235477058476952446495

theorem tailTrace_7858593 : CollatzResearch.WordTrace tailWord_7858593 prefixEnd_7858593 4035235477058476952446495 := by
  unfold tailWord_7858593
  simp only [CollatzResearch.WordTrace]
  refine ⟨286626434018667176676220433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191084289345778117784146955 286626434018667176676220433)
  ·
    refine ⟨214969825514000382507165325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286626434018667176676220433 214969825514000382507165325)
    ·
      refine ⟨80613684567750143440186997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214969825514000382507165325 80613684567750143440186997)
      ·
        refine ⟨7557532928226575947517531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80613684567750143440186997 7557532928226575947517531)
        ·
          refine ⟨11336299392339863921276297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7557532928226575947517531 11336299392339863921276297)
          ·
            refine ⟨8502224544254897940957223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11336299392339863921276297 8502224544254897940957223)
            ·
              refine ⟨12753336816382346911435835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8502224544254897940957223 12753336816382346911435835)
              ·
                refine ⟨19130005224573520367153753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12753336816382346911435835 19130005224573520367153753)
                ·
                  refine ⟨14347503918430140275365315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19130005224573520367153753 14347503918430140275365315)
                  ·
                    refine ⟨21521255877645210413047973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14347503918430140275365315 21521255877645210413047973)
                    ·
                      refine ⟨4035235477058476952446495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21521255877645210413047973 4035235477058476952446495)
                      ·
                        rfl

theorem cell23_7858593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_7858593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858593 prefixEnd_7858593 := by exact prefixLift 7858593
  have htrace : WordTrace (prefixWord ++ tailWord_7858593) baseStart_7858593 baseEnd_7858593 := by
    simpa [prefixWord, tailWord_7858593, baseEnd_7858593] using wordTrace_append hprefix tailTrace_7858593
  have hstable : (prefixWord ++ tailWord_7858593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858593).length < 2 ^ (prefixWord ++ tailWord_7858593).sum := by decide
  have hdescent : baseEnd_7858593 < baseStart_7858593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858649 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 2, 6, 2]
def baseStart_7858649 : Nat := 118140960795 + 7858649 * 2 ^ 59
def prefixEnd_7858649 : Nat := 4983230072969 + 3 ^ 40 * 7858649 * 2
def baseEnd_7858649 : Nat := 4035264231975128733346237

theorem tailTrace_7858649 : CollatzResearch.WordTrace tailWord_7858649 prefixEnd_7858649 4035264231975128733346237 := by
  unfold tailWord_7858649
  simp only [CollatzResearch.WordTrace]
  refine ⟨286628476506464298240259001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191085651004309532160172667 286628476506464298240259001)
  ·
    refine ⟨214971357379848223680194251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286628476506464298240259001 214971357379848223680194251)
    ·
      refine ⟨322457036069772335520291377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214971357379848223680194251 322457036069772335520291377)
      ·
        refine ⟨241842777052329251640218533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322457036069772335520291377 241842777052329251640218533)
        ·
          refine ⟨45345520697311734682540975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241842777052329251640218533 45345520697311734682540975)
          ·
            refine ⟨68018281045967602023811463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45345520697311734682540975 68018281045967602023811463)
            ·
              refine ⟨102027421568951403035717195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68018281045967602023811463 102027421568951403035717195)
              ·
                refine ⟨153041132353427104553575793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102027421568951403035717195 153041132353427104553575793)
                ·
                  refine ⟨114780849265070328415181845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153041132353427104553575793 114780849265070328415181845)
                  ·
                    refine ⟨5380352309300171644461649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114780849265070328415181845 5380352309300171644461649)
                    ·
                      refine ⟨4035264231975128733346237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5380352309300171644461649 4035264231975128733346237)
                      ·
                        rfl

theorem cell23_7858649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 6, 2].length) (baseStart_7858649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858649 prefixEnd_7858649 := by exact prefixLift 7858649
  have htrace : WordTrace (prefixWord ++ tailWord_7858649) baseStart_7858649 baseEnd_7858649 := by
    simpa [prefixWord, tailWord_7858649, baseEnd_7858649] using wordTrace_append hprefix tailTrace_7858649
  have hstable : (prefixWord ++ tailWord_7858649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858649).length < 2 ^ (prefixWord ++ tailWord_7858649).sum := by decide
  have hdescent : baseEnd_7858649 < baseStart_7858649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858666 : List Nat := [3, 1, 3, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_7858666 : Nat := 118140960795 + 7858666 * 2 ^ 59
def prefixEnd_7858666 : Nat := 4983230072969 + 3 ^ 40 * 7858666 * 2
def baseEnd_7858666 : Nat := 4035272961146255166833659

theorem tailTrace_7858666 : CollatzResearch.WordTrace tailWord_7858666 prefixEnd_7858666 4035272961146255166833659 := by
  unfold tailWord_7858666
  simp only [CollatzResearch.WordTrace]
  refine ⟨71657274136850677535906963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191086064364935140095751901 71657274136850677535906963)
  ·
    refine ⟨107485911205276016303860445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71657274136850677535906963 107485911205276016303860445)
    ·
      refine ⟨40307216701978506113947667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107485911205276016303860445 40307216701978506113947667)
      ·
        refine ⟨60460825052967759170921501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40307216701978506113947667 60460825052967759170921501)
        ·
          refine ⟨22672809394862909689095563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60460825052967759170921501 22672809394862909689095563)
          ·
            refine ⟨34009214092294364533643345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22672809394862909689095563 34009214092294364533643345)
            ·
              refine ⟨25506910569220773400232509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34009214092294364533643345 25506910569220773400232509)
              ·
                refine ⟨9565091463457790025087191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25506910569220773400232509 9565091463457790025087191)
                ·
                  refine ⟨14347637195186685037630787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9565091463457790025087191 14347637195186685037630787)
                  ·
                    refine ⟨21521455792780027556446181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14347637195186685037630787 21521455792780027556446181)
                    ·
                      refine ⟨4035272961146255166833659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21521455792780027556446181 4035272961146255166833659)
                      ·
                        rfl

theorem cell23_7858666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_7858666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858666 prefixEnd_7858666 := by exact prefixLift 7858666
  have htrace : WordTrace (prefixWord ++ tailWord_7858666) baseStart_7858666 baseEnd_7858666 := by
    simpa [prefixWord, tailWord_7858666, baseEnd_7858666] using wordTrace_append hprefix tailTrace_7858666
  have hstable : (prefixWord ++ tailWord_7858666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858666).length < 2 ^ (prefixWord ++ tailWord_7858666).sum := by decide
  have hdescent : baseEnd_7858666 < baseStart_7858666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858677 : List Nat := [1, 3, 5, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_7858677 : Nat := 118140960795 + 7858677 * 2 ^ 59
def prefixEnd_7858677 : Nat := 4983230072969 + 3 ^ 40 * 7858677 * 2
def baseEnd_7858677 : Nat := 4035278609433454623796109

theorem tailTrace_7858677 : CollatzResearch.WordTrace tailWord_7858677 prefixEnd_7858677 4035278609433454623796109 := by
  unfold tailWord_7858677
  simp only [CollatzResearch.WordTrace]
  refine ⟨286629497750362859022278285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191086331833575239348185523 286629497750362859022278285)
  ·
    refine ⟨107486061656386072133354357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286629497750362859022278285 107486061656386072133354357)
    ·
      refine ⟨10076818280286194262501971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107486061656386072133354357 10076818280286194262501971)
      ·
        refine ⟨15115227420429291393752957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10076818280286194262501971 15115227420429291393752957)
        ·
          refine ⟨5668210282660984272657359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15115227420429291393752957 5668210282660984272657359)
          ·
            refine ⟨8502315423991476408986039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5668210282660984272657359 8502315423991476408986039)
            ·
              refine ⟨12753473135987214613479059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8502315423991476408986039 12753473135987214613479059)
              ·
                refine ⟨19130209703980821920218589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12753473135987214613479059 19130209703980821920218589)
                ·
                  refine ⟨7173828638992808220081971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19130209703980821920218589 7173828638992808220081971)
                  ·
                    refine ⟨10760742958489212330122957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7173828638992808220081971 10760742958489212330122957)
                    ·
                      refine ⟨4035278609433454623796109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10760742958489212330122957 4035278609433454623796109)
                      ·
                        rfl

theorem cell23_7858677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_7858677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858677 prefixEnd_7858677 := by exact prefixLift 7858677
  have htrace : WordTrace (prefixWord ++ tailWord_7858677) baseStart_7858677 baseEnd_7858677 := by
    simpa [prefixWord, tailWord_7858677, baseEnd_7858677] using wordTrace_append hprefix tailTrace_7858677
  have hstable : (prefixWord ++ tailWord_7858677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858677).length < 2 ^ (prefixWord ++ tailWord_7858677).sum := by decide
  have hdescent : baseEnd_7858677 < baseStart_7858677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858689 : List Nat := [1, 2, 4, 1, 3, 2, 2, 8]
def baseStart_7858689 : Nat := 118140960795 + 7858689 * 2 ^ 59
def prefixEnd_7858689 : Nat := 4983230072969 + 3 ^ 40 * 7858689 * 2
def baseEnd_7858689 : Nat := 149454991525974391735039

theorem tailTrace_7858689 : CollatzResearch.WordTrace tailWord_7858689 prefixEnd_7858689 149454991525974391735039 := by
  unfold tailWord_7858689
  simp only [CollatzResearch.WordTrace]
  refine ⟨286629935426319385071715121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191086623617546256714476747 286629935426319385071715121)
  ·
    refine ⟨214972451569739538803786341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286629935426319385071715121 214972451569739538803786341)
    ·
      refine ⟨40307334669326163525709939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214972451569739538803786341 40307334669326163525709939)
      ·
        refine ⟨60461002003989245288564909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40307334669326163525709939 60461002003989245288564909)
        ·
          refine ⟨22672875751495966983211841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60461002003989245288564909 22672875751495966983211841)
          ·
            refine ⟨17004656813621975237408881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22672875751495966983211841 17004656813621975237408881)
            ·
              refine ⟨12753492610216481428056661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17004656813621975237408881 12753492610216481428056661)
              ·
                refine ⟨149454991525974391735039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12753492610216481428056661 149454991525974391735039)
                ·
                  rfl

theorem cell23_7858689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 8].length) (baseStart_7858689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858689 prefixEnd_7858689 := by exact prefixLift 7858689
  have htrace : WordTrace (prefixWord ++ tailWord_7858689) baseStart_7858689 baseEnd_7858689 := by
    simpa [prefixWord, tailWord_7858689, baseEnd_7858689] using wordTrace_append hprefix tailTrace_7858689
  have hstable : (prefixWord ++ tailWord_7858689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858689).length < 2 ^ (prefixWord ++ tailWord_7858689).sum := by decide
  have hdescent : baseEnd_7858689 < baseStart_7858689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858716 : List Nat := [2, 2, 3, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_7858716 : Nat := 118140960795 + 7858716 * 2 ^ 59
def prefixEnd_7858716 : Nat := 4983230072969 + 3 ^ 40 * 7858716 * 2
def baseEnd_7858716 : Nat := 4035298635178979971208429

theorem tailTrace_7858716 : CollatzResearch.WordTrace tailWord_7858716 prefixEnd_7858716 4035298635178979971208429 := by
  unfold tailWord_7858716
  simp only [CollatzResearch.WordTrace]
  refine ⟨143315460098610784341474001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191087280131481045788632001 143315460098610784341474001)
  ·
    refine ⟨107486595073958088256105501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143315460098610784341474001 107486595073958088256105501)
    ·
      refine ⟨40307473152734283096039563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107486595073958088256105501 40307473152734283096039563)
      ·
        refine ⟨60461209729101424644059345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40307473152734283096039563 60461209729101424644059345)
        ·
          refine ⟨45345907296826068483044509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60461209729101424644059345 45345907296826068483044509)
          ·
            refine ⟨17004715236309775681141691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45345907296826068483044509 17004715236309775681141691)
            ·
              refine ⟨25507072854464663521712537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17004715236309775681141691 25507072854464663521712537)
              ·
                refine ⟨19130304640848497641284403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25507072854464663521712537 19130304640848497641284403)
                ·
                  refine ⟨28695456961272746461926605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19130304640848497641284403 28695456961272746461926605)
                  ·
                    refine ⟨10760796360477279923222477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28695456961272746461926605 10760796360477279923222477)
                    ·
                      refine ⟨4035298635178979971208429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10760796360477279923222477 4035298635178979971208429)
                      ·
                        rfl

theorem cell23_7858716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_7858716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858716 prefixEnd_7858716 := by exact prefixLift 7858716
  have htrace : WordTrace (prefixWord ++ tailWord_7858716) baseStart_7858716 baseEnd_7858716 := by
    simpa [prefixWord, tailWord_7858716, baseEnd_7858716] using wordTrace_append hprefix tailTrace_7858716
  have hstable : (prefixWord ++ tailWord_7858716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858716).length < 2 ^ (prefixWord ++ tailWord_7858716).sum := by decide
  have hdescent : baseEnd_7858716 < baseStart_7858716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858720 : List Nat := [2, 1, 1, 6, 2, 1, 3, 1, 1, 2, 3]
def baseStart_7858720 : Nat := 118140960795 + 7858720 * 2 ^ 59
def prefixEnd_7858720 : Nat := 4983230072969 + 3 ^ 40 * 7858720 * 2
def baseEnd_7858720 : Nat := 4035300689101597955558411

theorem tailTrace_7858720 : CollatzResearch.WordTrace tailWord_7858720 prefixEnd_7858720 4035300689101597955558411 := by
  unfold tailWord_7858720
  simp only [CollatzResearch.WordTrace]
  refine ⟨143315533044603538683046807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191087377392804718244062409 143315533044603538683046807)
  ·
    refine ⟨214973299566905308024570211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143315533044603538683046807 214973299566905308024570211)
    ·
      refine ⟨322459949350357962036855317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214973299566905308024570211 322459949350357962036855317)
      ·
        refine ⟨15115310125798029470477593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 322459949350357962036855317 15115310125798029470477593)
        ·
          refine ⟨11336482594348522102858195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15115310125798029470477593 11336482594348522102858195)
          ·
            refine ⟨17004723891522783154287293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11336482594348522102858195 17004723891522783154287293)
            ·
              refine ⟨6376771459321043682857735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17004723891522783154287293 6376771459321043682857735)
              ·
                refine ⟨9565157188981565524286603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6376771459321043682857735 9565157188981565524286603)
                ·
                  refine ⟨14347735783472348286429905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9565157188981565524286603 14347735783472348286429905)
                  ·
                    refine ⟨10760801837604261214822429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14347735783472348286429905 10760801837604261214822429)
                    ·
                      refine ⟨4035300689101597955558411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10760801837604261214822429 4035300689101597955558411)
                      ·
                        rfl

theorem cell23_7858720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_7858720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858720 prefixEnd_7858720 := by exact prefixLift 7858720
  have htrace : WordTrace (prefixWord ++ tailWord_7858720) baseStart_7858720 baseEnd_7858720 := by
    simpa [prefixWord, tailWord_7858720, baseEnd_7858720] using wordTrace_append hprefix tailTrace_7858720
  have hstable : (prefixWord ++ tailWord_7858720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858720).length < 2 ^ (prefixWord ++ tailWord_7858720).sum := by decide
  have hdescent : baseEnd_7858720 < baseStart_7858720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858732 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 3, 8]
def baseStart_7858732 : Nat := 118140960795 + 7858732 * 2 ^ 59
def prefixEnd_7858732 : Nat := 4983230072969 + 3 ^ 40 * 7858732 * 2
def baseEnd_7858732 : Nat := 1345102283623150636202785

theorem tailTrace_7858732 : CollatzResearch.WordTrace tailWord_7858732 prefixEnd_7858732 1345102283623150636202785 := by
  unfold tailWord_7858732
  simp only [CollatzResearch.WordTrace]
  refine ⟨143315751882581801707765225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191087669176775735610353633 143315751882581801707765225)
  ·
    refine ⟨107486813911936351280823919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143315751882581801707765225 107486813911936351280823919)
    ·
      refine ⟨161230220867904526921235879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107486813911936351280823919 161230220867904526921235879)
      ·
        refine ⟨241845331301856790381853819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161230220867904526921235879 241845331301856790381853819)
        ·
          refine ⟨362767996952785185572780729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241845331301856790381853819 362767996952785185572780729)
          ·
            refine ⟨272075997714588889179585547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362767996952785185572780729 272075997714588889179585547)
            ·
              refine ⟨408113996571883333769378321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272075997714588889179585547 408113996571883333769378321)
              ·
                refine ⟨306085497428912500327033741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408113996571883333769378321 306085497428912500327033741)
                ·
                  refine ⟨114782061535842187622637653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306085497428912500327033741 114782061535842187622637653)
                  ·
                    refine ⟨1345102283623150636202785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114782061535842187622637653 1345102283623150636202785)
                    ·
                      rfl

theorem cell23_7858732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_7858732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858732 prefixEnd_7858732 := by exact prefixLift 7858732
  have htrace : WordTrace (prefixWord ++ tailWord_7858732) baseStart_7858732 baseEnd_7858732 := by
    simpa [prefixWord, tailWord_7858732, baseEnd_7858732] using wordTrace_append hprefix tailTrace_7858732
  have hstable : (prefixWord ++ tailWord_7858732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858732).length < 2 ^ (prefixWord ++ tailWord_7858732).sum := by decide
  have hdescent : baseEnd_7858732 < baseStart_7858732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858740 : List Nat := [2, 5, 1, 3, 2, 1, 1, 8]
def baseStart_7858740 : Nat := 118140960795 + 7858740 * 2 ^ 59
def prefixEnd_7858740 : Nat := 4983230072969 + 3 ^ 40 * 7858740 * 2
def baseEnd_7858740 : Nat := 149455961433877328789197

theorem tailTrace_7858740 : CollatzResearch.WordTrace tailWord_7858740 prefixEnd_7858740 149455961433877328789197 := by
  unfold tailWord_7858740
  simp only [CollatzResearch.WordTrace]
  refine ⟨143315897774567310390910837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191087863699423080521214449 143315897774567310390910837)
  ·
    refine ⟨13435865416365685349147891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143315897774567310390910837 13435865416365685349147891)
    ·
      refine ⟨20153798124548528023721837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13435865416365685349147891 20153798124548528023721837)
      ·
        refine ⟨7557674296705698008895689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20153798124548528023721837 7557674296705698008895689)
        ·
          refine ⟨5668255722529273506671767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7557674296705698008895689 5668255722529273506671767)
          ·
            refine ⟨8502383583793910260007651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5668255722529273506671767 8502383583793910260007651)
            ·
              refine ⟨12753575375690865390011477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8502383583793910260007651 12753575375690865390011477)
              ·
                refine ⟨149455961433877328789197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12753575375690865390011477 149455961433877328789197)
                ·
                  rfl

theorem cell23_7858740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 8].length) (baseStart_7858740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858740 prefixEnd_7858740 := by exact prefixLift 7858740
  have htrace : WordTrace (prefixWord ++ tailWord_7858740) baseStart_7858740 baseEnd_7858740 := by
    simpa [prefixWord, tailWord_7858740, baseEnd_7858740] using wordTrace_append hprefix tailTrace_7858740
  have hstable : (prefixWord ++ tailWord_7858740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858740).length < 2 ^ (prefixWord ++ tailWord_7858740).sum := by decide
  have hdescent : baseEnd_7858740 < baseStart_7858740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858749 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 1, 8]
def baseStart_7858749 : Nat := 118140960795 + 7858749 * 2 ^ 59
def prefixEnd_7858749 : Nat := 4983230072969 + 3 ^ 40 * 7858749 * 2
def baseEnd_7858749 : Nat := 1345105193346859447365259

theorem tailTrace_7858749 : CollatzResearch.WordTrace tailWord_7858749 prefixEnd_7858749 1345105193346859447365259 := by
  unfold tailWord_7858749
  simp only [CollatzResearch.WordTrace]
  refine ⟨286632123806102015318899301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191088082537401343545932867 286632123806102015318899301)
  ·
    refine ⟨53743523213644127872293619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286632123806102015318899301 53743523213644127872293619)
    ·
      refine ⟨80615284820466191808440429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53743523213644127872293619 80615284820466191808440429)
      ·
        refine ⟨30230731807674821928165161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80615284820466191808440429 30230731807674821928165161)
        ·
          refine ⟨22673048855756116446123871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30230731807674821928165161 22673048855756116446123871)
          ·
            refine ⟨34009573283634174669185807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22673048855756116446123871 34009573283634174669185807)
            ·
              refine ⟨51014359925451262003778711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34009573283634174669185807 51014359925451262003778711)
              ·
                refine ⟨76521539888176893005668067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51014359925451262003778711 76521539888176893005668067)
                ·
                  refine ⟨114782309832265339508502101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76521539888176893005668067 114782309832265339508502101)
                  ·
                    refine ⟨1345105193346859447365259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114782309832265339508502101 1345105193346859447365259)
                    ·
                      rfl

theorem cell23_7858749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_7858749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858749 prefixEnd_7858749 := by exact prefixLift 7858749
  have htrace : WordTrace (prefixWord ++ tailWord_7858749) baseStart_7858749 baseEnd_7858749 := by
    simpa [prefixWord, tailWord_7858749, baseEnd_7858749] using wordTrace_append hprefix tailTrace_7858749
  have hstable : (prefixWord ++ tailWord_7858749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858749).length < 2 ^ (prefixWord ++ tailWord_7858749).sum := by decide
  have hdescent : baseEnd_7858749 < baseStart_7858749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858750 : List Nat := [4, 2, 1, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_7858750 : Nat := 118140960795 + 7858750 * 2 ^ 59
def prefixEnd_7858750 : Nat := 4983230072969 + 3 ^ 40 * 7858750 * 2
def baseEnd_7858750 : Nat := 4035316093521232838183273

theorem tailTrace_7858750 : CollatzResearch.WordTrace tailWord_7858750 prefixEnd_7858750 4035316093521232838183273 := by
  unfold tailWord_7858750
  simp only [CollatzResearch.WordTrace]
  refine ⟨35829020034887299061210713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191088106852732261659790469 35829020034887299061210713)
  ·
    refine ⟨26871765026165474295908035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35829020034887299061210713 26871765026165474295908035)
    ·
      refine ⟨40307647539248211443862053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26871765026165474295908035 40307647539248211443862053)
      ·
        refine ⟨7557683913609039645724135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40307647539248211443862053 7557683913609039645724135)
        ·
          refine ⟨11336525870413559468586203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7557683913609039645724135 11336525870413559468586203)
          ·
            refine ⟨17004788805620339202879305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11336525870413559468586203 17004788805620339202879305)
            ·
              refine ⟨12753591604215254402159479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17004788805620339202879305 12753591604215254402159479)
              ·
                refine ⟨19130387406322881603239219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12753591604215254402159479 19130387406322881603239219)
                ·
                  refine ⟨28695581109484322404858829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19130387406322881603239219 28695581109484322404858829)
                  ·
                    refine ⟨10760842916056620901822061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28695581109484322404858829 10760842916056620901822061)
                    ·
                      refine ⟨4035316093521232838183273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10760842916056620901822061 4035316093521232838183273)
                      ·
                        rfl

theorem cell23_7858750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_7858750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858750 prefixEnd_7858750 := by exact prefixLift 7858750
  have htrace : WordTrace (prefixWord ++ tailWord_7858750) baseStart_7858750 baseEnd_7858750 := by
    simpa [prefixWord, tailWord_7858750, baseEnd_7858750] using wordTrace_append hprefix tailTrace_7858750
  have hstable : (prefixWord ++ tailWord_7858750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858750).length < 2 ^ (prefixWord ++ tailWord_7858750).sum := by decide
  have hdescent : baseEnd_7858750 < baseStart_7858750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858796 : List Nat := [2, 2, 1, 1, 3, 1, 4, 4, 5]
def baseStart_7858796 : Nat := 118140960795 + 7858796 * 2 ^ 59
def prefixEnd_7858796 : Nat := 4983230072969 + 3 ^ 40 * 7858796 * 2
def baseEnd_7858796 : Nat := 448371079292371073134229

theorem tailTrace_7858796 : CollatzResearch.WordTrace tailWord_7858796 prefixEnd_7858796 448371079292371073134229 := by
  unfold tailWord_7858796
  simp only [CollatzResearch.WordTrace]
  refine ⟨143316919018465871172930121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191089225357954494897240161 143316919018465871172930121)
  ·
    refine ⟨107487689263849403379697591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143316919018465871172930121 107487689263849403379697591)
    ·
      refine ⟨161231533895774105069546387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107487689263849403379697591 161231533895774105069546387)
      ·
        refine ⟨241847300843661157604319581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161231533895774105069546387 241847300843661157604319581)
        ·
          refine ⟨90692737816372934101619843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241847300843661157604319581 90692737816372934101619843)
          ·
            refine ⟨136039106724559401152429765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90692737816372934101619843 136039106724559401152429765)
            ·
              refine ⟨25507332510854887716080581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136039106724559401152429765 25507332510854887716080581)
              ·
                refine ⟨4782624845785291446765109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25507332510854887716080581 4782624845785291446765109)
                ·
                  refine ⟨448371079292371073134229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4782624845785291446765109 448371079292371073134229)
                  ·
                    rfl

theorem cell23_7858796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 5].length) (baseStart_7858796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858796 prefixEnd_7858796 := by exact prefixLift 7858796
  have htrace : WordTrace (prefixWord ++ tailWord_7858796) baseStart_7858796 baseEnd_7858796 := by
    simpa [prefixWord, tailWord_7858796, baseEnd_7858796] using wordTrace_append hprefix tailTrace_7858796
  have hstable : (prefixWord ++ tailWord_7858796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858796).length < 2 ^ (prefixWord ++ tailWord_7858796).sum := by decide
  have hdescent : baseEnd_7858796 < baseStart_7858796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858809 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 1, 7]
def baseStart_7858809 : Nat := 118140960795 + 7858809 * 2 ^ 59
def prefixEnd_7858809 : Nat := 4983230072969 + 3 ^ 40 * 7858809 * 2
def baseEnd_7858809 : Nat := 1345115462959949369115167

theorem tailTrace_7858809 : CollatzResearch.WordTrace tailWord_7858809 prefixEnd_7858809 1345115462959949369115167 := by
  unfold tailWord_7858809
  simp only [CollatzResearch.WordTrace]
  refine ⟨286634312185884645566083481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191089541457256430377388987 286634312185884645566083481)
  ·
    refine ⟨214975734139413484174562611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286634312185884645566083481 214975734139413484174562611)
    ·
      refine ⟨322463601209120226261843917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214975734139413484174562611 322463601209120226261843917)
      ·
        refine ⟨120923850453420084848191469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322463601209120226261843917 120923850453420084848191469)
        ·
          refine ⟨45346443920032531818071801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120923850453420084848191469 45346443920032531818071801)
          ·
            refine ⟨34009832940024398863553851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45346443920032531818071801 34009832940024398863553851)
            ·
              refine ⟨51014749410036598295330777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34009832940024398863553851 51014749410036598295330777)
              ·
                refine ⟨38261062057527448721498083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51014749410036598295330777 38261062057527448721498083)
                ·
                  refine ⟨57391593086291173082247125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38261062057527448721498083 57391593086291173082247125)
                  ·
                    refine ⟨1345115462959949369115167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57391593086291173082247125 1345115462959949369115167)
                    ·
                      rfl

theorem cell23_7858809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 7].length) (baseStart_7858809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858809 prefixEnd_7858809 := by exact prefixLift 7858809
  have htrace : WordTrace (prefixWord ++ tailWord_7858809) baseStart_7858809 baseEnd_7858809 := by
    simpa [prefixWord, tailWord_7858809, baseEnd_7858809] using wordTrace_append hprefix tailTrace_7858809
  have hstable : (prefixWord ++ tailWord_7858809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858809).length < 2 ^ (prefixWord ++ tailWord_7858809).sum := by decide
  have hdescent : baseEnd_7858809 < baseStart_7858809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858858 : List Nat := [3, 1, 5, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_7858858 : Nat := 118140960795 + 7858858 * 2 ^ 59
def prefixEnd_7858858 : Nat := 4983230072969 + 3 ^ 40 * 7858858 * 2
def baseEnd_7858858 : Nat := 4035371549431918415632777

theorem tailTrace_7858858 : CollatzResearch.WordTrace tailWord_7858858 prefixEnd_7858858 4035371549431918415632777 := by
  unfold tailWord_7858858
  simp only [CollatzResearch.WordTrace]
  refine ⟨71659024840676781733654307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191090732908471417956411485 71659024840676781733654307)
  ·
    refine ⟨107488537261015172600481461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71659024840676781733654307 107488537261015172600481461)
    ·
      refine ⟨10077050368220172431295137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107488537261015172600481461 10077050368220172431295137)
      ·
        refine ⟨7557787776165129323471353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10077050368220172431295137 7557787776165129323471353)
        ·
          refine ⟨5668340832123846992603515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7557787776165129323471353 5668340832123846992603515)
          ·
            refine ⟨8502511248185770488905273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5668340832123846992603515 8502511248185770488905273)
            ·
              refine ⟨6376883436139327866678955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8502511248185770488905273 6376883436139327866678955)
              ·
                refine ⟨9565325154208991800018433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6376883436139327866678955 9565325154208991800018433)
                ·
                  refine ⟨7173993865656743850013825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9565325154208991800018433 7173993865656743850013825)
                  ·
                    refine ⟨5380495399242557887510369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7173993865656743850013825 5380495399242557887510369)
                    ·
                      refine ⟨4035371549431918415632777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5380495399242557887510369 4035371549431918415632777)
                      ·
                        rfl

theorem cell23_7858858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_7858858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858858 prefixEnd_7858858 := by exact prefixLift 7858858
  have htrace : WordTrace (prefixWord ++ tailWord_7858858) baseStart_7858858 baseEnd_7858858 := by
    simpa [prefixWord, tailWord_7858858, baseEnd_7858858] using wordTrace_append hprefix tailTrace_7858858
  have hstable : (prefixWord ++ tailWord_7858858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858858).length < 2 ^ (prefixWord ++ tailWord_7858858).sum := by decide
  have hdescent : baseEnd_7858858 < baseStart_7858858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858866 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3]
def baseStart_7858866 : Nat := 118140960795 + 7858866 * 2 ^ 59
def prefixEnd_7858866 : Nat := 4983230072969 + 3 ^ 40 * 7858866 * 2
def baseEnd_7858866 : Nat := 4035375657277154384332739

theorem tailTrace_7858866 : CollatzResearch.WordTrace tailWord_7858866 prefixEnd_7858866 4035375657277154384332739 := by
  unfold tailWord_7858866
  simp only [CollatzResearch.WordTrace]
  refine ⟨71659097786669536075227113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191090927431118762867272301 71659097786669536075227113)
  ·
    refine ⟨53744323340002152056420335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71659097786669536075227113 53744323340002152056420335)
    ·
      refine ⟨80616485010003228084630503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53744323340002152056420335 80616485010003228084630503)
      ·
        refine ⟨120924727515004842126945755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80616485010003228084630503 120924727515004842126945755)
        ·
          refine ⟨181387091272507263190418633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120924727515004842126945755 181387091272507263190418633)
          ·
            refine ⟨136040318454380447392813975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181387091272507263190418633 136040318454380447392813975)
            ·
              refine ⟨204060477681570671089220963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136040318454380447392813975 204060477681570671089220963)
              ·
                refine ⟨306090716522356006633831445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204060477681570671089220963 306090716522356006633831445)
                ·
                  refine ⟨14348002336985437810960849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 306090716522356006633831445 14348002336985437810960849)
                  ·
                    refine ⟨10761001752739078358220637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14348002336985437810960849 10761001752739078358220637)
                    ·
                      refine ⟨4035375657277154384332739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10761001752739078358220637 4035375657277154384332739)
                      ·
                        rfl

theorem cell23_7858866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_7858866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858866 prefixEnd_7858866 := by exact prefixLift 7858866
  have htrace : WordTrace (prefixWord ++ tailWord_7858866) baseStart_7858866 baseEnd_7858866 := by
    simpa [prefixWord, tailWord_7858866, baseEnd_7858866] using wordTrace_append hprefix tailTrace_7858866
  have hstable : (prefixWord ++ tailWord_7858866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858866).length < 2 ^ (prefixWord ++ tailWord_7858866).sum := by decide
  have hdescent : baseEnd_7858866 < baseStart_7858866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858916 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 3, 5]
def baseStart_7858916 : Nat := 118140960795 + 7858916 * 2 ^ 59
def prefixEnd_7858916 : Nat := 4983230072969 + 3 ^ 40 * 7858916 * 2
def baseEnd_7858916 : Nat := 1345133777103293062902503

theorem tailTrace_7858916 : CollatzResearch.WordTrace tailWord_7858916 prefixEnd_7858916 1345133777103293062902503 := by
  unfold tailWord_7858916
  simp only [CollatzResearch.WordTrace]
  refine ⟨143319107398248501420114301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191092143197664668560152401 143319107398248501420114301)
  ·
    refine ⟨53744665274343188032542863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143319107398248501420114301 53744665274343188032542863)
    ·
      refine ⟨80616997911514782048814295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53744665274343188032542863 80616997911514782048814295)
      ·
        refine ⟨120925496867272173073221443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80616997911514782048814295 120925496867272173073221443)
        ·
          refine ⟨181388245300908259609832165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120925496867272173073221443 181388245300908259609832165)
          ·
            refine ⟨34010295993920298676843531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181388245300908259609832165 34010295993920298676843531)
            ·
              refine ⟨51015443990880448015265297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34010295993920298676843531 51015443990880448015265297)
              ·
                refine ⟨38261582993160336011448973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51015443990880448015265297 38261582993160336011448973)
                ·
                  refine ⟨14348093622435126004293365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38261582993160336011448973 14348093622435126004293365)
                  ·
                    refine ⟨1345133777103293062902503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14348093622435126004293365 1345133777103293062902503)
                    ·
                      rfl

theorem cell23_7858916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_7858916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858916 prefixEnd_7858916 := by exact prefixLift 7858916
  have htrace : WordTrace (prefixWord ++ tailWord_7858916) baseStart_7858916 baseEnd_7858916 := by
    simpa [prefixWord, tailWord_7858916, baseEnd_7858916] using wordTrace_append hprefix tailTrace_7858916
  have hstable : (prefixWord ++ tailWord_7858916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858916).length < 2 ^ (prefixWord ++ tailWord_7858916).sum := by decide
  have hdescent : baseEnd_7858916 < baseStart_7858916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858930 : List Nat := [3, 2, 1, 3, 1, 3, 1, 2, 3, 1, 3]
def baseStart_7858930 : Nat := 118140960795 + 7858930 * 2 ^ 59
def prefixEnd_7858930 : Nat := 4983230072969 + 3 ^ 40 * 7858930 * 2
def baseEnd_7858930 : Nat := 4035408520039042133932445

theorem tailTrace_7858930 : CollatzResearch.WordTrace tailWord_7858930 prefixEnd_7858930 4035408520039042133932445 := by
  unfold tailWord_7858930
  simp only [CollatzResearch.WordTrace]
  refine ⟨71659681354611570807809561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191092483612297522154158829 71659681354611570807809561)
  ·
    refine ⟨53744761015958678105857171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71659681354611570807809561 53744761015958678105857171)
    ·
      refine ⟨80617141523938017158785757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53744761015958678105857171 80617141523938017158785757)
      ·
        refine ⟨30231428071476756434544659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80617141523938017158785757 30231428071476756434544659)
        ·
          refine ⟨45347142107215134651816989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30231428071476756434544659 45347142107215134651816989)
          ·
            refine ⟨17005178290205675494431371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45347142107215134651816989 17005178290205675494431371)
            ·
              refine ⟨25507767435308513241647057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17005178290205675494431371 25507767435308513241647057)
              ·
                refine ⟨19130825576481384931235293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25507767435308513241647057 19130825576481384931235293)
                ·
                  refine ⟨7174059591180519349213235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19130825576481384931235293 7174059591180519349213235)
                  ·
                    refine ⟨10761089386770779023819853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7174059591180519349213235 10761089386770779023819853)
                    ·
                      refine ⟨4035408520039042133932445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10761089386770779023819853 4035408520039042133932445)
                      ·
                        rfl

theorem cell23_7858930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_7858930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858930 prefixEnd_7858930 := by exact prefixLift 7858930
  have htrace : WordTrace (prefixWord ++ tailWord_7858930) baseStart_7858930 baseEnd_7858930 := by
    simpa [prefixWord, tailWord_7858930, baseEnd_7858930] using wordTrace_append hprefix tailTrace_7858930
  have hstable : (prefixWord ++ tailWord_7858930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858930).length < 2 ^ (prefixWord ++ tailWord_7858930).sum := by decide
  have hdescent : baseEnd_7858930 < baseStart_7858930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858936 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 3, 1, 4]
def baseStart_7858936 : Nat := 118140960795 + 7858936 * 2 ^ 59
def prefixEnd_7858936 : Nat := 4983230072969 + 3 ^ 40 * 7858936 * 2
def baseEnd_7858936 : Nat := 4035411600922969110457417

theorem tailTrace_7858936 : CollatzResearch.WordTrace tailWord_7858936 prefixEnd_7858936 4035411600922969110457417 := by
  unfold tailWord_7858936
  simp only [CollatzResearch.WordTrace]
  refine ⟨143319472128212273127978331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191092629504283030837304441 143319472128212273127978331)
  ·
    refine ⟨214979208192318409691967497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143319472128212273127978331 214979208192318409691967497)
    ·
      refine ⟨161234406144238807268975623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214979208192318409691967497 161234406144238807268975623)
      ·
        refine ⟨241851609216358210903463435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161234406144238807268975623 241851609216358210903463435)
        ·
          refine ⟨362777413824537316355195153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241851609216358210903463435 362777413824537316355195153)
          ·
            refine ⟨272083060368402987266396365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362777413824537316355195153 272083060368402987266396365)
            ·
              refine ⟨102031147638151120224898637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272083060368402987266396365 102031147638151120224898637)
              ·
                refine ⟨38261680364306670084336989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102031147638151120224898637 38261680364306670084336989)
                ·
                  refine ⟨14348130136615001281626371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38261680364306670084336989 14348130136615001281626371)
                  ·
                    refine ⟨21522195204922501922439557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14348130136615001281626371 21522195204922501922439557)
                    ·
                      refine ⟨4035411600922969110457417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21522195204922501922439557 4035411600922969110457417)
                      ·
                        rfl

theorem cell23_7858936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_7858936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858936 prefixEnd_7858936 := by exact prefixLift 7858936
  have htrace : WordTrace (prefixWord ++ tailWord_7858936) baseStart_7858936 baseEnd_7858936 := by
    simpa [prefixWord, tailWord_7858936, baseEnd_7858936] using wordTrace_append hprefix tailTrace_7858936
  have hstable : (prefixWord ++ tailWord_7858936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858936).length < 2 ^ (prefixWord ++ tailWord_7858936).sum := by decide
  have hdescent : baseEnd_7858936 < baseStart_7858936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858940 : List Nat := [2, 2, 2, 1, 3, 2, 3, 1, 2, 3, 2]
def baseStart_7858940 : Nat := 118140960795 + 7858940 * 2 ^ 59
def prefixEnd_7858940 : Nat := 4983230072969 + 3 ^ 40 * 7858940 * 2
def baseEnd_7858940 : Nat := 4035413654845587094807399

theorem tailTrace_7858940 : CollatzResearch.WordTrace tailWord_7858940 prefixEnd_7858940 4035413654845587094807399 := by
  unfold tailWord_7858940
  simp only [CollatzResearch.WordTrace]
  refine ⟨143319545074205027469551137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191092726765606703292734849 143319545074205027469551137)
  ·
    refine ⟨107489658805653770602163353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143319545074205027469551137 107489658805653770602163353)
    ·
      refine ⟨80617244104240327951622515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107489658805653770602163353 80617244104240327951622515)
      ·
        refine ⟨120925866156360491927433773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80617244104240327951622515 120925866156360491927433773)
        ·
          refine ⟨45347199808635184472787665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120925866156360491927433773 45347199808635184472787665)
          ·
            refine ⟨34010399856476388354590749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45347199808635184472787665 34010399856476388354590749)
            ·
              refine ⟨12753899946178645632971531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34010399856476388354590749 12753899946178645632971531)
              ·
                refine ⟨19130849919267968449457297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12753899946178645632971531 19130849919267968449457297)
                ·
                  refine ⟨14348137439450976337092973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19130849919267968449457297 14348137439450976337092973)
                  ·
                    refine ⟨5380551539794116126409865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14348137439450976337092973 5380551539794116126409865)
                    ·
                      refine ⟨4035413654845587094807399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5380551539794116126409865 4035413654845587094807399)
                      ·
                        rfl

theorem cell23_7858940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_7858940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858940 prefixEnd_7858940 := by exact prefixLift 7858940
  have htrace : WordTrace (prefixWord ++ tailWord_7858940) baseStart_7858940 baseEnd_7858940 := by
    simpa [prefixWord, tailWord_7858940, baseEnd_7858940] using wordTrace_append hprefix tailTrace_7858940
  have hstable : (prefixWord ++ tailWord_7858940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858940).length < 2 ^ (prefixWord ++ tailWord_7858940).sum := by decide
  have hdescent : baseEnd_7858940 < baseStart_7858940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858956 : List Nat := [2, 2, 1, 2, 2, 1, 1, 5, 1, 1, 5]
def baseStart_7858956 : Nat := 118140960795 + 7858956 * 2 ^ 59
def prefixEnd_7858956 : Nat := 4983230072969 + 3 ^ 40 * 7858956 * 2
def baseEnd_7858956 : Nat := 4035421870536059032207325

theorem tailTrace_7858956 : CollatzResearch.WordTrace tailWord_7858956 prefixEnd_7858956 4035421870536059032207325 := by
  unfold tailWord_7858956
  simp only [CollatzResearch.WordTrace]
  refine ⟨143319836858176044835842361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191093115810901393114456481 143319836858176044835842361)
  ·
    refine ⟨107489877643632033626881771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143319836858176044835842361 107489877643632033626881771)
    ·
      refine ⟨161234816465448050440322657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107489877643632033626881771 161234816465448050440322657)
      ·
        refine ⟨120926112349086037830241993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161234816465448050440322657 120926112349086037830241993)
        ·
          refine ⟨90694584261814528372681495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120926112349086037830241993 90694584261814528372681495)
          ·
            refine ⟨136041876392721792559022243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90694584261814528372681495 136041876392721792559022243)
            ·
              refine ⟨204062814589082688838533365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136041876392721792559022243 204062814589082688838533365)
              ·
                refine ⟨19130888867726502078612503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204062814589082688838533365 19130888867726502078612503)
                ·
                  refine ⟨28696333301589753117918755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19130888867726502078612503 28696333301589753117918755)
                  ·
                    refine ⟨43044499952384629676878133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28696333301589753117918755 43044499952384629676878133)
                    ·
                      refine ⟨4035421870536059032207325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43044499952384629676878133 4035421870536059032207325)
                      ·
                        rfl

theorem cell23_7858956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_7858956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858956 prefixEnd_7858956 := by exact prefixLift 7858956
  have htrace : WordTrace (prefixWord ++ tailWord_7858956) baseStart_7858956 baseEnd_7858956 := by
    simpa [prefixWord, tailWord_7858956, baseEnd_7858956] using wordTrace_append hprefix tailTrace_7858956
  have hstable : (prefixWord ++ tailWord_7858956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858956).length < 2 ^ (prefixWord ++ tailWord_7858956).sum := by decide
  have hdescent : baseEnd_7858956 < baseStart_7858956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858959 : List Nat := [1, 1, 2, 1, 1, 1, 16]
def baseStart_7858959 : Nat := 118140960795 + 7858959 * 2 ^ 59
def prefixEnd_7858959 : Nat := 4983230072969 + 3 ^ 40 * 7858959 * 2
def baseEnd_7858959 : Nat := 49820042110839784203331

theorem tailTrace_7858959 : CollatzResearch.WordTrace tailWord_7858959 prefixEnd_7858959 49820042110839784203331 := by
  unfold tailWord_7858959
  simp only [CollatzResearch.WordTrace]
  refine ⟨286639783135341221184043931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191093188756894147456029287 286639783135341221184043931)
  ·
    refine ⟨429959674703011831776065897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286639783135341221184043931 429959674703011831776065897)
    ·
      refine ⟨322469756027258873832049423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429959674703011831776065897 322469756027258873832049423)
      ·
        refine ⟨483704634040888310748074135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322469756027258873832049423 483704634040888310748074135)
        ·
          refine ⟨725556951061332466122111203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483704634040888310748074135 725556951061332466122111203)
          ·
            refine ⟨1088335426591998699183166805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725556951061332466122111203 1088335426591998699183166805)
            ·
              refine ⟨49820042110839784203331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 16 1088335426591998699183166805 49820042110839784203331)
              ·
                rfl

theorem cell23_7858959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 16].length) (baseStart_7858959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858959 prefixEnd_7858959 := by exact prefixLift 7858959
  have htrace : WordTrace (prefixWord ++ tailWord_7858959) baseStart_7858959 baseEnd_7858959 := by
    simpa [prefixWord, tailWord_7858959, baseEnd_7858959] using wordTrace_append hprefix tailTrace_7858959
  have hstable : (prefixWord ++ tailWord_7858959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858959).length < 2 ^ (prefixWord ++ tailWord_7858959).sum := by decide
  have hdescent : baseEnd_7858959 < baseStart_7858959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858980 : List Nat := [2, 3, 1, 3, 3, 2, 1, 1, 1, 6]
def baseStart_7858980 : Nat := 118140960795 + 7858980 * 2 ^ 59
def prefixEnd_7858980 : Nat := 4983230072969 + 3 ^ 40 * 7858980 * 2
def baseEnd_7858980 : Nat := 1345144731357255646102405

theorem tailTrace_7858980 : CollatzResearch.WordTrace tailWord_7858980 prefixEnd_7858980 1345144731357255646102405 := by
  unfold tailWord_7858980
  simp only [CollatzResearch.WordTrace]
  refine ⟨143320274534132570885279197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191093699378843427847038929 143320274534132570885279197)
  ·
    refine ⟨53745102950299714081979699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143320274534132570885279197 53745102950299714081979699)
    ·
      refine ⟨80617654425449571122969549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53745102950299714081979699 80617654425449571122969549)
      ·
        refine ⟨30231620409543589171113581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80617654425449571122969549 30231620409543589171113581)
        ·
          refine ⟨11336857653578845939167593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30231620409543589171113581 11336857653578845939167593)
          ·
            refine ⟨8502643240184134454375695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11336857653578845939167593 8502643240184134454375695)
            ·
              refine ⟨12753964860276201681563543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8502643240184134454375695 12753964860276201681563543)
              ·
                refine ⟨19130947290414302522345315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12753964860276201681563543 19130947290414302522345315)
                ·
                  refine ⟨28696420935621453783517973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19130947290414302522345315 28696420935621453783517973)
                  ·
                    refine ⟨1345144731357255646102405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28696420935621453783517973 1345144731357255646102405)
                    ·
                      rfl

theorem cell23_7858980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_7858980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858980 prefixEnd_7858980 := by exact prefixLift 7858980
  have htrace : WordTrace (prefixWord ++ tailWord_7858980) baseStart_7858980 baseEnd_7858980 := by
    simpa [prefixWord, tailWord_7858980, baseEnd_7858980] using wordTrace_append hprefix tailTrace_7858980
  have hstable : (prefixWord ++ tailWord_7858980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858980).length < 2 ^ (prefixWord ++ tailWord_7858980).sum := by decide
  have hdescent : baseEnd_7858980 < baseStart_7858980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7858998 : List Nat := [5, 1, 2, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_7858998 : Nat := 118140960795 + 7858998 * 2 ^ 59
def prefixEnd_7858998 : Nat := 4983230072969 + 3 ^ 40 * 7858998 * 2
def baseEnd_7858998 : Nat := 4035443436723547867882133

theorem tailTrace_7858998 : CollatzResearch.WordTrace tailWord_7858998 prefixEnd_7858998 4035443436723547867882133 := by
  unfold tailWord_7858998
  simp only [CollatzResearch.WordTrace]
  refine ⟨17915075348887495677794603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191094137054799953896475765 17915075348887495677794603)
  ·
    refine ⟨26872613023331243516691905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17915075348887495677794603 26872613023331243516691905)
    ·
      refine ⟨20154459767498432637518929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26872613023331243516691905 20154459767498432637518929)
      ·
        refine ⟨15115844825623824478139197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20154459767498432637518929 15115844825623824478139197)
        ·
          refine ⟨5668441809608934179302199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15115844825623824478139197 5668441809608934179302199)
          ·
            refine ⟨8502662714413401268953299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5668441809608934179302199 8502662714413401268953299)
            ·
              refine ⟨12753994071620101903429949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8502662714413401268953299 12753994071620101903429949)
              ·
                refine ⟨4782747776857538213786231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12753994071620101903429949 4782747776857538213786231)
                ·
                  refine ⟨7174121665286307320679347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4782747776857538213786231 7174121665286307320679347)
                  ·
                    refine ⟨10761182497929460981019021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7174121665286307320679347 10761182497929460981019021)
                    ·
                      refine ⟨4035443436723547867882133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10761182497929460981019021 4035443436723547867882133)
                      ·
                        rfl

theorem cell23_7858998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_7858998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7858998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7858998 prefixEnd_7858998 := by exact prefixLift 7858998
  have htrace : WordTrace (prefixWord ++ tailWord_7858998) baseStart_7858998 baseEnd_7858998 := by
    simpa [prefixWord, tailWord_7858998, baseEnd_7858998] using wordTrace_append hprefix tailTrace_7858998
  have hstable : (prefixWord ++ tailWord_7858998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7858998).length < 2 ^ (prefixWord ++ tailWord_7858998).sum := by decide
  have hdescent : baseEnd_7858998 < baseStart_7858998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7858998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859016 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_7859016 : Nat := 118140960795 + 7859016 * 2 ^ 59
def prefixEnd_7859016 : Nat := 4983230072969 + 3 ^ 40 * 7859016 * 2
def baseEnd_7859016 : Nat := 4035452679375328797457049

theorem tailTrace_7859016 : CollatzResearch.WordTrace tailWord_7859016 prefixEnd_7859016 4035452679375328797457049 := by
  unfold tailWord_7859016
  simp only [CollatzResearch.WordTrace]
  refine ⟨143320931048067359959434451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191094574730756479945912601 143320931048067359959434451)
  ·
    refine ⟨214981396572101039939151677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143320931048067359959434451 214981396572101039939151677)
    ·
      refine ⟨80618023714537889977181879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214981396572101039939151677 80618023714537889977181879)
      ·
        refine ⟨120927035571806834965772819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80618023714537889977181879 120927035571806834965772819)
        ·
          refine ⟨181390553357710252448659229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120927035571806834965772819 181390553357710252448659229)
          ·
            refine ⟨68021457509141344668247211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181390553357710252448659229 68021457509141344668247211)
            ·
              refine ⟨102032186263712017002370817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68021457509141344668247211 102032186263712017002370817)
              ·
                refine ⟨76524139697784012751778113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102032186263712017002370817 76524139697784012751778113)
                ·
                  refine ⟨57393104773338009563833585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76524139697784012751778113 57393104773338009563833585)
                  ·
                    refine ⟨43044828580003507172875189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57393104773338009563833585 43044828580003507172875189)
                    ·
                      refine ⟨4035452679375328797457049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43044828580003507172875189 4035452679375328797457049)
                      ·
                        rfl

theorem cell23_7859016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_7859016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859016 prefixEnd_7859016 := by exact prefixLift 7859016
  have htrace : WordTrace (prefixWord ++ tailWord_7859016) baseStart_7859016 baseEnd_7859016 := by
    simpa [prefixWord, tailWord_7859016, baseEnd_7859016] using wordTrace_append hprefix tailTrace_7859016
  have hstable : (prefixWord ++ tailWord_7859016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859016).length < 2 ^ (prefixWord ++ tailWord_7859016).sum := by decide
  have hdescent : baseEnd_7859016 < baseStart_7859016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859020 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 4, 1, 3]
def baseStart_7859020 : Nat := 118140960795 + 7859020 * 2 ^ 59
def prefixEnd_7859020 : Nat := 4983230072969 + 3 ^ 40 * 7859020 * 2
def baseEnd_7859020 : Nat := 4035454733297946781807031

theorem tailTrace_7859020 : CollatzResearch.WordTrace tailWord_7859020 prefixEnd_7859020 4035454733297946781807031 := by
  unfold tailWord_7859020
  simp only [CollatzResearch.WordTrace]
  refine ⟨143321003994060114301007257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191094671992080152401343009 143321003994060114301007257)
  ·
    refine ⟨107490752995545085725755443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143321003994060114301007257 107490752995545085725755443)
    ·
      refine ⟨161236129493317628588633165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107490752995545085725755443 161236129493317628588633165)
      ·
        refine ⟨60463548559994110720737437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161236129493317628588633165 60463548559994110720737437)
        ·
          refine ⟨22673830709997791520276539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60463548559994110720737437 22673830709997791520276539)
          ·
            refine ⟨34010746064996687280414809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22673830709997791520276539 34010746064996687280414809)
            ·
              refine ⟨25508059548747515460311107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34010746064996687280414809 25508059548747515460311107)
              ·
                refine ⟨38262089323121273190466661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25508059548747515460311107 38262089323121273190466661)
                ·
                  refine ⟨7174141748085238723212499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38262089323121273190466661 7174141748085238723212499)
                  ·
                    refine ⟨10761212622127858084818749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7174141748085238723212499 10761212622127858084818749)
                    ·
                      refine ⟨4035454733297946781807031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10761212622127858084818749 4035454733297946781807031)
                      ·
                        rfl

theorem cell23_7859020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_7859020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859020 prefixEnd_7859020 := by exact prefixLift 7859020
  have htrace : WordTrace (prefixWord ++ tailWord_7859020) baseStart_7859020 baseEnd_7859020 := by
    simpa [prefixWord, tailWord_7859020, baseEnd_7859020] using wordTrace_append hprefix tailTrace_7859020
  have hstable : (prefixWord ++ tailWord_7859020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859020).length < 2 ^ (prefixWord ++ tailWord_7859020).sum := by decide
  have hdescent : baseEnd_7859020 < baseStart_7859020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859021 : List Nat := [1, 6, 1, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_7859021 : Nat := 118140960795 + 7859021 * 2 ^ 59
def prefixEnd_7859021 : Nat := 4983230072969 + 3 ^ 40 * 7859021 * 2
def baseEnd_7859021 : Nat := 4035455246778601277894527

theorem tailTrace_7859021 : CollatzResearch.WordTrace tailWord_7859021 prefixEnd_7859021 4035455246778601277894527 := by
  unfold tailWord_7859021
  simp only [CollatzResearch.WordTrace]
  refine ⟨286642044461116605772800917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191094696307411070515200611 286642044461116605772800917)
  ·
    refine ⟨13436345834114840895600043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 286642044461116605772800917 13436345834114840895600043)
    ·
      refine ⟨20154518751172261343400065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13436345834114840895600043 20154518751172261343400065)
      ·
        refine ⟨15115889063379196007550049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20154518751172261343400065 15115889063379196007550049)
        ·
          refine ⟨11336916797534397005662537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15115889063379196007550049 11336916797534397005662537)
          ·
            refine ⟨8502687598150797754246903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11336916797534397005662537 8502687598150797754246903)
            ·
              refine ⟨12754031397226196631370355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8502687598150797754246903 12754031397226196631370355)
              ·
                refine ⟨19131047095839294947055533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12754031397226196631370355 19131047095839294947055533)
                ·
                  refine ⟨7174142660939735605145825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19131047095839294947055533 7174142660939735605145825)
                  ·
                    refine ⟨5380606995704801703859369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7174142660939735605145825 5380606995704801703859369)
                    ·
                      refine ⟨4035455246778601277894527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5380606995704801703859369 4035455246778601277894527)
                      ·
                        rfl

theorem cell23_7859021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_7859021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859021 prefixEnd_7859021 := by exact prefixLift 7859021
  have htrace : WordTrace (prefixWord ++ tailWord_7859021) baseStart_7859021 baseEnd_7859021 := by
    simpa [prefixWord, tailWord_7859021, baseEnd_7859021] using wordTrace_append hprefix tailTrace_7859021
  have hstable : (prefixWord ++ tailWord_7859021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859021).length < 2 ^ (prefixWord ++ tailWord_7859021).sum := by decide
  have hdescent : baseEnd_7859021 < baseStart_7859021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859047 : List Nat := [1, 1, 5, 1, 2, 2, 3, 2, 1, 3, 2]
def baseStart_7859047 : Nat := 118140960795 + 7859047 * 2 ^ 59
def prefixEnd_7859047 : Nat := 4983230072969 + 3 ^ 40 * 7859047 * 2
def baseEnd_7859047 : Nat := 4035468597275618176169407

theorem tailTrace_7859047 : CollatzResearch.WordTrace tailWord_7859047 prefixEnd_7859047 4035468597275618176169407 := by
  unfold tailWord_7859047
  simp only [CollatzResearch.WordTrace]
  refine ⟨286642992759022412213247395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191095328506014941475498263 286642992759022412213247395)
  ·
    refine ⟨429964489138533618319871093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286642992759022412213247395 429964489138533618319871093)
    ·
      refine ⟨40309170856737526717487915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 429964489138533618319871093 40309170856737526717487915)
      ·
        refine ⟨60463756285106290076231873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40309170856737526717487915 60463756285106290076231873)
        ·
          refine ⟨45347817213829717557173905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60463756285106290076231873 45347817213829717557173905)
          ·
            refine ⟨34010862910372288167880429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45347817213829717557173905 34010862910372288167880429)
            ·
              refine ⟨12754073591389608062955161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34010862910372288167880429 12754073591389608062955161)
              ·
                refine ⟨9565555193542206047216371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12754073591389608062955161 9565555193542206047216371)
                ·
                  refine ⟨14348332790313309070824557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9565555193542206047216371 14348332790313309070824557)
                  ·
                    refine ⟨5380624796367490901559209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14348332790313309070824557 5380624796367490901559209)
                    ·
                      refine ⟨4035468597275618176169407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5380624796367490901559209 4035468597275618176169407)
                      ·
                        rfl

theorem cell23_7859047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_7859047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859047 prefixEnd_7859047 := by exact prefixLift 7859047
  have htrace : WordTrace (prefixWord ++ tailWord_7859047) baseStart_7859047 baseEnd_7859047 := by
    simpa [prefixWord, tailWord_7859047, baseEnd_7859047] using wordTrace_append hprefix tailTrace_7859047
  have hstable : (prefixWord ++ tailWord_7859047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859047).length < 2 ^ (prefixWord ++ tailWord_7859047).sum := by decide
  have hdescent : baseEnd_7859047 < baseStart_7859047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859077 : List Nat := [1, 3, 1, 1, 3, 3, 1, 4, 2, 2, 2]
def baseStart_7859077 : Nat := 118140960795 + 7859077 * 2 ^ 59
def prefixEnd_7859077 : Nat := 4983230072969 + 3 ^ 40 * 7859077 * 2
def baseEnd_7859077 : Nat := 4035484001695253058794269

theorem tailTrace_7859077 : CollatzResearch.WordTrace tailWord_7859077 prefixEnd_7859077 4035484001695253058794269 := by
  unfold tailWord_7859077
  simp only [CollatzResearch.WordTrace]
  refine ⟨286644086948913727336839485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191096057965942484891226323 286644086948913727336839485)
  ·
    refine ⟨107491532605842647751314807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286644086948913727336839485 107491532605842647751314807)
    ·
      refine ⟨161237298908763971626972211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107491532605842647751314807 161237298908763971626972211)
      ·
        refine ⟨241855948363145957440458317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161237298908763971626972211 241855948363145957440458317)
        ·
          refine ⟨90695980636179734040171869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241855948363145957440458317 90695980636179734040171869)
          ·
            refine ⟨34010992738567400265064451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90695980636179734040171869 34010992738567400265064451)
            ·
              refine ⟨51016489107851100397596677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34010992738567400265064451 51016489107851100397596677)
              ·
                refine ⟨9565591707722081324549377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51016489107851100397596677 9565591707722081324549377)
                ·
                  refine ⟨7174193780791560993412033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9565591707722081324549377 7174193780791560993412033)
                  ·
                    refine ⟨5380645335593670745059025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7174193780791560993412033 5380645335593670745059025)
                    ·
                      refine ⟨4035484001695253058794269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5380645335593670745059025 4035484001695253058794269)
                      ·
                        rfl

theorem cell23_7859077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 2, 2].length) (baseStart_7859077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859077 prefixEnd_7859077 := by exact prefixLift 7859077
  have htrace : WordTrace (prefixWord ++ tailWord_7859077) baseStart_7859077 baseEnd_7859077 := by
    simpa [prefixWord, tailWord_7859077, baseEnd_7859077] using wordTrace_append hprefix tailTrace_7859077
  have hstable : (prefixWord ++ tailWord_7859077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859077).length < 2 ^ (prefixWord ++ tailWord_7859077).sum := by decide
  have hdescent : baseEnd_7859077 < baseStart_7859077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859093 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 1, 5, 3]
def baseStart_7859093 : Nat := 118140960795 + 7859093 * 2 ^ 59
def prefixEnd_7859093 : Nat := 4983230072969 + 3 ^ 40 * 7859093 * 2
def baseEnd_7859093 : Nat := 4035492217385724996194195

theorem tailTrace_7859093 : CollatzResearch.WordTrace tailWord_7859093 prefixEnd_7859093 4035492217385724996194195 := by
  unfold tailWord_7859093
  simp only [CollatzResearch.WordTrace]
  refine ⟨286644670516855762069421933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191096447011237174712947955 286644670516855762069421933)
  ·
    refine ⟨107491751443820910776033225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286644670516855762069421933 107491751443820910776033225)
    ·
      refine ⟨80618813582865683082024919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107491751443820910776033225 80618813582865683082024919)
      ·
        refine ⟨120928220374298524623037379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80618813582865683082024919 120928220374298524623037379)
        ·
          refine ⟨181392330561447786934556069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120928220374298524623037379 181392330561447786934556069)
          ·
            refine ⟨34011061980271460050229263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181392330561447786934556069 34011061980271460050229263)
            ·
              refine ⟨51016592970407190075343895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34011061980271460050229263 51016592970407190075343895)
              ·
                refine ⟨76524889455610785113015843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51016592970407190075343895 76524889455610785113015843)
                ·
                  refine ⟨114787334183416177669523765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76524889455610785113015843 114787334183416177669523765)
                  ·
                    refine ⟨10761312579695266656517853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114787334183416177669523765 10761312579695266656517853)
                    ·
                      refine ⟨4035492217385724996194195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10761312579695266656517853 4035492217385724996194195)
                      ·
                        rfl

theorem cell23_7859093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_7859093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859093 prefixEnd_7859093 := by exact prefixLift 7859093
  have htrace : WordTrace (prefixWord ++ tailWord_7859093) baseStart_7859093 baseEnd_7859093 := by
    simpa [prefixWord, tailWord_7859093, baseEnd_7859093] using wordTrace_append hprefix tailTrace_7859093
  have hstable : (prefixWord ++ tailWord_7859093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859093).length < 2 ^ (prefixWord ++ tailWord_7859093).sum := by decide
  have hdescent : baseEnd_7859093 < baseStart_7859093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859100 : List Nat := [2, 2, 3, 3, 2, 1, 1, 2, 7]
def baseStart_7859100 : Nat := 118140960795 + 7859100 * 2 ^ 59
def prefixEnd_7859100 : Nat := 4983230072969 + 3 ^ 40 * 7859100 * 2
def baseEnd_7859100 : Nat := 448388423527811829867407

theorem tailTrace_7859100 : CollatzResearch.WordTrace tailWord_7859100 prefixEnd_7859100 448388423527811829867407 := by
  unfold tailWord_7859100
  simp only [CollatzResearch.WordTrace]
  refine ⟨143322462913915201132463377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191096617218553601509951169 143322462913915201132463377)
  ·
    refine ⟨107491847185436400849347533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143322462913915201132463377 107491847185436400849347533)
    ·
      refine ⟨40309442694538650318505325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107491847185436400849347533 40309442694538650318505325)
      ·
        refine ⟨15116041010451993869439497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40309442694538650318505325 15116041010451993869439497)
        ·
          refine ⟨11337030757838995402079623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15116041010451993869439497 11337030757838995402079623)
          ·
            refine ⟨17005546136758493103119435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11337030757838995402079623 17005546136758493103119435)
            ·
              refine ⟨25508319205137739654679153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17005546136758493103119435 25508319205137739654679153)
              ·
                refine ⟨19131239403853304741009365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25508319205137739654679153 19131239403853304741009365)
                ·
                  refine ⟨448388423527811829867407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19131239403853304741009365 448388423527811829867407)
                  ·
                    rfl

theorem cell23_7859100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 7].length) (baseStart_7859100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859100 prefixEnd_7859100 := by exact prefixLift 7859100
  have htrace : WordTrace (prefixWord ++ tailWord_7859100) baseStart_7859100 baseEnd_7859100 := by
    simpa [prefixWord, tailWord_7859100, baseEnd_7859100] using wordTrace_append hprefix tailTrace_7859100
  have hstable : (prefixWord ++ tailWord_7859100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859100).length < 2 ^ (prefixWord ++ tailWord_7859100).sum := by decide
  have hdescent : baseEnd_7859100 < baseStart_7859100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859153 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 3, 4, 3]
def baseStart_7859153 : Nat := 118140960795 + 7859153 * 2 ^ 59
def prefixEnd_7859153 : Nat := 4983230072969 + 3 ^ 40 * 7859153 * 2
def baseEnd_7859153 : Nat := 4035523026224994761443919

theorem tailTrace_7859153 : CollatzResearch.WordTrace tailWord_7859153 prefixEnd_7859153 4035523026224994761443919 := by
  unfold tailWord_7859153
  simp only [CollatzResearch.WordTrace]
  refine ⟨286646858896638392316606113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191097905931092261544404075 286646858896638392316606113)
  ·
    refine ⟨214985144172478794237454585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286646858896638392316606113 214985144172478794237454585)
    ·
      refine ⟨161238858129359095678090939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214985144172478794237454585 161238858129359095678090939)
      ·
        refine ⟨241858287194038643517136409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161238858129359095678090939 241858287194038643517136409)
        ·
          refine ⟨181393715395528982637852307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241858287194038643517136409 181393715395528982637852307)
          ·
            refine ⟨272090573093293473956778461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181393715395528982637852307 272090573093293473956778461)
            ·
              refine ⟨102033964909985052733791923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272090573093293473956778461 102033964909985052733791923)
              ·
                refine ⟨153050947364977579100687885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102033964909985052733791923 153050947364977579100687885)
                ·
                  refine ⟨57394105261866592162757957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153050947364977579100687885 57394105261866592162757957)
                  ·
                    refine ⟨10761394736599986030517117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57394105261866592162757957 10761394736599986030517117)
                    ·
                      refine ⟨4035523026224994761443919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10761394736599986030517117 4035523026224994761443919)
                      ·
                        rfl

theorem cell23_7859153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_7859153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859153 prefixEnd_7859153 := by exact prefixLift 7859153
  have htrace : WordTrace (prefixWord ++ tailWord_7859153) baseStart_7859153 baseEnd_7859153 := by
    simpa [prefixWord, tailWord_7859153, baseEnd_7859153] using wordTrace_append hprefix tailTrace_7859153
  have hstable : (prefixWord ++ tailWord_7859153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859153).length < 2 ^ (prefixWord ++ tailWord_7859153).sum := by decide
  have hdescent : baseEnd_7859153 < baseStart_7859153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859160 : List Nat := [2, 1, 2, 2, 2, 3, 2, 2, 3, 4]
def baseStart_7859160 : Nat := 118140960795 + 7859160 * 2 ^ 59
def prefixEnd_7859160 : Nat := 4983230072969 + 3 ^ 40 * 7859160 * 2
def baseEnd_7859160 : Nat := 1345175540196525411352129

theorem tailTrace_7859160 : CollatzResearch.WordTrace tailWord_7859160 prefixEnd_7859160 1345175540196525411352129 := by
  unfold tailWord_7859160
  simp only [CollatzResearch.WordTrace]
  refine ⟨143323557103806516256055467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191098076138408688341407289 143323557103806516256055467)
  ·
    refine ⟨214985335655709774384083201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143323557103806516256055467 214985335655709774384083201)
    ·
      refine ⟨161239001741782330788062401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214985335655709774384083201 161239001741782330788062401)
      ·
        refine ⟨120929251306336748091046801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161239001741782330788062401 120929251306336748091046801)
        ·
          refine ⟨90696938479752561068285101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120929251306336748091046801 90696938479752561068285101)
          ·
            refine ⟨34011351929907210400606913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90696938479752561068285101 34011351929907210400606913)
            ·
              refine ⟨25508513947430407800455185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34011351929907210400606913 25508513947430407800455185)
              ·
                refine ⟨19131385460572805850341389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25508513947430407800455185 19131385460572805850341389)
                ·
                  refine ⟨7174269547714802193878021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19131385460572805850341389 7174269547714802193878021)
                  ·
                    refine ⟨1345175540196525411352129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7174269547714802193878021 1345175540196525411352129)
                    ·
                      rfl

theorem cell23_7859160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_7859160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859160 prefixEnd_7859160 := by exact prefixLift 7859160
  have htrace : WordTrace (prefixWord ++ tailWord_7859160) baseStart_7859160 baseEnd_7859160 := by
    simpa [prefixWord, tailWord_7859160, baseEnd_7859160] using wordTrace_append hprefix tailTrace_7859160
  have hstable : (prefixWord ++ tailWord_7859160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859160).length < 2 ^ (prefixWord ++ tailWord_7859160).sum := by decide
  have hdescent : baseEnd_7859160 < baseStart_7859160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859190 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 8]
def baseStart_7859190 : Nat := 118140960795 + 7859190 * 2 ^ 59
def prefixEnd_7859190 : Nat := 4983230072969 + 3 ^ 40 * 7859190 * 2
def baseEnd_7859190 : Nat := 448393558334356790742361

theorem tailTrace_7859190 : CollatzResearch.WordTrace tailWord_7859190 prefixEnd_7859190 448393558334356790742361 := by
  unfold tailWord_7859190
  simp only [CollatzResearch.WordTrace]
  refine ⟨17915513024844021727231439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191098805598336231757135349 17915513024844021727231439)
  ·
    refine ⟨26873269537266032590847159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17915513024844021727231439 26873269537266032590847159)
    ·
      refine ⟨40309904305899048886270739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26873269537266032590847159 40309904305899048886270739)
      ·
        refine ⟨60464856458848573329406109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40309904305899048886270739 60464856458848573329406109)
        ·
          refine ⟨22674321172068214998527291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60464856458848573329406109 22674321172068214998527291)
          ·
            refine ⟨34011481758102322497790937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22674321172068214998527291 34011481758102322497790937)
            ·
              refine ⟨25508611318576741873343203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34011481758102322497790937 25508611318576741873343203)
              ·
                refine ⟨38262916977865112810014805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25508611318576741873343203 38262916977865112810014805)
                ·
                  refine ⟨448393558334356790742361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38262916977865112810014805 448393558334356790742361)
                  ·
                    rfl

theorem cell23_7859190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_7859190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859190 prefixEnd_7859190 := by exact prefixLift 7859190
  have htrace : WordTrace (prefixWord ++ tailWord_7859190) baseStart_7859190 baseEnd_7859190 := by
    simpa [prefixWord, tailWord_7859190, baseEnd_7859190] using wordTrace_append hprefix tailTrace_7859190
  have hstable : (prefixWord ++ tailWord_7859190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859190).length < 2 ^ (prefixWord ++ tailWord_7859190).sum := by decide
  have hdescent : baseEnd_7859190 < baseStart_7859190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859237 : List Nat := [1, 3, 1, 2, 2, 2, 5, 1, 1, 5]
def baseStart_7859237 : Nat := 118140960795 + 7859237 * 2 ^ 59
def prefixEnd_7859237 : Nat := 4983230072969 + 3 ^ 40 * 7859237 * 2
def baseEnd_7859237 : Nat := 1345188719533324144264511

theorem tailTrace_7859237 : CollatzResearch.WordTrace tailWord_7859237 prefixEnd_7859237 1345188719533324144264511 := by
  unfold tailWord_7859237
  simp only [CollatzResearch.WordTrace]
  refine ⟨286649922628334074662663965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191099948418889383108442643 286649922628334074662663965)
  ·
    refine ⟨107493720985625277998498987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286649922628334074662663965 107493720985625277998498987)
    ·
      refine ⟨161240581478437916997748481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107493720985625277998498987 161240581478437916997748481)
      ·
        refine ⟨120930436108828437748311361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161240581478437916997748481 120930436108828437748311361)
        ·
          refine ⟨90697827081621328311233521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120930436108828437748311361 90697827081621328311233521)
          ·
            refine ⟨68023370311215996233425141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90697827081621328311233521 68023370311215996233425141)
            ·
              refine ⟨6377190966676499646883607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68023370311215996233425141 6377190966676499646883607)
              ·
                refine ⟨9565786450014749470325411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6377190966676499646883607 9565786450014749470325411)
                ·
                  refine ⟨14348679675022124205488117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9565786450014749470325411 14348679675022124205488117)
                  ·
                    refine ⟨1345188719533324144264511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14348679675022124205488117 1345188719533324144264511)
                    ·
                      rfl

theorem cell23_7859237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 1, 5].length) (baseStart_7859237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859237 prefixEnd_7859237 := by exact prefixLift 7859237
  have htrace : WordTrace (prefixWord ++ tailWord_7859237) baseStart_7859237 baseEnd_7859237 := by
    simpa [prefixWord, tailWord_7859237, baseEnd_7859237] using wordTrace_append hprefix tailTrace_7859237
  have hstable : (prefixWord ++ tailWord_7859237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859237).length < 2 ^ (prefixWord ++ tailWord_7859237).sum := by decide
  have hdescent : baseEnd_7859237 < baseStart_7859237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859290 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3]
def baseStart_7859290 : Nat := 118140960795 + 7859290 * 2 ^ 59
def prefixEnd_7859290 : Nat := 4983230072969 + 3 ^ 40 * 7859290 * 2
def baseEnd_7859290 : Nat := 4035593373074660725430789

theorem tailTrace_7859290 : CollatzResearch.WordTrace tailWord_7859290 prefixEnd_7859290 4035593373074660725430789 := by
  unfold tailWord_7859290
  simp only [CollatzResearch.WordTrace]
  refine ⟨71662963924285516178585831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191101237131428043142895549 71662963924285516178585831)
  ·
    refine ⟨107494445886428274267878747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71662963924285516178585831 107494445886428274267878747)
    ·
      refine ⟨161241668829642411401818121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107494445886428274267878747 161241668829642411401818121)
      ·
        refine ⟨120931251622231808551363591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161241668829642411401818121 120931251622231808551363591)
        ·
          refine ⟨181396877433347712827045387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120931251622231808551363591 181396877433347712827045387)
          ·
            refine ⟨272095316150021569240568081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181396877433347712827045387 272095316150021569240568081)
            ·
              refine ⟨204071487112516176930426061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272095316150021569240568081 204071487112516176930426061)
              ·
                refine ⟨76526807667193566348909773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204071487112516176930426061 76526807667193566348909773)
                ·
                  refine ⟨28697552875197587380841165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76526807667193566348909773 28697552875197587380841165)
                  ·
                    refine ⟨10761582328199095267815437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28697552875197587380841165 10761582328199095267815437)
                    ·
                      refine ⟨4035593373074660725430789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10761582328199095267815437 4035593373074660725430789)
                      ·
                        rfl

theorem cell23_7859290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_7859290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859290 prefixEnd_7859290 := by exact prefixLift 7859290
  have htrace : WordTrace (prefixWord ++ tailWord_7859290) baseStart_7859290 baseEnd_7859290 := by
    simpa [prefixWord, tailWord_7859290, baseEnd_7859290] using wordTrace_append hprefix tailTrace_7859290
  have hstable : (prefixWord ++ tailWord_7859290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859290).length < 2 ^ (prefixWord ++ tailWord_7859290).sum := by decide
  have hdescent : baseEnd_7859290 < baseStart_7859290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859347 : List Nat := [1, 1, 1, 2, 1, 2, 4, 4, 1, 4, 2]
def baseStart_7859347 : Nat := 118140960795 + 7859347 * 2 ^ 59
def prefixEnd_7859347 : Nat := 4983230072969 + 3 ^ 40 * 7859347 * 2
def baseEnd_7859347 : Nat := 4035622641471967002418027

theorem tailTrace_7859347 : CollatzResearch.WordTrace tailWord_7859347 prefixEnd_7859347 4035622641471967002418027 := by
  unfold tailWord_7859347
  simp only [CollatzResearch.WordTrace]
  refine ⟨286653934657935563449168295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191102623105290375632778863 286653934657935563449168295)
  ·
    refine ⟨429980901986903345173752443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286653934657935563449168295 429980901986903345173752443)
    ·
      refine ⟨644971352980355017760628665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429980901986903345173752443 644971352980355017760628665)
      ·
        refine ⟨483728514735266263320471499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 644971352980355017760628665 483728514735266263320471499)
        ·
          refine ⟨725592772102899394980707249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483728514735266263320471499 725592772102899394980707249)
          ·
            refine ⟨544194579077174546235530437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 725592772102899394980707249 544194579077174546235530437)
            ·
              refine ⟨102036483576970227419161957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 544194579077174546235530437 102036483576970227419161957)
              ·
                refine ⟨19131840670681917641092867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102036483576970227419161957 19131840670681917641092867)
                ·
                  refine ⟨28697761006022876461639301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19131840670681917641092867 28697761006022876461639301)
                  ·
                    refine ⟨5380830188629289336557369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28697761006022876461639301 5380830188629289336557369)
                    ·
                      refine ⟨4035622641471967002418027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5380830188629289336557369 4035622641471967002418027)
                      ·
                        rfl

theorem cell23_7859347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 4, 2].length) (baseStart_7859347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859347 prefixEnd_7859347 := by exact prefixLift 7859347
  have htrace : WordTrace (prefixWord ++ tailWord_7859347) baseStart_7859347 baseEnd_7859347 := by
    simpa [prefixWord, tailWord_7859347, baseEnd_7859347] using wordTrace_append hprefix tailTrace_7859347
  have hstable : (prefixWord ++ tailWord_7859347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859347).length < 2 ^ (prefixWord ++ tailWord_7859347).sum := by decide
  have hdescent : baseEnd_7859347 < baseStart_7859347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859400 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 1, 7]
def baseStart_7859400 : Nat := 118140960795 + 7859400 * 2 ^ 59
def prefixEnd_7859400 : Nat := 4983230072969 + 3 ^ 40 * 7859400 * 2
def baseEnd_7859400 : Nat := 1345216618648885098351761

theorem tailTrace_7859400 : CollatzResearch.WordTrace tailWord_7859400 prefixEnd_7859400 1345216618648885098351761 := by
  unfold tailWord_7859400
  simp only [CollatzResearch.WordTrace]
  refine ⟨143327933863371776750423827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191103911817829035667231769 143327933863371776750423827)
  ·
    refine ⟨214991900795057665125635741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143327933863371776750423827 214991900795057665125635741)
    ·
      refine ⟨80621962798146624422113403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214991900795057665125635741 80621962798146624422113403)
      ·
        refine ⟨120932944197219936633170105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80621962798146624422113403 120932944197219936633170105)
        ·
          refine ⟨90699708147914952474877579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120932944197219936633170105 90699708147914952474877579)
          ·
            refine ⟨136049562221872428712316369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90699708147914952474877579 136049562221872428712316369)
            ·
              refine ⟨102037171666404321534237277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136049562221872428712316369 102037171666404321534237277)
              ·
                refine ⟨38263939374901620575338979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102037171666404321534237277 38263939374901620575338979)
                ·
                  refine ⟨57395909062352430863008469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38263939374901620575338979 57395909062352430863008469)
                  ·
                    refine ⟨1345216618648885098351761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57395909062352430863008469 1345216618648885098351761)
                    ·
                      rfl

theorem cell23_7859400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_7859400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859400 prefixEnd_7859400 := by exact prefixLift 7859400
  have htrace : WordTrace (prefixWord ++ tailWord_7859400) baseStart_7859400 baseEnd_7859400 := by
    simpa [prefixWord, tailWord_7859400, baseEnd_7859400] using wordTrace_append hprefix tailTrace_7859400
  have hstable : (prefixWord ++ tailWord_7859400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859400).length < 2 ^ (prefixWord ++ tailWord_7859400).sum := by decide
  have hdescent : baseEnd_7859400 < baseStart_7859400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859421 : List Nat := [1, 4, 3, 2, 2, 1, 1, 4, 5]
def baseStart_7859421 : Nat := 118140960795 + 7859421 * 2 ^ 59
def prefixEnd_7859421 : Nat := 4983230072969 + 3 ^ 40 * 7859421 * 2
def baseEnd_7859421 : Nat := 448406737671155523654743

theorem tailTrace_7859421 : CollatzResearch.WordTrace tailWord_7859421 prefixEnd_7859421 448406737671155523654743 := by
  unfold tailWord_7859421
  simp only [CollatzResearch.WordTrace]
  refine ⟨286656633659667474087362117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191104422439778316058241411 286656633659667474087362117)
  ·
    refine ⟨53748118811187651391380397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286656633659667474087362117 53748118811187651391380397)
    ·
      refine ⟨20155544554195369271767649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53748118811187651391380397 20155544554195369271767649)
      ·
        refine ⟨15116658415646526953825737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20155544554195369271767649 15116658415646526953825737)
        ·
          refine ⟨11337493811734895215369303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15116658415646526953825737 11337493811734895215369303)
          ·
            refine ⟨17006240717602342823053955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11337493811734895215369303 17006240717602342823053955)
            ·
              refine ⟨25509361076403514234580933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17006240717602342823053955 25509361076403514234580933)
              ·
                refine ⟨4783005201825658918983925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25509361076403514234580933 4783005201825658918983925)
                ·
                  refine ⟨448406737671155523654743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4783005201825658918983925 448406737671155523654743)
                  ·
                    rfl

theorem cell23_7859421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_7859421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859421 prefixEnd_7859421 := by exact prefixLift 7859421
  have htrace : WordTrace (prefixWord ++ tailWord_7859421) baseStart_7859421 baseEnd_7859421 := by
    simpa [prefixWord, tailWord_7859421, baseEnd_7859421] using wordTrace_append hprefix tailTrace_7859421
  have hstable : (prefixWord ++ tailWord_7859421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859421).length < 2 ^ (prefixWord ++ tailWord_7859421).sum := by decide
  have hdescent : baseEnd_7859421 < baseStart_7859421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859447 : List Nat := [1, 1, 3, 1, 1, 1, 2, 6, 3, 4]
def baseStart_7859447 : Nat := 118140960795 + 7859447 * 2 ^ 59
def prefixEnd_7859447 : Nat := 4983230072969 + 3 ^ 40 * 7859447 * 2
def baseEnd_7859447 : Nat := 1345224663179138870389189

theorem tailTrace_7859447 : CollatzResearch.WordTrace tailWord_7859447 prefixEnd_7859447 1345224663179138870389189 := by
  unfold tailWord_7859447
  simp only [CollatzResearch.WordTrace]
  refine ⟨286657581957573280527808595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191105054638382187018539063 286657581957573280527808595)
  ·
    refine ⟨429986372936359920791712893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286657581957573280527808595 429986372936359920791712893)
    ·
      refine ⟨161244889851134970296892335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429986372936359920791712893 161244889851134970296892335)
      ·
        refine ⟨241867334776702455445338503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161244889851134970296892335 241867334776702455445338503)
        ·
          refine ⟨362801002165053683168007755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241867334776702455445338503 362801002165053683168007755)
          ·
            refine ⟨544201503247580524752011633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362801002165053683168007755 544201503247580524752011633)
            ·
              refine ⟨408151127435685393564008725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544201503247580524752011633 408151127435685393564008725)
              ·
                refine ⟨19132084098547752823312909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 408151127435685393564008725 19132084098547752823312909)
                ·
                  refine ⟨7174531536955407308742341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19132084098547752823312909 7174531536955407308742341)
                  ·
                    refine ⟨1345224663179138870389189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7174531536955407308742341 1345224663179138870389189)
                    ·
                      rfl

theorem cell23_7859447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_7859447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859447 prefixEnd_7859447 := by exact prefixLift 7859447
  have htrace : WordTrace (prefixWord ++ tailWord_7859447) baseStart_7859447 baseEnd_7859447 := by
    simpa [prefixWord, tailWord_7859447, baseEnd_7859447] using wordTrace_append hprefix tailTrace_7859447
  have hstable : (prefixWord ++ tailWord_7859447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859447).length < 2 ^ (prefixWord ++ tailWord_7859447).sum := by decide
  have hdescent : baseEnd_7859447 < baseStart_7859447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859454 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_7859454 : Nat := 118140960795 + 7859454 * 2 ^ 59
def prefixEnd_7859454 : Nat := 4983230072969 + 3 ^ 40 * 7859454 * 2
def baseEnd_7859454 : Nat := 4035677583901998083780035

theorem tailTrace_7859454 : CollatzResearch.WordTrace tailWord_7859454 prefixEnd_7859454 4035677583901998083780035 := by
  unfold tailWord_7859454
  simp only [CollatzResearch.WordTrace]
  refine ⟨35832229658568490090414177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191105224845698613815542277 35832229658568490090414177)
  ·
    refine ⟨26874172243926367567810633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35832229658568490090414177 26874172243926367567810633)
    ·
      refine ⟨20155629182944775675857975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26874172243926367567810633 20155629182944775675857975)
      ·
        refine ⟨30233443774417163513786963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20155629182944775675857975 30233443774417163513786963)
        ·
          refine ⟨45350165661625745270680445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30233443774417163513786963 45350165661625745270680445)
          ·
            refine ⟨17006312123109654476505167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45350165661625745270680445 17006312123109654476505167)
            ·
              refine ⟨25509468184664481714757751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17006312123109654476505167 25509468184664481714757751)
              ·
                refine ⟨38264202276996722572136627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25509468184664481714757751 38264202276996722572136627)
                ·
                  refine ⟨57396303415495083858204941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38264202276996722572136627 57396303415495083858204941)
                  ·
                    refine ⟨21523613780810656446826853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57396303415495083858204941 21523613780810656446826853)
                    ·
                      refine ⟨4035677583901998083780035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21523613780810656446826853 4035677583901998083780035)
                      ·
                        rfl

theorem cell23_7859454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_7859454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859454 prefixEnd_7859454 := by exact prefixLift 7859454
  have htrace : WordTrace (prefixWord ++ tailWord_7859454) baseStart_7859454 baseEnd_7859454 := by
    simpa [prefixWord, tailWord_7859454, baseEnd_7859454] using wordTrace_append hprefix tailTrace_7859454
  have hstable : (prefixWord ++ tailWord_7859454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859454).length < 2 ^ (prefixWord ++ tailWord_7859454).sum := by decide
  have hdescent : baseEnd_7859454 < baseStart_7859454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859504 : List Nat := [2, 1, 1, 1, 2, 2, 3, 4, 3, 1, 3]
def baseStart_7859504 : Nat := 118140960795 + 7859504 * 2 ^ 59
def prefixEnd_7859504 : Nat := 4983230072969 + 3 ^ 40 * 7859504 * 2
def baseEnd_7859504 : Nat := 4035703257934722888154805

theorem tailTrace_7859504 : CollatzResearch.WordTrace tailWord_7859504 prefixEnd_7859504 4035703257934722888154805 := by
  unfold tailWord_7859504
  simp only [CollatzResearch.WordTrace]
  refine ⟨143329830459183389631316783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191106440612244519508422377 143329830459183389631316783)
  ·
    refine ⟨214994745688775084446975175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143329830459183389631316783 214994745688775084446975175)
    ·
      refine ⟨322492118533162626670462763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214994745688775084446975175 322492118533162626670462763)
      ·
        refine ⟨483738177799743940005694145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322492118533162626670462763 483738177799743940005694145)
        ·
          refine ⟨362803633349807955004270609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483738177799743940005694145 362803633349807955004270609)
          ·
            refine ⟨272102725012355966253202957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362803633349807955004270609 272102725012355966253202957)
            ·
              refine ⟨102038521879633487344951109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272102725012355966253202957 102038521879633487344951109)
              ·
                refine ⟨19132222852431278877178333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102038521879633487344951109 19132222852431278877178333)
                ·
                  refine ⟨7174583569661729578941875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19132222852431278877178333 7174583569661729578941875)
                  ·
                    refine ⟨10761875354492594368412813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7174583569661729578941875 10761875354492594368412813)
                    ·
                      refine ⟨4035703257934722888154805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10761875354492594368412813 4035703257934722888154805)
                      ·
                        rfl

theorem cell23_7859504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 3, 1, 3].length) (baseStart_7859504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859504 prefixEnd_7859504 := by exact prefixLift 7859504
  have htrace : WordTrace (prefixWord ++ tailWord_7859504) baseStart_7859504 baseEnd_7859504 := by
    simpa [prefixWord, tailWord_7859504, baseEnd_7859504] using wordTrace_append hprefix tailTrace_7859504
  have hstable : (prefixWord ++ tailWord_7859504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859504).length < 2 ^ (prefixWord ++ tailWord_7859504).sum := by decide
  have hdescent : baseEnd_7859504 < baseStart_7859504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859514 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2]
def baseStart_7859514 : Nat := 118140960795 + 7859514 * 2 ^ 59
def prefixEnd_7859514 : Nat := 4983230072969 + 3 ^ 40 * 7859514 * 2
def baseEnd_7859514 : Nat := 4035708392741267849029759

theorem tailTrace_7859514 : CollatzResearch.WordTrace tailWord_7859514 prefixEnd_7859514 4035708392741267849029759 := by
  unfold tailWord_7859514
  simp only [CollatzResearch.WordTrace]
  refine ⟨71665006412082637742624399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191106683765553700646998397 71665006412082637742624399)
  ·
    refine ⟨107497509618123956613936599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71665006412082637742624399 107497509618123956613936599)
    ·
      refine ⟨161246264427185934920904899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107497509618123956613936599 161246264427185934920904899)
      ·
        refine ⟨241869396640778902381357349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161246264427185934920904899 241869396640778902381357349)
        ·
          refine ⟨45350511870146044196504503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241869396640778902381357349 45350511870146044196504503)
          ·
            refine ⟨68025767805219066294756755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45350511870146044196504503 68025767805219066294756755)
            ·
              refine ⟨102038651707828599442135133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68025767805219066294756755 102038651707828599442135133)
              ·
                refine ⟨38264494390435724790800675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102038651707828599442135133 38264494390435724790800675)
                ·
                  refine ⟨57396741585653587186201013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38264494390435724790800675 57396741585653587186201013)
                  ·
                    refine ⟨5380944523655023798706345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57396741585653587186201013 5380944523655023798706345)
                    ·
                      refine ⟨4035708392741267849029759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5380944523655023798706345 4035708392741267849029759)
                      ·
                        rfl

theorem cell23_7859514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2].length) (baseStart_7859514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859514 prefixEnd_7859514 := by exact prefixLift 7859514
  have htrace : WordTrace (prefixWord ++ tailWord_7859514) baseStart_7859514 baseEnd_7859514 := by
    simpa [prefixWord, tailWord_7859514, baseEnd_7859514] using wordTrace_append hprefix tailTrace_7859514
  have hstable : (prefixWord ++ tailWord_7859514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859514).length < 2 ^ (prefixWord ++ tailWord_7859514).sum := by decide
  have hdescent : baseEnd_7859514 < baseStart_7859514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859554 : List Nat := [3, 3, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_7859554 : Nat := 118140960795 + 7859554 * 2 ^ 59
def prefixEnd_7859554 : Nat := 4983230072969 + 3 ^ 40 * 7859554 * 2
def baseEnd_7859554 : Nat := 1345242977322482564176525

theorem tailTrace_7859554 : CollatzResearch.WordTrace tailWord_7859554 prefixEnd_7859554 1345242977322482564176525 := by
  unfold tailWord_7859554
  simp only [CollatzResearch.WordTrace]
  refine ⟨71665371142046409450488429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191107656378790425201302477 71665371142046409450488429)
  ·
    refine ⟨26874514178267403543933161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71665371142046409450488429 26874514178267403543933161)
    ·
      refine ⟨20155885633700552657949871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26874514178267403543933161 20155885633700552657949871)
      ·
        refine ⟨30233828450550828986924807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20155885633700552657949871 30233828450550828986924807)
        ·
          refine ⟨45350742675826243480387211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30233828450550828986924807 45350742675826243480387211)
          ·
            refine ⟨68026114013739365220580817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45350742675826243480387211 68026114013739365220580817)
            ·
              refine ⟨51019585510304523915435613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68026114013739365220580817 51019585510304523915435613)
              ·
                refine ⟨19132344566364196468288355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51019585510304523915435613 19132344566364196468288355)
                ·
                  refine ⟨28698516849546294702432533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19132344566364196468288355 28698516849546294702432533)
                  ·
                    refine ⟨1345242977322482564176525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28698516849546294702432533 1345242977322482564176525)
                    ·
                      rfl

theorem cell23_7859554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_7859554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859554 prefixEnd_7859554 := by exact prefixLift 7859554
  have htrace : WordTrace (prefixWord ++ tailWord_7859554) baseStart_7859554 baseEnd_7859554 := by
    simpa [prefixWord, tailWord_7859554, baseEnd_7859554] using wordTrace_append hprefix tailTrace_7859554
  have hstable : (prefixWord ++ tailWord_7859554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859554).length < 2 ^ (prefixWord ++ tailWord_7859554).sum := by decide
  have hdescent : baseEnd_7859554 < baseStart_7859554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859557 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 1, 1, 6]
def baseStart_7859557 : Nat := 118140960795 + 7859557 * 2 ^ 59
def prefixEnd_7859557 : Nat := 4983230072969 + 3 ^ 40 * 7859557 * 2
def baseEnd_7859557 : Nat := 4035730472409411180792061

theorem tailTrace_7859557 : CollatzResearch.WordTrace tailWord_7859557 prefixEnd_7859557 4035730472409411180792061 := by
  unfold tailWord_7859557
  simp only [CollatzResearch.WordTrace]
  refine ⟨286661593987174769314312925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191107729324783179542875283 286661593987174769314312925)
  ·
    refine ⟨107498097745190538492867347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286661593987174769314312925 107498097745190538492867347)
    ·
      refine ⟨161247146617785807739301021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107498097745190538492867347 161247146617785807739301021)
      ·
        refine ⟨60467679981669677902237883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161247146617785807739301021 60467679981669677902237883)
        ·
          refine ⟨90701519972504516853356825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60467679981669677902237883 90701519972504516853356825)
          ·
            refine ⟨68026139979378387640017619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90701519972504516853356825 68026139979378387640017619)
            ·
              refine ⟨102039209969067581460026429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68026139979378387640017619 102039209969067581460026429)
              ·
                refine ⟨38264703738400343047509911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102039209969067581460026429 38264703738400343047509911)
                ·
                  refine ⟨57397055607600514571264867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38264703738400343047509911 57397055607600514571264867)
                  ·
                    refine ⟨86095583411400771856897301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57397055607600514571264867 86095583411400771856897301)
                    ·
                      refine ⟨4035730472409411180792061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86095583411400771856897301 4035730472409411180792061)
                      ·
                        rfl

theorem cell23_7859557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_7859557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859557 prefixEnd_7859557 := by exact prefixLift 7859557
  have htrace : WordTrace (prefixWord ++ tailWord_7859557) baseStart_7859557 baseEnd_7859557 := by
    simpa [prefixWord, tailWord_7859557, baseEnd_7859557] using wordTrace_append hprefix tailTrace_7859557
  have hstable : (prefixWord ++ tailWord_7859557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859557).length < 2 ^ (prefixWord ++ tailWord_7859557).sum := by decide
  have hdescent : baseEnd_7859557 < baseStart_7859557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859607 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 5]
def baseStart_7859607 : Nat := 118140960795 + 7859607 * 2 ^ 59
def prefixEnd_7859607 : Nat := 4983230072969 + 3 ^ 40 * 7859607 * 2
def baseEnd_7859607 : Nat := 4035756146442135985166831

theorem tailTrace_7859607 : CollatzResearch.WordTrace tailWord_7859607 prefixEnd_7859607 4035756146442135985166831 := by
  unfold tailWord_7859607
  simp only [CollatzResearch.WordTrace]
  refine ⟨286663417636993627853633075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191108945091329085235755383 286663417636993627853633075)
  ·
    refine ⟨429995126455490441780449613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286663417636993627853633075 429995126455490441780449613)
    ·
      refine ⟨161248172420808915667668605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429995126455490441780449613 161248172420808915667668605)
      ·
        refine ⟨60468064657803343375375727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161248172420808915667668605 60468064657803343375375727)
        ·
          refine ⟨90702096986705015063063591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60468064657803343375375727 90702096986705015063063591)
          ·
            refine ⟨136053145480057522594595387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90702096986705015063063591 136053145480057522594595387)
            ·
              refine ⟨204079718220086283891893081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136053145480057522594595387 204079718220086283891893081)
              ·
                refine ⟨153059788665064712918919811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204079718220086283891893081 153059788665064712918919811)
                ·
                  refine ⟨229589682997597069378379717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153059788665064712918919811 229589682997597069378379717)
                  ·
                    refine ⟨43048065562049450508446197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 229589682997597069378379717 43048065562049450508446197)
                    ·
                      refine ⟨4035756146442135985166831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43048065562049450508446197 4035756146442135985166831)
                      ·
                        rfl

theorem cell23_7859607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_7859607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859607 prefixEnd_7859607 := by exact prefixLift 7859607
  have htrace : WordTrace (prefixWord ++ tailWord_7859607) baseStart_7859607 baseEnd_7859607 := by
    simpa [prefixWord, tailWord_7859607, baseEnd_7859607] using wordTrace_append hprefix tailTrace_7859607
  have hstable : (prefixWord ++ tailWord_7859607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859607).length < 2 ^ (prefixWord ++ tailWord_7859607).sum := by decide
  have hdescent : baseEnd_7859607 < baseStart_7859607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859674 : List Nat := [3, 1, 1, 2, 3, 2, 2, 2, 7]
def baseStart_7859674 : Nat := 118140960795 + 7859674 * 2 ^ 59
def prefixEnd_7859674 : Nat := 4983230072969 + 3 ^ 40 * 7859674 * 2
def baseEnd_7859674 : Nat := 448421172182887469225447

theorem tailTrace_7859674 : CollatzResearch.WordTrace tailWord_7859674 prefixEnd_7859674 448421172182887469225447 := by
  unfold tailWord_7859674
  simp only [CollatzResearch.WordTrace]
  refine ⟨71666465331937724574080519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191110574218500598864214717 71666465331937724574080519)
  ·
    refine ⟨107499697997906586861120779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71666465331937724574080519 107499697997906586861120779)
    ·
      refine ⟨161249546996859880291681169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107499697997906586861120779 161249546996859880291681169)
      ·
        refine ⟨120937160247644910218760877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161249546996859880291681169 120937160247644910218760877)
        ·
          refine ⟨45351435092866841332035329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120937160247644910218760877 45351435092866841332035329)
          ·
            refine ⟨34013576319650130999026497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45351435092866841332035329 34013576319650130999026497)
            ·
              refine ⟨25510182239737598249269873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34013576319650130999026497 25510182239737598249269873)
              ·
                refine ⟨19132636679803198686952405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25510182239737598249269873 19132636679803198686952405)
                ·
                  refine ⟨448421172182887469225447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19132636679803198686952405 448421172182887469225447)
                  ·
                    rfl

theorem cell23_7859674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 7].length) (baseStart_7859674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859674 prefixEnd_7859674 := by exact prefixLift 7859674
  have htrace : WordTrace (prefixWord ++ tailWord_7859674) baseStart_7859674 baseEnd_7859674 := by
    simpa [prefixWord, tailWord_7859674, baseEnd_7859674] using wordTrace_append hprefix tailTrace_7859674
  have hstable : (prefixWord ++ tailWord_7859674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859674).length < 2 ^ (prefixWord ++ tailWord_7859674).sum := by decide
  have hdescent : baseEnd_7859674 < baseStart_7859674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859684 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 1, 5, 3]
def baseStart_7859684 : Nat := 118140960795 + 7859684 * 2 ^ 59
def prefixEnd_7859684 : Nat := 4983230072969 + 3 ^ 40 * 7859684 * 2
def baseEnd_7859684 : Nat := 4035795684452532183903977

theorem tailTrace_7859684 : CollatzResearch.WordTrace tailWord_7859684 prefixEnd_7859684 4035795684452532183903977 := by
  unfold tailWord_7859684
  simp only [CollatzResearch.WordTrace]
  refine ⟨143333113028857335002093053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191110817371809780002790737 143333113028857335002093053)
  ·
    refine ⟨53749917385821500625784895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143333113028857335002093053 53749917385821500625784895)
    ·
      refine ⟨80624876078732250938677343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53749917385821500625784895 80624876078732250938677343)
      ·
        refine ⟨120937314118098376408016015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80624876078732250938677343 120937314118098376408016015)
        ·
          refine ⟨181405971177147564612024023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120937314118098376408016015 181405971177147564612024023)
          ·
            refine ⟨272108956765721346918036035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181405971177147564612024023 272108956765721346918036035)
            ·
              refine ⟨408163435148582020377054053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272108956765721346918036035 408163435148582020377054053)
              ·
                refine ⟨76530644090359128820697635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 408163435148582020377054053 76530644090359128820697635)
                ·
                  refine ⟨114795966135538693231046453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76530644090359128820697635 114795966135538693231046453)
                  ·
                    refine ⟨10762121825206752490410605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114795966135538693231046453 10762121825206752490410605)
                    ·
                      refine ⟨4035795684452532183903977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10762121825206752490410605 4035795684452532183903977)
                      ·
                        rfl

theorem cell23_7859684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_7859684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859684 prefixEnd_7859684 := by exact prefixLift 7859684
  have htrace : WordTrace (prefixWord ++ tailWord_7859684) baseStart_7859684 baseEnd_7859684 := by
    simpa [prefixWord, tailWord_7859684, baseEnd_7859684] using wordTrace_append hprefix tailTrace_7859684
  have hstable : (prefixWord ++ tailWord_7859684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859684).length < 2 ^ (prefixWord ++ tailWord_7859684).sum := by decide
  have hdescent : baseEnd_7859684 < baseStart_7859684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859704 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 4, 5]
def baseStart_7859704 : Nat := 118140960795 + 7859704 * 2 ^ 59
def prefixEnd_7859704 : Nat := 4983230072969 + 3 ^ 40 * 7859704 * 2
def baseEnd_7859704 : Nat := 1345268651355207368551295

theorem tailTrace_7859704 : CollatzResearch.WordTrace tailWord_7859704 prefixEnd_7859704 1345268651355207368551295 := by
  unfold tailWord_7859704
  simp only [CollatzResearch.WordTrace]
  refine ⟨143333477758821106709957083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191111303678428142279942777 143333477758821106709957083)
  ·
    refine ⟨215000216638231660064935625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143333477758821106709957083 215000216638231660064935625)
    ·
      refine ⟨161250162478673745048701719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215000216638231660064935625 161250162478673745048701719)
      ·
        refine ⟨241875243718010617573052579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161250162478673745048701719 241875243718010617573052579)
        ·
          refine ⟨362812865577015926359578869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241875243718010617573052579 362812865577015926359578869)
          ·
            refine ⟨34013706147845243096210519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 362812865577015926359578869 34013706147845243096210519)
            ·
              refine ⟨51020559221767864644315779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34013706147845243096210519 51020559221767864644315779)
              ·
                refine ⟨76530838832651796966473669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51020559221767864644315779 76530838832651796966473669)
                ·
                  refine ⟨14349532281122211931213813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76530838832651796966473669 14349532281122211931213813)
                  ·
                    refine ⟨1345268651355207368551295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14349532281122211931213813 1345268651355207368551295)
                    ·
                      rfl

theorem cell23_7859704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_7859704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859704 prefixEnd_7859704 := by exact prefixLift 7859704
  have htrace : WordTrace (prefixWord ++ tailWord_7859704) baseStart_7859704 baseEnd_7859704 := by
    simpa [prefixWord, tailWord_7859704, baseEnd_7859704] using wordTrace_append hprefix tailTrace_7859704
  have hstable : (prefixWord ++ tailWord_7859704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859704).length < 2 ^ (prefixWord ++ tailWord_7859704).sum := by decide
  have hdescent : baseEnd_7859704 < baseStart_7859704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859758 : List Nat := [4, 1, 3, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_7859758 : Nat := 118140960795 + 7859758 * 2 ^ 59
def prefixEnd_7859758 : Nat := 4983230072969 + 3 ^ 40 * 7859758 * 2
def baseEnd_7859758 : Nat := 4035833682020964894378637

theorem tailTrace_7859758 : CollatzResearch.WordTrace tailWord_7859758 prefixEnd_7859758 4035833682020964894378637 := by
  unfold tailWord_7859758
  simp only [CollatzResearch.WordTrace]
  refine ⟨35833615632430822580297491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191112616706297720428253285 35833615632430822580297491)
  ·
    refine ⟨53750423448646233870446237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35833615632430822580297491 53750423448646233870446237)
    ·
      refine ⟨20156408793242337701417339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53750423448646233870446237 20156408793242337701417339)
      ·
        refine ⟨30234613189863506552126009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20156408793242337701417339 30234613189863506552126009)
        ·
          refine ⟨22675959892397629914094507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30234613189863506552126009 22675959892397629914094507)
          ·
            refine ⟨34013939838596444871141761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22675959892397629914094507 34013939838596444871141761)
            ·
              refine ⟨25510454878947333653356321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34013939838596444871141761 25510454878947333653356321)
              ·
                refine ⟨19132841159210500240017241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25510454878947333653356321 19132841159210500240017241)
                ·
                  refine ⟨14349630869407875180012931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19132841159210500240017241 14349630869407875180012931)
                  ·
                    refine ⟨21524446304111812770019397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14349630869407875180012931 21524446304111812770019397)
                    ·
                      refine ⟨4035833682020964894378637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21524446304111812770019397 4035833682020964894378637)
                      ·
                        rfl

theorem cell23_7859758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_7859758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859758 prefixEnd_7859758 := by exact prefixLift 7859758
  have htrace : WordTrace (prefixWord ++ tailWord_7859758) baseStart_7859758 baseEnd_7859758 := by
    simpa [prefixWord, tailWord_7859758, baseEnd_7859758] using wordTrace_append hprefix tailTrace_7859758
  have hstable : (prefixWord ++ tailWord_7859758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859758).length < 2 ^ (prefixWord ++ tailWord_7859758).sum := by decide
  have hdescent : baseEnd_7859758 < baseStart_7859758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859861 : List Nat := [1, 3, 2, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_7859861 : Nat := 118140960795 + 7859861 * 2 ^ 59
def prefixEnd_7859861 : Nat := 4983230072969 + 3 ^ 40 * 7859861 * 2
def baseEnd_7859861 : Nat := 4035886570528377991390663

theorem tailTrace_7859861 : CollatzResearch.WordTrace tailWord_7859861 prefixEnd_7859861 4035886570528377991390663 := by
  unfold tailWord_7859861
  simp only [CollatzResearch.WordTrace]
  refine ⟨286672681778073429233379437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191115121185382286155586291 286672681778073429233379437)
  ·
    refine ⟨107502255666777535962517289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286672681778073429233379437 107502255666777535962517289)
    ·
      refine ⟨80626691750083151971887967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107502255666777535962517289 80626691750083151971887967)
      ·
        refine ⟨120940037625124727957831951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80626691750083151971887967 120940037625124727957831951)
        ·
          refine ⟨181410056437687091936747927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120940037625124727957831951 181410056437687091936747927)
          ·
            refine ⟨272115084656530637905121891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181410056437687091936747927 272115084656530637905121891)
            ·
              refine ⟨408172626984795956857682837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272115084656530637905121891 408172626984795956857682837)
              ·
                refine ⟨19133091889912310477703883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 408172626984795956857682837 19133091889912310477703883)
                ·
                  refine ⟨28699637834868465716555825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19133091889912310477703883 28699637834868465716555825)
                  ·
                    refine ⟨21524728376151349287416869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28699637834868465716555825 21524728376151349287416869)
                    ·
                      refine ⟨4035886570528377991390663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21524728376151349287416869 4035886570528377991390663)
                      ·
                        rfl

theorem cell23_7859861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_7859861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859861 prefixEnd_7859861 := by exact prefixLift 7859861
  have htrace : WordTrace (prefixWord ++ tailWord_7859861) baseStart_7859861 baseEnd_7859861 := by
    simpa [prefixWord, tailWord_7859861, baseEnd_7859861] using wordTrace_append hprefix tailTrace_7859861
  have hstable : (prefixWord ++ tailWord_7859861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859861).length < 2 ^ (prefixWord ++ tailWord_7859861).sum := by decide
  have hdescent : baseEnd_7859861 < baseStart_7859861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859902 : List Nat := [4, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_7859902 : Nat := 118140960795 + 7859902 * 2 ^ 59
def prefixEnd_7859902 : Nat := 4983230072969 + 3 ^ 40 * 7859902 * 2
def baseEnd_7859902 : Nat := 4035907623235212330977975

theorem tailTrace_7859902 : CollatzResearch.WordTrace tailWord_7859902 prefixEnd_7859902 4035907623235212330977975 := by
  unfold tailWord_7859902
  simp only [CollatzResearch.WordTrace]
  refine ⟨35834272146365611654452745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191116118113949928823747973 35834272146365611654452745)
  ·
    refine ⟨26875704109774208740839559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35834272146365611654452745 26875704109774208740839559)
    ·
      refine ⟨40313556164661313111259339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26875704109774208740839559 40313556164661313111259339)
      ·
        refine ⟨60470334246991969666889009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40313556164661313111259339 60470334246991969666889009)
        ·
          refine ⟨45352750685243977250166757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60470334246991969666889009 45352750685243977250166757)
          ·
            refine ⟨8503640753483245734406267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45352750685243977250166757 8503640753483245734406267)
            ·
              refine ⟨12755461130224868601609401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8503640753483245734406267 12755461130224868601609401)
              ·
                refine ⟨9566595847668651451207051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12755461130224868601609401 9566595847668651451207051)
                ·
                  refine ⟨14349893771502977176810577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9566595847668651451207051 14349893771502977176810577)
                  ·
                    refine ⟨10762420328627232882607933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14349893771502977176810577 10762420328627232882607933)
                    ·
                      refine ⟨4035907623235212330977975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10762420328627232882607933 4035907623235212330977975)
                      ·
                        rfl

theorem cell23_7859902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_7859902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859902 prefixEnd_7859902 := by exact prefixLift 7859902
  have htrace : WordTrace (prefixWord ++ tailWord_7859902) baseStart_7859902 baseEnd_7859902 := by
    simpa [prefixWord, tailWord_7859902, baseEnd_7859902] using wordTrace_append hprefix tailTrace_7859902
  have hstable : (prefixWord ++ tailWord_7859902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859902).length < 2 ^ (prefixWord ++ tailWord_7859902).sum := by decide
  have hdescent : baseEnd_7859902 < baseStart_7859902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7859989 : List Nat := [1, 3, 2, 1, 2, 5, 1, 2, 2, 2, 2]
def baseStart_7859989 : Nat := 118140960795 + 7859989 * 2 ^ 59
def prefixEnd_7859989 : Nat := 4983230072969 + 3 ^ 40 * 7859989 * 2
def baseEnd_7859989 : Nat := 4035952296052153490590075

theorem tailTrace_7859989 : CollatzResearch.WordTrace tailWord_7859989 prefixEnd_7859989 4035952296052153490590075 := by
  unfold tailWord_7859989
  simp only [CollatzResearch.WordTrace]
  refine ⟨286677350321609707094039021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191118233547739804729359347 286677350321609707094039021)
  ·
    refine ⟨107504006370603640160264633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286677350321609707094039021 107504006370603640160264633)
    ·
      refine ⟨80628004777952730120198475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107504006370603640160264633 80628004777952730120198475)
      ·
        refine ⟨120942007166929095180297713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80628004777952730120198475 120942007166929095180297713)
        ·
          refine ⟨90706505375196821385223285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120942007166929095180297713 90706505375196821385223285)
          ·
            refine ⟨8503734878924702004864683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90706505375196821385223285 8503734878924702004864683)
            ·
              refine ⟨12755602318387053007297025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8503734878924702004864683 12755602318387053007297025)
              ·
                refine ⟨9566701738790289755472769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12755602318387053007297025 9566701738790289755472769)
                ·
                  refine ⟨7175026304092717316604577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9566701738790289755472769 7175026304092717316604577)
                  ·
                    refine ⟨5381269728069537987453433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7175026304092717316604577 5381269728069537987453433)
                    ·
                      refine ⟨4035952296052153490590075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5381269728069537987453433 4035952296052153490590075)
                      ·
                        rfl

theorem cell23_7859989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_7859989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7859989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7859989 prefixEnd_7859989 := by exact prefixLift 7859989
  have htrace : WordTrace (prefixWord ++ tailWord_7859989) baseStart_7859989 baseEnd_7859989 := by
    simpa [prefixWord, tailWord_7859989, baseEnd_7859989] using wordTrace_append hprefix tailTrace_7859989
  have hstable : (prefixWord ++ tailWord_7859989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7859989).length < 2 ^ (prefixWord ++ tailWord_7859989).sum := by decide
  have hdescent : baseEnd_7859989 < baseStart_7859989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7859989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860008 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 1, 7]
def baseStart_7860008 : Nat := 118140960795 + 7860008 * 2 ^ 59
def prefixEnd_7860008 : Nat := 4983230072969 + 3 ^ 40 * 7860008 * 2
def baseEnd_7860008 : Nat := 1345320684061529638750829

theorem tailTrace_7860008 : CollatzResearch.WordTrace tailWord_7860008 prefixEnd_7860008 1345320684061529638750829 := by
  unfold tailWord_7860008
  simp only [CollatzResearch.WordTrace]
  refine ⟨143339021654270436669490339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191118695539027248892653785 143339021654270436669490339)
  ·
    refine ⟨215008532481405655004235509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143339021654270436669490339 215008532481405655004235509)
    ·
      refine ⟨20157049920131780156647079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215008532481405655004235509 20157049920131780156647079)
      ·
        refine ⟨30235574880197670234970619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20157049920131780156647079 30235574880197670234970619)
        ·
          refine ⟨45353362320296505352455929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30235574880197670234970619 45353362320296505352455929)
          ·
            refine ⟨34015021740222379014341947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45353362320296505352455929 34015021740222379014341947)
            ·
              refine ⟨51022532610333568521512921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34015021740222379014341947 51022532610333568521512921)
              ·
                refine ⟨38266899457750176391134691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51022532610333568521512921 38266899457750176391134691)
                ·
                  refine ⟨57400349186625264586702037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38266899457750176391134691 57400349186625264586702037)
                  ·
                    refine ⟨1345320684061529638750829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57400349186625264586702037 1345320684061529638750829)
                    ·
                      rfl

theorem cell23_7860008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_7860008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860008 prefixEnd_7860008 := by exact prefixLift 7860008
  have htrace : WordTrace (prefixWord ++ tailWord_7860008) baseStart_7860008 baseEnd_7860008 := by
    simpa [prefixWord, tailWord_7860008, baseEnd_7860008] using wordTrace_append hprefix tailTrace_7860008
  have hstable : (prefixWord ++ tailWord_7860008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860008).length < 2 ^ (prefixWord ++ tailWord_7860008).sum := by decide
  have hdescent : baseEnd_7860008 < baseStart_7860008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860028 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_7860028 : Nat := 118140960795 + 7860028 * 2 ^ 59
def prefixEnd_7860028 : Nat := 4983230072969 + 3 ^ 40 * 7860028 * 2
def baseEnd_7860028 : Nat := 4035972321797678838002395

theorem tailTrace_7860028 : CollatzResearch.WordTrace tailWord_7860028 prefixEnd_7860028 4035972321797678838002395 := by
  unfold tailWord_7860028
  simp only [CollatzResearch.WordTrace]
  refine ⟨143339386384234208377354369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191119181845645611169805825 143339386384234208377354369)
  ·
    refine ⟨107504539788175656283015777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143339386384234208377354369 107504539788175656283015777)
    ·
      refine ⟨80628404841131742212261833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107504539788175656283015777 80628404841131742212261833)
      ·
        refine ⟨60471303630848806659196375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80628404841131742212261833 60471303630848806659196375)
        ·
          refine ⟨90706955446273209988794563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60471303630848806659196375 90706955446273209988794563)
          ·
            refine ⟨136060433169409814983191845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90706955446273209988794563 136060433169409814983191845)
            ·
              refine ⟨25511331219264340309348471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136060433169409814983191845 25511331219264340309348471)
              ·
                refine ⟨38266996828896510464022707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25511331219264340309348471 38266996828896510464022707)
                ·
                  refine ⟨57400495243344765696034061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38266996828896510464022707 57400495243344765696034061)
                  ·
                    refine ⟨21525185716254287136012773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57400495243344765696034061 21525185716254287136012773)
                    ·
                      refine ⟨4035972321797678838002395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21525185716254287136012773 4035972321797678838002395)
                      ·
                        rfl

theorem cell23_7860028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_7860028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860028 prefixEnd_7860028 := by exact prefixLift 7860028
  have htrace : WordTrace (prefixWord ++ tailWord_7860028) baseStart_7860028 baseEnd_7860028 := by
    simpa [prefixWord, tailWord_7860028, baseEnd_7860028] using wordTrace_append hprefix tailTrace_7860028
  have hstable : (prefixWord ++ tailWord_7860028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860028).length < 2 ^ (prefixWord ++ tailWord_7860028).sum := by decide
  have hdescent : baseEnd_7860028 < baseStart_7860028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860129 : List Nat := [1, 2, 3, 4, 2, 1, 1, 2, 3, 1, 3]
def baseStart_7860129 : Nat := 118140960795 + 7860129 * 2 ^ 59
def prefixEnd_7860129 : Nat := 4983230072969 + 3 ^ 40 * 7860129 * 2
def baseEnd_7860129 : Nat := 4036024183343782942839431

theorem tailTrace_7860129 : CollatzResearch.WordTrace tailWord_7860129 prefixEnd_7860129 4036024183343782942839431 := by
  unfold tailWord_7860129
  simp only [CollatzResearch.WordTrace]
  refine ⟨286682456541102511004135441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191121637694068340669423627 286682456541102511004135441)
  ·
    refine ⟨215011842405826883253101581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286682456541102511004135441 215011842405826883253101581)
    ·
      refine ⟨80629440902185081219913093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215011842405826883253101581 80629440902185081219913093)
      ·
        refine ⟨15118020169159702728733705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80629440902185081219913093 15118020169159702728733705)
        ·
          refine ⟨11338515126869777046550279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15118020169159702728733705 11338515126869777046550279)
          ·
            refine ⟨17007772690304665569825419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11338515126869777046550279 17007772690304665569825419)
            ·
              refine ⟨25511659035456998354738129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17007772690304665569825419 25511659035456998354738129)
              ·
                refine ⟨19133744276592748766053597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25511659035456998354738129 19133744276592748766053597)
                ·
                  refine ⟨7175154103722280787270099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19133744276592748766053597 7175154103722280787270099)
                  ·
                    refine ⟨10762731155583421180905149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7175154103722280787270099 10762731155583421180905149)
                    ·
                      refine ⟨4036024183343782942839431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10762731155583421180905149 4036024183343782942839431)
                      ·
                        rfl

theorem cell23_7860129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_7860129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860129 prefixEnd_7860129 := by exact prefixLift 7860129
  have htrace : WordTrace (prefixWord ++ tailWord_7860129) baseStart_7860129 baseEnd_7860129 := by
    simpa [prefixWord, tailWord_7860129, baseEnd_7860129] using wordTrace_append hprefix tailTrace_7860129
  have hstable : (prefixWord ++ tailWord_7860129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860129).length < 2 ^ (prefixWord ++ tailWord_7860129).sum := by decide
  have hdescent : baseEnd_7860129 < baseStart_7860129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860145 : List Nat := [1, 2, 2, 4, 2, 1, 2, 2, 1, 6]
def baseStart_7860145 : Nat := 118140960795 + 7860145 * 2 ^ 59
def prefixEnd_7860145 : Nat := 4983230072969 + 3 ^ 40 * 7860145 * 2
def baseEnd_7860145 : Nat := 1345344133011418293413119

theorem tailTrace_7860145 : CollatzResearch.WordTrace tailWord_7860145 prefixEnd_7860145 1345344133011418293413119 := by
  unfold tailWord_7860145
  simp only [CollatzResearch.WordTrace]
  refine ⟨286683040109044545736717889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191122026739363030491145259 286683040109044545736717889)
  ·
    refine ⟨215012280081783409302538417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286683040109044545736717889 215012280081783409302538417)
    ·
      refine ⟨161259210061337556976903813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215012280081783409302538417 161259210061337556976903813)
      ·
        refine ⟨30236101886500791933169465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161259210061337556976903813 30236101886500791933169465)
        ·
          refine ⟨22677076414875593949877099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30236101886500791933169465 22677076414875593949877099)
          ·
            refine ⟨34015614622313390924815649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22677076414875593949877099 34015614622313390924815649)
            ·
              refine ⟨25511710966735043193611737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34015614622313390924815649 25511710966735043193611737)
              ·
                refine ⟨19133783225051282395208803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25511710966735043193611737 19133783225051282395208803)
                ·
                  refine ⟨28700674837576923592813205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19133783225051282395208803 28700674837576923592813205)
                  ·
                    refine ⟨1345344133011418293413119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28700674837576923592813205 1345344133011418293413119)
                    ·
                      rfl

theorem cell23_7860145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_7860145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860145 prefixEnd_7860145 := by exact prefixLift 7860145
  have htrace : WordTrace (prefixWord ++ tailWord_7860145) baseStart_7860145 baseEnd_7860145 := by
    simpa [prefixWord, tailWord_7860145, baseEnd_7860145] using wordTrace_append hprefix tailTrace_7860145
  have hstable : (prefixWord ++ tailWord_7860145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860145).length < 2 ^ (prefixWord ++ tailWord_7860145).sum := by decide
  have hdescent : baseEnd_7860145 < baseStart_7860145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860149 : List Nat := [1, 3, 3, 2, 1, 4, 2, 1, 1, 5]
def baseStart_7860149 : Nat := 118140960795 + 7860149 * 2 ^ 59
def prefixEnd_7860149 : Nat := 4983230072969 + 3 ^ 40 * 7860149 * 2
def baseEnd_7860149 : Nat := 1345344817652290954863113

theorem tailTrace_7860149 : CollatzResearch.WordTrace tailWord_7860149 prefixEnd_7860149 1345344817652290954863113 := by
  unfold tailWord_7860149
  simp only [CollatzResearch.WordTrace]
  refine ⟨286683186001030054419863501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191122124000686702946575667 286683186001030054419863501)
  ·
    refine ⟨107506194750386270407448813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286683186001030054419863501 107506194750386270407448813)
    ·
      refine ⟨40314823031394851402793305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107506194750386270407448813 40314823031394851402793305)
      ·
        refine ⟨30236117273546138552094979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40314823031394851402793305 30236117273546138552094979)
        ·
          refine ⟨45354175910319207828142469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30236117273546138552094979 45354175910319207828142469)
          ·
            refine ⟨8503907983184851467776713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45354175910319207828142469 8503907983184851467776713)
            ·
              refine ⟨6377930987388638600832535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8503907983184851467776713 6377930987388638600832535)
              ·
                refine ⟨9566896481082957901248803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6377930987388638600832535 9566896481082957901248803)
                ·
                  refine ⟨14350344721624436851873205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9566896481082957901248803 14350344721624436851873205)
                  ·
                    refine ⟨1345344817652290954863113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14350344721624436851873205 1345344817652290954863113)
                    ·
                      rfl

theorem cell23_7860149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_7860149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860149 prefixEnd_7860149 := by exact prefixLift 7860149
  have htrace : WordTrace (prefixWord ++ tailWord_7860149) baseStart_7860149 baseEnd_7860149 := by
    simpa [prefixWord, tailWord_7860149, baseEnd_7860149] using wordTrace_append hprefix tailTrace_7860149
  have hstable : (prefixWord ++ tailWord_7860149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860149).length < 2 ^ (prefixWord ++ tailWord_7860149).sum := by decide
  have hdescent : baseEnd_7860149 < baseStart_7860149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860152 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 5, 2, 2]
def baseStart_7860152 : Nat := 118140960795 + 7860152 * 2 ^ 59
def prefixEnd_7860152 : Nat := 4983230072969 + 3 ^ 40 * 7860152 * 2
def baseEnd_7860152 : Nat := 4036035993398836352851825

theorem tailTrace_7860152 : CollatzResearch.WordTrace tailWord_7860152 prefixEnd_7860152 4036035993398836352851825 := by
  unfold tailWord_7860152
  simp only [CollatzResearch.WordTrace]
  refine ⟨143341647710009592966111355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191122196946679457288148473 143341647710009592966111355)
  ·
    refine ⟨215012471565014389449167033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143341647710009592966111355 215012471565014389449167033)
    ·
      refine ⟨161259353673760792086875275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215012471565014389449167033 161259353673760792086875275)
      ·
        refine ⟨241889030510641188130312913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161259353673760792086875275 241889030510641188130312913)
        ·
          refine ⟨181416772882980891097734685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241889030510641188130312913 181416772882980891097734685)
          ·
            refine ⟨68031289831117834161650507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181416772882980891097734685 68031289831117834161650507)
            ·
              refine ⟨102046934746676751242475761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68031289831117834161650507 102046934746676751242475761)
              ·
                refine ⟨76535201060007563431856821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102046934746676751242475761 76535201060007563431856821)
                ·
                  refine ⟨7175175099375709071736577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76535201060007563431856821 7175175099375709071736577)
                  ·
                    refine ⟨5381381324531781803802433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7175175099375709071736577 5381381324531781803802433)
                    ·
                      refine ⟨4036035993398836352851825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5381381324531781803802433 4036035993398836352851825)
                      ·
                        rfl

theorem cell23_7860152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 5, 2, 2].length) (baseStart_7860152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860152 prefixEnd_7860152 := by exact prefixLift 7860152
  have htrace : WordTrace (prefixWord ++ tailWord_7860152) baseStart_7860152 baseEnd_7860152 := by
    simpa [prefixWord, tailWord_7860152, baseEnd_7860152] using wordTrace_append hprefix tailTrace_7860152
  have hstable : (prefixWord ++ tailWord_7860152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860152).length < 2 ^ (prefixWord ++ tailWord_7860152).sum := by decide
  have hdescent : baseEnd_7860152 < baseStart_7860152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860202 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_7860202 : Nat := 118140960795 + 7860202 * 2 ^ 59
def prefixEnd_7860202 : Nat := 4983230072969 + 3 ^ 40 * 7860202 * 2
def baseEnd_7860202 : Nat := 4036061667431561157226595

theorem tailTrace_7860202 : CollatzResearch.WordTrace tailWord_7860202 prefixEnd_7860202 4036061667431561157226595 := by
  unfold tailWord_7860202
  simp only [CollatzResearch.WordTrace]
  refine ⟨71671279767459511117885715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191123412713225362981028573 71671279767459511117885715)
  ·
    refine ⟨107506919651189266676828573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71671279767459511117885715 107506919651189266676828573)
    ·
      refine ⟨40315094869195975003810715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107506919651189266676828573 40315094869195975003810715)
      ·
        refine ⟨60472642303793962505716073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40315094869195975003810715 60472642303793962505716073)
        ·
          refine ⟨45354481727845471879287055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60472642303793962505716073 45354481727845471879287055)
          ·
            refine ⟨68031722591768207818930583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45354481727845471879287055 68031722591768207818930583)
            ·
              refine ⟨102047583887652311728395875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68031722591768207818930583 102047583887652311728395875)
              ·
                refine ⟨153071375831478467592593813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102047583887652311728395875 153071375831478467592593813)
                ·
                  refine ⟨7175220742100553168402835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153071375831478467592593813 7175220742100553168402835)
                  ·
                    refine ⟨10762831113150829752604253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7175220742100553168402835 10762831113150829752604253)
                    ·
                      refine ⟨4036061667431561157226595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10762831113150829752604253 4036061667431561157226595)
                      ·
                        rfl

theorem cell23_7860202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_7860202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860202 prefixEnd_7860202 := by exact prefixLift 7860202
  have htrace : WordTrace (prefixWord ++ tailWord_7860202) baseStart_7860202 baseEnd_7860202 := by
    simpa [prefixWord, tailWord_7860202, baseEnd_7860202] using wordTrace_append hprefix tailTrace_7860202
  have hstable : (prefixWord ++ tailWord_7860202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860202).length < 2 ^ (prefixWord ++ tailWord_7860202).sum := by decide
  have hdescent : baseEnd_7860202 < baseStart_7860202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860225 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_7860225 : Nat := 118140960795 + 7860225 * 2 ^ 59
def prefixEnd_7860225 : Nat := 4983230072969 + 3 ^ 40 * 7860225 * 2
def baseEnd_7860225 : Nat := 4036073477486614567238989

theorem tailTrace_7860225 : CollatzResearch.WordTrace tailWord_7860225 prefixEnd_7860225 4036073477486614567238989 := by
  unfold tailWord_7860225
  simp only [CollatzResearch.WordTrace]
  refine ⟨286685957948754719399630129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191123971965836479599753419 286685957948754719399630129)
  ·
    refine ⟨215014468461566039549722597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286685957948754719399630129 215014468461566039549722597)
    ·
      refine ⟨40315212836543632415572987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215014468461566039549722597 40315212836543632415572987)
      ·
        refine ⟨60472819254815448623359481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40315212836543632415572987 60472819254815448623359481)
        ·
          refine ⟨45354614441111586467519611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60472819254815448623359481 45354614441111586467519611)
          ·
            refine ⟨68031921661667379701279417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45354614441111586467519611 68031921661667379701279417)
            ·
              refine ⟨51023941246250534775959563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68031921661667379701279417 51023941246250534775959563)
              ·
                refine ⟨76535911869375802163939345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51023941246250534775959563 76535911869375802163939345)
                ·
                  refine ⟨57401933902031851622954509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76535911869375802163939345 57401933902031851622954509)
                  ·
                    refine ⟨21525725213261944358607941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57401933902031851622954509 21525725213261944358607941)
                    ·
                      refine ⟨4036073477486614567238989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21525725213261944358607941 4036073477486614567238989)
                      ·
                        rfl

theorem cell23_7860225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_7860225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860225 prefixEnd_7860225 := by exact prefixLift 7860225
  have htrace : WordTrace (prefixWord ++ tailWord_7860225) baseStart_7860225 baseEnd_7860225 := by
    simpa [prefixWord, tailWord_7860225, baseEnd_7860225] using wordTrace_append hprefix tailTrace_7860225
  have hstable : (prefixWord ++ tailWord_7860225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860225).length < 2 ^ (prefixWord ++ tailWord_7860225).sum := by decide
  have hdescent : baseEnd_7860225 < baseStart_7860225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860230 : List Nat := [6, 2, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_7860230 : Nat := 118140960795 + 7860230 * 2 ^ 59
def prefixEnd_7860230 : Nat := 4983230072969 + 3 ^ 40 * 7860230 * 2
def baseEnd_7860230 : Nat := 1345358681629962349225489

theorem tailTrace_7860230 : CollatzResearch.WordTrace tailWord_7860230 prefixEnd_7860230 1345358681629962349225489 := by
  unfold tailWord_7860230
  simp only [CollatzResearch.WordTrace]
  refine ⟨8958941884804268914173817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 191124093542491070169041429 8958941884804268914173817)
  ·
    refine ⟨6719206413603201685630363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8958941884804268914173817 6719206413603201685630363)
    ·
      refine ⟨10078809620404802528445545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6719206413603201685630363 10078809620404802528445545)
      ·
        refine ⟨7559107215303601896334159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10078809620404802528445545 7559107215303601896334159)
        ·
          refine ⟨11338660822955402844501239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7559107215303601896334159 11338660822955402844501239)
          ·
            refine ⟨17007991234433104266751859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11338660822955402844501239 17007991234433104266751859)
            ·
              refine ⟨25511986851649656400127789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17007991234433104266751859 25511986851649656400127789)
              ·
                refine ⟨9566995069368621150047921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25511986851649656400127789 9566995069368621150047921)
                ·
                  refine ⟨7175246302026465862535941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9566995069368621150047921 7175246302026465862535941)
                  ·
                    refine ⟨1345358681629962349225489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7175246302026465862535941 1345358681629962349225489)
                    ·
                      rfl

theorem cell23_7860230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_7860230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860230 prefixEnd_7860230 := by exact prefixLift 7860230
  have htrace : WordTrace (prefixWord ++ tailWord_7860230) baseStart_7860230 baseEnd_7860230 := by
    simpa [prefixWord, tailWord_7860230, baseEnd_7860230] using wordTrace_append hprefix tailTrace_7860230
  have hstable : (prefixWord ++ tailWord_7860230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860230).length < 2 ^ (prefixWord ++ tailWord_7860230).sum := by decide
  have hdescent : baseEnd_7860230 < baseStart_7860230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860295 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 1, 7]
def baseStart_7860295 : Nat := 118140960795 + 7860295 * 2 ^ 59
def prefixEnd_7860295 : Nat := 4983230072969 + 3 ^ 40 * 7860295 * 2
def baseEnd_7860295 : Nat := 1345369807044143097787889

theorem tailTrace_7860295 : CollatzResearch.WordTrace tailWord_7860295 prefixEnd_7860295 1345369807044143097787889 := by
  unfold tailWord_7860295
  simp only [CollatzResearch.WordTrace]
  refine ⟨286688511058501121354678339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191125674039000747569785559 286688511058501121354678339)
  ·
    refine ⟨430032766587751682032017509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286688511058501121354678339 430032766587751682032017509)
    ·
      refine ⟨80631143735203440381003283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 430032766587751682032017509 80631143735203440381003283)
      ·
        refine ⟨120946715602805160571504925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80631143735203440381003283 120946715602805160571504925)
        ·
          refine ⟨45355018351051935214314347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120946715602805160571504925 45355018351051935214314347)
          ·
            refine ⟨68032527526577902821471521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45355018351051935214314347 68032527526577902821471521)
            ·
              refine ⟨51024395644933427116103641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68032527526577902821471521 51024395644933427116103641)
              ·
                refine ⟨38268296733700070337077731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51024395644933427116103641 38268296733700070337077731)
                ·
                  refine ⟨57402445100550105505616597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38268296733700070337077731 57402445100550105505616597)
                  ·
                    refine ⟨1345369807044143097787889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57402445100550105505616597 1345369807044143097787889)
                    ·
                      rfl

theorem cell23_7860295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_7860295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860295 prefixEnd_7860295 := by exact prefixLift 7860295
  have htrace : WordTrace (prefixWord ++ tailWord_7860295) baseStart_7860295 baseEnd_7860295 := by
    simpa [prefixWord, tailWord_7860295, baseEnd_7860295] using wordTrace_append hprefix tailTrace_7860295
  have hstable : (prefixWord ++ tailWord_7860295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860295).length < 2 ^ (prefixWord ++ tailWord_7860295).sum := by decide
  have hdescent : baseEnd_7860295 < baseStart_7860295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860312 : List Nat := [2, 1, 2, 2, 1, 4, 3, 1, 2, 5]
def baseStart_7860312 : Nat := 118140960795 + 7860312 * 2 ^ 59
def prefixEnd_7860312 : Nat := 4983230072969 + 3 ^ 40 * 7860312 * 2
def baseEnd_7860312 : Nat := 1345372716767851908950363

theorem tailTrace_7860312 : CollatzResearch.WordTrace tailWord_7860312 prefixEnd_7860312 1345372716767851908950363 := by
  unfold tailWord_7860312
  simp only [CollatzResearch.WordTrace]
  refine ⟨143344565549719766629023595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191126087399626355505364793 143344565549719766629023595)
  ·
    refine ⟨215016848324579649943535393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143344565549719766629023595 215016848324579649943535393)
    ·
      refine ⟨161262636243434737457651545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215016848324579649943535393 161262636243434737457651545)
      ·
        refine ⟨120946977182576053093238659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161262636243434737457651545 120946977182576053093238659)
        ·
          refine ⟨181420465773864079639857989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120946977182576053093238659 181420465773864079639857989)
          ·
            refine ⟨34016337332599514932473373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181420465773864079639857989 34016337332599514932473373)
            ·
              refine ⟨12756126499724818099677515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34016337332599514932473373 12756126499724818099677515)
              ·
                refine ⟨19134189749587227149516273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12756126499724818099677515 19134189749587227149516273)
                ·
                  refine ⟨14350642312190420362137205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19134189749587227149516273 14350642312190420362137205)
                  ·
                    refine ⟨1345372716767851908950363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14350642312190420362137205 1345372716767851908950363)
                    ·
                      rfl

theorem cell23_7860312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_7860312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860312 prefixEnd_7860312 := by exact prefixLift 7860312
  have htrace : WordTrace (prefixWord ++ tailWord_7860312) baseStart_7860312 baseEnd_7860312 := by
    simpa [prefixWord, tailWord_7860312, baseEnd_7860312] using wordTrace_append hprefix tailTrace_7860312
  have hstable : (prefixWord ++ tailWord_7860312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860312).length < 2 ^ (prefixWord ++ tailWord_7860312).sum := by decide
  have hdescent : baseEnd_7860312 < baseStart_7860312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860349 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 2, 4, 2]
def baseStart_7860349 : Nat := 118140960795 + 7860349 * 2 ^ 59
def prefixEnd_7860349 : Nat := 4983230072969 + 3 ^ 40 * 7860349 * 2
def baseEnd_7860349 : Nat := 4036137149087772082088419

theorem tailTrace_7860349 : CollatzResearch.WordTrace tailWord_7860349 prefixEnd_7860349 4036137149087772082088419 := by
  unfold tailWord_7860349
  simp only [CollatzResearch.WordTrace]
  refine ⟨286690480600305488577144101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191126987066870325718096067 286690480600305488577144101)
  ·
    refine ⟨53754465112557279108214519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286690480600305488577144101 53754465112557279108214519)
    ·
      refine ⟨80631697668835918662321779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53754465112557279108214519 80631697668835918662321779)
      ·
        refine ⟨120947546503253877993482669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80631697668835918662321779 120947546503253877993482669)
        ·
          refine ⟨45355329938720204247556001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120947546503253877993482669 45355329938720204247556001)
          ·
            refine ⟨34016497454040153185667001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45355329938720204247556001 34016497454040153185667001)
            ·
              refine ⟨25512373090530114889250251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34016497454040153185667001 25512373090530114889250251)
              ·
                refine ⟨38268559635795172333875377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25512373090530114889250251 38268559635795172333875377)
                ·
                  refine ⟨28701419726846379250406533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38268559635795172333875377 28701419726846379250406533)
                  ·
                    refine ⟨5381516198783696109451225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28701419726846379250406533 5381516198783696109451225)
                    ·
                      refine ⟨4036137149087772082088419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5381516198783696109451225 4036137149087772082088419)
                      ·
                        rfl

theorem cell23_7860349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_7860349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860349 prefixEnd_7860349 := by exact prefixLift 7860349
  have htrace : WordTrace (prefixWord ++ tailWord_7860349) baseStart_7860349 baseEnd_7860349 := by
    simpa [prefixWord, tailWord_7860349, baseEnd_7860349] using wordTrace_append hprefix tailTrace_7860349
  have hstable : (prefixWord ++ tailWord_7860349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860349).length < 2 ^ (prefixWord ++ tailWord_7860349).sum := by decide
  have hdescent : baseEnd_7860349 < baseStart_7860349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860386 : List Nat := [3, 3, 1, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_7860386 : Nat := 118140960795 + 7860386 * 2 ^ 59
def prefixEnd_7860386 : Nat := 4983230072969 + 3 ^ 40 * 7860386 * 2
def baseEnd_7860386 : Nat := 4036156147871988437325749

theorem tailTrace_7860386 : CollatzResearch.WordTrace tailWord_7860386 prefixEnd_7860386 4036156147871988437325749 := by
  unfold tailWord_7860386
  simp only [CollatzResearch.WordTrace]
  refine ⟨71672957525292860974060253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191127886734114295930827341 71672957525292860974060253)
  ·
    refine ⟨26877359071984822865272595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71672957525292860974060253 26877359071984822865272595)
    ·
      refine ⟨40316038607977234297908893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26877359071984822865272595 40316038607977234297908893)
      ·
        refine ⟨15118514477991462861715835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40316038607977234297908893 15118514477991462861715835)
        ·
          refine ⟨22677771716987194292573753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15118514477991462861715835 22677771716987194292573753)
          ·
            refine ⟨17008328787740395719430315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22677771716987194292573753 17008328787740395719430315)
            ·
              refine ⟨25512493181610593579145473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17008328787740395719430315 25512493181610593579145473)
              ·
                refine ⟨19134369886207945184359105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25512493181610593579145473 19134369886207945184359105)
                ·
                  refine ⟨14350777414655958888269329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19134369886207945184359105 14350777414655958888269329)
                  ·
                    refine ⟨10763083060991969166201997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14350777414655958888269329 10763083060991969166201997)
                    ·
                      refine ⟨4036156147871988437325749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10763083060991969166201997 4036156147871988437325749)
                      ·
                        rfl

theorem cell23_7860386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_7860386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860386 prefixEnd_7860386 := by exact prefixLift 7860386
  have htrace : WordTrace (prefixWord ++ tailWord_7860386) baseStart_7860386 baseEnd_7860386 := by
    simpa [prefixWord, tailWord_7860386, baseEnd_7860386] using wordTrace_append hprefix tailTrace_7860386
  have hstable : (prefixWord ++ tailWord_7860386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860386).length < 2 ^ (prefixWord ++ tailWord_7860386).sum := by decide
  have hdescent : baseEnd_7860386 < baseStart_7860386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860402 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 3, 5]
def baseStart_7860402 : Nat := 118140960795 + 7860402 * 2 ^ 59
def prefixEnd_7860402 : Nat := 4983230072969 + 3 ^ 40 * 7860402 * 2
def baseEnd_7860402 : Nat := 1345388121187486791575225

theorem tailTrace_7860402 : CollatzResearch.WordTrace tailWord_7860402 prefixEnd_7860402 1345388121187486791575225 := by
  unfold tailWord_7860402
  simp only [CollatzResearch.WordTrace]
  refine ⟨71673103417278369657205865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191128275779408985752548973 71673103417278369657205865)
  ·
    refine ⟨53754827562958777242904399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71673103417278369657205865 53754827562958777242904399)
    ·
      refine ⟨80632241344438165864356599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53754827562958777242904399 80632241344438165864356599)
      ·
        refine ⟨120948362016657248796534899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80632241344438165864356599 120948362016657248796534899)
        ·
          refine ⟨181422543024985873194802349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120948362016657248796534899 181422543024985873194802349)
          ·
            refine ⟨68033453634369702448050881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181422543024985873194802349 68033453634369702448050881)
            ·
              refine ⟨51025090225777276836038161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68033453634369702448050881 51025090225777276836038161)
              ·
                refine ⟨38268817669332957627028621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51025090225777276836038161 38268817669332957627028621)
                ·
                  refine ⟨14350806625999859110135733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38268817669332957627028621 14350806625999859110135733)
                  ·
                    refine ⟨1345388121187486791575225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14350806625999859110135733 1345388121187486791575225)
                    ·
                      rfl

theorem cell23_7860402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_7860402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860402 prefixEnd_7860402 := by exact prefixLift 7860402
  have htrace : WordTrace (prefixWord ++ tailWord_7860402) baseStart_7860402 baseEnd_7860402 := by
    simpa [prefixWord, tailWord_7860402, baseEnd_7860402] using wordTrace_append hprefix tailTrace_7860402
  have hstable : (prefixWord ++ tailWord_7860402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860402).length < 2 ^ (prefixWord ++ tailWord_7860402).sum := by decide
  have hdescent : baseEnd_7860402 < baseStart_7860402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7860409 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 4, 3, 2]
def baseStart_7860409 : Nat := 118140960795 + 7860409 * 2 ^ 59
def prefixEnd_7860409 : Nat := 4983230072969 + 3 ^ 40 * 7860409 * 2
def baseEnd_7860409 : Nat := 4036167957927041847338143

theorem tailTrace_7860409 : CollatzResearch.WordTrace tailWord_7860409 prefixEnd_7860409 4036167957927041847338143 := by
  unfold tailWord_7860409
  simp only [CollatzResearch.WordTrace]
  refine ⟨286692668980088118824328281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191128445986725412549552187 286692668980088118824328281)
  ·
    refine ⟨215019501735066089118246211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286692668980088118824328281 215019501735066089118246211)
    ·
      refine ⟨322529252602599133677369317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215019501735066089118246211 322529252602599133677369317)
      ·
        refine ⟨60474234862987337564506747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322529252602599133677369317 60474234862987337564506747)
        ·
          refine ⟨90711352294481006346760121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60474234862987337564506747 90711352294481006346760121)
          ·
            refine ⟨68033514220860754760070091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90711352294481006346760121 68033514220860754760070091)
            ·
              refine ⟨102050271331291132140105137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68033514220860754760070091 102050271331291132140105137)
              ·
                refine ⟨76537703498468349105078853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102050271331291132140105137 76537703498468349105078853)
                ·
                  refine ⟨14350819405962815457202285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76537703498468349105078853 14350819405962815457202285)
                  ·
                    refine ⟨5381557277236055796450857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14350819405962815457202285 5381557277236055796450857)
                    ·
                      refine ⟨4036167957927041847338143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5381557277236055796450857 4036167957927041847338143)
                      ·
                        rfl

theorem cell23_7860409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_7860409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7860409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7860409 prefixEnd_7860409 := by exact prefixLift 7860409
  have htrace : WordTrace (prefixWord ++ tailWord_7860409) baseStart_7860409 baseEnd_7860409 := by
    simpa [prefixWord, tailWord_7860409, baseEnd_7860409] using wordTrace_append hprefix tailTrace_7860409
  have hstable : (prefixWord ++ tailWord_7860409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7860409).length < 2 ^ (prefixWord ++ tailWord_7860409).sum := by decide
  have hdescent : baseEnd_7860409 < baseStart_7860409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7860409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
