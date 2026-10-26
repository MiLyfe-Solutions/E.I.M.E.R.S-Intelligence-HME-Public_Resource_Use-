import V185TrunkScan22Chunk253

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2265048 : List Nat := [2, 1, 2, 2, 2, 2, 1, 10]
def baseStart_2265048 : Nat := 118140960795 + 2265048 * 2 ^ 59
def prefixEnd_2265048 : Nat := 4983230072969 + 3 ^ 40 * 2265048 * 2
def baseEnd_2265048 : Nat := 86152468852234016517277

theorem tailTrace_2265048 : CollatzResearch.WordTrace tailWord_2265048 prefixEnd_2265048 86152468852234016517277 := by
  unfold tailWord_2265048
  simp only [CollatzResearch.WordTrace]
  refine ⟨41306543749062705122825899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55075391665416940163767865 41306543749062705122825899)
  ·
    refine ⟨61959815623594057684238849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41306543749062705122825899 61959815623594057684238849)
    ·
      refine ⟨46469861717695543263179137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61959815623594057684238849 46469861717695543263179137)
      ·
        refine ⟨34852396288271657447384353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46469861717695543263179137 34852396288271657447384353)
        ·
          refine ⟨26139297216203743085538265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34852396288271657447384353 26139297216203743085538265)
          ·
            refine ⟨19604472912152807314153699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26139297216203743085538265 19604472912152807314153699)
            ·
              refine ⟨29406709368229210971230549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19604472912152807314153699 29406709368229210971230549)
              ·
                refine ⟨86152468852234016517277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29406709368229210971230549 86152468852234016517277)
                ·
                  rfl

theorem cell22_2265048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 10].length) (baseStart_2265048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265048 prefixEnd_2265048 := by exact prefixLift 2265048
  have htrace : WordTrace (prefixWord ++ tailWord_2265048) baseStart_2265048 baseEnd_2265048 := by
    simpa [prefixWord, tailWord_2265048, baseEnd_2265048] using wordTrace_append hprefix tailTrace_2265048
  have hstable : (prefixWord ++ tailWord_2265048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265048).length < 2 ^ (prefixWord ++ tailWord_2265048).sum := by decide
  have hdescent : baseEnd_2265048 < baseStart_2265048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265101 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_2265101 : Nat := 118140960795 + 2265101 * 2 ^ 59
def prefixEnd_2265101 : Nat := 4983230072969 + 3 ^ 40 * 2265101 * 2
def baseEnd_2265101 : Nat := 775390362653231677080331

theorem tailTrace_2265101 : CollatzResearch.WordTrace tailWord_2265101 prefixEnd_2265101 775390362653231677080331 := by
  unfold tailWord_2265101
  simp only [CollatzResearch.WordTrace]
  refine ⟨82615020566933400297331157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55076680377955600198220771 82615020566933400297331157)
  ·
    refine ⟨1936289544537501569468699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 82615020566933400297331157 1936289544537501569468699)
    ·
      refine ⟨2904434316806252354203049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1936289544537501569468699 2904434316806252354203049)
      ·
        refine ⟨2178325737604689265652287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2904434316806252354203049 2178325737604689265652287)
        ·
          refine ⟨3267488606407033898478431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2178325737604689265652287 3267488606407033898478431)
          ·
            refine ⟨4901232909610550847717647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3267488606407033898478431 4901232909610550847717647)
            ·
              refine ⟨7351849364415826271576471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4901232909610550847717647 7351849364415826271576471)
              ·
                refine ⟨11027774046623739407364707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7351849364415826271576471 11027774046623739407364707)
                ·
                  refine ⟨16541661069935609111047061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11027774046623739407364707 16541661069935609111047061)
                  ·
                    refine ⟨775390362653231677080331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16541661069935609111047061 775390362653231677080331)
                    ·
                      rfl

theorem cell22_2265101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_2265101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265101 prefixEnd_2265101 := by exact prefixLift 2265101
  have htrace : WordTrace (prefixWord ++ tailWord_2265101) baseStart_2265101 baseEnd_2265101 := by
    simpa [prefixWord, tailWord_2265101, baseEnd_2265101] using wordTrace_append hprefix tailTrace_2265101
  have hstable : (prefixWord ++ tailWord_2265101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265101).length < 2 ^ (prefixWord ++ tailWord_2265101).sum := by decide
  have hdescent : baseEnd_2265101 < baseStart_2265101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265114 : List Nat := [3, 1, 1, 3, 1, 3, 1, 5, 1, 3]
def baseStart_2265114 : Nat := 118140960795 + 2265114 * 2 ^ 59
def prefixEnd_2265114 : Nat := 4983230072969 + 3 ^ 40 * 2265114 * 2
def baseEnd_2265114 : Nat := 775394812818903976505291

theorem tailTrace_2265114 : CollatzResearch.WordTrace tailWord_2265114 prefixEnd_2265114 775394812818903976505291 := by
  unfold tailWord_2265114
  simp only [CollatzResearch.WordTrace]
  refine ⟨20653873678971575879388599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55076996477257535678369597 20653873678971575879388599)
  ·
    refine ⟨30980810518457363819082899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20653873678971575879388599 30980810518457363819082899)
    ·
      refine ⟨46471215777686045728624349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30980810518457363819082899 46471215777686045728624349)
      ·
        refine ⟨17426705916632267148234131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46471215777686045728624349 17426705916632267148234131)
        ·
          refine ⟨26140058874948400722351197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17426705916632267148234131 26140058874948400722351197)
          ·
            refine ⟨9802522078105650270881699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26140058874948400722351197 9802522078105650270881699)
            ·
              refine ⟨14703783117158475406322549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9802522078105650270881699 14703783117158475406322549)
              ·
                refine ⟨1378479667233607069342739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14703783117158475406322549 1378479667233607069342739)
                ·
                  refine ⟨2067719500850410604014109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1378479667233607069342739 2067719500850410604014109)
                  ·
                    refine ⟨775394812818903976505291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2067719500850410604014109 775394812818903976505291)
                    ·
                      rfl

theorem cell22_2265114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 1, 3].length) (baseStart_2265114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265114 prefixEnd_2265114 := by exact prefixLift 2265114
  have htrace : WordTrace (prefixWord ++ tailWord_2265114) baseStart_2265114 baseEnd_2265114 := by
    simpa [prefixWord, tailWord_2265114, baseEnd_2265114] using wordTrace_append hprefix tailTrace_2265114
  have hstable : (prefixWord ++ tailWord_2265114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265114).length < 2 ^ (prefixWord ++ tailWord_2265114).sum := by decide
  have hdescent : baseEnd_2265114 < baseStart_2265114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265125 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 2, 5]
def baseStart_2265125 : Nat := 118140960795 + 2265125 * 2 ^ 59
def prefixEnd_2265125 : Nat := 4983230072969 + 3 ^ 40 * 2265125 * 2
def baseEnd_2265125 : Nat := 775398578343703614480257

theorem tailTrace_2265125 : CollatzResearch.WordTrace tailWord_2265125 prefixEnd_2265125 775398578343703614480257 := by
  unfold tailWord_2265125
  simp only [CollatzResearch.WordTrace]
  refine ⟨82615895918846452396204829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55077263945897634930803219 82615895918846452396204829)
  ·
    refine ⟨30980960969567419648576811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82615895918846452396204829 30980960969567419648576811)
    ·
      refine ⟨46471441454351129472865217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30980960969567419648576811 46471441454351129472865217)
      ·
        refine ⟨34853581090763347104648913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46471441454351129472865217 34853581090763347104648913)
        ·
          refine ⟨26140185818072510328486685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34853581090763347104648913 26140185818072510328486685)
          ·
            refine ⟨9802569681777191373182507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26140185818072510328486685 9802569681777191373182507)
            ·
              refine ⟨14703854522665787059773761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9802569681777191373182507 14703854522665787059773761)
              ·
                refine ⟨11027890891999340294830321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14703854522665787059773761 11027890891999340294830321)
                ·
                  refine ⟨8270918168999505221122741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11027890891999340294830321 8270918168999505221122741)
                  ·
                    refine ⟨775398578343703614480257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8270918168999505221122741 775398578343703614480257)
                    ·
                      rfl

theorem cell22_2265125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_2265125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265125 prefixEnd_2265125 := by exact prefixLift 2265125
  have htrace : WordTrace (prefixWord ++ tailWord_2265125) baseStart_2265125 baseEnd_2265125 := by
    simpa [prefixWord, tailWord_2265125, baseEnd_2265125] using wordTrace_append hprefix tailTrace_2265125
  have hstable : (prefixWord ++ tailWord_2265125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265125).length < 2 ^ (prefixWord ++ tailWord_2265125).sum := by decide
  have hdescent : baseEnd_2265125 < baseStart_2265125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265142 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_2265142 : Nat := 118140960795 + 2265142 * 2 ^ 59
def prefixEnd_2265142 : Nat := 4983230072969 + 3 ^ 40 * 2265142 * 2
def baseEnd_2265142 : Nat := 775404397791121236805205

theorem tailTrace_2265142 : CollatzResearch.WordTrace tailWord_2265142 prefixEnd_2265142 775404397791121236805205 := by
  unfold tailWord_2265142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5163532247486554018723355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55077677306523242866382453 5163532247486554018723355)
  ·
    refine ⟨7745298371229831028085033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5163532247486554018723355 7745298371229831028085033)
    ·
      refine ⟨5808973778422373271063775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7745298371229831028085033 5808973778422373271063775)
      ·
        refine ⟨8713460667633559906595663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5808973778422373271063775 8713460667633559906595663)
        ·
          refine ⟨13070191001450339859893495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8713460667633559906595663 13070191001450339859893495)
          ·
            refine ⟨19605286502175509789840243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13070191001450339859893495 19605286502175509789840243)
            ·
              refine ⟨29407929753263264684760365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19605286502175509789840243 29407929753263264684760365)
              ·
                refine ⟨11027973657473724256785137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29407929753263264684760365 11027973657473724256785137)
                ·
                  refine ⟨8270980243105293192588853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11027973657473724256785137 8270980243105293192588853)
                  ·
                    refine ⟨775404397791121236805205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8270980243105293192588853 775404397791121236805205)
                    ·
                      rfl

theorem cell22_2265142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_2265142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265142 prefixEnd_2265142 := by exact prefixLift 2265142
  have htrace : WordTrace (prefixWord ++ tailWord_2265142) baseStart_2265142 baseEnd_2265142 := by
    simpa [prefixWord, tailWord_2265142, baseEnd_2265142] using wordTrace_append hprefix tailTrace_2265142
  have hstable : (prefixWord ++ tailWord_2265142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265142).length < 2 ^ (prefixWord ++ tailWord_2265142).sum := by decide
  have hdescent : baseEnd_2265142 < baseStart_2265142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265144 : List Nat := [2, 1, 2, 1, 6, 1, 3, 1, 5]
def baseStart_2265144 : Nat := 118140960795 + 2265144 * 2 ^ 59
def prefixEnd_2265144 : Nat := 4983230072969 + 3 ^ 40 * 2265144 * 2
def baseEnd_2265144 : Nat := 258468360810664632751733

theorem tailTrace_2265144 : CollatzResearch.WordTrace tailWord_2265144 prefixEnd_2265144 258468360810664632751733 := by
  unfold tailWord_2265144
  simp only [CollatzResearch.WordTrace]
  refine ⟨41308294452888809320573243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55077725937185079094097657 41308294452888809320573243)
  ·
    refine ⟨61962441679333213980859865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41308294452888809320573243 61962441679333213980859865)
    ·
      refine ⟨46471831259499910485644899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61962441679333213980859865 46471831259499910485644899)
      ·
        refine ⟨69707746889249865728467349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46471831259499910485644899 69707746889249865728467349)
        ·
          refine ⟨3267550635433587456021907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69707746889249865728467349 3267550635433587456021907)
          ·
            refine ⟨4901325953150381184032861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3267550635433587456021907 4901325953150381184032861)
            ·
              refine ⟨1837997232431392944012323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4901325953150381184032861 1837997232431392944012323)
              ·
                refine ⟨2756995848647089416018485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837997232431392944012323 2756995848647089416018485)
                ·
                  refine ⟨258468360810664632751733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2756995848647089416018485 258468360810664632751733)
                  ·
                    rfl

theorem cell22_2265144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 5].length) (baseStart_2265144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265144 prefixEnd_2265144 := by exact prefixLift 2265144
  have htrace : WordTrace (prefixWord ++ tailWord_2265144) baseStart_2265144 baseEnd_2265144 := by
    simpa [prefixWord, tailWord_2265144, baseEnd_2265144] using wordTrace_append hprefix tailTrace_2265144
  have hstable : (prefixWord ++ tailWord_2265144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265144).length < 2 ^ (prefixWord ++ tailWord_2265144).sum := by decide
  have hdescent : baseEnd_2265144 < baseStart_2265144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265182 : List Nat := [4, 4, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_2265182 : Nat := 118140960795 + 2265182 * 2 ^ 59
def prefixEnd_2265182 : Nat := 4983230072969 + 3 ^ 40 * 2265182 * 2
def baseEnd_2265182 : Nat := 775418090608574465805083

theorem tailTrace_2265182 : CollatzResearch.WordTrace tailWord_2265182 prefixEnd_2265182 775418090608574465805083 := by
  unfold tailWord_2265182
  simp only [CollatzResearch.WordTrace]
  refine ⟨10327246859954993891378725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55078649919759967420686533 10327246859954993891378725)
  ·
    refine ⟨1936358786241561354633511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10327246859954993891378725 1936358786241561354633511)
    ·
      refine ⟨2904538179362342031950267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1936358786241561354633511 2904538179362342031950267)
      ·
        refine ⟨4356807269043513047925401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2904538179362342031950267 4356807269043513047925401)
        ·
          refine ⟨3267605451782634785944051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4356807269043513047925401 3267605451782634785944051)
          ·
            refine ⟨4901408177673952178916077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3267605451782634785944051 4901408177673952178916077)
            ·
              refine ⟨1838028066627732067093529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4901408177673952178916077 1838028066627732067093529)
              ·
                refine ⟨1378521049970799050320147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1838028066627732067093529 1378521049970799050320147)
                ·
                  refine ⟨2067781574956198575480221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1378521049970799050320147 2067781574956198575480221)
                  ·
                    refine ⟨775418090608574465805083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2067781574956198575480221 775418090608574465805083)
                    ·
                      rfl

theorem cell22_2265182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_2265182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265182 prefixEnd_2265182 := by exact prefixLift 2265182
  have htrace : WordTrace (prefixWord ++ tailWord_2265182) baseStart_2265182 baseEnd_2265182 := by
    simpa [prefixWord, tailWord_2265182, baseEnd_2265182] using wordTrace_append hprefix tailTrace_2265182
  have hstable : (prefixWord ++ tailWord_2265182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265182).length < 2 ^ (prefixWord ++ tailWord_2265182).sum := by decide
  have hdescent : baseEnd_2265182 < baseStart_2265182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265187 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 4, 3]
def baseStart_2265187 : Nat := 118140960795 + 2265187 * 2 ^ 59
def prefixEnd_2265187 : Nat := 4983230072969 + 3 ^ 40 * 2265187 * 2
def baseEnd_2265187 : Nat := 775419802210756119430067

theorem tailTrace_2265187 : CollatzResearch.WordTrace tailWord_2265187 prefixEnd_2265187 775419802210756119430067 := by
  unfold tailWord_2265187
  simp only [CollatzResearch.WordTrace]
  refine ⟨82618157244621836984961815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55078771496414557989974543 82618157244621836984961815)
  ·
    refine ⟨123927235866932755477442723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82618157244621836984961815 123927235866932755477442723)
    ·
      refine ⟨185890853800399133216164085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123927235866932755477442723 185890853800399133216164085)
      ·
        refine ⟨17427267543787418739015383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 185890853800399133216164085 17427267543787418739015383)
        ·
          refine ⟨26140901315681128108523075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17427267543787418739015383 26140901315681128108523075)
          ·
            refine ⟨39211351973521692162784613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26140901315681128108523075 39211351973521692162784613)
            ·
              refine ⟨7352128495035317280522115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39211351973521692162784613 7352128495035317280522115)
              ·
                refine ⟨11028192742552975920783173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7352128495035317280522115 11028192742552975920783173)
                ·
                  refine ⟨2067786139228682985146845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11028192742552975920783173 2067786139228682985146845)
                  ·
                    refine ⟨775419802210756119430067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2067786139228682985146845 775419802210756119430067)
                    ·
                      rfl

theorem cell22_2265187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 3].length) (baseStart_2265187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265187 prefixEnd_2265187 := by exact prefixLift 2265187
  have htrace : WordTrace (prefixWord ++ tailWord_2265187) baseStart_2265187 baseEnd_2265187 := by
    simpa [prefixWord, tailWord_2265187, baseEnd_2265187] using wordTrace_append hprefix tailTrace_2265187
  have hstable : (prefixWord ++ tailWord_2265187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265187).length < 2 ^ (prefixWord ++ tailWord_2265187).sum := by decide
  have hdescent : baseEnd_2265187 < baseStart_2265187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265200 : List Nat := [2, 1, 1, 1, 5, 2, 1, 9]
def baseStart_2265200 : Nat := 118140960795 + 2265200 * 2 ^ 59
def prefixEnd_2265200 : Nat := 4983230072969 + 3 ^ 40 * 2265200 * 2
def baseEnd_2265200 : Nat := 86158250264047602095003

theorem tailTrace_2265200 : CollatzResearch.WordTrace tailWord_2265200 prefixEnd_2265200 86158250264047602095003 := by
  unfold tailWord_2265200
  simp only [CollatzResearch.WordTrace]
  refine ⟨41309315696787370102592527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55079087595716493470123369 41309315696787370102592527)
  ·
    refine ⟨61963973545181055153888791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41309315696787370102592527 61963973545181055153888791)
    ·
      refine ⟨92945960317771582730833187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61963973545181055153888791 92945960317771582730833187)
      ·
        refine ⟨139418940476657374096249781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92945960317771582730833187 139418940476657374096249781)
        ·
          refine ⟨13070525669686628821523417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 139418940476657374096249781 13070525669686628821523417)
          ·
            refine ⟨9802894252264971616142563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13070525669686628821523417 9802894252264971616142563)
            ·
              refine ⟨14704341378397457424213845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9802894252264971616142563 14704341378397457424213845)
              ·
                refine ⟨86158250264047602095003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14704341378397457424213845 86158250264047602095003)
                ·
                  rfl

theorem cell22_2265200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 9].length) (baseStart_2265200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265200 prefixEnd_2265200 := by exact prefixLift 2265200
  have htrace : WordTrace (prefixWord ++ tailWord_2265200) baseStart_2265200 baseEnd_2265200 := by
    simpa [prefixWord, tailWord_2265200, baseEnd_2265200] using wordTrace_append hprefix tailTrace_2265200
  have hstable : (prefixWord ++ tailWord_2265200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265200).length < 2 ^ (prefixWord ++ tailWord_2265200).sum := by decide
  have hdescent : baseEnd_2265200 < baseStart_2265200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265247 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 2, 6]
def baseStart_2265247 : Nat := 118140960795 + 2265247 * 2 ^ 59
def prefixEnd_2265247 : Nat := 4983230072969 + 3 ^ 40 * 2265247 * 2
def baseEnd_2265247 : Nat := 775440341436935962929883

theorem tailTrace_2265247 : CollatzResearch.WordTrace tailWord_2265247 prefixEnd_2265247 775440341436935962929883 := by
  unfold tailWord_2265247
  simp only [CollatzResearch.WordTrace]
  refine ⟨82620345624404467232145995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55080230416269644821430663 82620345624404467232145995)
  ·
    refine ⟨123930518436606700848218993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82620345624404467232145995 123930518436606700848218993)
    ·
      refine ⟨92947888827455025636164245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123930518436606700848218993 92947888827455025636164245)
      ·
        refine ⟨4356932288786954326695199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 92947888827455025636164245 4356932288786954326695199)
        ·
          refine ⟨6535398433180431490042799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4356932288786954326695199 6535398433180431490042799)
          ·
            refine ⟨9803097649770647235064199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6535398433180431490042799 9803097649770647235064199)
            ·
              refine ⟨14704646474655970852596299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9803097649770647235064199 14704646474655970852596299)
              ·
                refine ⟨22056969711983956278894449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14704646474655970852596299 22056969711983956278894449)
                ·
                  refine ⟨16542727283987967209170837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22056969711983956278894449 16542727283987967209170837)
                  ·
                    refine ⟨775440341436935962929883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16542727283987967209170837 775440341436935962929883)
                    ·
                      rfl

theorem cell22_2265247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_2265247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265247 prefixEnd_2265247 := by exact prefixLift 2265247
  have htrace : WordTrace (prefixWord ++ tailWord_2265247) baseStart_2265247 baseEnd_2265247 := by
    simpa [prefixWord, tailWord_2265247, baseEnd_2265247] using wordTrace_append hprefix tailTrace_2265247
  have hstable : (prefixWord ++ tailWord_2265247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265247).length < 2 ^ (prefixWord ++ tailWord_2265247).sum := by decide
  have hdescent : baseEnd_2265247 < baseStart_2265247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265352 : List Nat := [2, 1, 3, 2, 3, 1, 10]
def baseStart_2265352 : Nat := 118140960795 + 2265352 * 2 ^ 59
def prefixEnd_2265352 : Nat := 4983230072969 + 3 ^ 40 * 2265352 * 2
def baseEnd_2265352 : Nat := 28721343891953729224243

theorem tailTrace_2265352 : CollatzResearch.WordTrace tailWord_2265352 prefixEnd_2265352 28721343891953729224243 := by
  unfold tailWord_2265352
  simp only [CollatzResearch.WordTrace]
  refine ⟨41312087644512035082359155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55082783526016046776478873 41312087644512035082359155)
  ·
    refine ⟨61968131466768052623538733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41312087644512035082359155 61968131466768052623538733)
    ·
      refine ⟨23238049300038019733827025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61968131466768052623538733 23238049300038019733827025)
      ·
        refine ⟨17428536975028514800370269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23238049300038019733827025 17428536975028514800370269)
        ·
          refine ⟨6535701365635693050138851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17428536975028514800370269 6535701365635693050138851)
          ·
            refine ⟨9803552048453539575208277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6535701365635693050138851 9803552048453539575208277)
            ·
              refine ⟨28721343891953729224243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9803552048453539575208277 28721343891953729224243)
              ·
                rfl

theorem cell22_2265352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 10].length) (baseStart_2265352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265352 prefixEnd_2265352 := by exact prefixLift 2265352
  have htrace : WordTrace (prefixWord ++ tailWord_2265352) baseStart_2265352 baseEnd_2265352 := by
    simpa [prefixWord, tailWord_2265352, baseEnd_2265352] using wordTrace_append hprefix tailTrace_2265352
  have hstable : (prefixWord ++ tailWord_2265352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265352).length < 2 ^ (prefixWord ++ tailWord_2265352).sum := by decide
  have hdescent : baseEnd_2265352 < baseStart_2265352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265373 : List Nat := [1, 4, 2, 3, 2, 1, 1, 3, 2, 3]
def baseStart_2265373 : Nat := 118140960795 + 2265373 * 2 ^ 59
def prefixEnd_2265373 : Nat := 4983230072969 + 3 ^ 40 * 2265373 * 2
def baseEnd_2265373 : Nat := 775483473811913634279497

theorem tailTrace_2265373 : CollatzResearch.WordTrace tailWord_2265373 prefixEnd_2265373 775483473811913634279497 := by
  unfold tailWord_2265373
  simp only [CollatzResearch.WordTrace]
  refine ⟨82624941221947990751232773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55083294147965327167488515 82624941221947990751232773)
  ·
    refine ⟨15492176479115248265856145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82624941221947990751232773 15492176479115248265856145)
    ·
      refine ⟨11619132359336436199392109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15492176479115248265856145 11619132359336436199392109)
      ·
        refine ⟨4357174634751163574772041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11619132359336436199392109 4357174634751163574772041)
        ·
          refine ⟨3267880976063372681079031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4357174634751163574772041 3267880976063372681079031)
          ·
            refine ⟨4901821464095059021618547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3267880976063372681079031 4901821464095059021618547)
            ·
              refine ⟨7352732196142588532427821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4901821464095059021618547 7352732196142588532427821)
              ·
                refine ⟨2757274573553470699660433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7352732196142588532427821 2757274573553470699660433)
                ·
                  refine ⟨2067955930165103024745325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2757274573553470699660433 2067955930165103024745325)
                  ·
                    refine ⟨775483473811913634279497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2067955930165103024745325 775483473811913634279497)
                    ·
                      rfl

theorem cell22_2265373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_2265373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265373 prefixEnd_2265373 := by exact prefixLift 2265373
  have htrace : WordTrace (prefixWord ++ tailWord_2265373) baseStart_2265373 baseEnd_2265373 := by
    simpa [prefixWord, tailWord_2265373, baseEnd_2265373] using wordTrace_append hprefix tailTrace_2265373
  have hstable : (prefixWord ++ tailWord_2265373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265373).length < 2 ^ (prefixWord ++ tailWord_2265373).sum := by decide
  have hdescent : baseEnd_2265373 < baseStart_2265373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265444 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_2265444 : Nat := 118140960795 + 2265444 * 2 ^ 59
def prefixEnd_2265444 : Nat := 4983230072969 + 3 ^ 40 * 2265444 * 2
def baseEnd_2265444 : Nat := 775507778562893115754279

theorem tailTrace_2265444 : CollatzResearch.WordTrace tailWord_2265444 prefixEnd_2265444 775507778562893115754279 := by
  unfold tailWord_2265444
  simp only [CollatzResearch.WordTrace]
  refine ⟨41313765402345384938533693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55085020536460513251378257 41313765402345384938533693)
  ·
    refine ⟨15492662025879519351950135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41313765402345384938533693 15492662025879519351950135)
    ·
      refine ⟨23238993038819279027925203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15492662025879519351950135 23238993038819279027925203)
      ·
        refine ⟨34858489558228918541887805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23238993038819279027925203 34858489558228918541887805)
        ·
          refine ⟨13071933584335844453207927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34858489558228918541887805 13071933584335844453207927)
          ·
            refine ⟨19607900376503766679811891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13071933584335844453207927 19607900376503766679811891)
            ·
              refine ⟨29411850564755650019717837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19607900376503766679811891 29411850564755650019717837)
              ·
                refine ⟨11029443961783368757394189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29411850564755650019717837 11029443961783368757394189)
                ·
                  refine ⟨4136041485668763284022821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11029443961783368757394189 4136041485668763284022821)
                  ·
                    refine ⟨775507778562893115754279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4136041485668763284022821 775507778562893115754279)
                    ·
                      rfl

theorem cell22_2265444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_2265444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265444 prefixEnd_2265444 := by exact prefixLift 2265444
  have htrace : WordTrace (prefixWord ++ tailWord_2265444) baseStart_2265444 baseEnd_2265444 := by
    simpa [prefixWord, tailWord_2265444, baseEnd_2265444] using wordTrace_append hprefix tailTrace_2265444
  have hstable : (prefixWord ++ tailWord_2265444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265444).length < 2 ^ (prefixWord ++ tailWord_2265444).sum := by decide
  have hdescent : baseEnd_2265444 < baseStart_2265444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265476 : List Nat := [2, 3, 2, 1, 1, 2, 1, 6, 4]
def baseStart_2265476 : Nat := 118140960795 + 2265476 * 2 ^ 59
def prefixEnd_2265476 : Nat := 4983230072969 + 3 ^ 40 * 2265476 * 2
def baseEnd_2265476 : Nat := 258506244272285232984727

theorem tailTrace_2265476 : CollatzResearch.WordTrace tailWord_2265476 prefixEnd_2265476 258506244272285232984727 := by
  unfold tailWord_2265476
  simp only [CollatzResearch.WordTrace]
  refine ⟨41314348970287419671116141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55085798627049892894821521 41314348970287419671116141)
  ·
    refine ⟨15492880863857782376668553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41314348970287419671116141 15492880863857782376668553)
    ·
      refine ⟨11619660647893336782501415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15492880863857782376668553 11619660647893336782501415)
      ·
        refine ⟨17429490971840005173752123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11619660647893336782501415 17429490971840005173752123)
        ·
          refine ⟨26144236457760007760628185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17429490971840005173752123 26144236457760007760628185)
          ·
            refine ⟨19608177343320005820471139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26144236457760007760628185 19608177343320005820471139)
            ·
              refine ⟨29412266014980008730706709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19608177343320005820471139 29412266014980008730706709)
              ·
                refine ⟨1378699969452187909251877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29412266014980008730706709 1378699969452187909251877)
                ·
                  refine ⟨258506244272285232984727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1378699969452187909251877 258506244272285232984727)
                  ·
                    rfl

theorem cell22_2265476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_2265476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265476 prefixEnd_2265476 := by exact prefixLift 2265476
  have htrace : WordTrace (prefixWord ++ tailWord_2265476) baseStart_2265476 baseEnd_2265476 := by
    simpa [prefixWord, tailWord_2265476, baseEnd_2265476] using wordTrace_append hprefix tailTrace_2265476
  have hstable : (prefixWord ++ tailWord_2265476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265476).length < 2 ^ (prefixWord ++ tailWord_2265476).sum := by decide
  have hdescent : baseEnd_2265476 < baseStart_2265476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265504 : List Nat := [2, 1, 1, 4, 1, 4, 1, 8]
def baseStart_2265504 : Nat := 118140960795 + 2265504 * 2 ^ 59
def prefixEnd_2265504 : Nat := 4983230072969 + 3 ^ 40 * 2265504 * 2
def baseEnd_2265504 : Nat := 86169813087674773250455

theorem tailTrace_2265504 : CollatzResearch.WordTrace tailWord_2265504 prefixEnd_2265504 86169813087674773250455 := by
  unfold tailWord_2265504
  simp only [CollatzResearch.WordTrace]
  refine ⟨41314859592236700062125783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55086479456315600082834377 41314859592236700062125783)
  ·
    refine ⟨61972289388355050093188675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41314859592236700062125783 61972289388355050093188675)
    ·
      refine ⟨92958434082532575139783013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61972289388355050093188675 92958434082532575139783013)
      ·
        refine ⟨17429706390474857838709315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92958434082532575139783013 17429706390474857838709315)
        ·
          refine ⟨26144559585712286758063973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17429706390474857838709315 26144559585712286758063973)
          ·
            refine ⟨4902104922321053767136995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26144559585712286758063973 4902104922321053767136995)
            ·
              refine ⟨7353157383481580650705493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4902104922321053767136995 7353157383481580650705493)
              ·
                refine ⟨86169813087674773250455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7353157383481580650705493 86169813087674773250455)
                ·
                  rfl

theorem cell22_2265504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 8].length) (baseStart_2265504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265504 prefixEnd_2265504 := by exact prefixLift 2265504
  have htrace : WordTrace (prefixWord ++ tailWord_2265504) baseStart_2265504 baseEnd_2265504 := by
    simpa [prefixWord, tailWord_2265504, baseEnd_2265504] using wordTrace_append hprefix tailTrace_2265504
  have hstable : (prefixWord ++ tailWord_2265504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265504).length < 2 ^ (prefixWord ++ tailWord_2265504).sum := by decide
  have hdescent : baseEnd_2265504 < baseStart_2265504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265506 : List Nat := [3, 3, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_2265506 : Nat := 118140960795 + 2265506 * 2 ^ 59
def prefixEnd_2265506 : Nat := 4983230072969 + 3 ^ 40 * 2265506 * 2
def baseEnd_2265506 : Nat := 775529002429945620704089

theorem tailTrace_2265506 : CollatzResearch.WordTrace tailWord_2265506 prefixEnd_2265506 775529002429945620704089 := by
  unfold tailWord_2265506
  simp only [CollatzResearch.WordTrace]
  refine ⟨20657448032616538616456093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55086528086977436310549581 20657448032616538616456093)
  ·
    refine ⟨7746543012231201981171035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20657448032616538616456093 7746543012231201981171035)
    ·
      refine ⟨11619814518346802971756553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7746543012231201981171035 11619814518346802971756553)
      ·
        refine ⟨8714860888760102228817415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11619814518346802971756553 8714860888760102228817415)
        ·
          refine ⟨13072291333140153343226123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8714860888760102228817415 13072291333140153343226123)
          ·
            refine ⟨19608436999710230014839185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13072291333140153343226123 19608436999710230014839185)
            ·
              refine ⟨14706327749782672511129389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19608436999710230014839185 14706327749782672511129389)
              ·
                refine ⟨5514872906168502191673521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14706327749782672511129389 5514872906168502191673521)
                ·
                  refine ⟨4136154679626376643755141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5514872906168502191673521 4136154679626376643755141)
                  ·
                    refine ⟨775529002429945620704089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4136154679626376643755141 775529002429945620704089)
                    ·
                      rfl

theorem cell22_2265506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_2265506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265506 prefixEnd_2265506 := by exact prefixLift 2265506
  have htrace : WordTrace (prefixWord ++ tailWord_2265506) baseStart_2265506 baseEnd_2265506 := by
    simpa [prefixWord, tailWord_2265506, baseEnd_2265506] using wordTrace_append hprefix tailTrace_2265506
  have hstable : (prefixWord ++ tailWord_2265506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265506).length < 2 ^ (prefixWord ++ tailWord_2265506).sum := by decide
  have hdescent : baseEnd_2265506 < baseStart_2265506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265611 : List Nat := [1, 1, 1, 1, 7, 2, 1, 2, 6]
def baseStart_2265611 : Nat := 118140960795 + 2265611 * 2 ^ 59
def prefixEnd_2265611 : Nat := 4983230072969 + 3 ^ 40 * 2265611 * 2
def baseEnd_2265611 : Nat := 258521648691920115609589

theorem tailTrace_2265611 : CollatzResearch.WordTrace tailWord_2265611 prefixEnd_2265611 258521648691920115609589 := by
  unfold tailWord_2265611
  simp only [CollatzResearch.WordTrace]
  refine ⟨82633621795085757398396687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55089081196723838265597791 82633621795085757398396687)
  ·
    refine ⟨123950432692628636097595031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82633621795085757398396687 123950432692628636097595031)
    ·
      refine ⟨185925649038942954146392547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123950432692628636097595031 185925649038942954146392547)
      ·
        refine ⟨278888473558414431219588821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185925649038942954146392547 278888473558414431219588821)
        ·
          refine ⟨6536448599025338231709113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 278888473558414431219588821 6536448599025338231709113)
          ·
            refine ⟨4902336449269003673781835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6536448599025338231709113 4902336449269003673781835)
            ·
              refine ⟨7353504673903505510672753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4902336449269003673781835 7353504673903505510672753)
              ·
                refine ⟨5515128505427629133004565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7353504673903505510672753 5515128505427629133004565)
                ·
                  refine ⟨258521648691920115609589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5515128505427629133004565 258521648691920115609589)
                  ·
                    rfl

theorem cell22_2265611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 6].length) (baseStart_2265611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265611 prefixEnd_2265611 := by exact prefixLift 2265611
  have htrace : WordTrace (prefixWord ++ tailWord_2265611) baseStart_2265611 baseEnd_2265611 := by
    simpa [prefixWord, tailWord_2265611, baseEnd_2265611] using wordTrace_append hprefix tailTrace_2265611
  have hstable : (prefixWord ++ tailWord_2265611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265611).length < 2 ^ (prefixWord ++ tailWord_2265611).sum := by decide
  have hdescent : baseEnd_2265611 < baseStart_2265611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265626 : List Nat := [3, 1, 1, 3, 1, 1, 4, 2, 1, 5]
def baseStart_2265626 : Nat := 118140960795 + 2265626 * 2 ^ 59
def prefixEnd_2265626 : Nat := 4983230072969 + 3 ^ 40 * 2265626 * 2
def baseEnd_2265626 : Nat := 775570080882305307703721

theorem tailTrace_2265626 : CollatzResearch.WordTrace tailWord_2265626 prefixEnd_2265626 775570080882305307703721 := by
  unfold tailWord_2265626
  simp only [CollatzResearch.WordTrace]
  refine ⟨20658542222507853740048183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55089445926687609973461821 20658542222507853740048183)
  ·
    refine ⟨30987813333761780610072275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20658542222507853740048183 30987813333761780610072275)
    ·
      refine ⟨46481720000642670915108413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30987813333761780610072275 46481720000642670915108413)
      ·
        refine ⟨17430645000241001593165655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46481720000642670915108413 17430645000241001593165655)
        ·
          refine ⟨26145967500361502389748483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17430645000241001593165655 26145967500361502389748483)
          ·
            refine ⟨39218951250542253584622725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26145967500361502389748483 39218951250542253584622725)
            ·
              refine ⟨7353553359476672547116761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39218951250542253584622725 7353553359476672547116761)
              ·
                refine ⟨5515165019607504410337571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7353553359476672547116761 5515165019607504410337571)
                ·
                  refine ⟨8272747529411256615506357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5515165019607504410337571 8272747529411256615506357)
                  ·
                    refine ⟨775570080882305307703721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8272747529411256615506357 775570080882305307703721)
                    ·
                      rfl

theorem cell22_2265626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_2265626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265626 prefixEnd_2265626 := by exact prefixLift 2265626
  have htrace : WordTrace (prefixWord ++ tailWord_2265626) baseStart_2265626 baseEnd_2265626 := by
    simpa [prefixWord, tailWord_2265626, baseEnd_2265626] using wordTrace_append hprefix tailTrace_2265626
  have hstable : (prefixWord ++ tailWord_2265626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265626).length < 2 ^ (prefixWord ++ tailWord_2265626).sum := by decide
  have hdescent : baseEnd_2265626 < baseStart_2265626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265628 : List Nat := [2, 2, 3, 1, 2, 2, 1, 5, 4]
def baseStart_2265628 : Nat := 118140960795 + 2265628 * 2 ^ 59
def prefixEnd_2265628 : Nat := 4983230072969 + 3 ^ 40 * 2265628 * 2
def baseEnd_2265628 : Nat := 258523588507725989717905

theorem tailTrace_2265628 : CollatzResearch.WordTrace tailWord_2265628 prefixEnd_2265628 258523588507725989717905 := by
  unfold tailWord_2265628
  simp only [CollatzResearch.WordTrace]
  refine ⟨41317120918012084650882769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55089494557349446201177025 41317120918012084650882769)
  ·
    refine ⟨30987840688509063488162077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41317120918012084650882769 30987840688509063488162077)
    ·
      refine ⟨11620440258190898808060779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30987840688509063488162077 11620440258190898808060779)
      ·
        refine ⟨17430660387286348212091169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11620440258190898808060779 17430660387286348212091169)
        ·
          refine ⟨13072995290464761159068377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17430660387286348212091169 13072995290464761159068377)
          ·
            refine ⟨9804746467848570869301283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13072995290464761159068377 9804746467848570869301283)
            ·
              refine ⟨14707119701772856303951925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9804746467848570869301283 14707119701772856303951925)
              ·
                refine ⟨1378792472041205278495493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14707119701772856303951925 1378792472041205278495493)
                ·
                  refine ⟨258523588507725989717905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1378792472041205278495493 258523588507725989717905)
                  ·
                    rfl

theorem cell22_2265628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_2265628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265628 prefixEnd_2265628 := by exact prefixLift 2265628
  have htrace : WordTrace (prefixWord ++ tailWord_2265628) baseStart_2265628 baseEnd_2265628 := by
    simpa [prefixWord, tailWord_2265628, baseEnd_2265628] using wordTrace_append hprefix tailTrace_2265628
  have hstable : (prefixWord ++ tailWord_2265628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265628).length < 2 ^ (prefixWord ++ tailWord_2265628).sum := by decide
  have hdescent : baseEnd_2265628 < baseStart_2265628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265776 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 1, 6]
def baseStart_2265776 : Nat := 118140960795 + 2265776 * 2 ^ 59
def prefixEnd_2265776 : Nat := 4983230072969 + 3 ^ 40 * 2265776 * 2
def baseEnd_2265776 : Nat := 775621428947754916453261

theorem tailTrace_2265776 : CollatzResearch.WordTrace tailWord_2265776 prefixEnd_2265776 775621428947754916453261 := by
  unfold tailWord_2265776
  simp only [CollatzResearch.WordTrace]
  refine ⟨41319819919743995289076591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55093093226325327052102121 41319819919743995289076591)
  ·
    refine ⟨61979729879615992933614887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41319819919743995289076591 61979729879615992933614887)
    ·
      refine ⟨92969594819423989400422331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61979729879615992933614887 92969594819423989400422331)
      ·
        refine ⟨139454392229135984100633497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92969594819423989400422331 139454392229135984100633497)
        ·
          refine ⟨104590794171851988075475123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139454392229135984100633497 104590794171851988075475123)
          ·
            refine ⟨156886191257777982113212685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104590794171851988075475123 156886191257777982113212685)
            ·
              refine ⟨58832321721666743292454757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156886191257777982113212685 58832321721666743292454757)
              ·
                refine ⟨11031060322812514367335267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58832321721666743292454757 11031060322812514367335267)
                ·
                  refine ⟨16546590484218771551002901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11031060322812514367335267 16546590484218771551002901)
                  ·
                    refine ⟨775621428947754916453261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16546590484218771551002901 775621428947754916453261)
                    ·
                      rfl

theorem cell22_2265776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_2265776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265776 prefixEnd_2265776 := by exact prefixLift 2265776
  have htrace : WordTrace (prefixWord ++ tailWord_2265776) baseStart_2265776 baseEnd_2265776 := by
    simpa [prefixWord, tailWord_2265776, baseEnd_2265776] using wordTrace_append hprefix tailTrace_2265776
  have hstable : (prefixWord ++ tailWord_2265776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265776).length < 2 ^ (prefixWord ++ tailWord_2265776).sum := by decide
  have hdescent : baseEnd_2265776 < baseStart_2265776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265778 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 6, 3]
def baseStart_2265778 : Nat := 118140960795 + 2265778 * 2 ^ 59
def prefixEnd_2265778 : Nat := 4983230072969 + 3 ^ 40 * 2265778 * 2
def baseEnd_2265778 : Nat := 775622113588627577903255

theorem tailTrace_2265778 : CollatzResearch.WordTrace tailWord_2265778 prefixEnd_2265778 775622113588627577903255 := by
  unfold tailWord_2265778
  simp only [CollatzResearch.WordTrace]
  refine ⟨20659928196370186229931497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55093141856987163279817325 20659928196370186229931497)
  ·
    refine ⟨15494946147277639672448623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20659928196370186229931497 15494946147277639672448623)
    ·
      refine ⟨23242419220916459508672935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15494946147277639672448623 23242419220916459508672935)
      ·
        refine ⟨34863628831374689263009403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23242419220916459508672935 34863628831374689263009403)
        ·
          refine ⟨52295443247062033894514105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34863628831374689263009403 52295443247062033894514105)
          ·
            refine ⟨39221582435296525420885579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52295443247062033894514105 39221582435296525420885579)
            ·
              refine ⟨58832373652944788131328369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39221582435296525420885579 58832373652944788131328369)
              ·
                refine ⟨44124280239708591098496277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58832373652944788131328369 44124280239708591098496277)
                ·
                  refine ⟨2068325636236340207742013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44124280239708591098496277 2068325636236340207742013)
                  ·
                    refine ⟨775622113588627577903255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2068325636236340207742013 775622113588627577903255)
                    ·
                      rfl

theorem cell22_2265778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_2265778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265778 prefixEnd_2265778 := by exact prefixLift 2265778
  have htrace : WordTrace (prefixWord ++ tailWord_2265778) baseStart_2265778 baseEnd_2265778 := by
    simpa [prefixWord, tailWord_2265778, baseEnd_2265778] using wordTrace_append hprefix tailTrace_2265778
  have hstable : (prefixWord ++ tailWord_2265778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265778).length < 2 ^ (prefixWord ++ tailWord_2265778).sum := by decide
  have hdescent : baseEnd_2265778 < baseStart_2265778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265812 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_2265812 : Nat := 118140960795 + 2265812 * 2 ^ 59
def prefixEnd_2265812 : Nat := 4983230072969 + 3 ^ 40 * 2265812 * 2
def baseEnd_2265812 : Nat := 775633752483462822553151

theorem tailTrace_2265812 : CollatzResearch.WordTrace tailWord_2265812 prefixEnd_2265812 775633752483462822553151 := by
  unfold tailWord_2265812
  simp only [CollatzResearch.WordTrace]
  refine ⟨41320476433678784363231845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55093968578238379150975793 41320476433678784363231845)
  ·
    refine ⟨7747589331314772068105971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41320476433678784363231845 7747589331314772068105971)
    ·
      refine ⟨11621383996972158102158957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7747589331314772068105971 11621383996972158102158957)
      ·
        refine ⟨4358018998864559288309609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11621383996972158102158957 4358018998864559288309609)
        ·
          refine ⟨3268514249148419466232207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4358018998864559288309609 3268514249148419466232207)
          ·
            refine ⟨4902771373722629199348311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3268514249148419466232207 4902771373722629199348311)
            ·
              refine ⟨7354157060583943799022467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4902771373722629199348311 7354157060583943799022467)
              ·
                refine ⟨11031235590875915698533701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7354157060583943799022467 11031235590875915698533701)
                ·
                  refine ⟨2068356673289234193475069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11031235590875915698533701 2068356673289234193475069)
                  ·
                    refine ⟨775633752483462822553151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2068356673289234193475069 775633752483462822553151)
                    ·
                      rfl

theorem cell22_2265812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_2265812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265812 prefixEnd_2265812 := by exact prefixLift 2265812
  have htrace : WordTrace (prefixWord ++ tailWord_2265812) baseStart_2265812 baseEnd_2265812 := by
    simpa [prefixWord, tailWord_2265812, baseEnd_2265812] using wordTrace_append hprefix tailTrace_2265812
  have hstable : (prefixWord ++ tailWord_2265812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265812).length < 2 ^ (prefixWord ++ tailWord_2265812).sum := by decide
  have hdescent : baseEnd_2265812 < baseStart_2265812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265887 : List Nat := [1, 1, 2, 4, 2, 4, 2, 1, 5]
def baseStart_2265887 : Nat := 118140960795 + 2265887 * 2 ^ 59
def prefixEnd_2265887 : Nat := 4983230072969 + 3 ^ 40 * 2265887 * 2
def baseEnd_2265887 : Nat := 258553142172062542309307

theorem tailTrace_2265887 : CollatzResearch.WordTrace tailWord_2265887 prefixEnd_2265887 258553142172062542309307 := by
  unfold tailWord_2265887
  simp only [CollatzResearch.WordTrace]
  refine ⟨82643688342085856535443915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55095792228057237690295943 82643688342085856535443915)
  ·
    refine ⟨123965532513128784803165873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82643688342085856535443915 123965532513128784803165873)
    ·
      refine ⟨92974149384846588602374405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123965532513128784803165873 92974149384846588602374405)
      ·
        refine ⟨17432653009658735362945201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92974149384846588602374405 17432653009658735362945201)
        ·
          refine ⟨13074489757244051522208901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17432653009658735362945201 13074489757244051522208901)
          ·
            refine ⟨2451466829483259660414169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13074489757244051522208901 2451466829483259660414169)
            ·
              refine ⟨1838600122112444745310627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2451466829483259660414169 1838600122112444745310627)
              ·
                refine ⟨2757900183168667117965941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1838600122112444745310627 2757900183168667117965941)
                ·
                  refine ⟨258553142172062542309307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2757900183168667117965941 258553142172062542309307)
                  ·
                    rfl

theorem cell22_2265887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 5].length) (baseStart_2265887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265887 prefixEnd_2265887 := by exact prefixLift 2265887
  have htrace : WordTrace (prefixWord ++ tailWord_2265887) baseStart_2265887 baseEnd_2265887 := by
    simpa [prefixWord, tailWord_2265887, baseEnd_2265887] using wordTrace_append hprefix tailTrace_2265887
  have hstable : (prefixWord ++ tailWord_2265887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265887).length < 2 ^ (prefixWord ++ tailWord_2265887).sum := by decide
  have hdescent : baseEnd_2265887 < baseStart_2265887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265932 : List Nat := [2, 2, 1, 3, 3, 2, 1, 4, 4]
def baseStart_2265932 : Nat := 118140960795 + 2265932 * 2 ^ 59
def prefixEnd_2265932 : Nat := 4983230072969 + 3 ^ 40 * 2265932 * 2
def baseEnd_2265932 : Nat := 258558276978607503184261

theorem tailTrace_2265932 : CollatzResearch.WordTrace tailWord_2265932 prefixEnd_2265932 258558276978607503184261 := by
  unfold tailWord_2265932
  simp only [CollatzResearch.WordTrace]
  refine ⟨41322664813461414610416025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55096886417948552813888033 41322664813461414610416025)
  ·
    refine ⟨30991998610096060957812019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41322664813461414610416025 30991998610096060957812019)
    ·
      refine ⟨46487997915144091436718029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30991998610096060957812019 46487997915144091436718029)
      ·
        refine ⟨17432999218179034288769261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46487997915144091436718029 17432999218179034288769261)
        ·
          refine ⟨6537374706817137858288473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17432999218179034288769261 6537374706817137858288473)
          ·
            refine ⟨4903031030112853393716355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6537374706817137858288473 4903031030112853393716355)
            ·
              refine ⟨7354546545169280090574533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4903031030112853393716355 7354546545169280090574533)
              ·
                refine ⟨1378977477219240016982725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7354546545169280090574533 1378977477219240016982725)
                ·
                  refine ⟨258558276978607503184261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1378977477219240016982725 258558276978607503184261)
                  ·
                    rfl

theorem cell22_2265932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_2265932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265932 prefixEnd_2265932 := by exact prefixLift 2265932
  have htrace : WordTrace (prefixWord ++ tailWord_2265932) baseStart_2265932 baseEnd_2265932 := by
    simpa [prefixWord, tailWord_2265932, baseEnd_2265932] using wordTrace_append hprefix tailTrace_2265932
  have hstable : (prefixWord ++ tailWord_2265932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265932).length < 2 ^ (prefixWord ++ tailWord_2265932).sum := by decide
  have hdescent : baseEnd_2265932 < baseStart_2265932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265992 : List Nat := [2, 1, 3, 3, 2, 1, 1, 3, 3, 3]
def baseStart_2265992 : Nat := 118140960795 + 2265992 * 2 ^ 59
def prefixEnd_2265992 : Nat := 4983230072969 + 3 ^ 40 * 2265992 * 2
def baseEnd_2265992 : Nat := 775695370162002353052599

theorem tailTrace_2265992 : CollatzResearch.WordTrace tailWord_2265992 prefixEnd_2265992 775695370162002353052599 := by
  unfold tailWord_2265992
  simp only [CollatzResearch.WordTrace]
  refine ⟨41323759003352729734008115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55098345337803639645344153 41323759003352729734008115)
  ·
    refine ⟨61985638505029094601012173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41323759003352729734008115 61985638505029094601012173)
    ·
      refine ⟨23244614439385910475379565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61985638505029094601012173 23244614439385910475379565)
      ·
        refine ⟨8716730414769716428267337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23244614439385910475379565 8716730414769716428267337)
        ·
          refine ⟨6537547811077287321200503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8716730414769716428267337 6537547811077287321200503)
          ·
            refine ⟨9806321716615930981800755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6537547811077287321200503 9806321716615930981800755)
            ·
              refine ⟨14709482574923896472701133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9806321716615930981800755 14709482574923896472701133)
              ·
                refine ⟨5516055965596461177262925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14709482574923896472701133 5516055965596461177262925)
                ·
                  refine ⟨2068520987098672941473597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5516055965596461177262925 2068520987098672941473597)
                  ·
                    refine ⟨775695370162002353052599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2068520987098672941473597 775695370162002353052599)
                    ·
                      rfl

theorem cell22_2265992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_2265992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265992 prefixEnd_2265992 := by exact prefixLift 2265992
  have htrace : WordTrace (prefixWord ++ tailWord_2265992) baseStart_2265992 baseEnd_2265992 := by
    simpa [prefixWord, tailWord_2265992, baseEnd_2265992] using wordTrace_append hprefix tailTrace_2265992
  have hstable : (prefixWord ++ tailWord_2265992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265992).length < 2 ^ (prefixWord ++ tailWord_2265992).sum := by decide
  have hdescent : baseEnd_2265992 < baseStart_2265992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266003 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 1, 7]
def baseStart_2266003 : Nat := 118140960795 + 2266003 * 2 ^ 59
def prefixEnd_2266003 : Nat := 4983230072969 + 3 ^ 40 * 2266003 * 2
def baseEnd_2266003 : Nat := 775699135686801991027565

theorem tailTrace_2266003 : CollatzResearch.WordTrace tailWord_2266003 prefixEnd_2266003 775699135686801991027565 := by
  unfold tailWord_2266003
  simp only [CollatzResearch.WordTrace]
  refine ⟨82647919209665608346666663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55098612806443738897777775 82647919209665608346666663)
  ·
    refine ⟨123971878814498412519999995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82647919209665608346666663 123971878814498412519999995)
    ·
      refine ⟨185957818221747618779999993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123971878814498412519999995 185957818221747618779999993)
      ·
        refine ⟨139468363666310714084999995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185957818221747618779999993 139468363666310714084999995)
        ·
          refine ⟨209202545499466071127499993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139468363666310714084999995 209202545499466071127499993)
          ·
            refine ⟨156901909124599553345624995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209202545499466071127499993 156901909124599553345624995)
            ·
              refine ⟨235352863686899330018437493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156901909124599553345624995 235352863686899330018437493)
              ·
                refine ⟨22064330970646812189228515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 235352863686899330018437493 22064330970646812189228515)
                ·
                  refine ⟨33096496455970218283842773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22064330970646812189228515 33096496455970218283842773)
                  ·
                    refine ⟨775699135686801991027565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33096496455970218283842773 775699135686801991027565)
                    ·
                      rfl

theorem cell22_2266003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 7].length) (baseStart_2266003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266003 prefixEnd_2266003 := by exact prefixLift 2266003
  have htrace : WordTrace (prefixWord ++ tailWord_2266003) baseStart_2266003 baseEnd_2266003 := by
    simpa [prefixWord, tailWord_2266003, baseEnd_2266003] using wordTrace_append hprefix tailTrace_2266003
  have hstable : (prefixWord ++ tailWord_2266003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266003).length < 2 ^ (prefixWord ++ tailWord_2266003).sum := by decide
  have hdescent : baseEnd_2266003 < baseStart_2266003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266056 : List Nat := [2, 1, 3, 1, 6, 1, 2, 1, 5]
def baseStart_2266056 : Nat := 118140960795 + 2266056 * 2 ^ 59
def prefixEnd_2266056 : Nat := 4983230072969 + 3 ^ 40 * 2266056 * 2
def baseEnd_2266056 : Nat := 258572426223309173150801

theorem tailTrace_2266056 : CollatzResearch.WordTrace tailWord_2266056 prefixEnd_2266056 258572426223309173150801 := by
  unfold tailWord_2266056
  simp only [CollatzResearch.WordTrace]
  refine ⟨41324926139236799199173011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55099901518982398932230681 41324926139236799199173011)
  ·
    refine ⟨61987389208855198798759517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41324926139236799199173011 61987389208855198798759517)
    ·
      refine ⟨23245270953320699549534819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61987389208855198798759517 23245270953320699549534819)
      ·
        refine ⟨34867906429981049324302229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23245270953320699549534819 34867906429981049324302229)
        ·
          refine ⟨1634433113905361687076667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34867906429981049324302229 1634433113905361687076667)
          ·
            refine ⟨2451649670858042530615001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1634433113905361687076667 2451649670858042530615001)
            ·
              refine ⟨1838737253143531897961251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2451649670858042530615001 1838737253143531897961251)
              ·
                refine ⟨2758105879715297846941877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1838737253143531897961251 2758105879715297846941877)
                ·
                  refine ⟨258572426223309173150801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2758105879715297846941877 258572426223309173150801)
                  ·
                    rfl

theorem cell22_2266056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 5].length) (baseStart_2266056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266056 prefixEnd_2266056 := by exact prefixLift 2266056
  have htrace : WordTrace (prefixWord ++ tailWord_2266056) baseStart_2266056 baseEnd_2266056 := by
    simpa [prefixWord, tailWord_2266056, baseEnd_2266056] using wordTrace_append hprefix tailTrace_2266056
  have hstable : (prefixWord ++ tailWord_2266056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266056).length < 2 ^ (prefixWord ++ tailWord_2266056).sum := by decide
  have hdescent : baseEnd_2266056 < baseStart_2266056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266065 : List Nat := [1, 2, 2, 1, 2, 1, 4, 3, 1, 5]
def baseStart_2266065 : Nat := 118140960795 + 2266065 * 2 ^ 59
def prefixEnd_2266065 : Nat := 4983230072969 + 3 ^ 40 * 2266065 * 2
def baseEnd_2266065 : Nat := 775720359553854495977375

theorem tailTrace_2266065 : CollatzResearch.WordTrace tailWord_2266065 prefixEnd_2266065 775720359553854495977375 := by
  unfold tailWord_2266065
  simp only [CollatzResearch.WordTrace]
  refine ⟨82650180535440992935423649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55100120356960661956949099 82650180535440992935423649)
  ·
    refine ⟨61987635401580744701567737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82650180535440992935423649 61987635401580744701567737)
    ·
      refine ⟨46490726551185558526175803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61987635401580744701567737 46490726551185558526175803)
      ·
        refine ⟨69736089826778337789263705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46490726551185558526175803 69736089826778337789263705)
        ·
          refine ⟨52302067370083753341947779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69736089826778337789263705 52302067370083753341947779)
          ·
            refine ⟨78453101055125630012921669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52302067370083753341947779 78453101055125630012921669)
            ·
              refine ⟨14709956447836055627422813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78453101055125630012921669 14709956447836055627422813)
              ·
                refine ⟨5516233667938520860283555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14709956447836055627422813 5516233667938520860283555)
                ·
                  refine ⟨8274350501907781290425333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5516233667938520860283555 8274350501907781290425333)
                  ·
                    refine ⟨775720359553854495977375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8274350501907781290425333 775720359553854495977375)
                    ·
                      rfl

theorem cell22_2266065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_2266065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266065 prefixEnd_2266065 := by exact prefixLift 2266065
  have htrace : WordTrace (prefixWord ++ tailWord_2266065) baseStart_2266065 baseEnd_2266065 := by
    simpa [prefixWord, tailWord_2266065, baseEnd_2266065] using wordTrace_append hprefix tailTrace_2266065
  have hstable : (prefixWord ++ tailWord_2266065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266065).length < 2 ^ (prefixWord ++ tailWord_2266065).sum := by decide
  have hdescent : baseEnd_2266065 < baseStart_2266065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266097 : List Nat := [1, 2, 2, 2, 4, 1, 2, 2, 2, 4]
def baseStart_2266097 : Nat := 118140960795 + 2266097 * 2 ^ 59
def prefixEnd_2266097 : Nat := 4983230072969 + 3 ^ 40 * 2266097 * 2
def baseEnd_2266097 : Nat := 775731313807817079177277

theorem tailTrace_2266097 : CollatzResearch.WordTrace tailWord_2266097 prefixEnd_2266097 775731313807817079177277 := by
  unfold tailWord_2266097
  simp only [CollatzResearch.WordTrace]
  refine ⟨82651347671325062400588545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55100898447550041600392363 82651347671325062400588545)
  ·
    refine ⟨61988510753493796800441409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82651347671325062400588545 61988510753493796800441409)
    ·
      refine ⟨46491383065120347600331057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61988510753493796800441409 46491383065120347600331057)
      ·
        refine ⟨34868537298840260700248293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46491383065120347600331057 34868537298840260700248293)
        ·
          refine ⟨6537850743532548881296555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34868537298840260700248293 6537850743532548881296555)
          ·
            refine ⟨9806776115298823321944833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6537850743532548881296555 9806776115298823321944833)
            ·
              refine ⟨7355082086474117491458625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9806776115298823321944833 7355082086474117491458625)
              ·
                refine ⟨5516311564855588118593969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7355082086474117491458625 5516311564855588118593969)
                ·
                  refine ⟨4137233673641691088945477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5516311564855588118593969 4137233673641691088945477)
                  ·
                    refine ⟨775731313807817079177277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4137233673641691088945477 775731313807817079177277)
                    ·
                      rfl

theorem cell22_2266097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_2266097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266097 prefixEnd_2266097 := by exact prefixLift 2266097
  have htrace : WordTrace (prefixWord ++ tailWord_2266097) baseStart_2266097 baseEnd_2266097 := by
    simpa [prefixWord, tailWord_2266097, baseEnd_2266097] using wordTrace_append hprefix tailTrace_2266097
  have hstable : (prefixWord ++ tailWord_2266097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266097).length < 2 ^ (prefixWord ++ tailWord_2266097).sum := by decide
  have hdescent : baseEnd_2266097 < baseStart_2266097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266155 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 4, 5]
def baseStart_2266155 : Nat := 118140960795 + 2266155 * 2 ^ 59
def prefixEnd_2266155 : Nat := 4983230072969 + 3 ^ 40 * 2266155 * 2
def baseEnd_2266155 : Nat := 775751168393124261227099

theorem tailTrace_2266155 : CollatzResearch.WordTrace tailWord_2266155 prefixEnd_2266155 775751168393124261227099 := by
  unfold tailWord_2266155
  simp only [CollatzResearch.WordTrace]
  refine ⟨82653463105114938306199919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55102308736743292204133279 82653463105114938306199919)
  ·
    refine ⟨123980194657672407459299879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82653463105114938306199919 123980194657672407459299879)
    ·
      refine ⟨185970291986508611188949819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123980194657672407459299879 185970291986508611188949819)
      ·
        refine ⟨278955437979762916783424729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185970291986508611188949819 278955437979762916783424729)
        ·
          refine ⟨209216578484822187587568547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278955437979762916783424729 209216578484822187587568547)
          ·
            refine ⟨313824867727233281381352821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209216578484822187587568547 313824867727233281381352821)
            ·
              refine ⟨29421081349428120129501827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 313824867727233281381352821 29421081349428120129501827)
              ·
                refine ⟨44131622024142180194252741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29421081349428120129501827 44131622024142180194252741)
                ·
                  refine ⟨8274679129526658786422389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44131622024142180194252741 8274679129526658786422389)
                  ·
                    refine ⟨775751168393124261227099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8274679129526658786422389 775751168393124261227099)
                    ·
                      rfl

theorem cell22_2266155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 5].length) (baseStart_2266155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266155 prefixEnd_2266155 := by exact prefixLift 2266155
  have htrace : WordTrace (prefixWord ++ tailWord_2266155) baseStart_2266155 baseEnd_2266155 := by
    simpa [prefixWord, tailWord_2266155, baseEnd_2266155] using wordTrace_append hprefix tailTrace_2266155
  have hstable : (prefixWord ++ tailWord_2266155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266155).length < 2 ^ (prefixWord ++ tailWord_2266155).sum := by decide
  have hdescent : baseEnd_2266155 < baseStart_2266155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266172 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 2, 5]
def baseStart_2266172 : Nat := 118140960795 + 2266172 * 2 ^ 59
def prefixEnd_2266172 : Nat := 4983230072969 + 3 ^ 40 * 2266172 * 2
def baseEnd_2266172 : Nat := 775756987840541883552047

theorem tailTrace_2266172 : CollatzResearch.WordTrace tailWord_2266172 prefixEnd_2266172 775756987840541883552047 := by
  unfold tailWord_2266172
  simp only [CollatzResearch.WordTrace]
  refine ⟨41327041573026675104784385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55102722097368900139712513 41327041573026675104784385)
  ·
    refine ⟨30995281179770006328588289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41327041573026675104784385 30995281179770006328588289)
    ·
      refine ⟨23246460884827504746441217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30995281179770006328588289 23246460884827504746441217)
      ·
        refine ⟨17434845663620628559830913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23246460884827504746441217 17434845663620628559830913)
        ·
          refine ⟨13076134247715471419873185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17434845663620628559830913 13076134247715471419873185)
          ·
            refine ⟨9807100685786603564904889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13076134247715471419873185 9807100685786603564904889)
            ·
              refine ⟨7355325514339952673678667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9807100685786603564904889 7355325514339952673678667)
              ·
                refine ⟨11032988271509929010518001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7355325514339952673678667 11032988271509929010518001)
                ·
                  refine ⟨8274741203632446757888501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11032988271509929010518001 8274741203632446757888501)
                  ·
                    refine ⟨775756987840541883552047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8274741203632446757888501 775756987840541883552047)
                    ·
                      rfl

theorem cell22_2266172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_2266172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266172 prefixEnd_2266172 := by exact prefixLift 2266172
  have htrace : WordTrace (prefixWord ++ tailWord_2266172) baseStart_2266172 baseEnd_2266172 := by
    simpa [prefixWord, tailWord_2266172, baseEnd_2266172] using wordTrace_append hprefix tailTrace_2266172
  have hstable : (prefixWord ++ tailWord_2266172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266172).length < 2 ^ (prefixWord ++ tailWord_2266172).sum := by decide
  have hdescent : baseEnd_2266172 < baseStart_2266172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266185 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 8]
def baseStart_2266185 : Nat := 118140960795 + 2266185 * 2 ^ 59
def prefixEnd_2266185 : Nat := 4983230072969 + 3 ^ 40 * 2266185 * 2
def baseEnd_2266185 : Nat := 258587146002071394325669

theorem tailTrace_2266185 : CollatzResearch.WordTrace tailWord_2266185 prefixEnd_2266185 258587146002071394325669 := by
  unfold tailWord_2266185
  simp only [CollatzResearch.WordTrace]
  refine ⟨82654557295006253429792009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55103038196670835619861339 82654557295006253429792009)
  ·
    refine ⟨61990917971254690072344007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82654557295006253429792009 61990917971254690072344007)
    ·
      refine ⟨92986376956882035108516011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61990917971254690072344007 92986376956882035108516011)
      ·
        refine ⟨139479565435323052662774017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92986376956882035108516011 139479565435323052662774017)
        ·
          refine ⟨104609674076492289497080513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139479565435323052662774017 104609674076492289497080513)
          ·
            refine ⟨78457255557369217122810385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104609674076492289497080513 78457255557369217122810385)
            ·
              refine ⟨58842941668026912842107789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78457255557369217122810385 58842941668026912842107789)
              ·
                refine ⟨22066103125510092315790421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58842941668026912842107789 22066103125510092315790421)
                ·
                  refine ⟨258587146002071394325669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22066103125510092315790421 258587146002071394325669)
                  ·
                    rfl

theorem cell22_2266185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 8].length) (baseStart_2266185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266185 prefixEnd_2266185 := by exact prefixLift 2266185
  have htrace : WordTrace (prefixWord ++ tailWord_2266185) baseStart_2266185 baseEnd_2266185 := by
    simpa [prefixWord, tailWord_2266185, baseEnd_2266185] using wordTrace_append hprefix tailTrace_2266185
  have hstable : (prefixWord ++ tailWord_2266185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266185).length < 2 ^ (prefixWord ++ tailWord_2266185).sum := by decide
  have hdescent : baseEnd_2266185 < baseStart_2266185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266204 : List Nat := [2, 2, 4, 1, 1, 1, 1, 5, 1, 4]
def baseStart_2266204 : Nat := 118140960795 + 2266204 * 2 ^ 59
def prefixEnd_2266204 : Nat := 4983230072969 + 3 ^ 40 * 2266204 * 2
def baseEnd_2266204 : Nat := 775767942094504466751949

theorem tailTrace_2266204 : CollatzResearch.WordTrace tailWord_2266204 prefixEnd_2266204 775767942094504466751949 := by
  unfold tailWord_2266204
  simp only [CollatzResearch.WordTrace]
  refine ⟨41327625140968709837366833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55103500187958279783155777 41327625140968709837366833)
  ·
    refine ⟨30995718855726532378025125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41327625140968709837366833 30995718855726532378025125)
    ·
      refine ⟨5811697285448724820879711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30995718855726532378025125 5811697285448724820879711)
      ·
        refine ⟨8717545928173087231319567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5811697285448724820879711 8717545928173087231319567)
        ·
          refine ⟨13076318892259630846979351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8717545928173087231319567 13076318892259630846979351)
          ·
            refine ⟨19614478338389446270469027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13076318892259630846979351 19614478338389446270469027)
            ·
              refine ⟨29421717507584169405703541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19614478338389446270469027 29421717507584169405703541)
              ·
                refine ⟨2758286016336015881784707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29421717507584169405703541 2758286016336015881784707)
                ·
                  refine ⟨4137429024504023822677061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2758286016336015881784707 4137429024504023822677061)
                  ·
                    refine ⟨775767942094504466751949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4137429024504023822677061 775767942094504466751949)
                    ·
                      rfl

theorem cell22_2266204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_2266204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266204 prefixEnd_2266204 := by exact prefixLift 2266204
  have htrace : WordTrace (prefixWord ++ tailWord_2266204) baseStart_2266204 baseEnd_2266204 := by
    simpa [prefixWord, tailWord_2266204, baseEnd_2266204] using wordTrace_append hprefix tailTrace_2266204
  have hstable : (prefixWord ++ tailWord_2266204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266204).length < 2 ^ (prefixWord ++ tailWord_2266204).sum := by decide
  have hdescent : baseEnd_2266204 < baseStart_2266204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266249 : List Nat := [1, 2, 1, 1, 4, 4, 2, 1, 2, 4]
def baseStart_2266249 : Nat := 118140960795 + 2266249 * 2 ^ 59
def prefixEnd_2266249 : Nat := 4983230072969 + 3 ^ 40 * 2266249 * 2
def baseEnd_2266249 : Nat := 775783346514139349376811

theorem tailTrace_2266249 : CollatzResearch.WordTrace tailWord_2266249 prefixEnd_2266249 775783346514139349376811 := by
  unfold tailWord_2266249
  simp only [CollatzResearch.WordTrace]
  refine ⟨82656891566774392360121801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55104594377849594906747867 82656891566774392360121801)
  ·
    refine ⟨61992668675080794270091351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82656891566774392360121801 61992668675080794270091351)
    ·
      refine ⟨92989003012621191405137027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61992668675080794270091351 92989003012621191405137027)
      ·
        refine ⟨139483504518931787107705541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92989003012621191405137027 139483504518931787107705541)
        ·
          refine ⟨26153157097299710082694789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139483504518931787107705541 26153157097299710082694789)
          ·
            refine ⟨4903716955743695640505273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26153157097299710082694789 4903716955743695640505273)
            ·
              refine ⟨3677787716807771730378955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4903716955743695640505273 3677787716807771730378955)
              ·
                refine ⟨5516681575211657595568433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3677787716807771730378955 5516681575211657595568433)
                ·
                  refine ⟨4137511181408743196676325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5516681575211657595568433 4137511181408743196676325)
                  ·
                    refine ⟨775783346514139349376811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4137511181408743196676325 775783346514139349376811)
                    ·
                      rfl

theorem cell22_2266249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 4].length) (baseStart_2266249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266249 prefixEnd_2266249 := by exact prefixLift 2266249
  have htrace : WordTrace (prefixWord ++ tailWord_2266249) baseStart_2266249 baseEnd_2266249 := by
    simpa [prefixWord, tailWord_2266249, baseEnd_2266249] using wordTrace_append hprefix tailTrace_2266249
  have hstable : (prefixWord ++ tailWord_2266249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266249).length < 2 ^ (prefixWord ++ tailWord_2266249).sum := by decide
  have hdescent : baseEnd_2266249 < baseStart_2266249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266270 : List Nat := [4, 3, 1, 1, 2, 3, 2, 2, 4]
def baseStart_2266270 : Nat := 118140960795 + 2266270 * 2 ^ 59
def prefixEnd_2266270 : Nat := 4983230072969 + 3 ^ 40 * 2266270 * 2
def baseEnd_2266270 : Nat := 258596845081100764867249

theorem tailTrace_2266270 : CollatzResearch.WordTrace tailWord_2266270 prefixEnd_2266270 258596845081100764867249 := by
  unfold tailWord_2266270
  simp only [CollatzResearch.WordTrace]
  refine ⟨10332207187462289118329533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55105104999798875297757509 10332207187462289118329533)
  ·
    refine ⟨3874577695298358419373575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10332207187462289118329533 3874577695298358419373575)
    ·
      refine ⟨5811866542947537629060363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3874577695298358419373575 5811866542947537629060363)
      ·
        refine ⟨8717799814421306443590545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5811866542947537629060363 8717799814421306443590545)
        ·
          refine ⟨6538349860815979832692909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8717799814421306443590545 6538349860815979832692909)
          ·
            refine ⟨2451881197805992437259841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6538349860815979832692909 2451881197805992437259841)
            ·
              refine ⟨1838910898354494327944881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2451881197805992437259841 1838910898354494327944881)
              ·
                refine ⟨1379183173765870745958661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1838910898354494327944881 1379183173765870745958661)
                ·
                  refine ⟨258596845081100764867249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1379183173765870745958661 258596845081100764867249)
                  ·
                    rfl

theorem cell22_2266270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_2266270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266270 prefixEnd_2266270 := by exact prefixLift 2266270
  have htrace : WordTrace (prefixWord ++ tailWord_2266270) baseStart_2266270 baseEnd_2266270 := by
    simpa [prefixWord, tailWord_2266270, baseEnd_2266270] using wordTrace_append hprefix tailTrace_2266270
  have hstable : (prefixWord ++ tailWord_2266270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266270).length < 2 ^ (prefixWord ++ tailWord_2266270).sum := by decide
  have hdescent : baseEnd_2266270 < baseStart_2266270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266277 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 2, 6]
def baseStart_2266277 : Nat := 118140960795 + 2266277 * 2 ^ 59
def prefixEnd_2266277 : Nat := 4983230072969 + 3 ^ 40 * 2266277 * 2
def baseEnd_2266277 : Nat := 775792931486356609676725

theorem tailTrace_2266277 : CollatzResearch.WordTrace tailWord_2266277 prefixEnd_2266277 775792931486356609676725 := by
  unfold tailWord_2266277
  simp only [CollatzResearch.WordTrace]
  refine ⟨82657912810672953142141085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55105275207115302094760723 82657912810672953142141085)
  ·
    refine ⟨30996717304002357428302907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82657912810672953142141085 30996717304002357428302907)
    ·
      refine ⟨46495075956003536142454361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30996717304002357428302907 46495075956003536142454361)
      ·
        refine ⟨34871306967002652106840771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46495075956003536142454361 34871306967002652106840771)
        ·
          refine ⟨52306960450503978160261157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34871306967002652106840771 52306960450503978160261157)
          ·
            refine ⟨9807555084469495905048967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52306960450503978160261157 9807555084469495905048967)
            ·
              refine ⟨14711332626704243857573451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9807555084469495905048967 14711332626704243857573451)
              ·
                refine ⟨22066998940056365786360177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14711332626704243857573451 22066998940056365786360177)
                ·
                  refine ⟨16550249205042274339770133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22066998940056365786360177 16550249205042274339770133)
                  ·
                    refine ⟨775792931486356609676725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16550249205042274339770133 775792931486356609676725)
                    ·
                      rfl

theorem cell22_2266277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_2266277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266277 prefixEnd_2266277 := by exact prefixLift 2266277
  have htrace : WordTrace (prefixWord ++ tailWord_2266277) baseStart_2266277 baseEnd_2266277 := by
    simpa [prefixWord, tailWord_2266277, baseEnd_2266277] using wordTrace_append hprefix tailTrace_2266277
  have hstable : (prefixWord ++ tailWord_2266277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266277).length < 2 ^ (prefixWord ++ tailWord_2266277).sum := by decide
  have hdescent : baseEnd_2266277 < baseStart_2266277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266343 : List Nat := [1, 1, 5, 3, 2, 1, 3, 1, 5]
def baseStart_2266343 : Nat := 118140960795 + 2266343 * 2 ^ 59
def prefixEnd_2266343 : Nat := 4983230072969 + 3 ^ 40 * 2266343 * 2
def baseEnd_2266343 : Nat := 258605174878384812508841

theorem tailTrace_2266343 : CollatzResearch.WordTrace tailWord_2266343 prefixEnd_2266343 258605174878384812508841 := by
  unfold tailWord_2266343
  simp only [CollatzResearch.WordTrace]
  refine ⟨82660320028433846414043683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55106880018955897609362455 82660320028433846414043683)
  ·
    refine ⟨123990480042650769621065525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82660320028433846414043683 123990480042650769621065525)
    ·
      refine ⟨11624107503998509651974893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123990480042650769621065525 11624107503998509651974893)
      ·
        refine ⟨4359040313999441119490585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11624107503998509651974893 4359040313999441119490585)
        ·
          refine ⟨3269280235499580839617939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4359040313999441119490585 3269280235499580839617939)
          ·
            refine ⟨4903920353249371259426909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3269280235499580839617939 4903920353249371259426909)
            ·
              refine ⟨1838970132468514222285091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4903920353249371259426909 1838970132468514222285091)
              ·
                refine ⟨2758455198702771333427637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1838970132468514222285091 2758455198702771333427637)
                ·
                  refine ⟨258605174878384812508841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2758455198702771333427637 258605174878384812508841)
                  ·
                    rfl

theorem cell22_2266343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 5].length) (baseStart_2266343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266343 prefixEnd_2266343 := by exact prefixLift 2266343
  have htrace : WordTrace (prefixWord ++ tailWord_2266343) baseStart_2266343 baseEnd_2266343 := by
    simpa [prefixWord, tailWord_2266343, baseEnd_2266343] using wordTrace_append hprefix tailTrace_2266343
  have hstable : (prefixWord ++ tailWord_2266343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266343).length < 2 ^ (prefixWord ++ tailWord_2266343).sum := by decide
  have hdescent : baseEnd_2266343 < baseStart_2266343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266371 : List Nat := [1, 1, 1, 3, 2, 4, 3, 3, 4]
def baseStart_2266371 : Nat := 118140960795 + 2266371 * 2 ^ 59
def prefixEnd_2266371 : Nat := 4983230072969 + 3 ^ 40 * 2266371 * 2
def baseEnd_2266371 : Nat := 258608369869123899275479

theorem tailTrace_2266371 : CollatzResearch.WordTrace tailWord_2266371 prefixEnd_2266371 258608369869123899275479 := by
  unfold tailWord_2266371
  simp only [CollatzResearch.WordTrace]
  refine ⟨82661341272332407196062967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55107560848221604797375311 82661341272332407196062967)
  ·
    refine ⟨123992011908498610794094451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82661341272332407196062967 123992011908498610794094451)
    ·
      refine ⟨185988017862747916191141677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123992011908498610794094451 185988017862747916191141677)
      ·
        refine ⟨69745506698530468571678129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185988017862747916191141677 69745506698530468571678129)
        ·
          refine ⟨52309130023897851428758597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69745506698530468571678129 52309130023897851428758597)
          ·
            refine ⟨9807961879480847142892237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52309130023897851428758597 9807961879480847142892237)
            ·
              refine ⟨3677985704805317678584589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9807961879480847142892237 3677985704805317678584589)
              ·
                refine ⟨1379244639301994129469221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3677985704805317678584589 1379244639301994129469221)
                ·
                  refine ⟨258608369869123899275479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1379244639301994129469221 258608369869123899275479)
                  ·
                    rfl

theorem cell22_2266371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 4].length) (baseStart_2266371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266371 prefixEnd_2266371 := by exact prefixLift 2266371
  have htrace : WordTrace (prefixWord ++ tailWord_2266371) baseStart_2266371 baseEnd_2266371 := by
    simpa [prefixWord, tailWord_2266371, baseEnd_2266371] using wordTrace_append hprefix tailTrace_2266371
  have hstable : (prefixWord ++ tailWord_2266371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266371).length < 2 ^ (prefixWord ++ tailWord_2266371).sum := by decide
  have hdescent : baseEnd_2266371 < baseStart_2266371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266403 : List Nat := [1, 1, 1, 4, 2, 3, 4, 1, 2, 3]
def baseStart_2266403 : Nat := 118140960795 + 2266403 * 2 ^ 59
def prefixEnd_2266403 : Nat := 4983230072969 + 3 ^ 40 * 2266403 * 2
def baseEnd_2266403 : Nat := 775836063861334281026339

theorem tailTrace_2266403 : CollatzResearch.WordTrace tailWord_2266403 prefixEnd_2266403 775836063861334281026339 := by
  unfold tailWord_2266403
  simp only [CollatzResearch.WordTrace]
  refine ⟨82662508408216476661227863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55108338938810984440818575 82662508408216476661227863)
  ·
    refine ⟨123993762612324714991841795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82662508408216476661227863 123993762612324714991841795)
    ·
      refine ⟨185990643918487072487762693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123993762612324714991841795 185990643918487072487762693)
      ·
        refine ⟨34873245734716326091455505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185990643918487072487762693 34873245734716326091455505)
        ·
          refine ⟨26154934301037244568591629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34873245734716326091455505 26154934301037244568591629)
          ·
            refine ⟨9808100362888966713221861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26154934301037244568591629 9808100362888966713221861)
            ·
              refine ⟨1839018818041681258729099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9808100362888966713221861 1839018818041681258729099)
              ·
                refine ⟨2758528227062521888093649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1839018818041681258729099 2758528227062521888093649)
                ·
                  refine ⟨2068896170296891416070237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2758528227062521888093649 2068896170296891416070237)
                  ·
                    refine ⟨775836063861334281026339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2068896170296891416070237 775836063861334281026339)
                    ·
                      rfl

theorem cell22_2266403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 2, 3].length) (baseStart_2266403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266403 prefixEnd_2266403 := by exact prefixLift 2266403
  have htrace : WordTrace (prefixWord ++ tailWord_2266403) baseStart_2266403 baseEnd_2266403 := by
    simpa [prefixWord, tailWord_2266403, baseEnd_2266403] using wordTrace_append hprefix tailTrace_2266403
  have hstable : (prefixWord ++ tailWord_2266403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266403).length < 2 ^ (prefixWord ++ tailWord_2266403).sum := by decide
  have hdescent : baseEnd_2266403 < baseStart_2266403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266448 : List Nat := [2, 1, 1, 1, 1, 5, 3, 4, 1, 3]
def baseStart_2266448 : Nat := 118140960795 + 2266448 * 2 ^ 59
def prefixEnd_2266448 : Nat := 4983230072969 + 3 ^ 40 * 2266448 * 2
def baseEnd_2266448 : Nat := 775851468280969163651201

theorem tailTrace_2266448 : CollatzResearch.WordTrace tailWord_2266448 prefixEnd_2266448 775851468280969163651201 := by
  unfold tailWord_2266448
  simp only [CollatzResearch.WordTrace]
  refine ⟨41332074846526724673307999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55109433128702299564410665 41332074846526724673307999)
  ·
    refine ⟨61998112269790087009961999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41332074846526724673307999 61998112269790087009961999)
    ·
      refine ⟨92997168404685130514942999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61998112269790087009961999 92997168404685130514942999)
      ·
        refine ⟨139495752607027695772414499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92997168404685130514942999 139495752607027695772414499)
        ·
          refine ⟨209243628910541543658621749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139495752607027695772414499 209243628910541543658621749)
          ·
            refine ⟨19616590210363269717995789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 209243628910541543658621749 19616590210363269717995789)
            ·
              refine ⟨7356221328886226144248421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19616590210363269717995789 7356221328886226144248421)
              ·
                refine ⟨1379291499166167402046579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7356221328886226144248421 1379291499166167402046579)
                ·
                  refine ⟨2068937248749251103069869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1379291499166167402046579 2068937248749251103069869)
                  ·
                    refine ⟨775851468280969163651201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2068937248749251103069869 775851468280969163651201)
                    ·
                      rfl

theorem cell22_2266448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 1, 3].length) (baseStart_2266448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266448 prefixEnd_2266448 := by exact prefixLift 2266448
  have htrace : WordTrace (prefixWord ++ tailWord_2266448) baseStart_2266448 baseEnd_2266448 := by
    simpa [prefixWord, tailWord_2266448, baseEnd_2266448] using wordTrace_append hprefix tailTrace_2266448
  have hstable : (prefixWord ++ tailWord_2266448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266448).length < 2 ^ (prefixWord ++ tailWord_2266448).sum := by decide
  have hdescent : baseEnd_2266448 < baseStart_2266448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266491 : List Nat := [1, 1, 1, 1, 1, 6, 3, 3, 1, 4]
def baseStart_2266491 : Nat := 118140960795 + 2266491 * 2 ^ 59
def prefixEnd_2266491 : Nat := 4983230072969 + 3 ^ 40 * 2266491 * 2
def baseEnd_2266491 : Nat := 775866188059731384826069

theorem tailTrace_2266491 : CollatzResearch.WordTrace tailWord_2266491 prefixEnd_2266491 775866188059731384826069 := by
  unfold tailWord_2266491
  simp only [CollatzResearch.WordTrace]
  refine ⟨82665718031897667690431327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55110478687931778460287551 82665718031897667690431327)
  ·
    refine ⟨123998577047846501535646991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82665718031897667690431327 123998577047846501535646991)
    ·
      refine ⟨185997865571769752303470487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123998577047846501535646991 185997865571769752303470487)
      ·
        refine ⟨278996798357654628455205731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185997865571769752303470487 278996798357654628455205731)
        ·
          refine ⟨418495197536481942682808597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278996798357654628455205731 418495197536481942682808597)
          ·
            refine ⟨19616962384522591063256653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 418495197536481942682808597 19616962384522591063256653)
            ·
              refine ⟨7356360894195971648721245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19616962384522591063256653 7356360894195971648721245)
              ·
                refine ⟨2758635335323489368270467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7356360894195971648721245 2758635335323489368270467)
                ·
                  refine ⟨4137953002985234052405701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2758635335323489368270467 4137953002985234052405701)
                  ·
                    refine ⟨775866188059731384826069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4137953002985234052405701 775866188059731384826069)
                    ·
                      rfl

theorem cell22_2266491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 4].length) (baseStart_2266491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266491 prefixEnd_2266491 := by exact prefixLift 2266491
  have htrace : WordTrace (prefixWord ++ tailWord_2266491) baseStart_2266491 baseEnd_2266491 := by
    simpa [prefixWord, tailWord_2266491, baseEnd_2266491] using wordTrace_append hprefix tailTrace_2266491
  have hstable : (prefixWord ++ tailWord_2266491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266491).length < 2 ^ (prefixWord ++ tailWord_2266491).sum := by decide
  have hdescent : baseEnd_2266491 < baseStart_2266491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266521 : List Nat := [1, 2, 1, 2, 1, 5, 3, 1, 1, 5]
def baseStart_2266521 : Nat := 118140960795 + 2266521 * 2 ^ 59
def prefixEnd_2266521 : Nat := 4983230072969 + 3 ^ 40 * 2266521 * 2
def baseEnd_2266521 : Nat := 775876457672821306575977

theorem tailTrace_2266521 : CollatzResearch.WordTrace tailWord_2266521 prefixEnd_2266521 775876457672821306575977 := by
  unfold tailWord_2266521
  simp only [CollatzResearch.WordTrace]
  refine ⟨82666812221788982814023417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55111208147859321876015611 82666812221788982814023417)
  ·
    refine ⟨62000109166341737110517563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82666812221788982814023417 62000109166341737110517563)
    ·
      refine ⟨93000163749512605665776345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62000109166341737110517563 93000163749512605665776345)
      ·
        refine ⟨69750122812134454249332259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93000163749512605665776345 69750122812134454249332259)
        ·
          refine ⟨104625184218201681373998389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69750122812134454249332259 104625184218201681373998389)
          ·
            refine ⟨9808611020456407628812349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104625184218201681373998389 9808611020456407628812349)
            ·
              refine ⟨3678229132671152860804631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9808611020456407628812349 3678229132671152860804631)
              ·
                refine ⟨5517343699006729291206947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3678229132671152860804631 5517343699006729291206947)
                ·
                  refine ⟨8276015548510093936810421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5517343699006729291206947 8276015548510093936810421)
                  ·
                    refine ⟨775876457672821306575977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8276015548510093936810421 775876457672821306575977)
                    ·
                      rfl

theorem cell22_2266521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 5].length) (baseStart_2266521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266521 prefixEnd_2266521 := by exact prefixLift 2266521
  have htrace : WordTrace (prefixWord ++ tailWord_2266521) baseStart_2266521 baseEnd_2266521 := by
    simpa [prefixWord, tailWord_2266521, baseEnd_2266521] using wordTrace_append hprefix tailTrace_2266521
  have hstable : (prefixWord ++ tailWord_2266521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266521).length < 2 ^ (prefixWord ++ tailWord_2266521).sum := by decide
  have hdescent : baseEnd_2266521 < baseStart_2266521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266553 : List Nat := [1, 2, 1, 4, 4, 1, 1, 2, 2, 4]
def baseStart_2266553 : Nat := 118140960795 + 2266553 * 2 ^ 59
def prefixEnd_2266553 : Nat := 4983230072969 + 3 ^ 40 * 2266553 * 2
def baseEnd_2266553 : Nat := 775887411926783889775879

theorem tailTrace_2266553 : CollatzResearch.WordTrace tailWord_2266553 prefixEnd_2266553 775887411926783889775879 := by
  unfold tailWord_2266553
  simp only [CollatzResearch.WordTrace]
  refine ⟨82667979357673052279188313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55111986238448701519458875 82667979357673052279188313)
  ·
    refine ⟨62000984518254789209391235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82667979357673052279188313 62000984518254789209391235)
    ·
      refine ⟨93001476777382183814086853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62000984518254789209391235 93001476777382183814086853)
      ·
        refine ⟨17437776895759159465141285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93001476777382183814086853 17437776895759159465141285)
        ·
          refine ⟨3269583167954842399713991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17437776895759159465141285 3269583167954842399713991)
          ·
            refine ⟨4904374751932263599570987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3269583167954842399713991 4904374751932263599570987)
            ·
              refine ⟨7356562127898395399356481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4904374751932263599570987 7356562127898395399356481)
              ·
                refine ⟨5517421595923796549517361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7356562127898395399356481 5517421595923796549517361)
                ·
                  refine ⟨4138066196942847412138021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5517421595923796549517361 4138066196942847412138021)
                  ·
                    refine ⟨775887411926783889775879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4138066196942847412138021 775887411926783889775879)
                    ·
                      rfl

theorem cell22_2266553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 4].length) (baseStart_2266553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266553 prefixEnd_2266553 := by exact prefixLift 2266553
  have htrace : WordTrace (prefixWord ++ tailWord_2266553) baseStart_2266553 baseEnd_2266553 := by
    simpa [prefixWord, tailWord_2266553, baseEnd_2266553] using wordTrace_append hprefix tailTrace_2266553
  have hstable : (prefixWord ++ tailWord_2266553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266553).length < 2 ^ (prefixWord ++ tailWord_2266553).sum := by decide
  have hdescent : baseEnd_2266553 < baseStart_2266553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266572 : List Nat := [2, 2, 1, 4, 2, 3, 2, 1, 2, 3]
def baseStart_2266572 : Nat := 118140960795 + 2266572 * 2 ^ 59
def prefixEnd_2266572 : Nat := 4983230072969 + 3 ^ 40 * 2266572 * 2
def baseEnd_2266572 : Nat := 775893916015074173550821

theorem tailTrace_2266572 : CollatzResearch.WordTrace tailWord_2266572 prefixEnd_2266572 775893916015074173550821 := by
  unfold tailWord_2266572
  simp only [CollatzResearch.WordTrace]
  refine ⟨41334336172302109262064985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55112448229736145682753313 41334336172302109262064985)
  ·
    refine ⟨31000752129226581946548739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41334336172302109262064985 31000752129226581946548739)
    ·
      refine ⟨46501128193839872919823109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31000752129226581946548739 46501128193839872919823109)
      ·
        refine ⟨8718961536344976172466833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46501128193839872919823109 8718961536344976172466833)
        ·
          refine ⟨6539221152258732129350125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8718961536344976172466833 6539221152258732129350125)
          ·
            refine ⟨2452207932097024548506297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6539221152258732129350125 2452207932097024548506297)
            ·
              refine ⟨1839155949072768411379723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2452207932097024548506297 1839155949072768411379723)
              ·
                refine ⟨2758733923609152617069585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1839155949072768411379723 2758733923609152617069585)
                ·
                  refine ⟨2069050442706864462802189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2758733923609152617069585 2069050442706864462802189)
                  ·
                    refine ⟨775893916015074173550821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2069050442706864462802189 775893916015074173550821)
                    ·
                      rfl

theorem cell22_2266572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 2, 3].length) (baseStart_2266572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266572 prefixEnd_2266572 := by exact prefixLift 2266572
  have htrace : WordTrace (prefixWord ++ tailWord_2266572) baseStart_2266572 baseEnd_2266572 := by
    simpa [prefixWord, tailWord_2266572, baseEnd_2266572] using wordTrace_append hprefix tailTrace_2266572
  have hstable : (prefixWord ++ tailWord_2266572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266572).length < 2 ^ (prefixWord ++ tailWord_2266572).sum := by decide
  have hdescent : baseEnd_2266572 < baseStart_2266572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266600 : List Nat := [2, 1, 4, 1, 1, 2, 2, 5, 1, 3]
def baseStart_2266600 : Nat := 118140960795 + 2266600 * 2 ^ 59
def prefixEnd_2266600 : Nat := 4983230072969 + 3 ^ 40 * 2266600 * 2
def baseEnd_2266600 : Nat := 775903500987291433850735

theorem tailTrace_2266600 : CollatzResearch.WordTrace tailWord_2266600 prefixEnd_2266600 775903500987291433850735 := by
  unfold tailWord_2266600
  simp only [CollatzResearch.WordTrace]
  refine ⟨41334846794251389653074627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55113129059001852870766169 41334846794251389653074627)
  ·
    refine ⟨62002270191377084479611941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41334846794251389653074627 62002270191377084479611941)
    ·
      refine ⟨11625425660883203339927239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62002270191377084479611941 11625425660883203339927239)
      ·
        refine ⟨17438138491324805009890859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11625425660883203339927239 17438138491324805009890859)
        ·
          refine ⟨26157207736987207514836289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17438138491324805009890859 26157207736987207514836289)
          ·
            refine ⟨19617905802740405636127217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26157207736987207514836289 19617905802740405636127217)
            ·
              refine ⟨14713429352055304227095413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19617905802740405636127217 14713429352055304227095413)
              ·
                refine ⟨1379384001755184771290195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14713429352055304227095413 1379384001755184771290195)
                ·
                  refine ⟨2069076002632777156935293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1379384001755184771290195 2069076002632777156935293)
                  ·
                    refine ⟨775903500987291433850735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2069076002632777156935293 775903500987291433850735)
                    ·
                      rfl

theorem cell22_2266600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_2266600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266600 prefixEnd_2266600 := by exact prefixLift 2266600
  have htrace : WordTrace (prefixWord ++ tailWord_2266600) baseStart_2266600 baseEnd_2266600 := by
    simpa [prefixWord, tailWord_2266600, baseEnd_2266600] using wordTrace_append hprefix tailTrace_2266600
  have hstable : (prefixWord ++ tailWord_2266600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266600).length < 2 ^ (prefixWord ++ tailWord_2266600).sum := by decide
  have hdescent : baseEnd_2266600 < baseStart_2266600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266641 : List Nat := [1, 2, 2, 1, 1, 2, 5, 2, 6]
def baseStart_2266641 : Nat := 118140960795 + 2266641 * 2 ^ 59
def prefixEnd_2266641 : Nat := 4983230072969 + 3 ^ 40 * 2266641 * 2
def baseEnd_2266641 : Nat := 258639178708393664525203

theorem tailTrace_2266641 : CollatzResearch.WordTrace tailWord_2266641 prefixEnd_2266641 258639178708393664525203 := by
  unfold tailWord_2266641
  simp only [CollatzResearch.WordTrace]
  refine ⟨82671188981354243308391777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55114125987569495538927851 82671188981354243308391777)
  ·
    refine ⟨62003391736015682481293833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82671188981354243308391777 62003391736015682481293833)
    ·
      refine ⟨46502543802011761860970375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62003391736015682481293833 46502543802011761860970375)
      ·
        refine ⟨69753815703017642791455563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46502543802011761860970375 69753815703017642791455563)
        ·
          refine ⟨104630723554526464187183345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69753815703017642791455563 104630723554526464187183345)
          ·
            refine ⟨78473042665894848140387509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104630723554526464187183345 78473042665894848140387509)
            ·
              refine ⟨7356847749927642013161329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78473042665894848140387509 7356847749927642013161329)
              ·
                refine ⟨5517635812445731509870997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7356847749927642013161329 5517635812445731509870997)
                ·
                  refine ⟨258639178708393664525203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5517635812445731509870997 258639178708393664525203)
                  ·
                    rfl

theorem cell22_2266641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 6].length) (baseStart_2266641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266641 prefixEnd_2266641 := by exact prefixLift 2266641
  have htrace : WordTrace (prefixWord ++ tailWord_2266641) baseStart_2266641 baseEnd_2266641 := by
    simpa [prefixWord, tailWord_2266641, baseEnd_2266641] using wordTrace_append hprefix tailTrace_2266641
  have hstable : (prefixWord ++ tailWord_2266641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266641).length < 2 ^ (prefixWord ++ tailWord_2266641).sum := by decide
  have hdescent : baseEnd_2266641 < baseStart_2266641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266694 : List Nat := [6, 1, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_2266694 : Nat := 118140960795 + 2266694 * 2 ^ 59
def prefixEnd_2266694 : Nat := 4983230072969 + 3 ^ 40 * 2266694 * 2
def baseEnd_2266694 : Nat := 775935679108306522000447

theorem tailTrace_2266694 : CollatzResearch.WordTrace tailWord_2266694 prefixEnd_2266694 775935679108306522000447 := by
  unfold tailWord_2266694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2583535064067569792502223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55115414700108155573380757 2583535064067569792502223)
  ·
    refine ⟨3875302596101354688753335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2583535064067569792502223 3875302596101354688753335)
    ·
      refine ⟨5812953894152032033130003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3875302596101354688753335 5812953894152032033130003)
      ·
        refine ⟨8719430841228048049695005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5812953894152032033130003 8719430841228048049695005)
        ·
          refine ⟨3269786565460518018635627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8719430841228048049695005 3269786565460518018635627)
          ·
            refine ⟨4904679848190777027953441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3269786565460518018635627 4904679848190777027953441)
            ·
              refine ⟨3678509886143082770965081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4904679848190777027953441 3678509886143082770965081)
              ·
                refine ⟨2758882414607312078223811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3678509886143082770965081 2758882414607312078223811)
                ·
                  refine ⟨4138323621910968117335717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2758882414607312078223811 4138323621910968117335717)
                  ·
                    refine ⟨775935679108306522000447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4138323621910968117335717 775935679108306522000447)
                    ·
                      rfl

theorem cell22_2266694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_2266694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266694 prefixEnd_2266694 := by exact prefixLift 2266694
  have htrace : WordTrace (prefixWord ++ tailWord_2266694) baseStart_2266694 baseEnd_2266694 := by
    simpa [prefixWord, tailWord_2266694, baseEnd_2266694] using wordTrace_append hprefix tailTrace_2266694
  have hstable : (prefixWord ++ tailWord_2266694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266694).length < 2 ^ (prefixWord ++ tailWord_2266694).sum := by decide
  have hdescent : baseEnd_2266694 < baseStart_2266694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266782 : List Nat := [4, 3, 1, 1, 1, 3, 2, 2, 5]
def baseStart_2266782 : Nat := 118140960795 + 2266782 * 2 ^ 59
def prefixEnd_2266782 : Nat := 4983230072969 + 3 ^ 40 * 2266782 * 2
def baseEnd_2266782 : Nat := 258655267768901208600059

theorem tailTrace_2266782 : CollatzResearch.WordTrace tailWord_2266782 prefixEnd_2266782 258655267768901208600059 := by
  unfold tailWord_2266782
  simp only [CollatzResearch.WordTrace]
  refine ⟨10334541459230428048659325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55117554449228949592849733 10334541459230428048659325)
  ·
    refine ⟨3875453047211410518247247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10334541459230428048659325 3875453047211410518247247)
    ·
      refine ⟨5813179570817115777370871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3875453047211410518247247 5813179570817115777370871)
      ·
        refine ⟨8719769356225673666056307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5813179570817115777370871 8719769356225673666056307)
        ·
          refine ⟨13079654034338510499084461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8719769356225673666056307 13079654034338510499084461)
          ·
            refine ⟨4904870262876941437156673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13079654034338510499084461 4904870262876941437156673)
            ·
              refine ⟨3678652697157706077867505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4904870262876941437156673 3678652697157706077867505)
              ·
                refine ⟨2758989522868279558400629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3678652697157706077867505 2758989522868279558400629)
                ·
                  refine ⟨258655267768901208600059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2758989522868279558400629 258655267768901208600059)
                  ·
                    rfl

theorem cell22_2266782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_2266782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266782 prefixEnd_2266782 := by exact prefixLift 2266782
  have htrace : WordTrace (prefixWord ++ tailWord_2266782) baseStart_2266782 baseEnd_2266782 := by
    simpa [prefixWord, tailWord_2266782, baseEnd_2266782] using wordTrace_append hprefix tailTrace_2266782
  have hstable : (prefixWord ++ tailWord_2266782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266782).length < 2 ^ (prefixWord ++ tailWord_2266782).sum := by decide
  have hdescent : baseEnd_2266782 < baseStart_2266782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266786 : List Nat := [3, 3, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_2266786 : Nat := 118140960795 + 2266786 * 2 ^ 59
def prefixEnd_2266786 : Nat := 4983230072969 + 3 ^ 40 * 2266786 * 2
def baseEnd_2266786 : Nat := 775967172588448948700165

theorem tailTrace_2266786 : CollatzResearch.WordTrace tailWord_2266786 prefixEnd_2266786 775967172588448948700165 := by
  unfold tailWord_2266786
  simp only [CollatzResearch.WordTrace]
  refine ⟨20669119391457233268105053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55117651710552622048280141 20669119391457233268105053)
  ·
    refine ⟨7750919771796462475539395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20669119391457233268105053 7750919771796462475539395)
    ·
      refine ⟨11626379657694693713309093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7750919771796462475539395 11626379657694693713309093)
      ·
        refine ⟨2179946185817755071245455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11626379657694693713309093 2179946185817755071245455)
        ·
          refine ⟨3269919278726632606868183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2179946185817755071245455 3269919278726632606868183)
          ·
            refine ⟨4904878918089948910302275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3269919278726632606868183 4904878918089948910302275)
            ·
              refine ⟨7357318377134923365453413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4904878918089948910302275 7357318377134923365453413)
              ·
                refine ⟨1379497195712798131022515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7357318377134923365453413 1379497195712798131022515)
                ·
                  refine ⟨2069245793569197196533773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1379497195712798131022515 2069245793569197196533773)
                  ·
                    refine ⟨775967172588448948700165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2069245793569197196533773 775967172588448948700165)
                    ·
                      rfl

theorem cell22_2266786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_2266786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266786 prefixEnd_2266786 := by exact prefixLift 2266786
  have htrace : WordTrace (prefixWord ++ tailWord_2266786) baseStart_2266786 baseEnd_2266786 := by
    simpa [prefixWord, tailWord_2266786, baseEnd_2266786] using wordTrace_append hprefix tailTrace_2266786
  have hstable : (prefixWord ++ tailWord_2266786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266786).length < 2 ^ (prefixWord ++ tailWord_2266786).sum := by decide
  have hdescent : baseEnd_2266786 < baseStart_2266786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266823 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 1, 6]
def baseStart_2266823 : Nat := 118140960795 + 2266823 * 2 ^ 59
def prefixEnd_2266823 : Nat := 4983230072969 + 3 ^ 40 * 2266823 * 2
def baseEnd_2266823 : Nat := 775979838444593185525051

theorem tailTrace_2266823 : CollatzResearch.WordTrace tailWord_2266823 prefixEnd_2266823 775979838444593185525051 := by
  unfold tailWord_2266823
  simp only [CollatzResearch.WordTrace]
  refine ⟨82677827066694888391517123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55118551377796592261011415 82677827066694888391517123)
  ·
    refine ⟨124016740600042332587275685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82677827066694888391517123 124016740600042332587275685)
    ·
      refine ⟨23253138862507937360114191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124016740600042332587275685 23253138862507937360114191)
      ·
        refine ⟨34879708293761906040171287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23253138862507937360114191 34879708293761906040171287)
        ·
          refine ⟨52319562440642859060256931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34879708293761906040171287 52319562440642859060256931)
          ·
            refine ⟨78479343660964288590385397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52319562440642859060256931 78479343660964288590385397)
            ·
              refine ⟨7357438468215402055348631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78479343660964288590385397 7357438468215402055348631)
              ·
                refine ⟨11036157702323103083022947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7357438468215402055348631 11036157702323103083022947)
                ·
                  refine ⟨16554236553484654624534421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11036157702323103083022947 16554236553484654624534421)
                  ·
                    refine ⟨775979838444593185525051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16554236553484654624534421 775979838444593185525051)
                    ·
                      rfl

theorem cell22_2266823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_2266823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266823 prefixEnd_2266823 := by exact prefixLift 2266823
  have htrace : WordTrace (prefixWord ++ tailWord_2266823) baseStart_2266823 baseEnd_2266823 := by
    simpa [prefixWord, tailWord_2266823, baseEnd_2266823] using wordTrace_append hprefix tailTrace_2266823
  have hstable : (prefixWord ++ tailWord_2266823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266823).length < 2 ^ (prefixWord ++ tailWord_2266823).sum := by decide
  have hdescent : baseEnd_2266823 < baseStart_2266823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266829 : List Nat := [1, 6, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_2266829 : Nat := 118140960795 + 2266829 * 2 ^ 59
def prefixEnd_2266829 : Nat := 4983230072969 + 3 ^ 40 * 2266829 * 2
def baseEnd_2266829 : Nat := 775981892367211169875033

theorem tailTrace_2266829 : CollatzResearch.WordTrace tailWord_2266829 prefixEnd_2266829 775981892367211169875033 := by
  unfold tailWord_2266829
  simp only [CollatzResearch.WordTrace]
  refine ⟨82678045904673151416235541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55118697269782100944157027 82678045904673151416235541)
  ·
    refine ⟨3875533401781553972636041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 82678045904673151416235541 3875533401781553972636041)
    ·
      refine ⟨2906650051336165479477031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3875533401781553972636041 2906650051336165479477031)
      ·
        refine ⟨4359975077004248219215547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2906650051336165479477031 4359975077004248219215547)
        ·
          refine ⟨6539962615506372328823321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4359975077004248219215547 6539962615506372328823321)
          ·
            refine ⟨4904971961629779246617491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6539962615506372328823321 4904971961629779246617491)
            ·
              refine ⟨7357457942444668869926237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4904971961629779246617491 7357457942444668869926237)
              ·
                refine ⟨2759046728416750826222339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7357457942444668869926237 2759046728416750826222339)
                ·
                  refine ⟨4138570092625126239333509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2759046728416750826222339 4138570092625126239333509)
                  ·
                    refine ⟨775981892367211169875033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4138570092625126239333509 775981892367211169875033)
                    ·
                      rfl

theorem cell22_2266829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_2266829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266829 prefixEnd_2266829 := by exact prefixLift 2266829
  have htrace : WordTrace (prefixWord ++ tailWord_2266829) baseStart_2266829 baseEnd_2266829 := by
    simpa [prefixWord, tailWord_2266829, baseEnd_2266829] using wordTrace_append hprefix tailTrace_2266829
  have hstable : (prefixWord ++ tailWord_2266829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266829).length < 2 ^ (prefixWord ++ tailWord_2266829).sum := by decide
  have hdescent : baseEnd_2266829 < baseStart_2266829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266842 : List Nat := [3, 1, 1, 2, 2, 3, 3, 2, 2, 3]
def baseStart_2266842 : Nat := 118140960795 + 2266842 * 2 ^ 59
def prefixEnd_2266842 : Nat := 4983230072969 + 3 ^ 40 * 2266842 * 2
def baseEnd_2266842 : Nat := 775986342532883469299993

theorem tailTrace_2266842 : CollatzResearch.WordTrace tailWord_2266842 prefixEnd_2266842 775986342532883469299993 := by
  unfold tailWord_2266842
  simp only [CollatzResearch.WordTrace]
  refine ⟨20669630013406513659114695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55119013369084036424305853 20669630013406513659114695)
  ·
    refine ⟨31004445020109770488672043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20669630013406513659114695 31004445020109770488672043)
    ·
      refine ⟨46506667530164655733008065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31004445020109770488672043 46506667530164655733008065)
      ·
        refine ⟨34880000647623491799756049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46506667530164655733008065 34880000647623491799756049)
        ·
          refine ⟨26160000485717618849817037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34880000647623491799756049 26160000485717618849817037)
          ·
            refine ⟨9810000182144107068681389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26160000485717618849817037 9810000182144107068681389)
            ·
              refine ⟨3678750068304040150755521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9810000182144107068681389 3678750068304040150755521)
              ·
                refine ⟨2759062551228030113066641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3678750068304040150755521 2759062551228030113066641)
                ·
                  refine ⟨2069296913421022584799981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2759062551228030113066641 2069296913421022584799981)
                  ·
                    refine ⟨775986342532883469299993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2069296913421022584799981 775986342532883469299993)
                    ·
                      rfl

theorem cell22_2266842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_2266842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266842 prefixEnd_2266842 := by exact prefixLift 2266842
  have htrace : WordTrace (prefixWord ++ tailWord_2266842) baseStart_2266842 baseEnd_2266842 := by
    simpa [prefixWord, tailWord_2266842, baseEnd_2266842] using wordTrace_append hprefix tailTrace_2266842
  have hstable : (prefixWord ++ tailWord_2266842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266842).length < 2 ^ (prefixWord ++ tailWord_2266842).sum := by decide
  have hdescent : baseEnd_2266842 < baseStart_2266842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266883 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 7]
def baseStart_2266883 : Nat := 118140960795 + 2266883 * 2 ^ 59
def prefixEnd_2266883 : Nat := 4983230072969 + 3 ^ 40 * 2266883 * 2
def baseEnd_2266883 : Nat := 258666792556924343008289

theorem tailTrace_2266883 : CollatzResearch.WordTrace tailWord_2266883 prefixEnd_2266883 258666792556924343008289 := by
  unfold tailWord_2266883
  simp only [CollatzResearch.WordTrace]
  refine ⟨82680015446477518638701303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55120010297651679092467535 82680015446477518638701303)
  ·
    refine ⟨124020023169716277958051955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82680015446477518638701303 124020023169716277958051955)
    ·
      refine ⟨186030034754574416937077933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124020023169716277958051955 186030034754574416937077933)
      ·
        refine ⟨69761263032965406351404225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186030034754574416937077933 69761263032965406351404225)
        ·
          refine ⟨52320947274724054763553169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69761263032965406351404225 52320947274724054763553169)
          ·
            refine ⟨39240710456043041072664877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52320947274724054763553169 39240710456043041072664877)
            ·
              refine ⟨14715266421016140402249329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39240710456043041072664877 14715266421016140402249329)
              ·
                refine ⟨11036449815762105301686997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14715266421016140402249329 11036449815762105301686997)
                ·
                  refine ⟨258666792556924343008289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11036449815762105301686997 258666792556924343008289)
                  ·
                    rfl

theorem cell22_2266883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 7].length) (baseStart_2266883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266883 prefixEnd_2266883 := by exact prefixLift 2266883
  have htrace : WordTrace (prefixWord ++ tailWord_2266883) baseStart_2266883 baseEnd_2266883 := by
    simpa [prefixWord, tailWord_2266883, baseEnd_2266883] using wordTrace_append hprefix tailTrace_2266883
  have hstable : (prefixWord ++ tailWord_2266883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266883).length < 2 ^ (prefixWord ++ tailWord_2266883).sum := by decide
  have hdescent : baseEnd_2266883 < baseStart_2266883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266910 : List Nat := [4, 3, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_2266910 : Nat := 118140960795 + 2266910 * 2 ^ 59
def prefixEnd_2266910 : Nat := 4983230072969 + 3 ^ 40 * 2266910 * 2
def baseEnd_2266910 : Nat := 776009620322553958599785

theorem tailTrace_2266910 : CollatzResearch.WordTrace tailWord_2266910 prefixEnd_2266910 776009620322553958599785 := by
  unfold tailWord_2266910
  simp only [CollatzResearch.WordTrace]
  refine ⟨10335125027172462781241773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55120666811586468166622789 10335125027172462781241773)
  ·
    refine ⟨3875671885189673542965665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10335125027172462781241773 3875671885189673542965665)
    ·
      refine ⟨2906753913892255157224249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3875671885189673542965665 2906753913892255157224249)
      ·
        refine ⟨2180065435419191367918187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2906753913892255157224249 2180065435419191367918187)
        ·
          refine ⟨3270098153128787051877281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2180065435419191367918187 3270098153128787051877281)
          ·
            refine ⟨2452573614846590288907961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3270098153128787051877281 2452573614846590288907961)
            ·
              refine ⟨1839430211134942716680971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2452573614846590288907961 1839430211134942716680971)
              ·
                refine ⟨2759145316702414075021457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1839430211134942716680971 2759145316702414075021457)
                ·
                  refine ⟨2069358987526810556266093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2759145316702414075021457 2069358987526810556266093)
                  ·
                    refine ⟨776009620322553958599785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2069358987526810556266093 776009620322553958599785)
                    ·
                      rfl

theorem cell22_2266910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_2266910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266910 prefixEnd_2266910 := by exact prefixLift 2266910
  have htrace : WordTrace (prefixWord ++ tailWord_2266910) baseStart_2266910 baseEnd_2266910 := by
    simpa [prefixWord, tailWord_2266910, baseEnd_2266910] using wordTrace_append hprefix tailTrace_2266910
  have hstable : (prefixWord ++ tailWord_2266910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266910).length < 2 ^ (prefixWord ++ tailWord_2266910).sum := by decide
  have hdescent : baseEnd_2266910 < baseStart_2266910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266917 : List Nat := [1, 3, 1, 2, 3, 2, 4, 1, 5]
def baseStart_2266917 : Nat := 118140960795 + 2266917 * 2 ^ 59
def prefixEnd_2266917 : Nat := 4983230072969 + 3 ^ 40 * 2266917 * 2
def baseEnd_2266917 : Nat := 258670672188536091224921

theorem tailTrace_2266917 : CollatzResearch.WordTrace tailWord_2266917 prefixEnd_2266917 258670672188536091224921 := by
  unfold tailWord_2266917
  simp only [CollatzResearch.WordTrace]
  refine ⟨82681255528354342445439005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55120837018902894963626003 82681255528354342445439005)
  ·
    refine ⟨31005470823132878417039627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82681255528354342445439005 31005470823132878417039627)
    ·
      refine ⟨46508206234699317625559441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31005470823132878417039627 46508206234699317625559441)
      ·
        refine ⟨34881154676024488219169581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46508206234699317625559441 34881154676024488219169581)
        ·
          refine ⟨13080433003509183082188593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34881154676024488219169581 13080433003509183082188593)
          ·
            refine ⟨9810324752631887311641445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13080433003509183082188593 9810324752631887311641445)
            ·
              refine ⟨1839435891118478870932771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9810324752631887311641445 1839435891118478870932771)
              ·
                refine ⟨2759153836677718306399157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1839435891118478870932771 2759153836677718306399157)
                ·
                  refine ⟨258670672188536091224921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2759153836677718306399157 258670672188536091224921)
                  ·
                    rfl

theorem cell22_2266917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_2266917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266917 prefixEnd_2266917 := by exact prefixLift 2266917
  have htrace : WordTrace (prefixWord ++ tailWord_2266917) baseStart_2266917 baseEnd_2266917 := by
    simpa [prefixWord, tailWord_2266917, baseEnd_2266917] using wordTrace_append hprefix tailTrace_2266917
  have hstable : (prefixWord ++ tailWord_2266917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266917).length < 2 ^ (prefixWord ++ tailWord_2266917).sum := by decide
  have hdescent : baseEnd_2266917 < baseStart_2266917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266977 : List Nat := [1, 2, 3, 1, 1, 1, 3, 5, 2, 3]
def baseStart_2266977 : Nat := 118140960795 + 2266977 * 2 ^ 59
def prefixEnd_2266977 : Nat := 4983230072969 + 3 ^ 40 * 2266977 * 2
def baseEnd_2266977 : Nat := 776032555791788117174579

theorem tailTrace_2266977 : CollatzResearch.WordTrace tailWord_2266977 prefixEnd_2266977 776032555791788117174579 := by
  unfold tailWord_2266977
  simp only [CollatzResearch.WordTrace]
  refine ⟨82683443908136972692623185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55122295938757981795082123 82683443908136972692623185)
  ·
    refine ⟨62012582931102729519467389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82683443908136972692623185 62012582931102729519467389)
    ·
      refine ⟨23254718599163523569800271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62012582931102729519467389 23254718599163523569800271)
      ·
        refine ⟨34882077898745285354700407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23254718599163523569800271 34882077898745285354700407)
        ·
          refine ⟨52323116848117928032050611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34882077898745285354700407 52323116848117928032050611)
          ·
            refine ⟨78484675272176892048075917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52323116848117928032050611 78484675272176892048075917)
            ·
              refine ⟨29431753227066334518028469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78484675272176892048075917 29431753227066334518028469)
              ·
                refine ⟨2759226865037468861065169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29431753227066334518028469 2759226865037468861065169)
                ·
                  refine ⟨2069420148778101645798877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2759226865037468861065169 2069420148778101645798877)
                  ·
                    refine ⟨776032555791788117174579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2069420148778101645798877 776032555791788117174579)
                    ·
                      rfl

theorem cell22_2266977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_2266977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266977 prefixEnd_2266977 := by exact prefixLift 2266977
  have htrace : WordTrace (prefixWord ++ tailWord_2266977) baseStart_2266977 baseEnd_2266977 := by
    simpa [prefixWord, tailWord_2266977, baseEnd_2266977] using wordTrace_append hprefix tailTrace_2266977
  have hstable : (prefixWord ++ tailWord_2266977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266977).length < 2 ^ (prefixWord ++ tailWord_2266977).sum := by decide
  have hdescent : baseEnd_2266977 < baseStart_2266977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266998 : List Nat := [5, 1, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_2266998 : Nat := 118140960795 + 2266998 * 2 ^ 59
def prefixEnd_2266998 : Nat := 4983230072969 + 3 ^ 40 * 2266998 * 2
def baseEnd_2266998 : Nat := 776039744520951062399515

theorem tailTrace_2266998 : CollatzResearch.WordTrace tailWord_2266998 prefixEnd_2266998 776039744520951062399515 := by
  unfold tailWord_2266998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5167763115066305829946103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55122806560707262186091765 5167763115066305829946103)
  ·
    refine ⟨7751644672599458744919155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5167763115066305829946103 7751644672599458744919155)
    ·
      refine ⟨11627467008899188117378733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7751644672599458744919155 11627467008899188117378733)
      ·
        refine ⟨4360300128337195544017025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11627467008899188117378733 4360300128337195544017025)
        ·
          refine ⟨3270225096252896658012769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4360300128337195544017025 3270225096252896658012769)
          ·
            refine ⟨2452668822189672493509577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3270225096252896658012769 2452668822189672493509577)
            ·
              refine ⟨1839501616642254370132183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2452668822189672493509577 1839501616642254370132183)
              ·
                refine ⟨2759252424963381555198275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1839501616642254370132183 2759252424963381555198275)
                ·
                  refine ⟨4138878637445072332797413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2759252424963381555198275 4138878637445072332797413)
                  ·
                    refine ⟨776039744520951062399515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4138878637445072332797413 776039744520951062399515)
                    ·
                      rfl

theorem cell22_2266998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_2266998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2266998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2266998 prefixEnd_2266998 := by exact prefixLift 2266998
  have htrace : WordTrace (prefixWord ++ tailWord_2266998) baseStart_2266998 baseEnd_2266998 := by
    simpa [prefixWord, tailWord_2266998, baseEnd_2266998] using wordTrace_append hprefix tailTrace_2266998
  have hstable : (prefixWord ++ tailWord_2266998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266998).length < 2 ^ (prefixWord ++ tailWord_2266998).sum := by decide
  have hdescent : baseEnd_2266998 < baseStart_2266998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267041 : List Nat := [1, 2, 3, 4, 3, 1, 2, 6]
def baseStart_2267041 : Nat := 118140960795 + 2267041 * 2 ^ 59
def prefixEnd_2267041 : Nat := 4983230072969 + 3 ^ 40 * 2267041 * 2
def baseEnd_2267041 : Nat := 86228273811079253730487

theorem tailTrace_2267041 : CollatzResearch.WordTrace tailWord_2267041 prefixEnd_2267041 86228273811079253730487 := by
  unfold tailWord_2267041
  simp only [CollatzResearch.WordTrace]
  refine ⟨82685778179905111622952977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55123852119936741081968651 82685778179905111622952977)
  ·
    refine ⟨62014333634928833717214733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82685778179905111622952977 62014333634928833717214733)
    ·
      refine ⟨23255375113098312643955525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62014333634928833717214733 23255375113098312643955525)
      ·
        refine ⟨4360382833705933620741661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23255375113098312643955525 4360382833705933620741661)
        ·
          refine ⟨1635143562639725107778123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4360382833705933620741661 1635143562639725107778123)
          ·
            refine ⟨2452715343959587661667185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1635143562639725107778123 2452715343959587661667185)
            ·
              refine ⟨1839536507969690746250389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2452715343959587661667185 1839536507969690746250389)
              ·
                refine ⟨86228273811079253730487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1839536507969690746250389 86228273811079253730487)
                ·
                  rfl

theorem cell22_2267041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 6].length) (baseStart_2267041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267041 prefixEnd_2267041 := by exact prefixLift 2267041
  have htrace : WordTrace (prefixWord ++ tailWord_2267041) baseStart_2267041 baseEnd_2267041 := by
    simpa [prefixWord, tailWord_2267041, baseEnd_2267041] using wordTrace_append hprefix tailTrace_2267041
  have hstable : (prefixWord ++ tailWord_2267041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267041).length < 2 ^ (prefixWord ++ tailWord_2267041).sum := by decide
  have hdescent : baseEnd_2267041 < baseStart_2267041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267114 : List Nat := [3, 1, 3, 1, 2, 1, 2, 5, 4]
def baseStart_2267114 : Nat := 118140960795 + 2267114 * 2 ^ 59
def prefixEnd_2267114 : Nat := 4983230072969 + 3 ^ 40 * 2267114 * 2
def baseEnd_2267114 : Nat := 258693151230521808833053

theorem tailTrace_2267114 : CollatzResearch.WordTrace tailWord_2267114 prefixEnd_2267114 258693151230521808833053 := by
  unfold tailWord_2267114
  simp only [CollatzResearch.WordTrace]
  refine ⟨20672110177160161272590099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55125627139093763393573597 20672110177160161272590099)
  ·
    refine ⟨31008165265740241908885149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20672110177160161272590099 31008165265740241908885149)
    ·
      refine ⟨11628061974652590715831931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31008165265740241908885149 11628061974652590715831931)
      ·
        refine ⟨17442092961978886073747897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11628061974652590715831931 17442092961978886073747897)
        ·
          refine ⟨13081569721484164555310923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17442092961978886073747897 13081569721484164555310923)
          ·
            refine ⟨19622354582226246832966385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13081569721484164555310923 19622354582226246832966385)
            ·
              refine ⟨14716765936669685124724789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19622354582226246832966385 14716765936669685124724789)
              ·
                refine ⟨1379696806562782980442949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14716765936669685124724789 1379696806562782980442949)
                ·
                  refine ⟨258693151230521808833053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1379696806562782980442949 258693151230521808833053)
                  ·
                    rfl

theorem cell22_2267114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_2267114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267114 prefixEnd_2267114 := by exact prefixLift 2267114
  have htrace : WordTrace (prefixWord ++ tailWord_2267114) baseStart_2267114 baseEnd_2267114 := by
    simpa [prefixWord, tailWord_2267114, baseEnd_2267114] using wordTrace_append hprefix tailTrace_2267114
  have hstable : (prefixWord ++ tailWord_2267114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267114).length < 2 ^ (prefixWord ++ tailWord_2267114).sum := by decide
  have hdescent : baseEnd_2267114 < baseStart_2267114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267129 : List Nat := [1, 2, 1, 3, 1, 4, 1, 4, 2, 3]
def baseStart_2267129 : Nat := 118140960795 + 2267129 * 2 ^ 59
def prefixEnd_2267129 : Nat := 4983230072969 + 3 ^ 40 * 2267129 * 2
def baseEnd_2267129 : Nat := 776084588498110387374113

theorem tailTrace_2267129 : CollatzResearch.WordTrace tailWord_2267129 prefixEnd_2267129 776084588498110387374113 := by
  unfold tailWord_2267129
  simp only [CollatzResearch.WordTrace]
  refine ⟨82688987803586302652156441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55125991869057535101437627 82688987803586302652156441)
  ·
    refine ⟨62016740852689726989117331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82688987803586302652156441 62016740852689726989117331)
    ·
      refine ⟨93025111279034590483675997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62016740852689726989117331 93025111279034590483675997)
      ·
        refine ⟨34884416729637971431378499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93025111279034590483675997 34884416729637971431378499)
        ·
          refine ⟨52326625094456957147067749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34884416729637971431378499 52326625094456957147067749)
          ·
            refine ⟨9811242205210679465075203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52326625094456957147067749 9811242205210679465075203)
            ·
              refine ⟨14716863307816019197612805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9811242205210679465075203 14716863307816019197612805)
              ·
                refine ⟨2759411870215503599552401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14716863307816019197612805 2759411870215503599552401)
                ·
                  refine ⟨2069558902661627699664301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2759411870215503599552401 2069558902661627699664301)
                  ·
                    refine ⟨776084588498110387374113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2069558902661627699664301 776084588498110387374113)
                    ·
                      rfl

theorem cell22_2267129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 3].length) (baseStart_2267129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267129 prefixEnd_2267129 := by exact prefixLift 2267129
  have htrace : WordTrace (prefixWord ++ tailWord_2267129) baseStart_2267129 baseEnd_2267129 := by
    simpa [prefixWord, tailWord_2267129, baseEnd_2267129] using wordTrace_append hprefix tailTrace_2267129
  have hstable : (prefixWord ++ tailWord_2267129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267129).length < 2 ^ (prefixWord ++ tailWord_2267129).sum := by decide
  have hdescent : baseEnd_2267129 < baseStart_2267129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267191 : List Nat := [1, 1, 3, 1, 2, 2, 4, 4, 1, 3]
def baseStart_2267191 : Nat := 118140960795 + 2267191 * 2 ^ 59
def prefixEnd_2267191 : Nat := 4983230072969 + 3 ^ 40 * 2267191 * 2
def baseEnd_2267191 : Nat := 776105812365162892323923

theorem tailTrace_2267191 : CollatzResearch.WordTrace tailWord_2267191 prefixEnd_2267191 776105812365162892323923 := by
  unfold tailWord_2267191
  simp only [CollatzResearch.WordTrace]
  refine ⟨82691249129361687240913427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55127499419574458160608951 82691249129361687240913427)
  ·
    refine ⟨124036873694042530861370141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82691249129361687240913427 124036873694042530861370141)
    ·
      refine ⟨46513827635265949073013803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124036873694042530861370141 46513827635265949073013803)
      ·
        refine ⟨69770741452898923609520705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46513827635265949073013803 69770741452898923609520705)
        ·
          refine ⟨52328056089674192707140529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69770741452898923609520705 52328056089674192707140529)
          ·
            refine ⟨39246042067255644530355397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52328056089674192707140529 39246042067255644530355397)
            ·
              refine ⟨7358632887610433349441637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39246042067255644530355397 7358632887610433349441637)
              ·
                refine ⟨1379743666426956253020307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7358632887610433349441637 1379743666426956253020307)
                ·
                  refine ⟨2069615499640434379530461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1379743666426956253020307 2069615499640434379530461)
                  ·
                    refine ⟨776105812365162892323923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2069615499640434379530461 776105812365162892323923)
                    ·
                      rfl

theorem cell22_2267191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 1, 3].length) (baseStart_2267191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267191 prefixEnd_2267191 := by exact prefixLift 2267191
  have htrace : WordTrace (prefixWord ++ tailWord_2267191) baseStart_2267191 baseEnd_2267191 := by
    simpa [prefixWord, tailWord_2267191, baseEnd_2267191] using wordTrace_append hprefix tailTrace_2267191
  have hstable : (prefixWord ++ tailWord_2267191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267191).length < 2 ^ (prefixWord ++ tailWord_2267191).sum := by decide
  have hdescent : baseEnd_2267191 < baseStart_2267191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267294 : List Nat := [4, 3, 1, 1, 13]
def baseStart_2267294 : Nat := 118140960795 + 2267294 * 2 ^ 59
def prefixEnd_2267294 : Nat := 4983230072969 + 3 ^ 40 * 2267294 * 2
def baseEnd_2267294 : Nat := 3193996178477798176949

theorem tailTrace_2267294 : CollatzResearch.WordTrace tailWord_2267294 prefixEnd_2267294 3193996178477798176949 := by
  unfold tailWord_2267294
  simp only [CollatzResearch.WordTrace]
  refine ⟨10336875730998566978989117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55130003898659023887941957 10336875730998566978989117)
  ·
    refine ⟨3876328399124462617120919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10336875730998566978989117 3876328399124462617120919)
    ·
      refine ⟨5814492598686693925681379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3876328399124462617120919 5814492598686693925681379)
      ·
        refine ⟨8721738898030040888522069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5814492598686693925681379 8721738898030040888522069)
        ·
          refine ⟨3193996178477798176949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 8721738898030040888522069 3193996178477798176949)
          ·
            rfl

theorem cell22_2267294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 13].length) (baseStart_2267294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267294 prefixEnd_2267294 := by exact prefixLift 2267294
  have htrace : WordTrace (prefixWord ++ tailWord_2267294) baseStart_2267294 baseEnd_2267294 := by
    simpa [prefixWord, tailWord_2267294, baseEnd_2267294] using wordTrace_append hprefix tailTrace_2267294
  have hstable : (prefixWord ++ tailWord_2267294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267294).length < 2 ^ (prefixWord ++ tailWord_2267294).sum := by decide
  have hdescent : baseEnd_2267294 < baseStart_2267294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267298 : List Nat := [3, 3, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_2267298 : Nat := 118140960795 + 2267298 * 2 ^ 59
def prefixEnd_2267298 : Nat := 4983230072969 + 3 ^ 40 * 2267298 * 2
def baseEnd_2267298 : Nat := 776142440651850279898595

theorem tailTrace_2267298 : CollatzResearch.WordTrace tailWord_2267298 prefixEnd_2267298 776142440651850279898595 := by
  unfold tailWord_2267298
  simp only [CollatzResearch.WordTrace]
  refine ⟨20673787934993511128764637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55130101159982696343372365 20673787934993511128764637)
  ·
    refine ⟨7752670475622566673286739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20673787934993511128764637 7752670475622566673286739)
    ·
      refine ⟨11629005713433850009930109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7752670475622566673286739 11629005713433850009930109)
      ·
        refine ⟨4360877142537693753723791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11629005713433850009930109 4360877142537693753723791)
        ·
          refine ⟨6541315713806540630585687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4360877142537693753723791 6541315713806540630585687)
          ·
            refine ⟨9811973570709810945878531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6541315713806540630585687 9811973570709810945878531)
            ·
              refine ⟨14717960356064716418817797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9811973570709810945878531 14717960356064716418817797)
              ·
                refine ⟨2759617566762134328528337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14717960356064716418817797 2759617566762134328528337)
                ·
                  refine ⟨2069713175071600746396253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2759617566762134328528337 2069713175071600746396253)
                  ·
                    refine ⟨776142440651850279898595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2069713175071600746396253 776142440651850279898595)
                    ·
                      rfl

theorem cell22_2267298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_2267298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267298 prefixEnd_2267298 := by exact prefixLift 2267298
  have htrace : WordTrace (prefixWord ++ tailWord_2267298) baseStart_2267298 baseEnd_2267298 := by
    simpa [prefixWord, tailWord_2267298, baseEnd_2267298] using wordTrace_append hprefix tailTrace_2267298
  have hstable : (prefixWord ++ tailWord_2267298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267298).length < 2 ^ (prefixWord ++ tailWord_2267298).sum := by decide
  have hdescent : baseEnd_2267298 < baseStart_2267298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267300 : List Nat := [2, 3, 1, 2, 4, 2, 2, 2, 4]
def baseStart_2267300 : Nat := 118140960795 + 2267300 * 2 ^ 59
def prefixEnd_2267300 : Nat := 4983230072969 + 3 ^ 40 * 2267300 * 2
def baseEnd_2267300 : Nat := 258714375097574313782863

theorem tailTrace_2267300 : CollatzResearch.WordTrace tailWord_2267300 prefixEnd_2267300 258714375097574313782863 := by
  unfold tailWord_2267300
  simp only [CollatzResearch.WordTrace]
  refine ⟨41347612342983399428315677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55130149790644532571087569 41347612342983399428315677)
  ·
    refine ⟨15505354628618774785618379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41347612342983399428315677 15505354628618774785618379)
    ·
      refine ⟨23258031942928162178427569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15505354628618774785618379 23258031942928162178427569)
      ·
        refine ⟨17443523957196121633820677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23258031942928162178427569 17443523957196121633820677)
        ·
          refine ⟨3270660741974272806341377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17443523957196121633820677 3270660741974272806341377)
          ·
            refine ⟨2452995556480704604756033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3270660741974272806341377 2452995556480704604756033)
            ·
              refine ⟨1839746667360528453567025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2452995556480704604756033 1839746667360528453567025)
              ·
                refine ⟨1379810000520396340175269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1839746667360528453567025 1379810000520396340175269)
                ·
                  refine ⟨258714375097574313782863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1379810000520396340175269 258714375097574313782863)
                  ·
                    rfl

theorem cell22_2267300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_2267300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267300 prefixEnd_2267300 := by exact prefixLift 2267300
  have htrace : WordTrace (prefixWord ++ tailWord_2267300) baseStart_2267300 baseEnd_2267300 := by
    simpa [prefixWord, tailWord_2267300, baseEnd_2267300] using wordTrace_append hprefix tailTrace_2267300
  have hstable : (prefixWord ++ tailWord_2267300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267300).length < 2 ^ (prefixWord ++ tailWord_2267300).sum := by decide
  have hdescent : baseEnd_2267300 < baseStart_2267300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267330 : List Nat := [3, 5, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_2267330 : Nat := 118140960795 + 2267330 * 2 ^ 59
def prefixEnd_2267330 : Nat := 4983230072969 + 3 ^ 40 * 2267330 * 2
def baseEnd_2267330 : Nat := 776153394905812863098497

theorem tailTrace_2267330 : CollatzResearch.WordTrace tailWord_2267330 prefixEnd_2267330 776153394905812863098497 := by
  unfold tailWord_2267330
  simp only [CollatzResearch.WordTrace]
  refine ⟨20674079718964528495055861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55130879250572075986815629 20674079718964528495055861)
  ·
    refine ⟨1938194973652924546411487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20674079718964528495055861 1938194973652924546411487)
    ·
      refine ⟨2907292460479386819617231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1938194973652924546411487 2907292460479386819617231)
      ·
        refine ⟨4360938690719080229425847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2907292460479386819617231 4360938690719080229425847)
        ·
          refine ⟨6541408036078620344138771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4360938690719080229425847 6541408036078620344138771)
          ·
            refine ⟨9812112054117930516208157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6541408036078620344138771 9812112054117930516208157)
            ·
              refine ⟨3679542020294223943578059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9812112054117930516208157 3679542020294223943578059)
              ·
                refine ⟨5519313030441335915367089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3679542020294223943578059 5519313030441335915367089)
                ·
                  refine ⟨4139484772831001936525317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5519313030441335915367089 4139484772831001936525317)
                  ·
                    refine ⟨776153394905812863098497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4139484772831001936525317 776153394905812863098497)
                    ·
                      rfl

theorem cell22_2267330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_2267330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267330 prefixEnd_2267330 := by exact prefixLift 2267330
  have htrace : WordTrace (prefixWord ++ tailWord_2267330) baseStart_2267330 baseEnd_2267330 := by
    simpa [prefixWord, tailWord_2267330, baseEnd_2267330] using wordTrace_append hprefix tailTrace_2267330
  have hstable : (prefixWord ++ tailWord_2267330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267330).length < 2 ^ (prefixWord ++ tailWord_2267330).sum := by decide
  have hdescent : baseEnd_2267330 < baseStart_2267330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267343 : List Nat := [1, 1, 2, 1, 1, 3, 6, 3, 1, 3]
def baseStart_2267343 : Nat := 118140960795 + 2267343 * 2 ^ 59
def prefixEnd_2267343 : Nat := 4983230072969 + 3 ^ 40 * 2267343 * 2
def baseEnd_2267343 : Nat := 776157845071485162523457

theorem tailTrace_2267343 : CollatzResearch.WordTrace tailWord_2267343 prefixEnd_2267343 776157845071485162523457 := by
  unfold tailWord_2267343
  simp only [CollatzResearch.WordTrace]
  refine ⟨82696793024811017200446683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55131195349874011466964455 82696793024811017200446683)
  ·
    refine ⟨124045189537216525800670025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82696793024811017200446683 124045189537216525800670025)
    ·
      refine ⟨93033892152912394350502519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124045189537216525800670025 93033892152912394350502519)
      ·
        refine ⟨139550838229368591525753779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93033892152912394350502519 139550838229368591525753779)
        ·
          refine ⟨209326257344052887288630669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139550838229368591525753779 209326257344052887288630669)
          ·
            refine ⟨78497346504019832733236501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209326257344052887288630669 78497346504019832733236501)
            ·
              refine ⟨3679563117375929659370461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78497346504019832733236501 3679563117375929659370461)
              ·
                refine ⟨1379836169015973622263923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3679563117375929659370461 1379836169015973622263923)
                ·
                  refine ⟨2069754253523960433395885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1379836169015973622263923 2069754253523960433395885)
                  ·
                    refine ⟨776157845071485162523457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2069754253523960433395885 776157845071485162523457)
                    ·
                      rfl

theorem cell22_2267343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 1, 3].length) (baseStart_2267343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267343 prefixEnd_2267343 := by exact prefixLift 2267343
  have htrace : WordTrace (prefixWord ++ tailWord_2267343) baseStart_2267343 baseEnd_2267343 := by
    simpa [prefixWord, tailWord_2267343, baseEnd_2267343] using wordTrace_append hprefix tailTrace_2267343
  have hstable : (prefixWord ++ tailWord_2267343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267343).length < 2 ^ (prefixWord ++ tailWord_2267343).sum := by decide
  have hdescent : baseEnd_2267343 < baseStart_2267343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267354 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 2, 5]
def baseStart_2267354 : Nat := 118140960795 + 2267354 * 2 ^ 59
def prefixEnd_2267354 : Nat := 4983230072969 + 3 ^ 40 * 2267354 * 2
def baseEnd_2267354 : Nat := 776161610596284800498423

theorem tailTrace_2267354 : CollatzResearch.WordTrace tailWord_2267354 prefixEnd_2267354 776161610596284800498423 := by
  unfold tailWord_2267354
  simp only [CollatzResearch.WordTrace]
  refine ⟨20674298556942791519774279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55131462818514110719398077 20674298556942791519774279)
  ·
    refine ⟨31011447835414187279661419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20674298556942791519774279 31011447835414187279661419)
    ·
      refine ⟨46517171753121280919492129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31011447835414187279661419 46517171753121280919492129)
      ·
        refine ⟨34887878814840960689619097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46517171753121280919492129 34887878814840960689619097)
        ·
          refine ⟨26165909111130720517214323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34887878814840960689619097 26165909111130720517214323)
          ·
            refine ⟨39248863666696080775821485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26165909111130720517214323 39248863666696080775821485)
            ·
              refine ⟨14718323875011030290933057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39248863666696080775821485 14718323875011030290933057)
              ·
                refine ⟨11038742906258272718199793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14718323875011030290933057 11038742906258272718199793)
                ·
                  refine ⟨8279057179693704538649845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11038742906258272718199793 8279057179693704538649845)
                  ·
                    refine ⟨776161610596284800498423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8279057179693704538649845 776161610596284800498423)
                    ·
                      rfl

theorem cell22_2267354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_2267354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267354 prefixEnd_2267354 := by exact prefixLift 2267354
  have htrace : WordTrace (prefixWord ++ tailWord_2267354) baseStart_2267354 baseEnd_2267354 := by
    simpa [prefixWord, tailWord_2267354, baseEnd_2267354] using wordTrace_append hprefix tailTrace_2267354
  have hstable : (prefixWord ++ tailWord_2267354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267354).length < 2 ^ (prefixWord ++ tailWord_2267354).sum := by decide
  have hdescent : baseEnd_2267354 < baseStart_2267354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267386 : List Nat := [3, 1, 1, 1, 1, 5, 1, 4, 1, 4]
def baseStart_2267386 : Nat := 118140960795 + 2267386 * 2 ^ 59
def prefixEnd_2267386 : Nat := 4983230072969 + 3 ^ 40 * 2267386 * 2
def baseEnd_2267386 : Nat := 776172564850247383698325

theorem tailTrace_2267386 : CollatzResearch.WordTrace tailWord_2267386 prefixEnd_2267386 776172564850247383698325 := by
  unfold tailWord_2267386
  simp only [CollatzResearch.WordTrace]
  refine ⟨20674590340913808886065503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55132240909103490362841341 20674590340913808886065503)
  ·
    refine ⟨31011885511370713329098255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20674590340913808886065503 31011885511370713329098255)
    ·
      refine ⟨46517828267056069993647383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31011885511370713329098255 46517828267056069993647383)
      ·
        refine ⟨69776742400584104990471075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46517828267056069993647383 69776742400584104990471075)
        ·
          refine ⟨104665113600876157485706613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69776742400584104990471075 104665113600876157485706613)
          ·
            refine ⟨9812354400082139764284995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104665113600876157485706613 9812354400082139764284995)
            ·
              refine ⟨14718531600123209646427493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9812354400082139764284995 14718531600123209646427493)
              ·
                refine ⟨2759724675023101808705155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14718531600123209646427493 2759724675023101808705155)
                ·
                  refine ⟨4139587012534652713057733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2759724675023101808705155 4139587012534652713057733)
                  ·
                    refine ⟨776172564850247383698325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4139587012534652713057733 776172564850247383698325)
                    ·
                      rfl

theorem cell22_2267386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_2267386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267386 prefixEnd_2267386 := by exact prefixLift 2267386
  have htrace : WordTrace (prefixWord ++ tailWord_2267386) baseStart_2267386 baseEnd_2267386 := by
    simpa [prefixWord, tailWord_2267386, baseEnd_2267386] using wordTrace_append hprefix tailTrace_2267386
  have hstable : (prefixWord ++ tailWord_2267386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267386).length < 2 ^ (prefixWord ++ tailWord_2267386).sum := by decide
  have hdescent : baseEnd_2267386 < baseStart_2267386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267416 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 4, 3]
def baseStart_2267416 : Nat := 118140960795 + 2267416 * 2 ^ 59
def prefixEnd_2267416 : Nat := 4983230072969 + 3 ^ 40 * 2267416 * 2
def baseEnd_2267416 : Nat := 776182834463337305448233

theorem tailTrace_2267416 : CollatzResearch.WordTrace tailWord_2267416 prefixEnd_2267416 776182834463337305448233 := by
  unfold tailWord_2267416
  simp only [CollatzResearch.WordTrace]
  refine ⟨41349727776773275333927051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55132970369031033778569401 41349727776773275333927051)
  ·
    refine ⟨62024591665159913000890577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41349727776773275333927051 62024591665159913000890577)
    ·
      refine ⟨46518443748869934750667933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62024591665159913000890577 46518443748869934750667933)
      ·
        refine ⟨17444416405826225531500475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46518443748869934750667933 17444416405826225531500475)
        ·
          refine ⟨26166624608739338297250713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17444416405826225531500475 26166624608739338297250713)
          ·
            refine ⟨19624968456554503722938035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26166624608739338297250713 19624968456554503722938035)
            ·
              refine ⟨29437452684831755584407053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19624968456554503722938035 29437452684831755584407053)
              ·
                refine ⟨11039044756811908344152645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29437452684831755584407053 11039044756811908344152645)
                ·
                  refine ⟨2069820891902232814528621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11039044756811908344152645 2069820891902232814528621)
                  ·
                    refine ⟨776182834463337305448233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2069820891902232814528621 776182834463337305448233)
                    ·
                      rfl

theorem cell22_2267416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_2267416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267416 prefixEnd_2267416 := by exact prefixLift 2267416
  have htrace : WordTrace (prefixWord ++ tailWord_2267416) baseStart_2267416 baseEnd_2267416 := by
    simpa [prefixWord, tailWord_2267416, baseEnd_2267416] using wordTrace_append hprefix tailTrace_2267416
  have hstable : (prefixWord ++ tailWord_2267416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267416).length < 2 ^ (prefixWord ++ tailWord_2267416).sum := by decide
  have hdescent : baseEnd_2267416 < baseStart_2267416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267418 : List Nat := [3, 1, 1, 3, 4, 2, 1, 1, 6]
def baseStart_2267418 : Nat := 118140960795 + 2267418 * 2 ^ 59
def prefixEnd_2267418 : Nat := 4983230072969 + 3 ^ 40 * 2267418 * 2
def baseEnd_2267418 : Nat := 258727839701403322299409

theorem tailTrace_2267418 : CollatzResearch.WordTrace tailWord_2267418 prefixEnd_2267418 258727839701403322299409 := by
  unfold tailWord_2267418
  simp only [CollatzResearch.WordTrace]
  refine ⟨20674882124884826252356727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55133018999692870006284605 20674882124884826252356727)
  ·
    refine ⟨31012323187327239378535091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20674882124884826252356727 31012323187327239378535091)
    ·
      refine ⟨46518484780990859067802637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31012323187327239378535091 46518484780990859067802637)
      ·
        refine ⟨17444431792871572150425989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46518484780990859067802637 17444431792871572150425989)
        ·
          refine ⟨3270830961163419778204873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17444431792871572150425989 3270830961163419778204873)
          ·
            refine ⟨2453123220872564833653655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3270830961163419778204873 2453123220872564833653655)
            ·
              refine ⟨3679684831308847250480483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453123220872564833653655 3679684831308847250480483)
              ·
                refine ⟨5519527246963270875720725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3679684831308847250480483 5519527246963270875720725)
                ·
                  refine ⟨258727839701403322299409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5519527246963270875720725 258727839701403322299409)
                  ·
                    rfl

theorem cell22_2267418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_2267418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267418 prefixEnd_2267418 := by exact prefixLift 2267418
  have htrace : WordTrace (prefixWord ++ tailWord_2267418) baseStart_2267418 baseEnd_2267418 := by
    simpa [prefixWord, tailWord_2267418, baseEnd_2267418] using wordTrace_append hprefix tailTrace_2267418
  have hstable : (prefixWord ++ tailWord_2267418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267418).length < 2 ^ (prefixWord ++ tailWord_2267418).sum := by decide
  have hdescent : baseEnd_2267418 < baseStart_2267418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267437 : List Nat := [1, 5, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_2267437 : Nat := 118140960795 + 2267437 * 2 ^ 59
def prefixEnd_2267437 : Nat := 4983230072969 + 3 ^ 40 * 2267437 * 2
def baseEnd_2267437 : Nat := 776190023192500250673169

theorem tailTrace_2267437 : CollatzResearch.WordTrace tailWord_2267437 prefixEnd_2267437 776190023192500250673169 := by
  unfold tailWord_2267437
  simp only [CollatzResearch.WordTrace]
  refine ⟨82700221486470471254368565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55133480990980314169579043 82700221486470471254368565)
  ·
    refine ⟨7753145764356606680097053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82700221486470471254368565 7753145764356606680097053)
    ·
      refine ⟨2907429661633727505036395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7753145764356606680097053 2907429661633727505036395)
      ·
        refine ⟨4361144492450591257554593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2907429661633727505036395 4361144492450591257554593)
        ·
          refine ⟨3270858369337943443165945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4361144492450591257554593 3270858369337943443165945)
          ·
            refine ⟨2453143777003457582374459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3270858369337943443165945 2453143777003457582374459)
            ·
              refine ⟨3679715665505186373561689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453143777003457582374459 3679715665505186373561689)
              ·
                refine ⟨2759786749128889780171267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3679715665505186373561689 2759786749128889780171267)
                ·
                  refine ⟨4139680123693334670256901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2759786749128889780171267 4139680123693334670256901)
                  ·
                    refine ⟨776190023192500250673169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4139680123693334670256901 776190023192500250673169)
                    ·
                      rfl

theorem cell22_2267437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_2267437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267437 prefixEnd_2267437 := by exact prefixLift 2267437
  have htrace : WordTrace (prefixWord ++ tailWord_2267437) baseStart_2267437 baseEnd_2267437 := by
    simpa [prefixWord, tailWord_2267437, baseEnd_2267437] using wordTrace_append hprefix tailTrace_2267437
  have hstable : (prefixWord ++ tailWord_2267437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267437).length < 2 ^ (prefixWord ++ tailWord_2267437).sum := by decide
  have hdescent : baseEnd_2267437 < baseStart_2267437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267476 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_2267476 : Nat := 118140960795 + 2267476 * 2 ^ 59
def prefixEnd_2267476 : Nat := 4983230072969 + 3 ^ 40 * 2267476 * 2
def baseEnd_2267476 : Nat := 776203373689517148948049

theorem tailTrace_2267476 : CollatzResearch.WordTrace tailWord_2267476 prefixEnd_2267476 776203373689517148948049 := by
  unfold tailWord_2267476
  simp only [CollatzResearch.WordTrace]
  refine ⟨41350821966664590457519141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55134429288886120610025521 41350821966664590457519141)
  ·
    refine ⟨7753279118749610710784839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41350821966664590457519141 7753279118749610710784839)
    ·
      refine ⟨11629918678124416066177259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7753279118749610710784839 11629918678124416066177259)
      ·
        refine ⟨17444878017186624099265889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11629918678124416066177259 17444878017186624099265889)
        ·
          refine ⟨13083658512889968074449417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17444878017186624099265889 13083658512889968074449417)
          ·
            refine ⟨9812743884667476055837063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13083658512889968074449417 9812743884667476055837063)
            ·
              refine ⟨14719115827001214083755595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9812743884667476055837063 14719115827001214083755595)
              ·
                refine ⟨22078673740501821125633393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14719115827001214083755595 22078673740501821125633393)
                ·
                  refine ⟨16559005305376365844225045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22078673740501821125633393 16559005305376365844225045)
                  ·
                    refine ⟨776203373689517148948049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16559005305376365844225045 776203373689517148948049)
                    ·
                      rfl

theorem cell22_2267476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_2267476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267476 prefixEnd_2267476 := by exact prefixLift 2267476
  have htrace : WordTrace (prefixWord ++ tailWord_2267476) baseStart_2267476 baseEnd_2267476 := by
    simpa [prefixWord, tailWord_2267476, baseEnd_2267476] using wordTrace_append hprefix tailTrace_2267476
  have hstable : (prefixWord ++ tailWord_2267476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267476).length < 2 ^ (prefixWord ++ tailWord_2267476).sum := by decide
  have hdescent : baseEnd_2267476 < baseStart_2267476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267491 : List Nat := [1, 1, 1, 5, 2, 1, 1, 5, 5]
def baseStart_2267491 : Nat := 118140960795 + 2267491 * 2 ^ 59
def prefixEnd_2267491 : Nat := 4983230072969 + 3 ^ 40 * 2267491 * 2
def baseEnd_2267491 : Nat := 258736169498687369941001

theorem tailTrace_2267491 : CollatzResearch.WordTrace tailWord_2267491 prefixEnd_2267491 258736169498687369941001 := by
  unfold tailWord_2267491
  simp only [CollatzResearch.WordTrace]
  refine ⟨82702191028274838476834327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55134794018849892317889551 82702191028274838476834327)
  ·
    refine ⟨124053286542412257715251491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82702191028274838476834327 124053286542412257715251491)
    ·
      refine ⟨186079929813618386572877237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124053286542412257715251491 186079929813618386572877237)
      ·
        refine ⟨17444993420026723741207241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 186079929813618386572877237 17444993420026723741207241)
        ·
          refine ⟨13083745065020042805905431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17444993420026723741207241 13083745065020042805905431)
          ·
            refine ⟨19625617597530064208858147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13083745065020042805905431 19625617597530064208858147)
            ·
              refine ⟨29438426396295096313287221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19625617597530064208858147 29438426396295096313287221)
              ·
                refine ⟨2759852474652665279370677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29438426396295096313287221 2759852474652665279370677)
                ·
                  refine ⟨258736169498687369941001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2759852474652665279370677 258736169498687369941001)
                  ·
                    rfl

theorem cell22_2267491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 5].length) (baseStart_2267491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267491 prefixEnd_2267491 := by exact prefixLift 2267491
  have htrace : WordTrace (prefixWord ++ tailWord_2267491) baseStart_2267491 baseEnd_2267491 := by
    simpa [prefixWord, tailWord_2267491, baseEnd_2267491] using wordTrace_append hprefix tailTrace_2267491
  have hstable : (prefixWord ++ tailWord_2267491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267491).length < 2 ^ (prefixWord ++ tailWord_2267491).sum := by decide
  have hdescent : baseEnd_2267491 < baseStart_2267491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267581 : List Nat := [1, 4, 1, 2, 2, 2, 10]
def baseStart_2267581 : Nat := 118140960795 + 2267581 * 2 ^ 59
def prefixEnd_2267581 : Nat := 4983230072969 + 3 ^ 40 * 2267581 * 2
def baseEnd_2267581 : Nat := 28749604345753032410101

theorem tailTrace_2267581 : CollatzResearch.WordTrace tailWord_2267581 prefixEnd_2267581 28749604345753032410101 := by
  unfold tailWord_2267581
  simp only [CollatzResearch.WordTrace]
  refine ⟨82705473597948783847610597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55136982398632522565073731 82705473597948783847610597)
  ·
    refine ⟨15507276299615396971426987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82705473597948783847610597 15507276299615396971426987)
    ·
      refine ⟨23260914449423095457140481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15507276299615396971426987 23260914449423095457140481)
      ·
        refine ⟨17445685837067321592855361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23260914449423095457140481 17445685837067321592855361)
        ·
          refine ⟨13084264377800491194641521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17445685837067321592855361 13084264377800491194641521)
          ·
            refine ⟨9813198283350368395981141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13084264377800491194641521 9813198283350368395981141)
            ·
              refine ⟨28749604345753032410101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9813198283350368395981141 28749604345753032410101)
              ·
                rfl

theorem cell22_2267581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 10].length) (baseStart_2267581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267581 prefixEnd_2267581 := by exact prefixLift 2267581
  have htrace : WordTrace (prefixWord ++ tailWord_2267581) baseStart_2267581 baseEnd_2267581 := by
    simpa [prefixWord, tailWord_2267581, baseEnd_2267581] using wordTrace_append hprefix tailTrace_2267581
  have hstable : (prefixWord ++ tailWord_2267581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267581).length < 2 ^ (prefixWord ++ tailWord_2267581).sum := by decide
  have hdescent : baseEnd_2267581 < baseStart_2267581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267658 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 2, 5]
def baseStart_2267658 : Nat := 118140960795 + 2267658 * 2 ^ 59
def prefixEnd_2267658 : Nat := 4983230072969 + 3 ^ 40 * 2267658 * 2
def baseEnd_2267658 : Nat := 776265676008929340897491

theorem tailTrace_2267658 : CollatzResearch.WordTrace tailWord_2267658 prefixEnd_2267658 776265676008929340897491 := by
  unfold tailWord_2267658
  simp only [CollatzResearch.WordTrace]
  refine ⟨20677070504667456499540907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55138854679113217332109085 20677070504667456499540907)
  ·
    refine ⟨31015605757001184749311361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20677070504667456499540907 31015605757001184749311361)
    ·
      refine ⟨23261704317750888561983521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31015605757001184749311361 23261704317750888561983521)
      ·
        refine ⟨17446278238313166421487641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23261704317750888561983521 17446278238313166421487641)
        ·
          refine ⟨13084708678734874816115731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17446278238313166421487641 13084708678734874816115731)
          ·
            refine ⟨19627063018102312224173597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13084708678734874816115731 19627063018102312224173597)
            ·
              refine ⟨7360148631788367084065099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19627063018102312224173597 7360148631788367084065099)
              ·
                refine ⟨11040222947682550626097649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7360148631788367084065099 11040222947682550626097649)
                ·
                  refine ⟨8280167210761912969573237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11040222947682550626097649 8280167210761912969573237)
                  ·
                    refine ⟨776265676008929340897491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8280167210761912969573237 776265676008929340897491)
                    ·
                      rfl

theorem cell22_2267658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_2267658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267658 prefixEnd_2267658 := by exact prefixLift 2267658
  have htrace : WordTrace (prefixWord ++ tailWord_2267658) baseStart_2267658 baseEnd_2267658 := by
    simpa [prefixWord, tailWord_2267658, baseEnd_2267658] using wordTrace_append hprefix tailTrace_2267658
  have hstable : (prefixWord ++ tailWord_2267658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267658).length < 2 ^ (prefixWord ++ tailWord_2267658).sum := by decide
  have hdescent : baseEnd_2267658 < baseStart_2267658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267694 : List Nat := [4, 1, 3, 1, 4, 1, 1, 2, 5]
def baseStart_2267694 : Nat := 118140960795 + 2267694 * 2 ^ 59
def prefixEnd_2267694 : Nat := 4983230072969 + 3 ^ 40 * 2267694 * 2
def baseEnd_2267694 : Nat := 258759333181545748999127

theorem tailTrace_2267694 : CollatzResearch.WordTrace tailWord_2267694 prefixEnd_2267694 258759333181545748999127 := by
  unfold tailWord_2267694
  simp only [CollatzResearch.WordTrace]
  refine ⟨10338699380817425518309267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55139730031026269430982757 10338699380817425518309267)
  ·
    refine ⟨15508049071226138277463901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10338699380817425518309267 15508049071226138277463901)
    ·
      refine ⟨5815518401709801854048963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15508049071226138277463901 5815518401709801854048963)
      ·
        refine ⟨8723277602564702781073445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5815518401709801854048963 8723277602564702781073445)
        ·
          refine ⟨1635614550480881771451271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8723277602564702781073445 1635614550480881771451271)
          ·
            refine ⟨2453421825721322657176907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1635614550480881771451271 2453421825721322657176907)
            ·
              refine ⟨3680132738581983985765361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453421825721322657176907 3680132738581983985765361)
              ·
                refine ⟨2760099553936487989324021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3680132738581983985765361 2760099553936487989324021)
                ·
                  refine ⟨258759333181545748999127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2760099553936487989324021 258759333181545748999127)
                  ·
                    rfl

theorem cell22_2267694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_2267694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267694 prefixEnd_2267694 := by exact prefixLift 2267694
  have htrace : WordTrace (prefixWord ++ tailWord_2267694) baseStart_2267694 baseEnd_2267694 := by
    simpa [prefixWord, tailWord_2267694, baseEnd_2267694] using wordTrace_append hprefix tailTrace_2267694
  have hstable : (prefixWord ++ tailWord_2267694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267694).length < 2 ^ (prefixWord ++ tailWord_2267694).sum := by decide
  have hdescent : baseEnd_2267694 < baseStart_2267694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267705 : List Nat := [1, 2, 1, 5, 1, 1, 1, 6, 4]
def baseStart_2267705 : Nat := 118140960795 + 2267705 * 2 ^ 59
def prefixEnd_2267705 : Nat := 4983230072969 + 3 ^ 40 * 2267705 * 2
def baseEnd_2267705 : Nat := 258760588356478961657449

theorem tailTrace_2267705 : CollatzResearch.WordTrace tailWord_2267705 prefixEnd_2267705 258760588356478961657449 := by
  unfold tailWord_2267705
  simp only [CollatzResearch.WordTrace]
  refine ⟨82709996249499553025124569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55139997499666368683416379 82709996249499553025124569)
  ·
    refine ⟨62032497187124664768843427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82709996249499553025124569 62032497187124664768843427)
    ·
      refine ⟨93048745780686997153265141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62032497187124664768843427 93048745780686997153265141)
      ·
        refine ⟨8723319916939405983118607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93048745780686997153265141 8723319916939405983118607)
        ·
          refine ⟨13084979875409108974677911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8723319916939405983118607 13084979875409108974677911)
          ·
            refine ⟨19627469813113663462016867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13084979875409108974677911 19627469813113663462016867)
            ·
              refine ⟨29441204719670495193025301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19627469813113663462016867 29441204719670495193025301)
              ·
                refine ⟨1380056471234554462173061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29441204719670495193025301 1380056471234554462173061)
                ·
                  refine ⟨258760588356478961657449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1380056471234554462173061 258760588356478961657449)
                  ·
                    rfl

theorem cell22_2267705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 4].length) (baseStart_2267705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267705 prefixEnd_2267705 := by exact prefixLift 2267705
  have htrace : WordTrace (prefixWord ++ tailWord_2267705) baseStart_2267705 baseEnd_2267705 := by
    simpa [prefixWord, tailWord_2267705, baseEnd_2267705] using wordTrace_append hprefix tailTrace_2267705
  have hstable : (prefixWord ++ tailWord_2267705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267705).length < 2 ^ (prefixWord ++ tailWord_2267705).sum := by decide
  have hdescent : baseEnd_2267705 < baseStart_2267705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267720 : List Nat := [2, 1, 3, 1, 1, 1, 1, 7, 2, 3]
def baseStart_2267720 : Nat := 118140960795 + 2267720 * 2 ^ 59
def prefixEnd_2267720 : Nat := 4983230072969 + 3 ^ 40 * 2267720 * 2
def baseEnd_2267720 : Nat := 776286899875981845847301

theorem tailTrace_2267720 : CollatzResearch.WordTrace tailWord_2267720 prefixEnd_2267720 776286899875981845847301 := by
  unfold tailWord_2267720
  simp only [CollatzResearch.WordTrace]
  refine ⟨41355271672222605293460307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55140362229630140391280409 41355271672222605293460307)
  ·
    refine ⟨62032907508333907940190461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41355271672222605293460307 62032907508333907940190461)
    ·
      refine ⟨23262340315625215477571423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62032907508333907940190461 23262340315625215477571423)
      ·
        refine ⟨34893510473437823216357135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23262340315625215477571423 34893510473437823216357135)
        ·
          refine ⟨52340265710156734824535703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34893510473437823216357135 52340265710156734824535703)
          ·
            refine ⟨78510398565235102236803555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52340265710156734824535703 78510398565235102236803555)
            ·
              refine ⟨117765597847852653355205333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78510398565235102236803555 117765597847852653355205333)
              ·
                refine ⟨2760131199559046563012625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 117765597847852653355205333 2760131199559046563012625)
                ·
                  refine ⟨2070098399669284922259469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2760131199559046563012625 2070098399669284922259469)
                  ·
                    refine ⟨776286899875981845847301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2070098399669284922259469 776286899875981845847301)
                    ·
                      rfl

theorem cell22_2267720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_2267720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267720 prefixEnd_2267720 := by exact prefixLift 2267720
  have htrace : WordTrace (prefixWord ++ tailWord_2267720) baseStart_2267720 baseEnd_2267720 := by
    simpa [prefixWord, tailWord_2267720, baseEnd_2267720] using wordTrace_append hprefix tailTrace_2267720
  have hstable : (prefixWord ++ tailWord_2267720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267720).length < 2 ^ (prefixWord ++ tailWord_2267720).sum := by decide
  have hdescent : baseEnd_2267720 < baseStart_2267720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267752 : List Nat := [2, 1, 4, 3, 2, 1, 1, 2, 2, 4]
def baseStart_2267752 : Nat := 118140960795 + 2267752 * 2 ^ 59
def prefixEnd_2267752 : Nat := 4983230072969 + 3 ^ 40 * 2267752 * 2
def baseEnd_2267752 : Nat := 776297854129944429047203

theorem tailTrace_2267752 : CollatzResearch.WordTrace tailWord_2267752 prefixEnd_2267752 776297854129944429047203 := by
  unfold tailWord_2267752
  simp only [CollatzResearch.WordTrace]
  refine ⟨41355855240164640026042755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55141140320219520034723673 41355855240164640026042755)
  ·
    refine ⟨62033782860246960039064133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41355855240164640026042755 62033782860246960039064133)
    ·
      refine ⟨11631334286296305007324525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62033782860246960039064133 11631334286296305007324525)
      ·
        refine ⟨4361750357361114377746697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11631334286296305007324525 4361750357361114377746697)
        ·
          refine ⟨3271312768020835783310023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4361750357361114377746697 3271312768020835783310023)
          ·
            refine ⟨4906969152031253674965035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3271312768020835783310023 4906969152031253674965035)
            ·
              refine ⟨7360453728046880512447553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4906969152031253674965035 7360453728046880512447553)
              ·
                refine ⟨5520340296035160384335665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7360453728046880512447553 5520340296035160384335665)
                ·
                  refine ⟨4140255222026370288251749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5520340296035160384335665 4140255222026370288251749)
                  ·
                    refine ⟨776297854129944429047203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4140255222026370288251749 776297854129944429047203)
                    ·
                      rfl

theorem cell22_2267752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_2267752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267752 prefixEnd_2267752 := by exact prefixLift 2267752
  have htrace : WordTrace (prefixWord ++ tailWord_2267752) baseStart_2267752 baseEnd_2267752 := by
    simpa [prefixWord, tailWord_2267752, baseEnd_2267752] using wordTrace_append hprefix tailTrace_2267752
  have hstable : (prefixWord ++ tailWord_2267752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267752).length < 2 ^ (prefixWord ++ tailWord_2267752).sum := by decide
  have hdescent : baseEnd_2267752 < baseStart_2267752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267840 : List Nat := [2, 1, 1, 2, 4, 3, 1, 2, 6]
def baseStart_2267840 : Nat := 118140960795 + 2267840 * 2 ^ 59
def prefixEnd_2267840 : Nat := 4983230072969 + 3 ^ 40 * 2267840 * 2
def baseEnd_2267840 : Nat := 258775992776113844282311

theorem tailTrace_2267840 : CollatzResearch.WordTrace tailWord_2267840 prefixEnd_2267840 258775992776113844282311 := by
  unfold tailWord_2267840
  simp only [CollatzResearch.WordTrace]
  refine ⟨41357460052005235540644487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55143280069340314054192649 41357460052005235540644487)
  ·
    refine ⟨62036190078007853310966731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41357460052005235540644487 62036190078007853310966731)
    ·
      refine ⟨93054285117011779966450097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62036190078007853310966731 93054285117011779966450097)
      ·
        refine ⟨69790713837758834974837573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93054285117011779966450097 69790713837758834974837573)
        ·
          refine ⟨13085758844579781557782045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69790713837758834974837573 13085758844579781557782045)
          ·
            refine ⟨4907159566717418084168267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13085758844579781557782045 4907159566717418084168267)
            ·
              refine ⟨7360739350076127126252401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4907159566717418084168267 7360739350076127126252401)
              ·
                refine ⟨5520554512557095344689301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7360739350076127126252401 5520554512557095344689301)
                ·
                  refine ⟨258775992776113844282311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5520554512557095344689301 258775992776113844282311)
                  ·
                    rfl

theorem cell22_2267840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 6].length) (baseStart_2267840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267840 prefixEnd_2267840 := by exact prefixLift 2267840
  have htrace : WordTrace (prefixWord ++ tailWord_2267840) baseStart_2267840 baseEnd_2267840 := by
    simpa [prefixWord, tailWord_2267840, baseEnd_2267840] using wordTrace_append hprefix tailTrace_2267840
  have hstable : (prefixWord ++ tailWord_2267840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267840).length < 2 ^ (prefixWord ++ tailWord_2267840).sum := by decide
  have hdescent : baseEnd_2267840 < baseStart_2267840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267857 : List Nat := [1, 2, 2, 1, 2, 3, 4, 3, 4]
def baseStart_2267857 : Nat := 118140960795 + 2267857 * 2 ^ 59
def prefixEnd_2267857 : Nat := 4983230072969 + 3 ^ 40 * 2267857 * 2
def baseEnd_2267857 : Nat := 258777932591919718390627

theorem tailTrace_2267857 : CollatzResearch.WordTrace tailWord_2267857 prefixEnd_2267857 258777932591919718390627 := by
  unfold tailWord_2267857
  simp only [CollatzResearch.WordTrace]
  refine ⟨82715540144948882984657825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55143693429965921989771883 82715540144948882984657825)
  ·
    refine ⟨62036655108711662238493369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82715540144948882984657825 62036655108711662238493369)
    ·
      refine ⟨46527491331533746678870027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62036655108711662238493369 46527491331533746678870027)
      ·
        refine ⟨69791236997300620018305041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46527491331533746678870027 69791236997300620018305041)
        ·
          refine ⟨52343427747975465013728781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69791236997300620018305041 52343427747975465013728781)
          ·
            refine ⟨19628785405490799380148293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52343427747975465013728781 19628785405490799380148293)
            ·
              refine ⟨3680397263529524883777805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19628785405490799380148293 3680397263529524883777805)
              ·
                refine ⟨1380148973823571831416677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3680397263529524883777805 1380148973823571831416677)
                ·
                  refine ⟨258777932591919718390627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1380148973823571831416677 258777932591919718390627)
                  ·
                    rfl

theorem cell22_2267857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 4].length) (baseStart_2267857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267857 prefixEnd_2267857 := by exact prefixLift 2267857
  have htrace : WordTrace (prefixWord ++ tailWord_2267857) baseStart_2267857 baseEnd_2267857 := by
    simpa [prefixWord, tailWord_2267857, baseEnd_2267857] using wordTrace_append hprefix tailTrace_2267857
  have hstable : (prefixWord ++ tailWord_2267857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267857).length < 2 ^ (prefixWord ++ tailWord_2267857).sum := by decide
  have hdescent : baseEnd_2267857 < baseStart_2267857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267885 : List Nat := [1, 5, 1, 2, 1, 1, 2, 9]
def baseStart_2267885 : Nat := 118140960795 + 2267885 * 2 ^ 59
def prefixEnd_2267885 : Nat := 4983230072969 + 3 ^ 40 * 2267885 * 2
def baseEnd_2267885 : Nat := 86260375860886268385755

theorem tailTrace_2267885 : CollatzResearch.WordTrace tailWord_2267885 prefixEnd_2267885 86260375860886268385755 := by
  unfold tailWord_2267885
  simp only [CollatzResearch.WordTrace]
  refine ⟨82716561388847443766677109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55144374259231629177784739 82716561388847443766677109)
  ·
    refine ⟨7754677630204447853125979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82716561388847443766677109 7754677630204447853125979)
    ·
      refine ⟨11632016445306671779688969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7754677630204447853125979 11632016445306671779688969)
      ·
        refine ⟨8724012333980003834766727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11632016445306671779688969 8724012333980003834766727)
        ·
          refine ⟨13086018500970005752150091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8724012333980003834766727 13086018500970005752150091)
          ·
            refine ⟨19629027751455008628225137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13086018500970005752150091 19629027751455008628225137)
            ·
              refine ⟨14721770813591256471168853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19629027751455008628225137 14721770813591256471168853)
              ·
                refine ⟨86260375860886268385755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14721770813591256471168853 86260375860886268385755)
                ·
                  rfl

theorem cell22_2267885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 9].length) (baseStart_2267885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267885 prefixEnd_2267885 := by exact prefixLift 2267885
  have htrace : WordTrace (prefixWord ++ tailWord_2267885) baseStart_2267885 baseEnd_2267885 := by
    simpa [prefixWord, tailWord_2267885, baseEnd_2267885] using wordTrace_append hprefix tailTrace_2267885
  have hstable : (prefixWord ++ tailWord_2267885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267885).length < 2 ^ (prefixWord ++ tailWord_2267885).sum := by decide
  have hdescent : baseEnd_2267885 < baseStart_2267885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267889 : List Nat := [1, 2, 2, 2, 2, 2, 5, 1, 2, 3]
def baseStart_2267889 : Nat := 118140960795 + 2267889 * 2 ^ 59
def prefixEnd_2267889 : Nat := 4983230072969 + 3 ^ 40 * 2267889 * 2
def baseEnd_2267889 : Nat := 776344752029721738371783

theorem tailTrace_2267889 : CollatzResearch.WordTrace tailWord_2267889 prefixEnd_2267889 776344752029721738371783 := by
  unfold tailWord_2267889
  simp only [CollatzResearch.WordTrace]
  refine ⟨82716707280832952449822721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55144471520555301633215147 82716707280832952449822721)
  ·
    refine ⟨62037530460624714337367041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82716707280832952449822721 62037530460624714337367041)
    ·
      refine ⟨46528147845468535753025281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62037530460624714337367041 46528147845468535753025281)
      ·
        refine ⟨34896110884101401814768961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46528147845468535753025281 34896110884101401814768961)
        ·
          refine ⟨26172083163076051361076721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34896110884101401814768961 26172083163076051361076721)
          ·
            refine ⟨19629062372307038520807541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26172083163076051361076721 19629062372307038520807541)
            ·
              refine ⟨1840224597403784861325707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19629062372307038520807541 1840224597403784861325707)
              ·
                refine ⟨2760336896105677291988561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840224597403784861325707 2760336896105677291988561)
                ·
                  refine ⟨2070252672079257968991421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2760336896105677291988561 2070252672079257968991421)
                  ·
                    refine ⟨776344752029721738371783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2070252672079257968991421 776344752029721738371783)
                    ·
                      rfl

theorem cell22_2267889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 2, 3].length) (baseStart_2267889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267889 prefixEnd_2267889 := by exact prefixLift 2267889
  have htrace : WordTrace (prefixWord ++ tailWord_2267889) baseStart_2267889 baseEnd_2267889 := by
    simpa [prefixWord, tailWord_2267889, baseEnd_2267889] using wordTrace_append hprefix tailTrace_2267889
  have hstable : (prefixWord ++ tailWord_2267889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267889).length < 2 ^ (prefixWord ++ tailWord_2267889).sum := by decide
  have hdescent : baseEnd_2267889 < baseStart_2267889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267893 : List Nat := [1, 3, 6, 1, 1, 1, 2, 2, 1, 4]
def baseStart_2267893 : Nat := 118140960795 + 2267893 * 2 ^ 59
def prefixEnd_2267893 : Nat := 4983230072969 + 3 ^ 40 * 2267893 * 2
def baseEnd_2267893 : Nat := 776346121311467061271771

theorem tailTrace_2267893 : CollatzResearch.WordTrace tailWord_2267893 prefixEnd_2267893 776346121311467061271771 := by
  unfold tailWord_2267893
  simp only [CollatzResearch.WordTrace]
  refine ⟨82716853172818461132968333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55144568781878974088645555 82716853172818461132968333)
  ·
    refine ⟨31018819939806922924863125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82716853172818461132968333 31018819939806922924863125)
    ·
      refine ⟨1454007184678449512102959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31018819939806922924863125 1454007184678449512102959)
      ·
        refine ⟨2181010777017674268154439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1454007184678449512102959 2181010777017674268154439)
        ·
          refine ⟨3271516165526511402231659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2181010777017674268154439 3271516165526511402231659)
          ·
            refine ⟨4907274248289767103347489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3271516165526511402231659 4907274248289767103347489)
            ·
              refine ⟨3680455686217325327510617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4907274248289767103347489 3680455686217325327510617)
              ·
                refine ⟨2760341764662993995632963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3680455686217325327510617 2760341764662993995632963)
                ·
                  refine ⟨4140512646994490993449445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2760341764662993995632963 4140512646994490993449445)
                  ·
                    refine ⟨776346121311467061271771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4140512646994490993449445 776346121311467061271771)
                    ·
                      rfl

theorem cell22_2267893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_2267893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267893 prefixEnd_2267893 := by exact prefixLift 2267893
  have htrace : WordTrace (prefixWord ++ tailWord_2267893) baseStart_2267893 baseEnd_2267893 := by
    simpa [prefixWord, tailWord_2267893, baseEnd_2267893] using wordTrace_append hprefix tailTrace_2267893
  have hstable : (prefixWord ++ tailWord_2267893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267893).length < 2 ^ (prefixWord ++ tailWord_2267893).sum := by decide
  have hdescent : baseEnd_2267893 < baseStart_2267893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267902 : List Nat := [4, 2, 2, 1, 2, 2, 1, 8]
def baseStart_2267902 : Nat := 118140960795 + 2267902 * 2 ^ 59
def prefixEnd_2267902 : Nat := 4983230072969 + 3 ^ 40 * 2267902 * 2
def baseEnd_2267902 : Nat := 86261022466154893088527

theorem tailTrace_2267902 : CollatzResearch.WordTrace tailWord_2267902 prefixEnd_2267902 86261022466154893088527 := by
  unfold tailWord_2267902
  simp only [CollatzResearch.WordTrace]
  refine ⟨10339647678723231958755745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55144787619857237113363973 10339647678723231958755745)
  ·
    refine ⟨7754735759042423969066809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10339647678723231958755745 7754735759042423969066809)
    ·
      refine ⟨5816051819281817976800107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7754735759042423969066809 5816051819281817976800107)
      ·
        refine ⟨8724077728922726965200161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5816051819281817976800107 8724077728922726965200161)
        ·
          refine ⟨6543058296692045223900121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8724077728922726965200161 6543058296692045223900121)
          ·
            refine ⟨4907293722519033917925091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6543058296692045223900121 4907293722519033917925091)
            ·
              refine ⟨7360940583778550876887637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4907293722519033917925091 7360940583778550876887637)
              ·
                refine ⟨86261022466154893088527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7360940583778550876887637 86261022466154893088527)
                ·
                  rfl

theorem cell22_2267902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_2267902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267902 prefixEnd_2267902 := by exact prefixLift 2267902
  have htrace : WordTrace (prefixWord ++ tailWord_2267902) baseStart_2267902 baseEnd_2267902 := by
    simpa [prefixWord, tailWord_2267902, baseEnd_2267902] using wordTrace_append hprefix tailTrace_2267902
  have hstable : (prefixWord ++ tailWord_2267902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267902).length < 2 ^ (prefixWord ++ tailWord_2267902).sum := by decide
  have hdescent : baseEnd_2267902 < baseStart_2267902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267930 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 7]
def baseStart_2267930 : Nat := 118140960795 + 2267930 * 2 ^ 59
def prefixEnd_2267930 : Nat := 4983230072969 + 3 ^ 40 * 2267930 * 2
def baseEnd_2267930 : Nat := 258786262389203766032219

theorem tailTrace_2267930 : CollatzResearch.WordTrace tailWord_2267930 prefixEnd_2267930 258786262389203766032219 := by
  unfold tailWord_2267930
  simp only [CollatzResearch.WordTrace]
  refine ⟨20679550668421104113016311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55145468449122944301376829 20679550668421104113016311)
  ·
    refine ⟨31019326002631656169524467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20679550668421104113016311 31019326002631656169524467)
    ·
      refine ⟨46528989003947484254286701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31019326002631656169524467 46528989003947484254286701)
      ·
        refine ⟨17448370876480306595357513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46528989003947484254286701 17448370876480306595357513)
        ·
          refine ⟨13086278157360229946518135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17448370876480306595357513 13086278157360229946518135)
          ·
            refine ⟨19629417236040344919777203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13086278157360229946518135 19629417236040344919777203)
            ·
              refine ⟨29444125854060517379665805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19629417236040344919777203 29444125854060517379665805)
              ·
                refine ⟨11041547195272694017374677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29444125854060517379665805 11041547195272694017374677)
                ·
                  refine ⟨258786262389203766032219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11041547195272694017374677 258786262389203766032219)
                  ·
                    rfl

theorem cell22_2267930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_2267930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267930 prefixEnd_2267930 := by exact prefixLift 2267930
  have htrace : WordTrace (prefixWord ++ tailWord_2267930) baseStart_2267930 baseEnd_2267930 := by
    simpa [prefixWord, tailWord_2267930, baseEnd_2267930] using wordTrace_append hprefix tailTrace_2267930
  have hstable : (prefixWord ++ tailWord_2267930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267930).length < 2 ^ (prefixWord ++ tailWord_2267930).sum := by decide
  have hdescent : baseEnd_2267930 < baseStart_2267930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267981 : List Nat := [1, 6, 1, 2, 2, 1, 2, 2, 5]
def baseStart_2267981 : Nat := 118140960795 + 2267981 * 2 ^ 59
def prefixEnd_2267981 : Nat := 4983230072969 + 3 ^ 40 * 2267981 * 2
def baseEnd_2267981 : Nat := 258792081836621388357167

theorem tailTrace_2267981 : CollatzResearch.WordTrace tailWord_2267981 prefixEnd_2267981 258792081836621388357167 := by
  unfold tailWord_2267981
  simp only [CollatzResearch.WordTrace]
  refine ⟨82720062796499652162171797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55146708530999768108114531 82720062796499652162171797)
  ·
    refine ⟨3877502943585921195101803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 82720062796499652162171797 3877502943585921195101803)
    ·
      refine ⟨5816254415378881792652705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3877502943585921195101803 5816254415378881792652705)
      ·
        refine ⟨4362190811534161344489529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5816254415378881792652705 4362190811534161344489529)
        ·
          refine ⟨3271643108650621008367147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4362190811534161344489529 3271643108650621008367147)
          ·
            refine ⟨4907464662975931512550721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3271643108650621008367147 4907464662975931512550721)
            ·
              refine ⟨3680598497231948634413041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4907464662975931512550721 3680598497231948634413041)
              ·
                refine ⟨2760448872923961475809781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3680598497231948634413041 2760448872923961475809781)
                ·
                  refine ⟨258792081836621388357167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2760448872923961475809781 258792081836621388357167)
                  ·
                    rfl

theorem cell22_2267981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_2267981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267981 prefixEnd_2267981 := by exact prefixLift 2267981
  have htrace : WordTrace (prefixWord ++ tailWord_2267981) baseStart_2267981 baseEnd_2267981 := by
    simpa [prefixWord, tailWord_2267981, baseEnd_2267981] using wordTrace_append hprefix tailTrace_2267981
  have hstable : (prefixWord ++ tailWord_2267981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267981).length < 2 ^ (prefixWord ++ tailWord_2267981).sum := by decide
  have hdescent : baseEnd_2267981 < baseStart_2267981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267985 : List Nat := [1, 2, 2, 1, 7, 1, 2, 2, 1, 3]
def baseStart_2267985 : Nat := 118140960795 + 2267985 * 2 ^ 59
def prefixEnd_2267985 : Nat := 4983230072969 + 3 ^ 40 * 2267985 * 2
def baseEnd_2267985 : Nat := 776377614791609487971489

theorem tailTrace_2267985 : CollatzResearch.WordTrace tailWord_2267985 prefixEnd_2267985 776377614791609487971489 := by
  unfold tailWord_2267985
  simp only [CollatzResearch.WordTrace]
  refine ⟨82720208688485160845317409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55146805792323440563544939 82720208688485160845317409)
  ·
    refine ⟨62040156516363870633988057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82720208688485160845317409 62040156516363870633988057)
    ·
      refine ⟨46530117387272902975491043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62040156516363870633988057 46530117387272902975491043)
      ·
        refine ⟨69795176080909354463236565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46530117387272902975491043 69795176080909354463236565)
        ·
          refine ⟨1635824439396312995232107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 69795176080909354463236565 1635824439396312995232107)
          ·
            refine ⟨2453736659094469492848161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1635824439396312995232107 2453736659094469492848161)
            ·
              refine ⟨1840302494320852119636121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2453736659094469492848161 1840302494320852119636121)
              ·
                refine ⟨1380226870740639089727091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1840302494320852119636121 1380226870740639089727091)
                ·
                  refine ⟨2070340306110958634590637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1380226870740639089727091 2070340306110958634590637)
                  ·
                    refine ⟨776377614791609487971489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2070340306110958634590637 776377614791609487971489)
                    ·
                      rfl

theorem cell22_2267985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 1, 3].length) (baseStart_2267985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2267985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2267985 prefixEnd_2267985 := by exact prefixLift 2267985
  have htrace : WordTrace (prefixWord ++ tailWord_2267985) baseStart_2267985 baseEnd_2267985 := by
    simpa [prefixWord, tailWord_2267985, baseEnd_2267985] using wordTrace_append hprefix tailTrace_2267985
  have hstable : (prefixWord ++ tailWord_2267985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267985).length < 2 ^ (prefixWord ++ tailWord_2267985).sum := by decide
  have hdescent : baseEnd_2267985 < baseStart_2267985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268007 : List Nat := [1, 1, 5, 1, 2, 2, 1, 3, 1, 5]
def baseStart_2268007 : Nat := 118140960795 + 2268007 * 2 ^ 59
def prefixEnd_2268007 : Nat := 4983230072969 + 3 ^ 40 * 2268007 * 2
def baseEnd_2268007 : Nat := 776385145841208763921421

theorem tailTrace_2268007 : CollatzResearch.WordTrace tailWord_2268007 prefixEnd_2268007 776385145841208763921421 := by
  unfold tailWord_2268007
  simp only [CollatzResearch.WordTrace]
  refine ⟨82721011094405458602618275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55147340729603639068412183 82721011094405458602618275)
  ·
    refine ⟨124081516641608187903927413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82721011094405458602618275 124081516641608187903927413)
    ·
      refine ⟨11632642185150767615993195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124081516641608187903927413 11632642185150767615993195)
      ·
        refine ⟨17448963277726151423989793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11632642185150767615993195 17448963277726151423989793)
        ·
          refine ⟨13086722458294613567992345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17448963277726151423989793 13086722458294613567992345)
          ·
            refine ⟨9815041843720960175994259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13086722458294613567992345 9815041843720960175994259)
            ·
              refine ⟨14722562765581440263991389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9815041843720960175994259 14722562765581440263991389)
              ·
                refine ⟨5520961037093040098996771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14722562765581440263991389 5520961037093040098996771)
                ·
                  refine ⟨8281441555639560148495157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5520961037093040098996771 8281441555639560148495157)
                  ·
                    refine ⟨776385145841208763921421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8281441555639560148495157 776385145841208763921421)
                    ·
                      rfl

theorem cell22_2268007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_2268007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268007 prefixEnd_2268007 := by exact prefixLift 2268007
  have htrace : WordTrace (prefixWord ++ tailWord_2268007) baseStart_2268007 baseEnd_2268007 := by
    simpa [prefixWord, tailWord_2268007, baseEnd_2268007] using wordTrace_append hprefix tailTrace_2268007
  have hstable : (prefixWord ++ tailWord_2268007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268007).length < 2 ^ (prefixWord ++ tailWord_2268007).sum := by decide
  have hdescent : baseEnd_2268007 < baseStart_2268007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268041 : List Nat := [1, 2, 1, 1, 5, 4, 1, 2, 2, 3]
def baseStart_2268041 : Nat := 118140960795 + 2268041 * 2 ^ 59
def prefixEnd_2268041 : Nat := 4983230072969 + 3 ^ 40 * 2268041 * 2
def baseEnd_2268041 : Nat := 776396784736044008571317

theorem tailTrace_2268041 : CollatzResearch.WordTrace tailWord_2268041 prefixEnd_2268041 776396784736044008571317 := by
  unfold tailWord_2268041
  simp only [CollatzResearch.WordTrace]
  refine ⟨82722251176282282409355977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55148167450854854939570651 82722251176282282409355977)
  ·
    refine ⟨62041688382211711807016983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82722251176282282409355977 62041688382211711807016983)
    ·
      refine ⟨93062532573317567710525475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62041688382211711807016983 93062532573317567710525475)
      ·
        refine ⟨139593798859976351565788213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93062532573317567710525475 139593798859976351565788213)
        ·
          refine ⟨13086918643122782959292645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 139593798859976351565788213 13086918643122782959292645)
          ·
            refine ⟨2453797245585521804867371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13086918643122782959292645 2453797245585521804867371)
            ·
              refine ⟨3680695868378282707301057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453797245585521804867371 3680695868378282707301057)
              ·
                refine ⟨2760521901283712030475793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3680695868378282707301057 2760521901283712030475793)
                ·
                  refine ⟨2070391425962784022856845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2760521901283712030475793 2070391425962784022856845)
                  ·
                    refine ⟨776396784736044008571317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2070391425962784022856845 776396784736044008571317)
                    ·
                      rfl

theorem cell22_2268041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 3].length) (baseStart_2268041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268041 prefixEnd_2268041 := by exact prefixLift 2268041
  have htrace : WordTrace (prefixWord ++ tailWord_2268041) baseStart_2268041 baseEnd_2268041 := by
    simpa [prefixWord, tailWord_2268041, baseEnd_2268041] using wordTrace_append hprefix tailTrace_2268041
  have hstable : (prefixWord ++ tailWord_2268041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268041).length < 2 ^ (prefixWord ++ tailWord_2268041).sum := by decide
  have hdescent : baseEnd_2268041 < baseStart_2268041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268058 : List Nat := [3, 1, 1, 4, 3, 1, 3, 1, 2, 3]
def baseStart_2268058 : Nat := 118140960795 + 2268058 * 2 ^ 59
def prefixEnd_2268058 : Nat := 4983230072969 + 3 ^ 40 * 2268058 * 2
def baseEnd_2268058 : Nat := 776402604183461630896265

theorem tailTrace_2268058 : CollatzResearch.WordTrace tailWord_2268058 prefixEnd_2268058 776402604183461630896265 := by
  unfold tailWord_2268058
  simp only [CollatzResearch.WordTrace]
  refine ⟨20680717804305173578181207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55148580811480462875149885 20680717804305173578181207)
  ·
    refine ⟨31021076706457760367271811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20680717804305173578181207 31021076706457760367271811)
    ·
      refine ⟨46531615059686640550907717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31021076706457760367271811 46531615059686640550907717)
      ·
        refine ⟨8724677823691245103295197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46531615059686640550907717 8724677823691245103295197)
        ·
          refine ⟨3271754183884216913735699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8724677823691245103295197 3271754183884216913735699)
          ·
            refine ⟨4907631275826325370603549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3271754183884216913735699 4907631275826325370603549)
            ·
              refine ⟨1840361728434872013976331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4907631275826325370603549 1840361728434872013976331)
              ·
                refine ⟨2760542592652308020964497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840361728434872013976331 2760542592652308020964497)
                ·
                  refine ⟨2070406944489231015723373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2760542592652308020964497 2070406944489231015723373)
                  ·
                    refine ⟨776402604183461630896265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2070406944489231015723373 776402604183461630896265)
                    ·
                      rfl

theorem cell22_2268058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 2, 3].length) (baseStart_2268058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268058 prefixEnd_2268058 := by exact prefixLift 2268058
  have htrace : WordTrace (prefixWord ++ tailWord_2268058) baseStart_2268058 baseEnd_2268058 := by
    simpa [prefixWord, tailWord_2268058, baseEnd_2268058] using wordTrace_append hprefix tailTrace_2268058
  have hstable : (prefixWord ++ tailWord_2268058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268058).length < 2 ^ (prefixWord ++ tailWord_2268058).sum := by decide
  have hdescent : baseEnd_2268058 < baseStart_2268058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268071 : List Nat := [1, 1, 6, 1, 3, 2, 2, 6]
def baseStart_2268071 : Nat := 118140960795 + 2268071 * 2 ^ 59
def prefixEnd_2268071 : Nat := 4983230072969 + 3 ^ 40 * 2268071 * 2
def baseEnd_2268071 : Nat := 86267450483237103369025

theorem tailTrace_2268071 : CollatzResearch.WordTrace tailWord_2268071 prefixEnd_2268071 86267450483237103369025 := by
  unfold tailWord_2268071
  simp only [CollatzResearch.WordTrace]
  refine ⟨82723345366173597532948067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55148896910782398355298711 82723345366173597532948067)
  ·
    refine ⟨124085018049260396299422101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82723345366173597532948067 124085018049260396299422101)
    ·
      refine ⟨5816485221059081076535411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 124085018049260396299422101 5816485221059081076535411)
      ·
        refine ⟨8724727831588621614803117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5816485221059081076535411 8724727831588621614803117)
        ·
          refine ⟨3271772936845733105551169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8724727831588621614803117 3271772936845733105551169)
          ·
            refine ⟨2453829702634299829163377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3271772936845733105551169 2453829702634299829163377)
            ·
              refine ⟨1840372276975724871872533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2453829702634299829163377 1840372276975724871872533)
              ·
                refine ⟨86267450483237103369025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1840372276975724871872533 86267450483237103369025)
                ·
                  rfl

theorem cell22_2268071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 6].length) (baseStart_2268071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268071 prefixEnd_2268071 := by exact prefixLift 2268071
  have htrace : WordTrace (prefixWord ++ tailWord_2268071) baseStart_2268071 baseEnd_2268071 := by
    simpa [prefixWord, tailWord_2268071, baseEnd_2268071] using wordTrace_append hprefix tailTrace_2268071
  have hstable : (prefixWord ++ tailWord_2268071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268071).length < 2 ^ (prefixWord ++ tailWord_2268071).sum := by decide
  have hdescent : baseEnd_2268071 < baseStart_2268071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268109 : List Nat := [1, 6, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_2268109 : Nat := 118140960795 + 2268109 * 2 ^ 59
def prefixEnd_2268109 : Nat := 4983230072969 + 3 ^ 40 * 2268109 * 2
def baseEnd_2268109 : Nat := 776420062525714497871109

theorem tailTrace_2268109 : CollatzResearch.WordTrace tailWord_2268109 prefixEnd_2268109 776420062525714497871109 := by
  unfold tailWord_2268109
  simp only [CollatzResearch.WordTrace]
  refine ⟨82724731340035930022831381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55149820893357286681887587 82724731340035930022831381)
  ·
    refine ⟨3877721781564184219820221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 82724731340035930022831381 3877721781564184219820221)
    ·
      refine ⟨1454145668086569082432583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3877721781564184219820221 1454145668086569082432583)
      ·
        refine ⟨2181218502129853623648875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1454145668086569082432583 2181218502129853623648875)
        ·
          refine ⟨3271827753194780435473313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2181218502129853623648875 3271827753194780435473313)
          ·
            refine ⟨2453870814896085326604985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3271827753194780435473313 2453870814896085326604985)
            ·
              refine ⟨1840403111172063994953739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2453870814896085326604985 1840403111172063994953739)
              ·
                refine ⟨2760604666758095992430609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840403111172063994953739 2760604666758095992430609)
                ·
                  refine ⟨2070453500068571994322957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2760604666758095992430609 2070453500068571994322957)
                  ·
                    refine ⟨776420062525714497871109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2070453500068571994322957 776420062525714497871109)
                    ·
                      rfl

theorem cell22_2268109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_2268109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268109 prefixEnd_2268109 := by exact prefixLift 2268109
  have htrace : WordTrace (prefixWord ++ tailWord_2268109) baseStart_2268109 baseEnd_2268109 := by
    simpa [prefixWord, tailWord_2268109, baseEnd_2268109] using wordTrace_append hprefix tailTrace_2268109
  have hstable : (prefixWord ++ tailWord_2268109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268109).length < 2 ^ (prefixWord ++ tailWord_2268109).sum := by decide
  have hdescent : baseEnd_2268109 < baseStart_2268109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268112 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 3, 4]
def baseStart_2268112 : Nat := 118140960795 + 2268112 * 2 ^ 59
def prefixEnd_2268112 : Nat := 4983230072969 + 3 ^ 40 * 2268112 * 2
def baseEnd_2268112 : Nat := 776421089487023490046099

theorem tailTrace_2268112 : CollatzResearch.WordTrace tailWord_2268112 prefixEnd_2268112 776421089487023490046099 := by
  unfold tailWord_2268112
  simp only [CollatzResearch.WordTrace]
  refine ⟨41362420379512530767595295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55149893839350041023460393 41362420379512530767595295)
  ·
    refine ⟨62043630569268796151392943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41362420379512530767595295 62043630569268796151392943)
    ·
      refine ⟨93065445853903194227089415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62043630569268796151392943 93065445853903194227089415)
      ·
        refine ⟨139598168780854791340634123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93065445853903194227089415 139598168780854791340634123)
        ·
          refine ⟨209397253171282187010951185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139598168780854791340634123 209397253171282187010951185)
          ·
            refine ⟨157047939878461640258213389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209397253171282187010951185 157047939878461640258213389)
            ·
              refine ⟨58892977454423115096830021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157047939878461640258213389 58892977454423115096830021)
              ·
                refine ⟨11042433272704334080655629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58892977454423115096830021 11042433272704334080655629)
                ·
                  refine ⟨4140912477264125280245861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11042433272704334080655629 4140912477264125280245861)
                  ·
                    refine ⟨776421089487023490046099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4140912477264125280245861 776421089487023490046099)
                    ·
                      rfl

theorem cell22_2268112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_2268112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268112 prefixEnd_2268112 := by exact prefixLift 2268112
  have htrace : WordTrace (prefixWord ++ tailWord_2268112) baseStart_2268112 baseEnd_2268112 := by
    simpa [prefixWord, tailWord_2268112, baseEnd_2268112] using wordTrace_append hprefix tailTrace_2268112
  have hstable : (prefixWord ++ tailWord_2268112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268112).length < 2 ^ (prefixWord ++ tailWord_2268112).sum := by decide
  have hdescent : baseEnd_2268112 < baseStart_2268112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268116 : List Nat := [2, 4, 1, 2, 1, 2, 4, 1, 5]
def baseStart_2268116 : Nat := 118140960795 + 2268116 * 2 ^ 59
def prefixEnd_2268116 : Nat := 4983230072969 + 3 ^ 40 * 2268116 * 2
def baseEnd_2268116 : Nat := 258807486256256270982029

theorem tailTrace_2268116 : CollatzResearch.WordTrace tailWord_2268116 prefixEnd_2268116 258807486256256270982029 := by
  unfold tailWord_2268116
  simp only [CollatzResearch.WordTrace]
  refine ⟨41362493325505285109168101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55149991100673713478890801 41362493325505285109168101)
  ·
    refine ⟨7755467498532240957969019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41362493325505285109168101 7755467498532240957969019)
    ·
      refine ⟨11633201247798361436953529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7755467498532240957969019 11633201247798361436953529)
      ·
        refine ⟨8724900935848771077715147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11633201247798361436953529 8724900935848771077715147)
        ·
          refine ⟨13087351403773156616572721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8724900935848771077715147 13087351403773156616572721)
          ·
            refine ⟨9815513552829867462429541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13087351403773156616572721 9815513552829867462429541)
            ·
              refine ⟨1840408791155600149205539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9815513552829867462429541 1840408791155600149205539)
              ·
                refine ⟨2760613186733400223808309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840408791155600149205539 2760613186733400223808309)
                ·
                  refine ⟨258807486256256270982029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2760613186733400223808309 258807486256256270982029)
                  ·
                    rfl

theorem cell22_2268116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_2268116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268116 prefixEnd_2268116 := by exact prefixLift 2268116
  have htrace : WordTrace (prefixWord ++ tailWord_2268116) baseStart_2268116 baseEnd_2268116 := by
    simpa [prefixWord, tailWord_2268116, baseEnd_2268116] using wordTrace_append hprefix tailTrace_2268116
  have hstable : (prefixWord ++ tailWord_2268116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268116).length < 2 ^ (prefixWord ++ tailWord_2268116).sum := by decide
  have hdescent : baseEnd_2268116 < baseStart_2268116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268144 : List Nat := [2, 1, 1, 1, 3, 2, 1, 7, 4]
def baseStart_2268144 : Nat := 118140960795 + 2268144 * 2 ^ 59
def prefixEnd_2268144 : Nat := 4983230072969 + 3 ^ 40 * 2268144 * 2
def baseEnd_2268144 : Nat := 258810681246995357748667

theorem tailTrace_2268144 : CollatzResearch.WordTrace tailWord_2268144 prefixEnd_2268144 258810681246995357748667 := by
  unfold tailWord_2268144
  simp only [CollatzResearch.WordTrace]
  refine ⟨41363003947454565500177743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55150671929939420666903657 41363003947454565500177743)
  ·
    refine ⟨62044505921181848250266615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41363003947454565500177743 62044505921181848250266615)
    ·
      refine ⟨93066758881772772375399923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62044505921181848250266615 93066758881772772375399923)
      ·
        refine ⟨139600138322659158563099885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93066758881772772375399923 139600138322659158563099885)
        ·
          refine ⟨52350051870997184461162457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139600138322659158563099885 52350051870997184461162457)
          ·
            refine ⟨39262538903247888345871843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52350051870997184461162457 39262538903247888345871843)
            ·
              refine ⟨58893808354871832518807765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39262538903247888345871843 58893808354871832518807765)
              ·
                refine ⟨1380323633317308574659557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 58893808354871832518807765 1380323633317308574659557)
                ·
                  refine ⟨258810681246995357748667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1380323633317308574659557 258810681246995357748667)
                  ·
                    rfl

theorem cell22_2268144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 4].length) (baseStart_2268144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268144 prefixEnd_2268144 := by exact prefixLift 2268144
  have htrace : WordTrace (prefixWord ++ tailWord_2268144) baseStart_2268144 baseEnd_2268144 := by
    simpa [prefixWord, tailWord_2268144, baseEnd_2268144] using wordTrace_append hprefix tailTrace_2268144
  have hstable : (prefixWord ++ tailWord_2268144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268144).length < 2 ^ (prefixWord ++ tailWord_2268144).sum := by decide
  have hdescent : baseEnd_2268144 < baseStart_2268144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268157 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_2268157 : Nat := 118140960795 + 2268157 * 2 ^ 59
def prefixEnd_2268157 : Nat := 4983230072969 + 3 ^ 40 * 2268157 * 2
def baseEnd_2268157 : Nat := 776436493906658372670961

theorem tailTrace_2268157 : CollatzResearch.WordTrace tailWord_2268157 prefixEnd_2268157 776436493906658372670961 := by
  unfold tailWord_2268157
  simp only [CollatzResearch.WordTrace]
  refine ⟨82726482043862034220578725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55150988029241356147052483 82726482043862034220578725)
  ·
    refine ⟨15511215383224131416358511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82726482043862034220578725 15511215383224131416358511)
    ·
      refine ⟨23266823074836197124537767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15511215383224131416358511 23266823074836197124537767)
      ·
        refine ⟨34900234612254295686806651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23266823074836197124537767 34900234612254295686806651)
        ·
          refine ⟨52350351918381443530209977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34900234612254295686806651 52350351918381443530209977)
          ·
            refine ⟨39262763938786082647657483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52350351918381443530209977 39262763938786082647657483)
            ·
              refine ⟨58894145908179123971486225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39262763938786082647657483 58894145908179123971486225)
              ·
                refine ⟨44170609431134342978614669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58894145908179123971486225 44170609431134342978614669)
                ·
                  refine ⟨16563978536675378616980501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44170609431134342978614669 16563978536675378616980501)
                  ·
                    refine ⟨776436493906658372670961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16563978536675378616980501 776436493906658372670961)
                    ·
                      rfl

theorem cell22_2268157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_2268157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268157 prefixEnd_2268157 := by exact prefixLift 2268157
  have htrace : WordTrace (prefixWord ++ tailWord_2268157) baseStart_2268157 baseEnd_2268157 := by
    simpa [prefixWord, tailWord_2268157, baseEnd_2268157] using wordTrace_append hprefix tailTrace_2268157
  have hstable : (prefixWord ++ tailWord_2268157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268157).length < 2 ^ (prefixWord ++ tailWord_2268157).sum := by decide
  have hdescent : baseEnd_2268157 < baseStart_2268157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268161 : List Nat := [1, 2, 4, 1, 2, 3, 1, 4, 4]
def baseStart_2268161 : Nat := 118140960795 + 2268161 * 2 ^ 59
def prefixEnd_2268161 : Nat := 4983230072969 + 3 ^ 40 * 2268161 * 2
def baseEnd_2268161 : Nat := 258812621062801231856983

theorem tailTrace_2268161 : CollatzResearch.WordTrace tailWord_2268161 prefixEnd_2268161 258812621062801231856983 := by
  unfold tailWord_2268161
  simp only [CollatzResearch.WordTrace]
  refine ⟨82726627935847542903724337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55151085290565028602482891 82726627935847542903724337)
  ·
    refine ⟨62044970951885657177793253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82726627935847542903724337 62044970951885657177793253)
    ·
      refine ⟨11633432053478560720836235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62044970951885657177793253 11633432053478560720836235)
      ·
        refine ⟨17450148080217841081254353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11633432053478560720836235 17450148080217841081254353)
        ·
          refine ⟨13087611060163380810940765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17450148080217841081254353 13087611060163380810940765)
          ·
            refine ⟨4907854147561267804102787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13087611060163380810940765 4907854147561267804102787)
            ·
              refine ⟨7361781221341901706154181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4907854147561267804102787 7361781221341901706154181)
              ·
                refine ⟨1380333979001606569903909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7361781221341901706154181 1380333979001606569903909)
                ·
                  refine ⟨258812621062801231856983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1380333979001606569903909 258812621062801231856983)
                  ·
                    rfl

theorem cell22_2268161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 4].length) (baseStart_2268161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268161 prefixEnd_2268161 := by exact prefixLift 2268161
  have htrace : WordTrace (prefixWord ++ tailWord_2268161) baseStart_2268161 baseEnd_2268161 := by
    simpa [prefixWord, tailWord_2268161, baseEnd_2268161] using wordTrace_append hprefix tailTrace_2268161
  have hstable : (prefixWord ++ tailWord_2268161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268161).length < 2 ^ (prefixWord ++ tailWord_2268161).sum := by decide
  have hdescent : baseEnd_2268161 < baseStart_2268161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268191 : List Nat := [1, 1, 2, 4, 1, 5, 1, 1, 2, 4]
def baseStart_2268191 : Nat := 118140960795 + 2268191 * 2 ^ 59
def prefixEnd_2268191 : Nat := 4983230072969 + 3 ^ 40 * 2268191 * 2
def baseEnd_2268191 : Nat := 776448132801493617320857

theorem tailTrace_2268191 : CollatzResearch.WordTrace tailWord_2268191 prefixEnd_2268191 776448132801493617320857 := by
  unfold tailWord_2268191
  simp only [CollatzResearch.WordTrace]
  refine ⟨82727722125738858027316427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55151814750492572018210951 82727722125738858027316427)
  ·
    refine ⟨124091583188608287040974641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82727722125738858027316427 124091583188608287040974641)
    ·
      refine ⟨93068687391456215280730981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124091583188608287040974641 93068687391456215280730981)
      ·
        refine ⟨17450378885898040365137059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93068687391456215280730981 17450378885898040365137059)
        ·
          refine ⟨26175568328847060547705589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17450378885898040365137059 26175568328847060547705589)
          ·
            refine ⟨2453959530829411926347399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26175568328847060547705589 2453959530829411926347399)
            ·
              refine ⟨3680939296244117889521099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453959530829411926347399 3680939296244117889521099)
              ·
                refine ⟨5521408944366176834281649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3680939296244117889521099 5521408944366176834281649)
                ·
                  refine ⟨4141056708274632625711237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5521408944366176834281649 4141056708274632625711237)
                  ·
                    refine ⟨776448132801493617320857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4141056708274632625711237 776448132801493617320857)
                    ·
                      rfl

theorem cell22_2268191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 4].length) (baseStart_2268191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268191 prefixEnd_2268191 := by exact prefixLift 2268191
  have htrace : WordTrace (prefixWord ++ tailWord_2268191) baseStart_2268191 baseEnd_2268191 := by
    simpa [prefixWord, tailWord_2268191, baseEnd_2268191] using wordTrace_append hprefix tailTrace_2268191
  have hstable : (prefixWord ++ tailWord_2268191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268191).length < 2 ^ (prefixWord ++ tailWord_2268191).sum := by decide
  have hdescent : baseEnd_2268191 < baseStart_2268191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268204 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 5, 3]
def baseStart_2268204 : Nat := 118140960795 + 2268204 * 2 ^ 59
def prefixEnd_2268204 : Nat := 4983230072969 + 3 ^ 40 * 2268204 * 2
def baseEnd_2268204 : Nat := 776452582967165916745817

theorem tailTrace_2268204 : CollatzResearch.WordTrace tailWord_2268204 prefixEnd_2268204 776452582967165916745817 := by
  unfold tailWord_2268204
  simp only [CollatzResearch.WordTrace]
  refine ⟨41364098137345880623769833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55152130849794507498359777 41364098137345880623769833)
  ·
    refine ⟨31023073603009410467827375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41364098137345880623769833 31023073603009410467827375)
    ·
      refine ⟨46534610404514115701741063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31023073603009410467827375 46534610404514115701741063)
      ·
        refine ⟨69801915606771173552611595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46534610404514115701741063 69801915606771173552611595)
        ·
          refine ⟨104702873410156760328917393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69801915606771173552611595 104702873410156760328917393)
          ·
            refine ⟨78527155057617570246688045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104702873410156760328917393 78527155057617570246688045)
            ·
              refine ⟨29447683146606588842508017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78527155057617570246688045 29447683146606588842508017)
              ·
                refine ⟨22085762359954941631881013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29447683146606588842508017 22085762359954941631881013)
                ·
                  refine ⟨2070540221245775777988845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22085762359954941631881013 2070540221245775777988845)
                  ·
                    refine ⟨776452582967165916745817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2070540221245775777988845 776452582967165916745817)
                    ·
                      rfl

theorem cell22_2268204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_2268204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268204 prefixEnd_2268204 := by exact prefixLift 2268204
  have htrace : WordTrace (prefixWord ++ tailWord_2268204) baseStart_2268204 baseEnd_2268204 := by
    simpa [prefixWord, tailWord_2268204, baseEnd_2268204] using wordTrace_append hprefix tailTrace_2268204
  have hstable : (prefixWord ++ tailWord_2268204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268204).length < 2 ^ (prefixWord ++ tailWord_2268204).sum := by decide
  have hdescent : baseEnd_2268204 < baseStart_2268204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268221 : List Nat := [1, 4, 1, 3, 1, 2, 1, 3, 3, 3]
def baseStart_2268221 : Nat := 118140960795 + 2268221 * 2 ^ 59
def prefixEnd_2268221 : Nat := 4983230072969 + 3 ^ 40 * 2268221 * 2
def baseEnd_2268221 : Nat := 776458402414583539070765

theorem tailTrace_2268221 : CollatzResearch.WordTrace tailWord_2268221 prefixEnd_2268221 776458402414583539070765 := by
  unfold tailWord_2268221
  simp only [CollatzResearch.WordTrace]
  refine ⟨82728816315630173150908517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55152544210420115433939011 82728816315630173150908517)
  ·
    refine ⟨15511653059180657465795347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82728816315630173150908517 15511653059180657465795347)
    ·
      refine ⟨23267479588770986198693021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15511653059180657465795347 23267479588770986198693021)
      ·
        refine ⟨8725304845789119824509883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23267479588770986198693021 8725304845789119824509883)
        ·
          refine ⟨13087957268683679736764825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8725304845789119824509883 13087957268683679736764825)
          ·
            refine ⟨9815967951512759802573619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13087957268683679736764825 9815967951512759802573619)
            ·
              refine ⟨14723951927269139703860429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9815967951512759802573619 14723951927269139703860429)
              ·
                refine ⟨5521481972725927388947661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14723951927269139703860429 5521481972725927388947661)
                ·
                  refine ⟨2070555739772222770855373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5521481972725927388947661 2070555739772222770855373)
                  ·
                    refine ⟨776458402414583539070765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2070555739772222770855373 776458402414583539070765)
                    ·
                      rfl

theorem cell22_2268221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_2268221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268221 prefixEnd_2268221 := by exact prefixLift 2268221
  have htrace : WordTrace (prefixWord ++ tailWord_2268221) baseStart_2268221 baseEnd_2268221 := by
    simpa [prefixWord, tailWord_2268221, baseEnd_2268221] using wordTrace_append hprefix tailTrace_2268221
  have hstable : (prefixWord ++ tailWord_2268221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268221).length < 2 ^ (prefixWord ++ tailWord_2268221).sum := by decide
  have hdescent : baseEnd_2268221 < baseStart_2268221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268234 : List Nat := [3, 1, 2, 1, 1, 2, 2, 5, 5]
def baseStart_2268234 : Nat := 118140960795 + 2268234 * 2 ^ 59
def prefixEnd_2268234 : Nat := 4983230072969 + 3 ^ 40 * 2268234 * 2
def baseEnd_2268234 : Nat := 258820950860085279498575

theorem tailTrace_2268234 : CollatzResearch.WordTrace tailWord_2268234 prefixEnd_2268234 258820950860085279498575 := by
  unfold tailWord_2268234
  simp only [CollatzResearch.WordTrace]
  refine ⟨20682322616145769092782939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55152860309722050914087837 20682322616145769092782939)
  ·
    refine ⟨31023483924218653639174409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20682322616145769092782939 31023483924218653639174409)
    ·
      refine ⟨23267612943163990229380807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31023483924218653639174409 23267612943163990229380807)
      ·
        refine ⟨34901419414745985344071211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23267612943163990229380807 34901419414745985344071211)
        ·
          refine ⟨52352129122118978016106817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34901419414745985344071211 52352129122118978016106817)
          ·
            refine ⟨39264096841589233512080113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52352129122118978016106817 39264096841589233512080113)
            ·
              refine ⟨29448072631191925134060085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39264096841589233512080113 29448072631191925134060085)
              ·
                refine ⟨2760756809174242981318133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29448072631191925134060085 2760756809174242981318133)
                ·
                  refine ⟨258820950860085279498575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2760756809174242981318133 258820950860085279498575)
                  ·
                    rfl

theorem cell22_2268234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_2268234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268234 prefixEnd_2268234 := by exact prefixLift 2268234
  have htrace : WordTrace (prefixWord ++ tailWord_2268234) baseStart_2268234 baseEnd_2268234 := by
    simpa [prefixWord, tailWord_2268234, baseEnd_2268234] using wordTrace_append hprefix tailTrace_2268234
  have hstable : (prefixWord ++ tailWord_2268234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268234).length < 2 ^ (prefixWord ++ tailWord_2268234).sum := by decide
  have hdescent : baseEnd_2268234 < baseStart_2268234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268311 : List Nat := [1, 1, 3, 3, 3, 2, 1, 2, 1, 5]
def baseStart_2268311 : Nat := 118140960795 + 2268311 * 2 ^ 59
def prefixEnd_2268311 : Nat := 4983230072969 + 3 ^ 40 * 2268311 * 2
def baseEnd_2268311 : Nat := 776489211253853304320489

theorem tailTrace_2268311 : CollatzResearch.WordTrace tailWord_2268311 prefixEnd_2268311 776489211253853304320489 := by
  unfold tailWord_2268311
  simp only [CollatzResearch.WordTrace]
  refine ⟨82732098885304118521684787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55154732590202745681123191 82732098885304118521684787)
  ·
    refine ⟨124098148327956177782527181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82732098885304118521684787 124098148327956177782527181)
    ·
      refine ⟨46536805622983566668447693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124098148327956177782527181 46536805622983566668447693)
      ·
        refine ⟨17451302108618837500667885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46536805622983566668447693 17451302108618837500667885)
        ·
          refine ⟨6544238290732064062750457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17451302108618837500667885 6544238290732064062750457)
          ·
            refine ⟨4908178718049048047062843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6544238290732064062750457 4908178718049048047062843)
            ·
              refine ⟨7362268077073572070594265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4908178718049048047062843 7362268077073572070594265)
              ·
                refine ⟨5521701057805179052945699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7362268077073572070594265 5521701057805179052945699)
                ·
                  refine ⟨8282551586707768579418549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5521701057805179052945699 8282551586707768579418549)
                  ·
                    refine ⟨776489211253853304320489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8282551586707768579418549 776489211253853304320489)
                    ·
                      rfl

theorem cell22_2268311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_2268311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268311 prefixEnd_2268311 := by exact prefixLift 2268311
  have htrace : WordTrace (prefixWord ++ tailWord_2268311) baseStart_2268311 baseEnd_2268311 := by
    simpa [prefixWord, tailWord_2268311, baseEnd_2268311] using wordTrace_append hprefix tailTrace_2268311
  have hstable : (prefixWord ++ tailWord_2268311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268311).length < 2 ^ (prefixWord ++ tailWord_2268311).sum := by decide
  have hdescent : baseEnd_2268311 < baseStart_2268311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268324 : List Nat := [2, 3, 1, 2, 3, 11]
def baseStart_2268324 : Nat := 118140960795 + 2268324 * 2 ^ 59
def prefixEnd_2268324 : Nat := 4983230072969 + 3 ^ 40 * 2268324 * 2
def baseEnd_2268324 : Nat := 9586341499006488935129

theorem tailTrace_2268324 : CollatzResearch.WordTrace tailWord_2268324 prefixEnd_2268324 9586341499006488935129 := by
  unfold tailWord_2268324
  simp only [CollatzResearch.WordTrace]
  refine ⟨41366286517128510870954013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55155048689504681161272017 41366286517128510870954013)
  ·
    refine ⟨15512357443923191576607755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41366286517128510870954013 15512357443923191576607755)
    ·
      refine ⟨23268536165884787364911633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15512357443923191576607755 23268536165884787364911633)
      ·
        refine ⟨17451402124413590523683725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23268536165884787364911633 17451402124413590523683725)
        ·
          refine ⟨6544275796655096446381397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17451402124413590523683725 6544275796655096446381397)
          ·
            refine ⟨9586341499006488935129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6544275796655096446381397 9586341499006488935129)
            ·
              rfl

theorem cell22_2268324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 11].length) (baseStart_2268324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268324 prefixEnd_2268324 := by exact prefixLift 2268324
  have htrace : WordTrace (prefixWord ++ tailWord_2268324) baseStart_2268324 baseEnd_2268324 := by
    simpa [prefixWord, tailWord_2268324, baseEnd_2268324] using wordTrace_append hprefix tailTrace_2268324
  have hstable : (prefixWord ++ tailWord_2268324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268324).length < 2 ^ (prefixWord ++ tailWord_2268324).sum := by decide
  have hdescent : baseEnd_2268324 < baseStart_2268324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268330 : List Nat := [3, 1, 5, 1, 1, 2, 1, 4, 4]
def baseStart_2268330 : Nat := 118140960795 + 2268330 * 2 ^ 59
def prefixEnd_2268330 : Nat := 4983230072969 + 3 ^ 40 * 2268330 * 2
def baseEnd_2268330 : Nat := 258831905114047862698477

theorem tailTrace_2268330 : CollatzResearch.WordTrace tailWord_2268330 prefixEnd_2268330 258831905114047862698477 := by
  unfold tailWord_2268330
  simp only [CollatzResearch.WordTrace]
  refine ⟨20683197968058821191656611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55155194581490189844417629 20683197968058821191656611)
  ·
    refine ⟨31024796952088231787484917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20683197968058821191656611 31024796952088231787484917)
    ·
      refine ⟨2908574714258271730076711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31024796952088231787484917 2908574714258271730076711)
      ·
        refine ⟨4362862071387407595115067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2908574714258271730076711 4362862071387407595115067)
        ·
          refine ⟨6544293107081111392672601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4362862071387407595115067 6544293107081111392672601)
          ·
            refine ⟨4908219830310833544504451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6544293107081111392672601 4908219830310833544504451)
            ·
              refine ⟨7362329745466250316756677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4908219830310833544504451 7362329745466250316756677)
              ·
                refine ⟨1380436827274921934391877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7362329745466250316756677 1380436827274921934391877)
                ·
                  refine ⟨258831905114047862698477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1380436827274921934391877 258831905114047862698477)
                  ·
                    rfl

theorem cell22_2268330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_2268330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268330 prefixEnd_2268330 := by exact prefixLift 2268330
  have htrace : WordTrace (prefixWord ++ tailWord_2268330) baseStart_2268330 baseEnd_2268330 := by
    simpa [prefixWord, tailWord_2268330, baseEnd_2268330] using wordTrace_append hprefix tailTrace_2268330
  have hstable : (prefixWord ++ tailWord_2268330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268330).length < 2 ^ (prefixWord ++ tailWord_2268330).sum := by decide
  have hdescent : baseEnd_2268330 < baseStart_2268330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268369 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 7]
def baseStart_2268369 : Nat := 118140960795 + 2268369 * 2 ^ 59
def prefixEnd_2268369 : Nat := 4983230072969 + 3 ^ 40 * 2268369 * 2
def baseEnd_2268369 : Nat := 258836355279720162123437

theorem tailTrace_2268369 : CollatzResearch.WordTrace tailWord_2268369 prefixEnd_2268369 258836355279720162123437 := by
  unfold tailWord_2268369
  simp only [CollatzResearch.WordTrace]
  refine ⟨82734214319093994427296161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55156142879395996284864107 82734214319093994427296161)
  ·
    refine ⟨62050660739320495820472121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82734214319093994427296161 62050660739320495820472121)
    ·
      refine ⟨46537995554490371865354091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62050660739320495820472121 46537995554490371865354091)
      ·
        refine ⟨69806993331735557798031137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46537995554490371865354091 69806993331735557798031137)
        ·
          refine ⟨52355244998801668348523353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69806993331735557798031137 52355244998801668348523353)
          ·
            refine ⟨39266433749101251261392515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52355244998801668348523353 39266433749101251261392515)
            ·
              refine ⟨58899650623651876892088773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39266433749101251261392515 58899650623651876892088773)
              ·
                refine ⟨11043684491934726917266645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58899650623651876892088773 11043684491934726917266645)
                ·
                  refine ⟨258836355279720162123437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11043684491934726917266645 258836355279720162123437)
                  ·
                    rfl

theorem cell22_2268369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 7].length) (baseStart_2268369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268369 prefixEnd_2268369 := by exact prefixLift 2268369
  have htrace : WordTrace (prefixWord ++ tailWord_2268369) baseStart_2268369 baseEnd_2268369 := by
    simpa [prefixWord, tailWord_2268369, baseEnd_2268369] using wordTrace_append hprefix tailTrace_2268369
  have hstable : (prefixWord ++ tailWord_2268369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268369).length < 2 ^ (prefixWord ++ tailWord_2268369).sum := by decide
  have hdescent : baseEnd_2268369 < baseStart_2268369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268403 : List Nat := [1, 1, 1, 2, 2, 6, 3, 1, 5]
def baseStart_2268403 : Nat := 118140960795 + 2268403 * 2 ^ 59
def prefixEnd_2268403 : Nat := 4983230072969 + 3 ^ 40 * 2268403 * 2
def baseEnd_2268403 : Nat := 258840234911331910340069

theorem tailTrace_2268403 : CollatzResearch.WordTrace tailWord_2268403 prefixEnd_2268403 258840234911331910340069 := by
  unfold tailWord_2268403
  simp only [CollatzResearch.WordTrace]
  refine ⟨82735454400970818234033863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55156969600647212156022575 82735454400970818234033863)
  ·
    refine ⟨124103181601456227351050795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82735454400970818234033863 124103181601456227351050795)
    ·
      refine ⟨186154772402184341026576193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124103181601456227351050795 186154772402184341026576193)
      ·
        refine ⟨139616079301638255769932145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186154772402184341026576193 139616079301638255769932145)
        ·
          refine ⟨104712059476228691827449109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139616079301638255769932145 104712059476228691827449109)
          ·
            refine ⟨4908377787948219929411677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 104712059476228691827449109 4908377787948219929411677)
            ·
              refine ⟨1840641670480582473529379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4908377787948219929411677 1840641670480582473529379)
              ·
                refine ⟨2760962505720873710294069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840641670480582473529379 2760962505720873710294069)
                ·
                  refine ⟨258840234911331910340069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2760962505720873710294069 258840234911331910340069)
                  ·
                    rfl

theorem cell22_2268403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 5].length) (baseStart_2268403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268403 prefixEnd_2268403 := by exact prefixLift 2268403
  have htrace : WordTrace (prefixWord ++ tailWord_2268403) baseStart_2268403 baseEnd_2268403 := by
    simpa [prefixWord, tailWord_2268403, baseEnd_2268403] using wordTrace_append hprefix tailTrace_2268403
  have hstable : (prefixWord ++ tailWord_2268403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268403).length < 2 ^ (prefixWord ++ tailWord_2268403).sum := by decide
  have hdescent : baseEnd_2268403 < baseStart_2268403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268424 : List Nat := [2, 1, 3, 2, 5, 1, 1, 3, 1, 3]
def baseStart_2268424 : Nat := 118140960795 + 2268424 * 2 ^ 59
def prefixEnd_2268424 : Nat := 4983230072969 + 3 ^ 40 * 2268424 * 2
def baseEnd_2268424 : Nat := 776527893463158676245143

theorem tailTrace_2268424 : CollatzResearch.WordTrace tailWord_2268424 prefixEnd_2268424 776527893463158676245143 := by
  unfold tailWord_2268424
  simp only [CollatzResearch.WordTrace]
  refine ⟨41368110166947369410274163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55157480222596492547032217 41368110166947369410274163)
  ·
    refine ⟨62052165250421054115411245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41368110166947369410274163 62052165250421054115411245)
    ·
      refine ⟨23269561968907895293279217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62052165250421054115411245 23269561968907895293279217)
      ·
        refine ⟨17452171476680921469959413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23269561968907895293279217 17452171476680921469959413)
        ·
          refine ⟨1636141075938836387808695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17452171476680921469959413 1636141075938836387808695)
          ·
            refine ⟨2454211613908254581713043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1636141075938836387808695 2454211613908254581713043)
            ·
              refine ⟨3681317420862381872569565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2454211613908254581713043 3681317420862381872569565)
              ·
                refine ⟨1380494032823393202213587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3681317420862381872569565 1380494032823393202213587)
                ·
                  refine ⟨2070741049235089803320381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1380494032823393202213587 2070741049235089803320381)
                  ·
                    refine ⟨776527893463158676245143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2070741049235089803320381 776527893463158676245143)
                    ·
                      rfl

theorem cell22_2268424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_2268424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268424 prefixEnd_2268424 := by exact prefixLift 2268424
  have htrace : WordTrace (prefixWord ++ tailWord_2268424) baseStart_2268424 baseEnd_2268424 := by
    simpa [prefixWord, tailWord_2268424, baseEnd_2268424] using wordTrace_append hprefix tailTrace_2268424
  have hstable : (prefixWord ++ tailWord_2268424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268424).length < 2 ^ (prefixWord ++ tailWord_2268424).sum := by decide
  have hdescent : baseEnd_2268424 < baseStart_2268424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268476 : List Nat := [2, 2, 2, 2, 1, 3, 2, 8]
def baseStart_2268476 : Nat := 118140960795 + 2268476 * 2 ^ 59
def prefixEnd_2268476 : Nat := 4983230072969 + 3 ^ 40 * 2268476 * 2
def baseEnd_2268476 : Nat := 86282854902871985993887

theorem tailTrace_2268476 : CollatzResearch.WordTrace tailWord_2268476 prefixEnd_2268476 86282854902871985993887 := by
  unfold tailWord_2268476
  simp only [CollatzResearch.WordTrace]
  refine ⟨41369058464853175850720641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55158744619804234467627521 41369058464853175850720641)
  ·
    refine ⟨31026793848639881888040481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41369058464853175850720641 31026793848639881888040481)
    ·
      refine ⟨23270095386479911416030361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31026793848639881888040481 23270095386479911416030361)
      ·
        refine ⟨17452571539859933562022771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23270095386479911416030361 17452571539859933562022771)
        ·
          refine ⟨26178857309789900343034157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17452571539859933562022771 26178857309789900343034157)
          ·
            refine ⟨9817071491171212628637809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26178857309789900343034157 9817071491171212628637809)
            ·
              refine ⟨7362803618378409471478357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9817071491171212628637809 7362803618378409471478357)
              ·
                refine ⟨86282854902871985993887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7362803618378409471478357 86282854902871985993887)
                ·
                  rfl

theorem cell22_2268476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 8].length) (baseStart_2268476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268476 prefixEnd_2268476 := by exact prefixLift 2268476
  have htrace : WordTrace (prefixWord ++ tailWord_2268476) baseStart_2268476 baseEnd_2268476 := by
    simpa [prefixWord, tailWord_2268476, baseEnd_2268476] using wordTrace_append hprefix tailTrace_2268476
  have hstable : (prefixWord ++ tailWord_2268476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268476).length < 2 ^ (prefixWord ++ tailWord_2268476).sum := by decide
  have hdescent : baseEnd_2268476 < baseStart_2268476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268493 : List Nat := [1, 6, 1, 3, 11]
def baseStart_2268493 : Nat := 118140960795 + 2268493 * 2 ^ 59
def prefixEnd_2268493 : Nat := 4983230072969 + 3 ^ 40 * 2268493 * 2
def baseEnd_2268493 : Nat := 3195685241042244840617

theorem tailTrace_2268493 : CollatzResearch.WordTrace tailWord_2268493 prefixEnd_2268493 3195685241042244840617 := by
  unfold tailWord_2268493
  simp only [CollatzResearch.WordTrace]
  refine ⟨82738736970644763604810133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55159157980429842403206755 82738736970644763604810133)
  ·
    refine ⟨3878378295498973293975475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 82738736970644763604810133 3878378295498973293975475)
    ·
      refine ⟨5817567443248459940963213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3878378295498973293975475 5817567443248459940963213)
      ·
        refine ⟨2181587791218172477861205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5817567443248459940963213 2181587791218172477861205)
        ·
          refine ⟨3195685241042244840617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2181587791218172477861205 3195685241042244840617)
          ·
            rfl

theorem cell22_2268493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 11].length) (baseStart_2268493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268493 prefixEnd_2268493 := by exact prefixLift 2268493
  have htrace : WordTrace (prefixWord ++ tailWord_2268493) baseStart_2268493 baseEnd_2268493 := by
    simpa [prefixWord, tailWord_2268493, baseEnd_2268493] using wordTrace_append hprefix tailTrace_2268493
  have hstable : (prefixWord ++ tailWord_2268493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268493).length < 2 ^ (prefixWord ++ tailWord_2268493).sum := by decide
  have hdescent : baseEnd_2268493 < baseStart_2268493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268506 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 2, 6]
def baseStart_2268506 : Nat := 118140960795 + 2268506 * 2 ^ 59
def prefixEnd_2268506 : Nat := 4983230072969 + 3 ^ 40 * 2268506 * 2
def baseEnd_2268506 : Nat := 776555963738937795694891

theorem tailTrace_2268506 : CollatzResearch.WordTrace tailWord_2268506 prefixEnd_2268506 776555963738937795694891 := by
  unfold tailWord_2268506
  simp only [CollatzResearch.WordTrace]
  refine ⟨20684802779899416706258343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55159474079731777883355581 20684802779899416706258343)
  ·
    refine ⟨31027204169849125059387515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20684802779899416706258343 31027204169849125059387515)
    ·
      refine ⟨46540806254773687589081273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31027204169849125059387515 46540806254773687589081273)
      ·
        refine ⟨34905604691080265691810955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46540806254773687589081273 34905604691080265691810955)
        ·
          refine ⟨52358407036620398537716433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34905604691080265691810955 52358407036620398537716433)
          ·
            refine ⟨39268805277465298903287325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52358407036620398537716433 39268805277465298903287325)
            ·
              refine ⟨14725801979049487088732747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39268805277465298903287325 14725801979049487088732747)
              ·
                refine ⟨22088702968574230633099121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14725801979049487088732747 22088702968574230633099121)
                ·
                  refine ⟨16566527226430672974824341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22088702968574230633099121 16566527226430672974824341)
                  ·
                    refine ⟨776555963738937795694891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16566527226430672974824341 776555963738937795694891)
                    ·
                      rfl

theorem cell22_2268506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_2268506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268506 prefixEnd_2268506 := by exact prefixLift 2268506
  have htrace : WordTrace (prefixWord ++ tailWord_2268506) baseStart_2268506 baseEnd_2268506 := by
    simpa [prefixWord, tailWord_2268506, baseEnd_2268506] using wordTrace_append hprefix tailTrace_2268506
  have hstable : (prefixWord ++ tailWord_2268506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268506).length < 2 ^ (prefixWord ++ tailWord_2268506).sum := by decide
  have hdescent : baseEnd_2268506 < baseStart_2268506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268525 : List Nat := [1, 5, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_2268525 : Nat := 118140960795 + 2268525 * 2 ^ 59
def prefixEnd_2268525 : Nat := 4983230072969 + 3 ^ 40 * 2268525 * 2
def baseEnd_2268525 : Nat := 776562467827228079469833

theorem tailTrace_2268525 : CollatzResearch.WordTrace tailWord_2268525 prefixEnd_2268525 776562467827228079469833 := by
  unfold tailWord_2268525
  simp only [CollatzResearch.WordTrace]
  refine ⟨82739904106528833069975029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55159936071019222046650019 82739904106528833069975029)
  ·
    refine ⟨7756866009987078100310159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82739904106528833069975029 7756866009987078100310159)
    ·
      refine ⟨11635299014980617150465239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7756866009987078100310159 11635299014980617150465239)
      ·
        refine ⟨17452948522470925725697859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11635299014980617150465239 17452948522470925725697859)
        ·
          refine ⟨26179422783706388588546789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17452948522470925725697859 26179422783706388588546789)
          ·
            refine ⟨4908641771944947860352523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26179422783706388588546789 4908641771944947860352523)
            ·
              refine ⟨7362962657917421790528785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4908641771944947860352523 7362962657917421790528785)
              ·
                refine ⟨5522221993438066342896589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7362962657917421790528785 5522221993438066342896589)
                ·
                  refine ⟨2070833247539274878586221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5522221993438066342896589 2070833247539274878586221)
                  ·
                    refine ⟨776562467827228079469833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2070833247539274878586221 776562467827228079469833)
                    ·
                      rfl

theorem cell22_2268525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_2268525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268525 prefixEnd_2268525 := by exact prefixLift 2268525
  have htrace : WordTrace (prefixWord ++ tailWord_2268525) baseStart_2268525 baseEnd_2268525 := by
    simpa [prefixWord, tailWord_2268525, baseEnd_2268525] using wordTrace_append hprefix tailTrace_2268525
  have hstable : (prefixWord ++ tailWord_2268525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268525).length < 2 ^ (prefixWord ++ tailWord_2268525).sum := by decide
  have hdescent : baseEnd_2268525 < baseStart_2268525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268583 : List Nat := [1, 1, 6, 1, 1, 1, 1, 4, 6]
def baseStart_2268583 : Nat := 118140960795 + 2268583 * 2 ^ 59
def prefixEnd_2268583 : Nat := 4983230072969 + 3 ^ 40 * 2268583 * 2
def baseEnd_2268583 : Nat := 258860774137511753839885

theorem tailTrace_2268583 : CollatzResearch.WordTrace tailWord_2268583 prefixEnd_2268583 258860774137511753839885 := by
  unfold tailWord_2268583
  simp only [CollatzResearch.WordTrace]
  refine ⟨82742019540318708975586403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55161346360212472650390935 82742019540318708975586403)
  ·
    refine ⟨124113029310478063463379605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82742019540318708975586403 124113029310478063463379605)
    ·
      refine ⟨5817798248928659224845919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 124113029310478063463379605 5817798248928659224845919)
      ·
        refine ⟨8726697373392988837268879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5817798248928659224845919 8726697373392988837268879)
        ·
          refine ⟨13090046060089483255903319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8726697373392988837268879 13090046060089483255903319)
          ·
            refine ⟨19635069090134224883854979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13090046060089483255903319 19635069090134224883854979)
            ·
              refine ⟨29452603635201337325782469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19635069090134224883854979 29452603635201337325782469)
              ·
                refine ⟨5522363181600250748584213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29452603635201337325782469 5522363181600250748584213)
                ·
                  refine ⟨258860774137511753839885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5522363181600250748584213 258860774137511753839885)
                  ·
                    rfl

theorem cell22_2268583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 6].length) (baseStart_2268583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268583 prefixEnd_2268583 := by exact prefixLift 2268583
  have htrace : WordTrace (prefixWord ++ tailWord_2268583) baseStart_2268583 baseEnd_2268583 := by
    simpa [prefixWord, tailWord_2268583, baseEnd_2268583] using wordTrace_append hprefix tailTrace_2268583
  have hstable : (prefixWord ++ tailWord_2268583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268583).length < 2 ^ (prefixWord ++ tailWord_2268583).sum := by decide
  have hdescent : baseEnd_2268583 < baseStart_2268583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268600 : List Nat := [2, 1, 2, 1, 2, 2, 5, 3, 4]
def baseStart_2268600 : Nat := 118140960795 + 2268600 * 2 ^ 59
def prefixEnd_2268600 : Nat := 4983230072969 + 3 ^ 40 * 2268600 * 2
def baseEnd_2268600 : Nat := 258862713953317627948201

theorem tailTrace_2268600 : CollatzResearch.WordTrace tailWord_2268600 prefixEnd_2268600 258862713953317627948201 := by
  unfold tailWord_2268600
  simp only [CollatzResearch.WordTrace]
  refine ⟨41371319790628560439477627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55161759720838080585970169 41371319790628560439477627)
  ·
    refine ⟨62056979685942840659216441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41371319790628560439477627 62056979685942840659216441)
    ·
      refine ⟨46542734764457130494412331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62056979685942840659216441 46542734764457130494412331)
      ·
        refine ⟨69814102146685695741618497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46542734764457130494412331 69814102146685695741618497)
        ·
          refine ⟨52360576610014271806213873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69814102146685695741618497 52360576610014271806213873)
          ·
            refine ⟨39270432457510703854660405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52360576610014271806213873 39270432457510703854660405)
            ·
              refine ⟨3681603042891628486374413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39270432457510703854660405 3681603042891628486374413)
              ·
                refine ⟨1380601141084360682390405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3681603042891628486374413 1380601141084360682390405)
                ·
                  refine ⟨258862713953317627948201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1380601141084360682390405 258862713953317627948201)
                  ·
                    rfl

theorem cell22_2268600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 4].length) (baseStart_2268600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268600 prefixEnd_2268600 := by exact prefixLift 2268600
  have htrace : WordTrace (prefixWord ++ tailWord_2268600) baseStart_2268600 baseEnd_2268600 := by
    simpa [prefixWord, tailWord_2268600, baseEnd_2268600] using wordTrace_append hprefix tailTrace_2268600
  have hstable : (prefixWord ++ tailWord_2268600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268600).length < 2 ^ (prefixWord ++ tailWord_2268600).sum := by decide
  have hdescent : baseEnd_2268600 < baseStart_2268600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268610 : List Nat := [3, 5, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2268610 : Nat := 118140960795 + 2268610 * 2 ^ 59
def prefixEnd_2268610 : Nat := 4983230072969 + 3 ^ 40 * 2268610 * 2
def baseEnd_2268610 : Nat := 776591565064316191094573

theorem tailTrace_2268610 : CollatzResearch.WordTrace tailWord_2268610 prefixEnd_2268610 776591565064316191094573 := by
  unfold tailWord_2268610
  simp only [CollatzResearch.WordTrace]
  refine ⟨20685751077805223146704821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55162002874147261724546189 20685751077805223146704821)
  ·
    refine ⟨1939289163544239670003577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20685751077805223146704821 1939289163544239670003577)
    ·
      refine ⟨1454466872658179752502683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1939289163544239670003577 1454466872658179752502683)
      ·
        refine ⟨2181700308987269628754025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1454466872658179752502683 2181700308987269628754025)
        ·
          refine ⟨1636275231740452221565519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2181700308987269628754025 1636275231740452221565519)
          ·
            refine ⟨2454412847610678332348279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1636275231740452221565519 2454412847610678332348279)
            ·
              refine ⟨3681619271416017498522419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2454412847610678332348279 3681619271416017498522419)
              ·
                refine ⟨5522428907124026247783629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3681619271416017498522419 5522428907124026247783629)
                ·
                  refine ⟨2070910840171509842918861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5522428907124026247783629 2070910840171509842918861)
                  ·
                    refine ⟨776591565064316191094573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2070910840171509842918861 776591565064316191094573)
                    ·
                      rfl

theorem cell22_2268610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2268610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268610 prefixEnd_2268610 := by exact prefixLift 2268610
  have htrace : WordTrace (prefixWord ++ tailWord_2268610) baseStart_2268610 baseEnd_2268610 := by
    simpa [prefixWord, tailWord_2268610, baseEnd_2268610] using wordTrace_append hprefix tailTrace_2268610
  have hstable : (prefixWord ++ tailWord_2268610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268610).length < 2 ^ (prefixWord ++ tailWord_2268610).sum := by decide
  have hdescent : baseEnd_2268610 < baseStart_2268610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268611 : List Nat := [1, 1, 1, 3, 1, 1, 14]
def baseStart_2268611 : Nat := 118140960795 + 2268611 * 2 ^ 59
def prefixEnd_2268611 : Nat := 4983230072969 + 3 ^ 40 * 2268611 * 2
def baseEnd_2268611 : Nat := 28762663236472315622947

theorem tailTrace_2268611 : CollatzResearch.WordTrace tailWord_2268611 prefixEnd_2268611 28762663236472315622947 := by
  unfold tailWord_2268611
  simp only [CollatzResearch.WordTrace]
  refine ⟨82743040784217269757605687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55162027189478179838403791 82743040784217269757605687)
  ·
    refine ⟨124114561176325904636408531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82743040784217269757605687 124114561176325904636408531)
    ·
      refine ⟨186171841764488856954612797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124114561176325904636408531 186171841764488856954612797)
      ·
        refine ⟨69814440661683321357979799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186171841764488856954612797 69814440661683321357979799)
        ·
          refine ⟨104721660992524982036969699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69814440661683321357979799 104721660992524982036969699)
          ·
            refine ⟨157082491488787473055454549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104721660992524982036969699 157082491488787473055454549)
            ·
              refine ⟨28762663236472315622947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 157082491488787473055454549 28762663236472315622947)
              ·
                rfl

theorem cell22_2268611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 14].length) (baseStart_2268611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268611 prefixEnd_2268611 := by exact prefixLift 2268611
  have htrace : WordTrace (prefixWord ++ tailWord_2268611) baseStart_2268611 baseEnd_2268611 := by
    simpa [prefixWord, tailWord_2268611, baseEnd_2268611] using wordTrace_append hprefix tailTrace_2268611
  have hstable : (prefixWord ++ tailWord_2268611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268611).length < 2 ^ (prefixWord ++ tailWord_2268611).sum := by decide
  have hdescent : baseEnd_2268611 < baseStart_2268611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268615 : List Nat := [1, 1, 4, 1, 1, 3, 2, 4, 2, 3]
def baseStart_2268615 : Nat := 118140960795 + 2268615 * 2 ^ 59
def prefixEnd_2268615 : Nat := 4983230072969 + 3 ^ 40 * 2268615 * 2
def baseEnd_2268615 : Nat := 776593276666497844719557

theorem tailTrace_2268615 : CollatzResearch.WordTrace tailWord_2268615 prefixEnd_2268615 776593276666497844719557 := by
  unfold tailWord_2268615
  simp only [CollatzResearch.WordTrace]
  refine ⟨82743186676202778440751299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55162124450801852293834199 82743186676202778440751299)
  ·
    refine ⟨124114780014304167661126949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82743186676202778440751299 124114780014304167661126949)
    ·
      refine ⟨23271521252682031436461303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124114780014304167661126949 23271521252682031436461303)
      ·
        refine ⟨34907281879023047154691955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23271521252682031436461303 34907281879023047154691955)
        ·
          refine ⟨52360922818534570732037933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34907281879023047154691955 52360922818534570732037933)
          ·
            refine ⟨19635346056950464024514225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52360922818534570732037933 19635346056950464024514225)
            ·
              refine ⟨14726509542712848018385669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19635346056950464024514225 14726509542712848018385669)
              ·
                refine ⟨2761220539258659003447313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14726509542712848018385669 2761220539258659003447313)
                ·
                  refine ⟨2070915404443994252585485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2761220539258659003447313 2070915404443994252585485)
                  ·
                    refine ⟨776593276666497844719557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2070915404443994252585485 776593276666497844719557)
                    ·
                      rfl

theorem cell22_2268615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_2268615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268615 prefixEnd_2268615 := by exact prefixLift 2268615
  have htrace : WordTrace (prefixWord ++ tailWord_2268615) baseStart_2268615 baseEnd_2268615 := by
    simpa [prefixWord, tailWord_2268615, baseEnd_2268615] using wordTrace_append hprefix tailTrace_2268615
  have hstable : (prefixWord ++ tailWord_2268615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268615).length < 2 ^ (prefixWord ++ tailWord_2268615).sum := by decide
  have hdescent : baseEnd_2268615 < baseStart_2268615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268632 : List Nat := [2, 1, 2, 2, 2, 1, 6, 1, 2, 3]
def baseStart_2268632 : Nat := 118140960795 + 2268632 * 2 ^ 59
def prefixEnd_2268632 : Nat := 4983230072969 + 3 ^ 40 * 2268632 * 2
def baseEnd_2268632 : Nat := 776599096113915467044505

theorem tailTrace_2268632 : CollatzResearch.WordTrace tailWord_2268632 prefixEnd_2268632 776599096113915467044505 := by
  unfold tailWord_2268632
  simp only [CollatzResearch.WordTrace]
  refine ⟨41371903358570595172060075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55162537811427460229413433 41371903358570595172060075)
  ·
    refine ⟨62057855037855892758090113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41371903358570595172060075 62057855037855892758090113)
    ·
      refine ⟨46543391278391919568567585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62057855037855892758090113 46543391278391919568567585)
      ·
        refine ⟨34907543458793939676425689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46543391278391919568567585 34907543458793939676425689)
        ·
          refine ⟨26180657594095454757319267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34907543458793939676425689 26180657594095454757319267)
          ·
            refine ⟨39270986391143182135978901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26180657594095454757319267 39270986391143182135978901)
            ·
              refine ⟨1840827487084836662624011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39270986391143182135978901 1840827487084836662624011)
              ·
                refine ⟨2761241230627254993936017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840827487084836662624011 2761241230627254993936017)
                ·
                  refine ⟨2070930922970441245452013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2761241230627254993936017 2070930922970441245452013)
                  ·
                    refine ⟨776599096113915467044505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2070930922970441245452013 776599096113915467044505)
                    ·
                      rfl

theorem cell22_2268632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 2, 3].length) (baseStart_2268632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268632 prefixEnd_2268632 := by exact prefixLift 2268632
  have htrace : WordTrace (prefixWord ++ tailWord_2268632) baseStart_2268632 baseEnd_2268632 := by
    simpa [prefixWord, tailWord_2268632, baseEnd_2268632] using wordTrace_append hprefix tailTrace_2268632
  have hstable : (prefixWord ++ tailWord_2268632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268632).length < 2 ^ (prefixWord ++ tailWord_2268632).sum := by decide
  have hdescent : baseEnd_2268632 < baseStart_2268632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268735 : List Nat := [1, 1, 2, 2, 3, 4, 2, 1, 6]
def baseStart_2268735 : Nat := 118140960795 + 2268735 * 2 ^ 59
def prefixEnd_2268735 : Nat := 4983230072969 + 3 ^ 40 * 2268735 * 2
def baseEnd_2268735 : Nat := 258878118372952510573063

theorem tailTrace_2268735 : CollatzResearch.WordTrace tailWord_2268735 prefixEnd_2268735 258878118372952510573063 := by
  unfold tailWord_2268735
  simp only [CollatzResearch.WordTrace]
  refine ⟨82747563435768038935119659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55165042290512025956746439 82747563435768038935119659)
  ·
    refine ⟨124121345153652058402679489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82747563435768038935119659 124121345153652058402679489)
    ·
      refine ⟨93091008865239043802009617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124121345153652058402679489 93091008865239043802009617)
      ·
        refine ⟨69818256648929282851507213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93091008865239043802009617 69818256648929282851507213)
        ·
          refine ⟨26181846243348481069315205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69818256648929282851507213 26181846243348481069315205)
          ·
            refine ⟨4909096170627840200496601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26181846243348481069315205 4909096170627840200496601)
            ·
              refine ⟨3681822127970880150372451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4909096170627840200496601 3681822127970880150372451)
              ·
                refine ⟨5522733191956320225558677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3681822127970880150372451 5522733191956320225558677)
                ·
                  refine ⟨258878118372952510573063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5522733191956320225558677 258878118372952510573063)
                  ·
                    rfl

theorem cell22_2268735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 6].length) (baseStart_2268735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268735 prefixEnd_2268735 := by exact prefixLift 2268735
  have htrace : WordTrace (prefixWord ++ tailWord_2268735) baseStart_2268735 baseEnd_2268735 := by
    simpa [prefixWord, tailWord_2268735, baseEnd_2268735] using wordTrace_append hprefix tailTrace_2268735
  have hstable : (prefixWord ++ tailWord_2268735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268735).length < 2 ^ (prefixWord ++ tailWord_2268735).sum := by decide
  have hdescent : baseEnd_2268735 < baseStart_2268735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268801 : List Nat := [1, 2, 4, 2, 1, 4, 2, 1, 2, 3]
def baseStart_2268801 : Nat := 118140960795 + 2268801 * 2 ^ 59
def prefixEnd_2268801 : Nat := 4983230072969 + 3 ^ 40 * 2268801 * 2
def baseEnd_2268801 : Nat := 776656948267655359568987

theorem tailTrace_2268801 : CollatzResearch.WordTrace tailWord_2268801 prefixEnd_2268801 776656948267655359568987 := by
  unfold tailWord_2268801
  simp only [CollatzResearch.WordTrace]
  refine ⟨82749970653528932207022257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55166647102352621471348171 82749970653528932207022257)
  ·
    refine ⟨62062477990146699155266693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82749970653528932207022257 62062477990146699155266693)
    ·
      refine ⟨11636714623152506091612505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62062477990146699155266693 11636714623152506091612505)
      ·
        refine ⟨8727535967364379568709379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11636714623152506091612505 8727535967364379568709379)
        ·
          refine ⟨13091303951046569353064069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8727535967364379568709379 13091303951046569353064069)
          ·
            refine ⟨2454619490821231753699513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13091303951046569353064069 2454619490821231753699513)
            ·
              refine ⟨1840964618115923815274635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2454619490821231753699513 1840964618115923815274635)
              ·
                refine ⟨2761446927173885722911953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840964618115923815274635 2761446927173885722911953)
                ·
                  refine ⟨2071085195380414292183965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2761446927173885722911953 2071085195380414292183965)
                  ·
                    refine ⟨776656948267655359568987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2071085195380414292183965 776656948267655359568987)
                    ·
                      rfl

theorem cell22_2268801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_2268801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268801 prefixEnd_2268801 := by exact prefixLift 2268801
  have htrace : WordTrace (prefixWord ++ tailWord_2268801) baseStart_2268801 baseEnd_2268801 := by
    simpa [prefixWord, tailWord_2268801, baseEnd_2268801] using wordTrace_append hprefix tailTrace_2268801
  have hstable : (prefixWord ++ tailWord_2268801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268801).length < 2 ^ (prefixWord ++ tailWord_2268801).sum := by decide
  have hdescent : baseEnd_2268801 < baseStart_2268801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268829 : List Nat := [1, 4, 2, 1, 1, 1, 1, 7, 1, 3]
def baseStart_2268829 : Nat := 118140960795 + 2268829 * 2 ^ 59
def prefixEnd_2268829 : Nat := 4983230072969 + 3 ^ 40 * 2268829 * 2
def baseEnd_2268829 : Nat := 776666533239872619868901

theorem tailTrace_2268829 : CollatzResearch.WordTrace tailWord_2268829 prefixEnd_2268829 776666533239872619868901 := by
  unfold tailWord_2268829
  simp only [CollatzResearch.WordTrace]
  refine ⟨82750991897427492989041541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55167327931618328659361027 82750991897427492989041541)
  ·
    refine ⟨15515810980767654935445289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82750991897427492989041541 15515810980767654935445289)
    ·
      refine ⟨11636858235575741201583967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15515810980767654935445289 11636858235575741201583967)
      ·
        refine ⟨17455287353363611802375951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11636858235575741201583967 17455287353363611802375951)
        ·
          refine ⟨26182931030045417703563927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17455287353363611802375951 26182931030045417703563927)
          ·
            refine ⟨39274396545068126555345891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26182931030045417703563927 39274396545068126555345891)
            ·
              refine ⟨58911594817602189833018837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39274396545068126555345891 58911594817602189833018837)
              ·
                refine ⟨1380740503537551324211379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 58911594817602189833018837 1380740503537551324211379)
                ·
                  refine ⟨2071110755306326986317069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1380740503537551324211379 2071110755306326986317069)
                  ·
                    refine ⟨776666533239872619868901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2071110755306326986317069 776666533239872619868901)
                    ·
                      rfl

theorem cell22_2268829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_2268829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268829 prefixEnd_2268829 := by exact prefixLift 2268829
  have htrace : WordTrace (prefixWord ++ tailWord_2268829) baseStart_2268829 baseEnd_2268829 := by
    simpa [prefixWord, tailWord_2268829, baseEnd_2268829] using wordTrace_append hprefix tailTrace_2268829
  have hstable : (prefixWord ++ tailWord_2268829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268829).length < 2 ^ (prefixWord ++ tailWord_2268829).sum := by decide
  have hdescent : baseEnd_2268829 < baseStart_2268829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268872 : List Nat := [2, 1, 3, 1, 2, 2, 2, 4, 1, 4]
def baseStart_2268872 : Nat := 118140960795 + 2268872 * 2 ^ 59
def prefixEnd_2268872 : Nat := 4983230072969 + 3 ^ 40 * 2268872 * 2
def baseEnd_2268872 : Nat := 776681253018634841043769

theorem tailTrace_2268872 : CollatzResearch.WordTrace tailWord_2268872 prefixEnd_2268872 776681253018634841043769 := by
  unfold tailWord_2268872
  simp only [CollatzResearch.WordTrace]
  refine ⟨41376280118135855666428435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55168373490847807555237913 41376280118135855666428435)
  ·
    refine ⟨62064420177203783499642653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41376280118135855666428435 62064420177203783499642653)
    ·
      refine ⟨23274157566451418812365995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62064420177203783499642653 23274157566451418812365995)
      ·
        refine ⟨34911236349677128218548993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23274157566451418812365995 34911236349677128218548993)
        ·
          refine ⟨26183427262257846163911745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34911236349677128218548993 26183427262257846163911745)
          ·
            refine ⟨19637570446693384622933809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26183427262257846163911745 19637570446693384622933809)
            ·
              refine ⟨14728177835020038467200357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19637570446693384622933809 14728177835020038467200357)
              ·
                refine ⟨2761533344066257212600067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14728177835020038467200357 2761533344066257212600067)
                ·
                  refine ⟨4142300016099385818900101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2761533344066257212600067 4142300016099385818900101)
                  ·
                    refine ⟨776681253018634841043769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4142300016099385818900101 776681253018634841043769)
                    ·
                      rfl

theorem cell22_2268872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_2268872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268872 prefixEnd_2268872 := by exact prefixLift 2268872
  have htrace : WordTrace (prefixWord ++ tailWord_2268872) baseStart_2268872 baseEnd_2268872 := by
    simpa [prefixWord, tailWord_2268872, baseEnd_2268872] using wordTrace_append hprefix tailTrace_2268872
  have hstable : (prefixWord ++ tailWord_2268872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268872).length < 2 ^ (prefixWord ++ tailWord_2268872).sum := by decide
  have hdescent : baseEnd_2268872 < baseStart_2268872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268889 : List Nat := [1, 2, 1, 2, 3, 3, 4, 1, 1, 4]
def baseStart_2268889 : Nat := 118140960795 + 2268889 * 2 ^ 59
def prefixEnd_2268889 : Nat := 4983230072969 + 3 ^ 40 * 2268889 * 2
def baseEnd_2268889 : Nat := 776687072466052463368717

theorem tailTrace_2268889 : CollatzResearch.WordTrace tailWord_2268889 prefixEnd_2268889 776687072466052463368717 := by
  unfold tailWord_2268889
  simp only [CollatzResearch.WordTrace]
  refine ⟨82753180277210123236225721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55168786851473415490817147 82753180277210123236225721)
  ·
    refine ⟨62064885207907592427169291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82753180277210123236225721 62064885207907592427169291)
    ·
      refine ⟨93097327811861388640753937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62064885207907592427169291 93097327811861388640753937)
      ·
        refine ⟨69822995858896041480565453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93097327811861388640753937 69822995858896041480565453)
        ·
          refine ⟨26183623447086015555212045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69822995858896041480565453 26183623447086015555212045)
          ·
            refine ⟨9818858792657255833204517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26183623447086015555212045 9818858792657255833204517)
            ·
              refine ⟨1841036023623235468725847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9818858792657255833204517 1841036023623235468725847)
              ·
                refine ⟨2761554035434853203088771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1841036023623235468725847 2761554035434853203088771)
                ·
                  refine ⟨4142331053152279804633157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2761554035434853203088771 4142331053152279804633157)
                  ·
                    refine ⟨776687072466052463368717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4142331053152279804633157 776687072466052463368717)
                    ·
                      rfl

theorem cell22_2268889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 1, 4].length) (baseStart_2268889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268889 prefixEnd_2268889 := by exact prefixLift 2268889
  have htrace : WordTrace (prefixWord ++ tailWord_2268889) baseStart_2268889 baseEnd_2268889 := by
    simpa [prefixWord, tailWord_2268889, baseEnd_2268889] using wordTrace_append hprefix tailTrace_2268889
  have hstable : (prefixWord ++ tailWord_2268889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268889).length < 2 ^ (prefixWord ++ tailWord_2268889).sum := by decide
  have hdescent : baseEnd_2268889 < baseStart_2268889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268893 : List Nat := [1, 4, 3, 3, 2, 1, 1, 2, 5]
def baseStart_2268893 : Nat := 118140960795 + 2268893 * 2 ^ 59
def prefixEnd_2268893 : Nat := 4983230072969 + 3 ^ 40 * 2268893 * 2
def baseEnd_2268893 : Nat := 258896147249265928756235

theorem tailTrace_2268893 : CollatzResearch.WordTrace tailWord_2268893 prefixEnd_2268893 258896147249265928756235 := by
  unfold tailWord_2268893
  simp only [CollatzResearch.WordTrace]
  refine ⟨82753326169195631919371333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55168884112797087946247555 82753326169195631919371333)
  ·
    refine ⟨15516248656724180984882125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82753326169195631919371333 15516248656724180984882125)
    ·
      refine ⟨5818593246271567869330797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15516248656724180984882125 5818593246271567869330797)
      ·
        refine ⟨2181972467351837950999049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5818593246271567869330797 2181972467351837950999049)
        ·
          refine ⟨1636479350513878463249287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2181972467351837950999049 1636479350513878463249287)
          ·
            refine ⟨2454719025770817694873931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1636479350513878463249287 2454719025770817694873931)
            ·
              refine ⟨3682078538656226542310897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2454719025770817694873931 3682078538656226542310897)
              ·
                refine ⟨2761558903992169906733173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3682078538656226542310897 2761558903992169906733173)
                ·
                  refine ⟨258896147249265928756235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2761558903992169906733173 258896147249265928756235)
                  ·
                    rfl

theorem cell22_2268893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_2268893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268893 prefixEnd_2268893 := by exact prefixLift 2268893
  have htrace : WordTrace (prefixWord ++ tailWord_2268893) baseStart_2268893 baseEnd_2268893 := by
    simpa [prefixWord, tailWord_2268893, baseEnd_2268893] using wordTrace_append hprefix tailTrace_2268893
  have hstable : (prefixWord ++ tailWord_2268893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268893).length < 2 ^ (prefixWord ++ tailWord_2268893).sum := by decide
  have hdescent : baseEnd_2268893 < baseStart_2268893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268904 : List Nat := [2, 1, 4, 1, 3, 1, 2, 4, 4]
def baseStart_2268904 : Nat := 118140960795 + 2268904 * 2 ^ 59
def prefixEnd_2268904 : Nat := 4983230072969 + 3 ^ 40 * 2268904 * 2
def baseEnd_2268904 : Nat := 258897402424199141414557

theorem tailTrace_2268904 : CollatzResearch.WordTrace tailWord_2268904 prefixEnd_2268904 258897402424199141414557 := by
  unfold tailWord_2268904
  simp only [CollatzResearch.WordTrace]
  refine ⟨41376863686077890399010883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55169151581437187198681177 41376863686077890399010883)
  ·
    refine ⟨62065295529116835598516325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41376863686077890399010883 62065295529116835598516325)
    ·
      refine ⟨11637242911709406674721811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62065295529116835598516325 11637242911709406674721811)
      ·
        refine ⟨17455864367564110012082717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11637242911709406674721811 17455864367564110012082717)
        ·
          refine ⟨6545949137836541254531019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17455864367564110012082717 6545949137836541254531019)
          ·
            refine ⟨9818923706754811881796529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6545949137836541254531019 9818923706754811881796529)
            ·
              refine ⟨7364192780066108911347397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9818923706754811881796529 7364192780066108911347397)
              ·
                refine ⟨1380786146262395420877637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7364192780066108911347397 1380786146262395420877637)
                ·
                  refine ⟨258897402424199141414557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1380786146262395420877637 258897402424199141414557)
                  ·
                    rfl

theorem cell22_2268904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 4].length) (baseStart_2268904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268904 prefixEnd_2268904 := by exact prefixLift 2268904
  have htrace : WordTrace (prefixWord ++ tailWord_2268904) baseStart_2268904 baseEnd_2268904 := by
    simpa [prefixWord, tailWord_2268904, baseEnd_2268904] using wordTrace_append hprefix tailTrace_2268904
  have hstable : (prefixWord ++ tailWord_2268904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268904).length < 2 ^ (prefixWord ++ tailWord_2268904).sum := by decide
  have hdescent : baseEnd_2268904 < baseStart_2268904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268932 : List Nat := [2, 3, 2, 2, 1, 3, 1, 8]
def baseStart_2268932 : Nat := 118140960795 + 2268932 * 2 ^ 59
def prefixEnd_2268932 : Nat := 4983230072969 + 3 ^ 40 * 2268932 * 2
def baseEnd_2268932 : Nat := 86300199138312742727065

theorem tailTrace_2268932 : CollatzResearch.WordTrace tailWord_2268932 prefixEnd_2268932 86300199138312742727065 := by
  unfold tailWord_2268932
  simp only [CollatzResearch.WordTrace]
  refine ⟨41377374308027170790020525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55169832410702894386694033 41377374308027170790020525)
  ·
    refine ⟨15516515365510189046257697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41377374308027170790020525 15516515365510189046257697)
    ·
      refine ⟨11637386524132641784693273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15516515365510189046257697 11637386524132641784693273)
      ·
        refine ⟨8728039893099481338519955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11637386524132641784693273 8728039893099481338519955)
        ·
          refine ⟨13092059839649222007779933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8728039893099481338519955 13092059839649222007779933)
          ·
            refine ⟨4909522439868458252917475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13092059839649222007779933 4909522439868458252917475)
            ·
              refine ⟨7364283659802687379376213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4909522439868458252917475 7364283659802687379376213)
              ·
                refine ⟨86300199138312742727065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7364283659802687379376213 86300199138312742727065)
                ·
                  rfl

theorem cell22_2268932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 8].length) (baseStart_2268932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268932 prefixEnd_2268932 := by exact prefixLift 2268932
  have htrace : WordTrace (prefixWord ++ tailWord_2268932) baseStart_2268932 baseEnd_2268932 := by
    simpa [prefixWord, tailWord_2268932, baseEnd_2268932] using wordTrace_append hprefix tailTrace_2268932
  have hstable : (prefixWord ++ tailWord_2268932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268932).length < 2 ^ (prefixWord ++ tailWord_2268932).sum := by decide
  have hdescent : baseEnd_2268932 < baseStart_2268932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268945 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 1, 8]
def baseStart_2268945 : Nat := 118140960795 + 2268945 * 2 ^ 59
def prefixEnd_2268945 : Nat := 4983230072969 + 3 ^ 40 * 2268945 * 2
def baseEnd_2268945 : Nat := 776706242410486983968545

theorem tailTrace_2268945 : CollatzResearch.WordTrace tailWord_2268945 prefixEnd_2268945 776706242410486983968545 := by
  unfold tailWord_2268945
  simp only [CollatzResearch.WordTrace]
  refine ⟨82755222765007244800264289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55170148510004829866842859 82755222765007244800264289)
  ·
    refine ⟨62066417073755433600198217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82755222765007244800264289 62066417073755433600198217)
    ·
      refine ⟨46549812805316575200148663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62066417073755433600198217 46549812805316575200148663)
      ·
        refine ⟨69824719207974862800222995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46549812805316575200148663 69824719207974862800222995)
        ·
          refine ⟨104737078811962294200334493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69824719207974862800222995 104737078811962294200334493)
          ·
            refine ⟨39276404554485860325125435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104737078811962294200334493 39276404554485860325125435)
            ·
              refine ⟨58914606831728790487688153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39276404554485860325125435 58914606831728790487688153)
              ·
                refine ⟨44185955123796592865766115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58914606831728790487688153 44185955123796592865766115)
                ·
                  refine ⟨66278932685694889298649173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44185955123796592865766115 66278932685694889298649173)
                  ·
                    refine ⟨776706242410486983968545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66278932685694889298649173 776706242410486983968545)
                    ·
                      rfl

theorem cell22_2268945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_2268945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268945 prefixEnd_2268945 := by exact prefixLift 2268945
  have htrace : WordTrace (prefixWord ++ tailWord_2268945) baseStart_2268945 baseEnd_2268945 := by
    simpa [prefixWord, tailWord_2268945, baseEnd_2268945] using wordTrace_append hprefix tailTrace_2268945
  have hstable : (prefixWord ++ tailWord_2268945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268945).length < 2 ^ (prefixWord ++ tailWord_2268945).sum := by decide
  have hdescent : baseEnd_2268945 < baseStart_2268945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268962 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_2268962 : Nat := 118140960795 + 2268962 * 2 ^ 59
def prefixEnd_2268962 : Nat := 4983230072969 + 3 ^ 40 * 2268962 * 2
def baseEnd_2268962 : Nat := 776712061857904606293493

theorem tailTrace_2268962 : CollatzResearch.WordTrace tailWord_2268962 prefixEnd_2268962 776712061857904606293493 := by
  unfold tailWord_2268962
  simp only [CollatzResearch.WordTrace]
  refine ⟨20688960701486414175908285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55170561870630437802422093 20688960701486414175908285)
  ·
    refine ⟨7758360263057405315965607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20688960701486414175908285 7758360263057405315965607)
    ·
      refine ⟨11637540394586107973948411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7758360263057405315965607 11637540394586107973948411)
      ·
        refine ⟨17456310591879161960922617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11637540394586107973948411 17456310591879161960922617)
        ·
          refine ⟨13092232943909371470691963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17456310591879161960922617 13092232943909371470691963)
          ·
            refine ⟨19638349415864057206037945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13092232943909371470691963 19638349415864057206037945)
            ·
              refine ⟨14728762061898042904528459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19638349415864057206037945 14728762061898042904528459)
              ·
                refine ⟨22093143092847064356792689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14728762061898042904528459 22093143092847064356792689)
                ·
                  refine ⟨16569857319635298267594517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22093143092847064356792689 16569857319635298267594517)
                  ·
                    refine ⟨776712061857904606293493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16569857319635298267594517 776712061857904606293493)
                    ·
                      rfl

theorem cell22_2268962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_2268962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2268962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2268962 prefixEnd_2268962 := by exact prefixLift 2268962
  have htrace : WordTrace (prefixWord ++ tailWord_2268962) baseStart_2268962 baseEnd_2268962 := by
    simpa [prefixWord, tailWord_2268962, baseEnd_2268962] using wordTrace_append hprefix tailTrace_2268962
  have hstable : (prefixWord ++ tailWord_2268962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268962).length < 2 ^ (prefixWord ++ tailWord_2268962).sum := by decide
  have hdescent : baseEnd_2268962 < baseStart_2268962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269015 : List Nat := [1, 1, 3, 2, 5, 2, 2, 2, 1, 3]
def baseStart_2269015 : Nat := 118140960795 + 2269015 * 2 ^ 59
def prefixEnd_2269015 : Nat := 4983230072969 + 3 ^ 40 * 2269015 * 2
def baseEnd_2269015 : Nat := 776730204841030134718331

theorem tailTrace_2269015 : CollatzResearch.WordTrace tailWord_2269015 prefixEnd_2269015 776730204841030134718331 := by
  unfold tailWord_2269015
  simp only [CollatzResearch.WordTrace]
  refine ⟨82757775874753646755312499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55171850583169097836874999 82757775874753646755312499)
  ·
    refine ⟨124136663812130470132968749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82757775874753646755312499 124136663812130470132968749)
    ·
      refine ⟨46551248929548926299863281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124136663812130470132968749 46551248929548926299863281)
      ·
        refine ⟨34913436697161694724897461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46551248929548926299863281 34913436697161694724897461)
        ·
          refine ⟨3273134690358908880459137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34913436697161694724897461 3273134690358908880459137)
          ·
            refine ⟨2454851017769181660344353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3273134690358908880459137 2454851017769181660344353)
            ·
              refine ⟨1841138263326886245258265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2454851017769181660344353 1841138263326886245258265)
              ·
                refine ⟨1380853697495164683943699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1841138263326886245258265 1380853697495164683943699)
                ·
                  refine ⟨2071280546242747025915549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1380853697495164683943699 2071280546242747025915549)
                  ·
                    refine ⟨776730204841030134718331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2071280546242747025915549 776730204841030134718331)
                    ·
                      rfl

theorem cell22_2269015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 1, 3].length) (baseStart_2269015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269015 prefixEnd_2269015 := by exact prefixLift 2269015
  have htrace : WordTrace (prefixWord ++ tailWord_2269015) baseStart_2269015 baseEnd_2269015 := by
    simpa [prefixWord, tailWord_2269015, baseEnd_2269015] using wordTrace_append hprefix tailTrace_2269015
  have hstable : (prefixWord ++ tailWord_2269015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269015).length < 2 ^ (prefixWord ++ tailWord_2269015).sum := by decide
  have hdescent : baseEnd_2269015 < baseStart_2269015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269112 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 9]
def baseStart_2269112 : Nat := 118140960795 + 2269112 * 2 ^ 59
def prefixEnd_2269112 : Nat := 4983230072969 + 3 ^ 40 * 2269112 * 2
def baseEnd_2269112 : Nat := 258921136641118071681011

theorem tailTrace_2269112 : CollatzResearch.WordTrace tailWord_2269112 prefixEnd_2269112 258921136641118071681011 := by
  unfold tailWord_2269112
  simp only [CollatzResearch.WordTrace]
  refine ⟨41380656877701116160796795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55174209170268154881062393 41380656877701116160796795)
  ·
    refine ⟨62070985316551674241195193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41380656877701116160796795 62070985316551674241195193)
    ·
      refine ⟨46553238987413755680896395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62070985316551674241195193 46553238987413755680896395)
      ·
        refine ⟨69829858481120633521344593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46553238987413755680896395 69829858481120633521344593)
        ·
          refine ⟨52372393860840475141008445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69829858481120633521344593 52372393860840475141008445)
          ·
            refine ⟨19639647697815178177878167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52372393860840475141008445 19639647697815178177878167)
            ·
              refine ⟨29459471546722767266817251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19639647697815178177878167 29459471546722767266817251)
              ·
                refine ⟨44189207320084150900225877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29459471546722767266817251 44189207320084150900225877)
                ·
                  refine ⟨258921136641118071681011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44189207320084150900225877 258921136641118071681011)
                  ·
                    rfl

theorem cell22_2269112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 9].length) (baseStart_2269112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269112 prefixEnd_2269112 := by exact prefixLift 2269112
  have htrace : WordTrace (prefixWord ++ tailWord_2269112) baseStart_2269112 baseEnd_2269112 := by
    simpa [prefixWord, tailWord_2269112, baseEnd_2269112] using wordTrace_append hprefix tailTrace_2269112
  have hstable : (prefixWord ++ tailWord_2269112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269112).length < 2 ^ (prefixWord ++ tailWord_2269112).sum := by decide
  have hdescent : baseEnd_2269112 < baseStart_2269112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269146 : List Nat := [3, 1, 1, 2, 5, 1, 1, 3, 5]
def baseStart_2269146 : Nat := 118140960795 + 2269146 * 2 ^ 59
def prefixEnd_2269146 : Nat := 4983230072969 + 3 ^ 40 * 2269146 * 2
def baseEnd_2269146 : Nat := 258925016272729819897643

theorem tailTrace_2269146 : CollatzResearch.WordTrace tailWord_2269146 prefixEnd_2269146 258925016272729819897643 := by
  unfold tailWord_2269146
  simp only [CollatzResearch.WordTrace]
  refine ⟨20690638459319764032082823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55175035891519370752220861 20690638459319764032082823)
  ·
    refine ⟨31035957688979646048124235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20690638459319764032082823 31035957688979646048124235)
    ·
      refine ⟨46553936533469469072186353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31035957688979646048124235 46553936533469469072186353)
      ·
        refine ⟨34915452400102101804139765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46553936533469469072186353 34915452400102101804139765)
        ·
          refine ⟨3273323662509572044138103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34915452400102101804139765 3273323662509572044138103)
          ·
            refine ⟨4909985493764358066207155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3273323662509572044138103 4909985493764358066207155)
            ·
              refine ⟨7364978240646537099310733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4909985493764358066207155 7364978240646537099310733)
              ·
                refine ⟨2761866840242451412241525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7364978240646537099310733 2761866840242451412241525)
                ·
                  refine ⟨258925016272729819897643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2761866840242451412241525 258925016272729819897643)
                  ·
                    rfl

theorem cell22_2269146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_2269146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269146 prefixEnd_2269146 := by exact prefixLift 2269146
  have htrace : WordTrace (prefixWord ++ tailWord_2269146) baseStart_2269146 baseEnd_2269146 := by
    simpa [prefixWord, tailWord_2269146, baseEnd_2269146] using wordTrace_append hprefix tailTrace_2269146
  have hstable : (prefixWord ++ tailWord_2269146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269146).length < 2 ^ (prefixWord ++ tailWord_2269146).sum := by decide
  have hdescent : baseEnd_2269146 < baseStart_2269146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269221 : List Nat := [1, 3, 1, 2, 2, 3, 3, 1, 2, 4]
def baseStart_2269221 : Nat := 118140960795 + 2269221 * 2 ^ 59
def prefixEnd_2269221 : Nat := 4983230072969 + 3 ^ 40 * 2269221 * 2
def baseEnd_2269221 : Nat := 776800722850914264067699

theorem tailTrace_2269221 : CollatzResearch.WordTrace tailWord_2269221 prefixEnd_2269221 776800722850914264067699 := by
  unfold tailWord_2269221
  simp only [CollatzResearch.WordTrace]
  refine ⟨82765289312007343937311517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55176859541338229291541011 82765289312007343937311517)
  ·
    refine ⟨31036983492002753976491819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82765289312007343937311517 31036983492002753976491819)
    ·
      refine ⟨46555475238004130964737729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31036983492002753976491819 46555475238004130964737729)
      ·
        refine ⟨34916606428503098223553297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46555475238004130964737729 34916606428503098223553297)
        ·
          refine ⟨26187454821377323667664973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34916606428503098223553297 26187454821377323667664973)
          ·
            refine ⟨9820295558016496375374365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26187454821377323667664973 9820295558016496375374365)
            ·
              refine ⟨3682610834256186140765387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9820295558016496375374365 3682610834256186140765387)
              ·
                refine ⟨5523916251384279211148081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3682610834256186140765387 5523916251384279211148081)
                ·
                  refine ⟨4142937188538209408361061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5523916251384279211148081 4142937188538209408361061)
                  ·
                    refine ⟨776800722850914264067699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4142937188538209408361061 776800722850914264067699)
                    ·
                      rfl

theorem cell22_2269221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_2269221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269221 prefixEnd_2269221 := by exact prefixLift 2269221
  have htrace : WordTrace (prefixWord ++ tailWord_2269221) baseStart_2269221 baseEnd_2269221 := by
    simpa [prefixWord, tailWord_2269221, baseEnd_2269221] using wordTrace_append hprefix tailTrace_2269221
  have hstable : (prefixWord ++ tailWord_2269221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269221).length < 2 ^ (prefixWord ++ tailWord_2269221).sum := by decide
  have hdescent : baseEnd_2269221 < baseStart_2269221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269240 : List Nat := [2, 1, 2, 1, 6, 2, 1, 2, 2, 3]
def baseStart_2269240 : Nat := 118140960795 + 2269240 * 2 ^ 59
def prefixEnd_2269240 : Nat := 4983230072969 + 3 ^ 40 * 2269240 * 2
def baseEnd_2269240 : Nat := 776807226939204547842641

theorem tailTrace_2269240 : CollatzResearch.WordTrace tailWord_2269240 prefixEnd_2269240 776807226939204547842641 := by
  unfold tailWord_2269240
  simp only [CollatzResearch.WordTrace]
  refine ⟨41382991149469255091126587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55177321532625673454835449 41382991149469255091126587)
  ·
    refine ⟨62074486724203882636689881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41382991149469255091126587 62074486724203882636689881)
    ·
      refine ⟨46555865043152911977517411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62074486724203882636689881 46555865043152911977517411)
      ·
        refine ⟨69833797564729367966276117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46555865043152911977517411 69833797564729367966276117)
        ·
          refine ⟨3273459260846689123419193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69833797564729367966276117 3273459260846689123419193)
          ·
            refine ⟨2455094445635016842564395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3273459260846689123419193 2455094445635016842564395)
            ·
              refine ⟨3682641668452525263846593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2455094445635016842564395 3682641668452525263846593)
              ·
                refine ⟨2761981251339393947884945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3682641668452525263846593 2761981251339393947884945)
                ·
                  refine ⟨2071485938504545460913709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2761981251339393947884945 2071485938504545460913709)
                  ·
                    refine ⟨776807226939204547842641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2071485938504545460913709 776807226939204547842641)
                    ·
                      rfl

theorem cell22_2269240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_2269240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269240 prefixEnd_2269240 := by exact prefixLift 2269240
  have htrace : WordTrace (prefixWord ++ tailWord_2269240) baseStart_2269240 baseEnd_2269240 := by
    simpa [prefixWord, tailWord_2269240, baseEnd_2269240] using wordTrace_append hprefix tailTrace_2269240
  have hstable : (prefixWord ++ tailWord_2269240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269240).length < 2 ^ (prefixWord ++ tailWord_2269240).sum := by decide
  have hdescent : baseEnd_2269240 < baseStart_2269240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269270 : List Nat := [5, 2, 2, 1, 1, 1, 4, 6]
def baseStart_2269270 : Nat := 118140960795 + 2269270 * 2 ^ 59
def prefixEnd_2269270 : Nat := 4983230072969 + 3 ^ 40 * 2269270 * 2
def baseEnd_2269270 : Nat := 86313055172477163288061

theorem tailTrace_2269270 : CollatzResearch.WordTrace tailWord_2269270 prefixEnd_2269270 86313055172477163288061 := by
  unfold tailWord_2269270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5172942280551864081615329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55178050992553216870563509 5172942280551864081615329)
  ·
    refine ⟨3879706710413898061211497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5172942280551864081615329 3879706710413898061211497)
    ·
      refine ⟨2909780032810423545908623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3879706710413898061211497 2909780032810423545908623)
      ·
        refine ⟨4364670049215635318862935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2909780032810423545908623 4364670049215635318862935)
        ·
          refine ⟨6547005073823452978294403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4364670049215635318862935 6547005073823452978294403)
          ·
            refine ⟨9820507610735179467441605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6547005073823452978294403 9820507610735179467441605)
            ·
              refine ⟨1841345177012846150145301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9820507610735179467441605 1841345177012846150145301)
              ·
                refine ⟨86313055172477163288061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1841345177012846150145301 86313055172477163288061)
                ·
                  rfl

theorem cell22_2269270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_2269270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269270 prefixEnd_2269270 := by exact prefixLift 2269270
  have htrace : WordTrace (prefixWord ++ tailWord_2269270) baseStart_2269270 baseEnd_2269270 := by
    simpa [prefixWord, tailWord_2269270, baseEnd_2269270] using wordTrace_append hprefix tailTrace_2269270
  have hstable : (prefixWord ++ tailWord_2269270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269270).length < 2 ^ (prefixWord ++ tailWord_2269270).sum := by decide
  have hdescent : baseEnd_2269270 < baseStart_2269270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269279 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 4, 5]
def baseStart_2269279 : Nat := 118140960795 + 2269279 * 2 ^ 59
def prefixEnd_2269279 : Nat := 4983230072969 + 3 ^ 40 * 2269279 * 2
def baseEnd_2269279 : Nat := 776820577436221446117521

theorem tailTrace_2269279 : CollatzResearch.WordTrace tailWord_2269279 prefixEnd_2269279 776820577436221446117521 := by
  unfold tailWord_2269279
  simp only [CollatzResearch.WordTrace]
  refine ⟨82767404745797219842922891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55178269830531479895281927 82767404745797219842922891)
  ·
    refine ⟨124151107118695829764384337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82767404745797219842922891 124151107118695829764384337)
    ·
      refine ⟨93113330339021872323288253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124151107118695829764384337 93113330339021872323288253)
      ·
        refine ⟨34917498877133202121233095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93113330339021872323288253 34917498877133202121233095)
        ·
          refine ⟨52376248315699803181849643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34917498877133202121233095 52376248315699803181849643)
          ·
            refine ⟨78564372473549704772774465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52376248315699803181849643 78564372473549704772774465)
            ·
              refine ⟨58923279355162278579580849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78564372473549704772774465 58923279355162278579580849)
              ·
                refine ⟨44192459516371708934685637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58923279355162278579580849 44192459516371708934685637)
                ·
                  refine ⟨8286086159319695425253557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44192459516371708934685637 8286086159319695425253557)
                  ·
                    refine ⟨776820577436221446117521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8286086159319695425253557 776820577436221446117521)
                    ·
                      rfl

theorem cell22_2269279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_2269279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269279 prefixEnd_2269279 := by exact prefixLift 2269279
  have htrace : WordTrace (prefixWord ++ tailWord_2269279) baseStart_2269279 baseEnd_2269279 := by
    simpa [prefixWord, tailWord_2269279, baseEnd_2269279] using wordTrace_append hprefix tailTrace_2269279
  have hstable : (prefixWord ++ tailWord_2269279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269279).length < 2 ^ (prefixWord ++ tailWord_2269279).sum := by decide
  have hdescent : baseEnd_2269279 < baseStart_2269279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269285 : List Nat := [1, 3, 1, 3, 2, 2, 3, 3, 1, 3]
def baseStart_2269285 : Nat := 118140960795 + 2269285 * 2 ^ 59
def prefixEnd_2269285 : Nat := 4983230072969 + 3 ^ 40 * 2269285 * 2
def baseEnd_2269285 : Nat := 776822631358839430467503

theorem tailTrace_2269285 : CollatzResearch.WordTrace tailWord_2269285 prefixEnd_2269285 776822631358839430467503 := by
  unfold tailWord_2269285
  simp only [CollatzResearch.WordTrace]
  refine ⟨82767623583775482867641309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55178415722516988578427539 82767623583775482867641309)
  ·
    refine ⟨31037858843915806075365491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82767623583775482867641309 31037858843915806075365491)
    ·
      refine ⟨46556788265873709113048237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31037858843915806075365491 46556788265873709113048237)
      ·
        refine ⟨17458795599702640917393089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46556788265873709113048237 17458795599702640917393089)
        ·
          refine ⟨13094096699776980688044817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17458795599702640917393089 13094096699776980688044817)
          ·
            refine ⟨9820572524832735516033613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13094096699776980688044817 9820572524832735516033613)
            ·
              refine ⟨3682714696812275818512605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9820572524832735516033613 3682714696812275818512605)
              ·
                refine ⟨1381018011304603431942227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3682714696812275818512605 1381018011304603431942227)
                ·
                  refine ⟨2071527016956905147913341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1381018011304603431942227 2071527016956905147913341)
                  ·
                    refine ⟨776822631358839430467503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2071527016956905147913341 776822631358839430467503)
                    ·
                      rfl

theorem cell22_2269285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 1, 3].length) (baseStart_2269285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269285 prefixEnd_2269285 := by exact prefixLift 2269285
  have htrace : WordTrace (prefixWord ++ tailWord_2269285) baseStart_2269285 baseEnd_2269285 := by
    simpa [prefixWord, tailWord_2269285, baseEnd_2269285] using wordTrace_append hprefix tailTrace_2269285
  have hstable : (prefixWord ++ tailWord_2269285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269285).length < 2 ^ (prefixWord ++ tailWord_2269285).sum := by decide
  have hdescent : baseEnd_2269285 < baseStart_2269285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269341 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_2269341 : Nat := 118140960795 + 2269341 * 2 ^ 59
def prefixEnd_2269341 : Nat := 4983230072969 + 3 ^ 40 * 2269341 * 2
def baseEnd_2269341 : Nat := 776841801303273951067331

theorem tailTrace_2269341 : CollatzResearch.WordTrace tailWord_2269341 prefixEnd_2269341 776841801303273951067331 := by
  unfold tailWord_2269341
  simp only [CollatzResearch.WordTrace]
  refine ⟨82769666071572604431679877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55179777381048402954453251 82769666071572604431679877)
  ·
    refine ⟨15519312388419863330939977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82769666071572604431679877 15519312388419863330939977)
    ·
      refine ⟨11639484291314897498204983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15519312388419863330939977 11639484291314897498204983)
      ·
        refine ⟨17459226436972346247307475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11639484291314897498204983 17459226436972346247307475)
        ·
          refine ⟨26188839655458519370961213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17459226436972346247307475 26188839655458519370961213)
          ·
            refine ⟨9820814870796944764110455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26188839655458519370961213 9820814870796944764110455)
            ·
              refine ⟨14731222306195417146165683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9820814870796944764110455 14731222306195417146165683)
              ·
                refine ⟨22096833459293125719248525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14731222306195417146165683 22096833459293125719248525)
                ·
                  refine ⟨8286312547234922144718197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22096833459293125719248525 8286312547234922144718197)
                  ·
                    refine ⟨776841801303273951067331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8286312547234922144718197 776841801303273951067331)
                    ·
                      rfl

theorem cell22_2269341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_2269341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269341 prefixEnd_2269341 := by exact prefixLift 2269341
  have htrace : WordTrace (prefixWord ++ tailWord_2269341) baseStart_2269341 baseEnd_2269341 := by
    simpa [prefixWord, tailWord_2269341, baseEnd_2269341] using wordTrace_append hprefix tailTrace_2269341
  have hstable : (prefixWord ++ tailWord_2269341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269341).length < 2 ^ (prefixWord ++ tailWord_2269341).sum := by decide
  have hdescent : baseEnd_2269341 < baseStart_2269341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269345 : List Nat := [1, 2, 3, 3, 1, 3, 3, 1, 1, 4]
def baseStart_2269345 : Nat := 118140960795 + 2269345 * 2 ^ 59
def prefixEnd_2269345 : Nat := 4983230072969 + 3 ^ 40 * 2269345 * 2
def baseEnd_2269345 : Nat := 776843170585019273967319

theorem tailTrace_2269345 : CollatzResearch.WordTrace tailWord_2269345 prefixEnd_2269345 776843170585019273967319 := by
  unfold tailWord_2269345
  simp only [CollatzResearch.WordTrace]
  refine ⟨82769811963558113114825489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55179874642372075409883659 82769811963558113114825489)
  ·
    refine ⟨62077358972668584836119117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82769811963558113114825489 62077358972668584836119117)
    ·
      refine ⟨23279009614750719313544669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62077358972668584836119117 23279009614750719313544669)
      ·
        refine ⟨8729628605531519742579251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23279009614750719313544669 8729628605531519742579251)
        ·
          refine ⟨13094442908297279613868877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8729628605531519742579251 13094442908297279613868877)
          ·
            refine ⟨4910416090611479855200829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13094442908297279613868877 4910416090611479855200829)
            ·
              refine ⟨1841406033979304945700311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4910416090611479855200829 1841406033979304945700311)
              ·
                refine ⟨2762109050968957418550467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1841406033979304945700311 2762109050968957418550467)
                ·
                  refine ⟨4143163576453436127825701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2762109050968957418550467 4143163576453436127825701)
                  ·
                    refine ⟨776843170585019273967319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4143163576453436127825701 776843170585019273967319)
                    ·
                      rfl

theorem cell22_2269345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_2269345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269345 prefixEnd_2269345 := by exact prefixLift 2269345
  have htrace : WordTrace (prefixWord ++ tailWord_2269345) baseStart_2269345 baseEnd_2269345 := by
    simpa [prefixWord, tailWord_2269345, baseEnd_2269345] using wordTrace_append hprefix tailTrace_2269345
  have hstable : (prefixWord ++ tailWord_2269345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269345).length < 2 ^ (prefixWord ++ tailWord_2269345).sum := by decide
  have hdescent : baseEnd_2269345 < baseStart_2269345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269390 : List Nat := [4, 1, 1, 1, 4, 3, 1, 1, 2, 4]
def baseStart_2269390 : Nat := 118140960795 + 2269390 * 2 ^ 59
def prefixEnd_2269390 : Nat := 4983230072969 + 3 ^ 40 * 2269390 * 2
def baseEnd_2269390 : Nat := 776858575004654156592181

theorem tailTrace_2269390 : CollatzResearch.WordTrace tailWord_2269390 prefixEnd_2269390 776858575004654156592181 := by
  unfold tailWord_2269390
  simp only [CollatzResearch.WordTrace]
  refine ⟨10346431656049385725026703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55180968832263390533475749 10346431656049385725026703)
  ·
    refine ⟨15519647484074078587540055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10346431656049385725026703 15519647484074078587540055)
    ·
      refine ⟨23279471226111117881310083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15519647484074078587540055 23279471226111117881310083)
      ·
        refine ⟨34919206839166676821965125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23279471226111117881310083 34919206839166676821965125)
        ·
          refine ⟨6547351282343751904118461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34919206839166676821965125 6547351282343751904118461)
          ·
            refine ⟨2455256730878906964044423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6547351282343751904118461 2455256730878906964044423)
            ·
              refine ⟨3682885096318360446066635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2455256730878906964044423 3682885096318360446066635)
              ·
                refine ⟨5524327644477540669099953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3682885096318360446066635 5524327644477540669099953)
                ·
                  refine ⟨4143245733358155501824965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5524327644477540669099953 4143245733358155501824965)
                  ·
                    refine ⟨776858575004654156592181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4143245733358155501824965 776858575004654156592181)
                    ·
                      rfl

theorem cell22_2269390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_2269390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269390 prefixEnd_2269390 := by exact prefixLift 2269390
  have htrace : WordTrace (prefixWord ++ tailWord_2269390) baseStart_2269390 baseEnd_2269390 := by
    simpa [prefixWord, tailWord_2269390, baseEnd_2269390] using wordTrace_append hprefix tailTrace_2269390
  have hstable : (prefixWord ++ tailWord_2269390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269390).length < 2 ^ (prefixWord ++ tailWord_2269390).sum := by decide
  have hdescent : baseEnd_2269390 < baseStart_2269390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269420 : List Nat := [2, 2, 1, 1, 2, 3, 1, 6, 1, 3]
def baseStart_2269420 : Nat := 118140960795 + 2269420 * 2 ^ 59
def prefixEnd_2269420 : Nat := 4983230072969 + 3 ^ 40 * 2269420 * 2
def baseEnd_2269420 : Nat := 776868844617744078342089

theorem tailTrace_2269420 : CollatzResearch.WordTrace tailWord_2269420 prefixEnd_2269420 776868844617744078342089 := by
  unfold tailWord_2269420
  simp only [CollatzResearch.WordTrace]
  refine ⟨41386273719143200461902857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55181698292190933949203809 41386273719143200461902857)
  ·
    refine ⟨31039705289357400346427143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41386273719143200461902857 31039705289357400346427143)
    ·
      refine ⟨46559557934036100519640715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31039705289357400346427143 46559557934036100519640715)
      ·
        refine ⟨69839336901054150779461073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46559557934036100519640715 69839336901054150779461073)
        ·
          refine ⟨52379502675790613084595805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69839336901054150779461073 52379502675790613084595805)
          ·
            refine ⟨19642313503421479906723427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52379502675790613084595805 19642313503421479906723427)
            ·
              refine ⟨29463470255132219860085141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19642313503421479906723427 29463470255132219860085141)
              ·
                refine ⟨1381100168209322805941491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29463470255132219860085141 1381100168209322805941491)
                ·
                  refine ⟨2071650252313984208912237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1381100168209322805941491 2071650252313984208912237)
                  ·
                    refine ⟨776868844617744078342089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2071650252313984208912237 776868844617744078342089)
                    ·
                      rfl

theorem cell22_2269420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 1, 3].length) (baseStart_2269420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269420 prefixEnd_2269420 := by exact prefixLift 2269420
  have htrace : WordTrace (prefixWord ++ tailWord_2269420) baseStart_2269420 baseEnd_2269420 := by
    simpa [prefixWord, tailWord_2269420, baseEnd_2269420] using wordTrace_append hprefix tailTrace_2269420
  have hstable : (prefixWord ++ tailWord_2269420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269420).length < 2 ^ (prefixWord ++ tailWord_2269420).sum := by decide
  have hdescent : baseEnd_2269420 < baseStart_2269420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269461 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 8]
def baseStart_2269461 : Nat := 118140960795 + 2269461 * 2 ^ 59
def prefixEnd_2269461 : Nat := 4983230072969 + 3 ^ 40 * 2269461 * 2
def baseEnd_2269461 : Nat := 258960959918544546022321

theorem tailTrace_2269461 : CollatzResearch.WordTrace tailWord_2269461 prefixEnd_2269461 258960959918544546022321 := by
  unfold tailWord_2269461
  simp only [CollatzResearch.WordTrace]
  refine ⟨82774042831137864926048237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55182695220758576617365491 82774042831137864926048237)
  ·
    refine ⟨31040266061676699347268089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82774042831137864926048237 31040266061676699347268089)
    ·
      refine ⟨23280199546257524510451067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31040266061676699347268089 23280199546257524510451067)
      ·
        refine ⟨34920299319386286765676601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23280199546257524510451067 34920299319386286765676601)
        ·
          refine ⟨26190224489539715074257451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34920299319386286765676601 26190224489539715074257451)
          ·
            refine ⟨39285336734309572611386177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26190224489539715074257451 39285336734309572611386177)
            ·
              refine ⟨29464002550732179458539633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39285336734309572611386177 29464002550732179458539633)
              ·
                refine ⟨22098001913049134593904725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29464002550732179458539633 22098001913049134593904725)
                ·
                  refine ⟨258960959918544546022321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22098001913049134593904725 258960959918544546022321)
                  ·
                    rfl

theorem cell22_2269461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_2269461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269461 prefixEnd_2269461 := by exact prefixLift 2269461
  have htrace : WordTrace (prefixWord ++ tailWord_2269461) baseStart_2269461 baseEnd_2269461 := by
    simpa [prefixWord, tailWord_2269461, baseEnd_2269461] using wordTrace_append hprefix tailTrace_2269461
  have hstable : (prefixWord ++ tailWord_2269461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269461).length < 2 ^ (prefixWord ++ tailWord_2269461).sum := by decide
  have hdescent : baseEnd_2269461 < baseStart_2269461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269493 : List Nat := [1, 3, 3, 1, 2, 1, 2, 3, 1, 5]
def baseStart_2269493 : Nat := 118140960795 + 2269493 * 2 ^ 59
def prefixEnd_2269493 : Nat := 4983230072969 + 3 ^ 40 * 2269493 * 2
def baseEnd_2269493 : Nat := 776893834009596221266865

theorem tailTrace_2269493 : CollatzResearch.WordTrace tailWord_2269493 prefixEnd_2269493 776893834009596221266865 := by
  unfold tailWord_2269493
  simp only [CollatzResearch.WordTrace]
  refine ⟨82775209967021934391213133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55183473311347956260808755 82775209967021934391213133)
  ·
    refine ⟨31040703737633225396704925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82775209967021934391213133 31040703737633225396704925)
    ·
      refine ⟨11640263901612459523764347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31040703737633225396704925 11640263901612459523764347)
      ·
        refine ⟨17460395852418689285646521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11640263901612459523764347 17460395852418689285646521)
        ·
          refine ⟨13095296889314016964234891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17460395852418689285646521 13095296889314016964234891)
          ·
            refine ⟨19642945333971025446352337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13095296889314016964234891 19642945333971025446352337)
            ·
              refine ⟨14732209000478269084764253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19642945333971025446352337 14732209000478269084764253)
              ·
                refine ⟨5524578375179350906786595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14732209000478269084764253 5524578375179350906786595)
                ·
                  refine ⟨8286867562769026360179893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5524578375179350906786595 8286867562769026360179893)
                  ·
                    refine ⟨776893834009596221266865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8286867562769026360179893 776893834009596221266865)
                    ·
                      rfl

theorem cell22_2269493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_2269493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269493 prefixEnd_2269493 := by exact prefixLift 2269493
  have htrace : WordTrace (prefixWord ++ tailWord_2269493) baseStart_2269493 baseEnd_2269493 := by
    simpa [prefixWord, tailWord_2269493, baseEnd_2269493] using wordTrace_append hprefix tailTrace_2269493
  have hstable : (prefixWord ++ tailWord_2269493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269493).length < 2 ^ (prefixWord ++ tailWord_2269493).sum := by decide
  have hdescent : baseEnd_2269493 < baseStart_2269493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269497 : List Nat := [1, 2, 1, 6, 1, 3, 1, 2, 1, 4]
def baseStart_2269497 : Nat := 118140960795 + 2269497 * 2 ^ 59
def prefixEnd_2269497 : Nat := 4983230072969 + 3 ^ 40 * 2269497 * 2
def baseEnd_2269497 : Nat := 776895203291341544166853

theorem tailTrace_2269497 : CollatzResearch.WordTrace tailWord_2269497 prefixEnd_2269497 776895203291341544166853 := by
  unfold tailWord_2269497
  simp only [CollatzResearch.WordTrace]
  refine ⟨82775355859007443074358745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55183570572671628716239163 82775355859007443074358745)
  ·
    refine ⟨62081516894255582305769059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82775355859007443074358745 62081516894255582305769059)
    ·
      refine ⟨93122275341383373458653589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62081516894255582305769059 93122275341383373458653589)
      ·
        refine ⟨4365106656627345630874387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 93122275341383373458653589 4365106656627345630874387)
        ·
          refine ⟨6547659984941018446311581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4365106656627345630874387 6547659984941018446311581)
          ·
            refine ⟨2455372494352881917366843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6547659984941018446311581 2455372494352881917366843)
            ·
              refine ⟨3683058741529322876050265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2455372494352881917366843 3683058741529322876050265)
              ·
                refine ⟨2762294056146992157037699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3683058741529322876050265 2762294056146992157037699)
                ·
                  refine ⟨4143441084220488235556549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2762294056146992157037699 4143441084220488235556549)
                  ·
                    refine ⟨776895203291341544166853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4143441084220488235556549 776895203291341544166853)
                    ·
                      rfl

theorem cell22_2269497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 4].length) (baseStart_2269497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269497 prefixEnd_2269497 := by exact prefixLift 2269497
  have htrace : WordTrace (prefixWord ++ tailWord_2269497) baseStart_2269497 baseEnd_2269497 := by
    simpa [prefixWord, tailWord_2269497, baseEnd_2269497] using wordTrace_append hprefix tailTrace_2269497
  have hstable : (prefixWord ++ tailWord_2269497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269497).length < 2 ^ (prefixWord ++ tailWord_2269497).sum := by decide
  have hdescent : baseEnd_2269497 < baseStart_2269497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269602 : List Nat := [3, 3, 1, 2, 1, 1, 5, 1, 5]
def baseStart_2269602 : Nat := 118140960795 + 2269602 * 2 ^ 59
def prefixEnd_2269602 : Nat := 4983230072969 + 3 ^ 40 * 2269602 * 2
def baseEnd_2269602 : Nat := 258977048979052090097177

theorem tailTrace_2269602 : CollatzResearch.WordTrace tailWord_2269602 prefixEnd_2269602 258977048979052090097177 := by
  unfold tailWord_2269602
  simp only [CollatzResearch.WordTrace]
  refine ⟨20694796380906761501732765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55186123682418030671287373 20694796380906761501732765)
  ·
    refine ⟨7760548642840035563149787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20694796380906761501732765 7760548642840035563149787)
    ·
      refine ⟨11640822964260053344724681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7760548642840035563149787 11640822964260053344724681)
      ·
        refine ⟨8730617223195040008543511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11640822964260053344724681 8730617223195040008543511)
        ·
          refine ⟨13095925834792560012815267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8730617223195040008543511 13095925834792560012815267)
          ·
            refine ⟨19643888752188840019222901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13095925834792560012815267 19643888752188840019222901)
            ·
              refine ⟨1841614570517703751802147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19643888752188840019222901 1841614570517703751802147)
              ·
                refine ⟨2762421855776555627703221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1841614570517703751802147 2762421855776555627703221)
                ·
                  refine ⟨258977048979052090097177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2762421855776555627703221 258977048979052090097177)
                  ·
                    rfl

theorem cell22_2269602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_2269602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269602 prefixEnd_2269602 := by exact prefixLift 2269602
  have htrace : WordTrace (prefixWord ++ tailWord_2269602) baseStart_2269602 baseEnd_2269602 := by
    simpa [prefixWord, tailWord_2269602, baseEnd_2269602] using wordTrace_append hprefix tailTrace_2269602
  have hstable : (prefixWord ++ tailWord_2269602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269602).length < 2 ^ (prefixWord ++ tailWord_2269602).sum := by decide
  have hdescent : baseEnd_2269602 < baseStart_2269602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269677 : List Nat := [1, 5, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_2269677 : Nat := 118140960795 + 2269677 * 2 ^ 59
def prefixEnd_2269677 : Nat := 4983230072969 + 3 ^ 40 * 2269677 * 2
def baseEnd_2269677 : Nat := 776956820969881074666301

theorem tailTrace_2269677 : CollatzResearch.WordTrace tailWord_2269677 prefixEnd_2269677 776956820969881074666301 := by
  unfold tailWord_2269677
  simp only [CollatzResearch.WordTrace]
  refine ⟨82781920998355333815911285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55187947332236889210607523 82781920998355333815911285)
  ·
    refine ⟨7760805093595812545241683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82781920998355333815911285 7760805093595812545241683)
    ·
      refine ⟨11641207640393718817862525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7760805093595812545241683 11641207640393718817862525)
      ·
        refine ⟨4365452865147644556698447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11641207640393718817862525 4365452865147644556698447)
        ·
          refine ⟨6548179297721466835047671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4365452865147644556698447 6548179297721466835047671)
          ·
            refine ⟨9822268946582200252571507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6548179297721466835047671 9822268946582200252571507)
            ·
              refine ⟨14733403419873300378857261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9822268946582200252571507 14733403419873300378857261)
              ·
                refine ⟨5525026282452487642071473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14733403419873300378857261 5525026282452487642071473)
                ·
                  refine ⟨4143769711839365731553605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5525026282452487642071473 4143769711839365731553605)
                  ·
                    refine ⟨776956820969881074666301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4143769711839365731553605 776956820969881074666301)
                    ·
                      rfl

theorem cell22_2269677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_2269677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269677 prefixEnd_2269677 := by exact prefixLift 2269677
  have htrace : WordTrace (prefixWord ++ tailWord_2269677) baseStart_2269677 baseEnd_2269677 := by
    simpa [prefixWord, tailWord_2269677, baseEnd_2269677] using wordTrace_append hprefix tailTrace_2269677
  have hstable : (prefixWord ++ tailWord_2269677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269677).length < 2 ^ (prefixWord ++ tailWord_2269677).sum := by decide
  have hdescent : baseEnd_2269677 < baseStart_2269677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269690 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 7, 3]
def baseStart_2269690 : Nat := 118140960795 + 2269690 * 2 ^ 59
def prefixEnd_2269690 : Nat := 4983230072969 + 3 ^ 40 * 2269690 * 2
def baseEnd_2269690 : Nat := 776961271135553374091261

theorem tailTrace_2269690 : CollatzResearch.WordTrace tailWord_2269690 prefixEnd_2269690 776961271135553374091261 := by
  unfold tailWord_2269690
  simp only [CollatzResearch.WordTrace]
  refine ⟨20695598786827059259033631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55188263431538824690756349 20695598786827059259033631)
  ·
    refine ⟨31043398180240588888550447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20695598786827059259033631 31043398180240588888550447)
    ·
      refine ⟨46565097270360883332825671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31043398180240588888550447 46565097270360883332825671)
      ·
        refine ⟨69847645905541324999238507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46565097270360883332825671 69847645905541324999238507)
        ·
          refine ⟨104771468858311987498857761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69847645905541324999238507 104771468858311987498857761)
          ·
            refine ⟨78578601643733990624143321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104771468858311987498857761 78578601643733990624143321)
            ·
              refine ⟨58933951232800492968107491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78578601643733990624143321 58933951232800492968107491)
              ·
                refine ⟨88400926849200739452161237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58933951232800492968107491 88400926849200739452161237)
                ·
                  refine ⟨2071896723028142330910029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 88400926849200739452161237 2071896723028142330910029)
                  ·
                    refine ⟨776961271135553374091261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2071896723028142330910029 776961271135553374091261)
                    ·
                      rfl

theorem cell22_2269690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_2269690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269690 prefixEnd_2269690 := by exact prefixLift 2269690
  have htrace : WordTrace (prefixWord ++ tailWord_2269690) baseStart_2269690 baseEnd_2269690 := by
    simpa [prefixWord, tailWord_2269690, baseEnd_2269690] using wordTrace_append hprefix tailTrace_2269690
  have hstable : (prefixWord ++ tailWord_2269690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269690).length < 2 ^ (prefixWord ++ tailWord_2269690).sum := by decide
  have hdescent : baseEnd_2269690 < baseStart_2269690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269698 : List Nat := [3, 4, 1, 2, 2, 2, 2, 2, 4]
def baseStart_2269698 : Nat := 118140960795 + 2269698 * 2 ^ 59
def prefixEnd_2269698 : Nat := 4983230072969 + 3 ^ 40 * 2269698 * 2
def baseEnd_2269698 : Nat := 258988003233014673297079

theorem tailTrace_2269698 : CollatzResearch.WordTrace tailWord_2269698 prefixEnd_2269698 258988003233014673297079 := by
  unfold tailWord_2269698
  simp only [CollatzResearch.WordTrace]
  refine ⟨20695671732819813600606437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55188457954186169601617165 20695671732819813600606437)
  ·
    refine ⟨3880438449903715050113707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20695671732819813600606437 3880438449903715050113707)
    ·
      refine ⟨5820657674855572575170561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3880438449903715050113707 5820657674855572575170561)
      ·
        refine ⟨4365493256141679431377921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5820657674855572575170561 4365493256141679431377921)
        ·
          refine ⟨3274119942106259573533441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4365493256141679431377921 3274119942106259573533441)
          ·
            refine ⟨2455589956579694680150081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3274119942106259573533441 2455589956579694680150081)
            ·
              refine ⟨1841692467434771010112561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2455589956579694680150081 1841692467434771010112561)
              ·
                refine ⟨1381269350576078257584421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1841692467434771010112561 1381269350576078257584421)
                ·
                  refine ⟨258988003233014673297079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1381269350576078257584421 258988003233014673297079)
                  ·
                    rfl

theorem cell22_2269698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_2269698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269698 prefixEnd_2269698 := by exact prefixLift 2269698
  have htrace : WordTrace (prefixWord ++ tailWord_2269698) baseStart_2269698 baseEnd_2269698 := by
    simpa [prefixWord, tailWord_2269698, baseEnd_2269698] using wordTrace_append hprefix tailTrace_2269698
  have hstable : (prefixWord ++ tailWord_2269698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269698).length < 2 ^ (prefixWord ++ tailWord_2269698).sum := by decide
  have hdescent : baseEnd_2269698 < baseStart_2269698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269709 : List Nat := [1, 7, 1, 1, 1, 1, 3, 7]
def baseStart_2269709 : Nat := 118140960795 + 2269709 * 2 ^ 59
def prefixEnd_2269709 : Nat := 4983230072969 + 3 ^ 40 * 2269709 * 2
def baseEnd_2269709 : Nat := 86329752802649295318467

theorem tailTrace_2269709 : CollatzResearch.WordTrace tailWord_2269709 prefixEnd_2269709 86329752802649295318467 := by
  unfold tailWord_2269709
  simp only [CollatzResearch.WordTrace]
  refine ⟨82783088134239403281076181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55188725422826268854050787 82783088134239403281076181)
  ·
    refine ⟨1940228628146236014400223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 82783088134239403281076181 1940228628146236014400223)
    ·
      refine ⟨2910342942219354021600335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1940228628146236014400223 2910342942219354021600335)
      ·
        refine ⟨4365514413329031032400503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2910342942219354021600335 4365514413329031032400503)
        ·
          refine ⟨6548271619993546548600755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4365514413329031032400503 6548271619993546548600755)
          ·
            refine ⟨9822407429990319822901133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6548271619993546548600755 9822407429990319822901133)
            ·
              refine ⟨3683402786246369933587925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9822407429990319822901133 3683402786246369933587925)
              ·
                refine ⟨86329752802649295318467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3683402786246369933587925 86329752802649295318467)
                ·
                  rfl

theorem cell22_2269709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 7].length) (baseStart_2269709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269709 prefixEnd_2269709 := by exact prefixLift 2269709
  have htrace : WordTrace (prefixWord ++ tailWord_2269709) baseStart_2269709 baseEnd_2269709 := by
    simpa [prefixWord, tailWord_2269709, baseEnd_2269709] using wordTrace_append hprefix tailTrace_2269709
  have hstable : (prefixWord ++ tailWord_2269709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269709).length < 2 ^ (prefixWord ++ tailWord_2269709).sum := by decide
  have hdescent : baseEnd_2269709 < baseStart_2269709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269765 : List Nat := [1, 3, 1, 1, 1, 5, 1, 3, 6]
def baseStart_2269765 : Nat := 118140960795 + 2269765 * 2 ^ 59
def prefixEnd_2269765 : Nat := 4983230072969 + 3 ^ 40 * 2269765 * 2
def baseEnd_2269765 : Nat := 258995648389426059488677

theorem tailTrace_2269765 : CollatzResearch.WordTrace tailWord_2269765 prefixEnd_2269765 258995648389426059488677 := by
  unfold tailWord_2269765
  simp only [CollatzResearch.WordTrace]
  refine ⟨82785130622036524845114749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55190087081357683230076499 82785130622036524845114749)
  ·
    refine ⟨31044423983263696816918031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82785130622036524845114749 31044423983263696816918031)
    ·
      refine ⟨46566635974895545225377047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31044423983263696816918031 46566635974895545225377047)
      ·
        refine ⟨69849953962343317838065571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46566635974895545225377047 69849953962343317838065571)
        ·
          refine ⟨104774930943514976757098357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69849953962343317838065571 104774930943514976757098357)
          ·
            refine ⟨9822649775954529070977971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104774930943514976757098357 9822649775954529070977971)
            ·
              refine ⟨14733974663931793606466957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9822649775954529070977971 14733974663931793606466957)
              ·
                refine ⟨5525240498974422602425109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14733974663931793606466957 5525240498974422602425109)
                ·
                  refine ⟨258995648389426059488677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5525240498974422602425109 258995648389426059488677)
                  ·
                    rfl

theorem cell22_2269765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_2269765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269765 prefixEnd_2269765 := by exact prefixLift 2269765
  have htrace : WordTrace (prefixWord ++ tailWord_2269765) baseStart_2269765 baseEnd_2269765 := by
    simpa [prefixWord, tailWord_2269765, baseEnd_2269765] using wordTrace_append hprefix tailTrace_2269765
  have hstable : (prefixWord ++ tailWord_2269765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269765).length < 2 ^ (prefixWord ++ tailWord_2269765).sum := by decide
  have hdescent : baseEnd_2269765 < baseStart_2269765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269795 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 1, 6]
def baseStart_2269795 : Nat := 118140960795 + 2269795 * 2 ^ 59
def prefixEnd_2269795 : Nat := 4983230072969 + 3 ^ 40 * 2269795 * 2
def baseEnd_2269795 : Nat := 776997214781368100215939

theorem tailTrace_2269795 : CollatzResearch.WordTrace tailWord_2269795 prefixEnd_2269795 776997214781368100215939 := by
  unfold tailWord_2269795
  simp only [CollatzResearch.WordTrace]
  refine ⟨82786224811927839968706839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55190816541285226645804559 82786224811927839968706839)
  ·
    refine ⟨124179337217891759953060259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82786224811927839968706839 124179337217891759953060259)
    ·
      refine ⟨186269005826837639929590389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124179337217891759953060259 186269005826837639929590389)
      ·
        refine ⟨17462719296266028743399099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 186269005826837639929590389 17462719296266028743399099)
        ·
          refine ⟨26194078944399043115098649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17462719296266028743399099 26194078944399043115098649)
          ·
            refine ⟨19645559208299282336323987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26194078944399043115098649 19645559208299282336323987)
            ·
              refine ⟨29468338812448923504485981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19645559208299282336323987 29468338812448923504485981)
              ·
                refine ⟨11050627054668346314182243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29468338812448923504485981 11050627054668346314182243)
                ·
                  refine ⟨16575940582002519471273365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11050627054668346314182243 16575940582002519471273365)
                  ·
                    refine ⟨776997214781368100215939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16575940582002519471273365 776997214781368100215939)
                    ·
                      rfl

theorem cell22_2269795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 6].length) (baseStart_2269795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269795 prefixEnd_2269795 := by exact prefixLift 2269795
  have htrace : WordTrace (prefixWord ++ tailWord_2269795) baseStart_2269795 baseEnd_2269795 := by
    simpa [prefixWord, tailWord_2269795, baseEnd_2269795] using wordTrace_append hprefix tailTrace_2269795
  have hstable : (prefixWord ++ tailWord_2269795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269795).length < 2 ^ (prefixWord ++ tailWord_2269795).sum := by decide
  have hdescent : baseEnd_2269795 < baseStart_2269795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269878 : List Nat := [5, 1, 3, 1, 3, 1, 1, 7]
def baseStart_2269878 : Nat := 118140960795 + 2269878 * 2 ^ 59
def prefixEnd_2269878 : Nat := 4983230072969 + 3 ^ 40 * 2269878 * 2
def baseEnd_2269878 : Nat := 86336180819731505598965

theorem tailTrace_2269878 : CollatzResearch.WordTrace tailWord_2269878 prefixEnd_2269878 86336180819731505598965 := by
  unfold tailWord_2269878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5174328254414196571498643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55192834713751430095985525 5174328254414196571498643)
  ·
    refine ⟨7761492381621294857247965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5174328254414196571498643 7761492381621294857247965)
    ·
      refine ⟨2910559643107985571467987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7761492381621294857247965 2910559643107985571467987)
      ·
        refine ⟨4365839464661978357201981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2910559643107985571467987 4365839464661978357201981)
        ·
          refine ⟨1637189799248241883950743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4365839464661978357201981 1637189799248241883950743)
          ·
            refine ⟨2455784698872362825926115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1637189799248241883950743 2455784698872362825926115)
            ·
              refine ⟨3683677048308544238889173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2455784698872362825926115 3683677048308544238889173)
              ·
                refine ⟨86336180819731505598965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3683677048308544238889173 86336180819731505598965)
                ·
                  rfl

theorem cell22_2269878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_2269878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269878 prefixEnd_2269878 := by exact prefixLift 2269878
  have htrace : WordTrace (prefixWord ++ tailWord_2269878) baseStart_2269878 baseEnd_2269878 := by
    simpa [prefixWord, tailWord_2269878, baseEnd_2269878] using wordTrace_append hprefix tailTrace_2269878
  have hstable : (prefixWord ++ tailWord_2269878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269878).length < 2 ^ (prefixWord ++ tailWord_2269878).sum := by decide
  have hdescent : baseEnd_2269878 < baseStart_2269878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269887 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 2, 5]
def baseStart_2269887 : Nat := 118140960795 + 2269887 * 2 ^ 59
def prefixEnd_2269887 : Nat := 4983230072969 + 3 ^ 40 * 2269887 * 2
def baseEnd_2269887 : Nat := 777028708261510526915657

theorem tailTrace_2269887 : CollatzResearch.WordTrace tailWord_2269887 prefixEnd_2269887 777028708261510526915657 := by
  unfold tailWord_2269887
  simp only [CollatzResearch.WordTrace]
  refine ⟨82789580327594539681055915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55193053551729693120703943 82789580327594539681055915)
  ·
    refine ⟨124184370491391809521583873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82789580327594539681055915 124184370491391809521583873)
    ·
      refine ⟨93138277868543857141187905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124184370491391809521583873 93138277868543857141187905)
      ·
        refine ⟨69853708401407892855890929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93138277868543857141187905 69853708401407892855890929)
        ·
          refine ⟨52390281301055919641918197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69853708401407892855890929 52390281301055919641918197)
          ·
            refine ⟨4911588871973992466429831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52390281301055919641918197 4911588871973992466429831)
            ·
              refine ⟨7367383307960988699644747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4911588871973992466429831 7367383307960988699644747)
              ·
                refine ⟨11051074961941483049467121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7367383307960988699644747 11051074961941483049467121)
                ·
                  refine ⟨8288306221456112287100341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11051074961941483049467121 8288306221456112287100341)
                  ·
                    refine ⟨777028708261510526915657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8288306221456112287100341 777028708261510526915657)
                    ·
                      rfl

theorem cell22_2269887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_2269887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269887 prefixEnd_2269887 := by exact prefixLift 2269887
  have htrace : WordTrace (prefixWord ++ tailWord_2269887) baseStart_2269887 baseEnd_2269887 := by
    simpa [prefixWord, tailWord_2269887, baseEnd_2269887] using wordTrace_append hprefix tailTrace_2269887
  have hstable : (prefixWord ++ tailWord_2269887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269887).length < 2 ^ (prefixWord ++ tailWord_2269887).sum := by decide
  have hdescent : baseEnd_2269887 < baseStart_2269887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269919 : List Nat := [1, 1, 2, 3, 2, 4, 1, 3, 1, 4]
def baseStart_2269919 : Nat := 118140960795 + 2269919 * 2 ^ 59
def prefixEnd_2269919 : Nat := 4983230072969 + 3 ^ 40 * 2269919 * 2
def baseEnd_2269919 : Nat := 777039662515473110115559

theorem tailTrace_2269919 : CollatzResearch.WordTrace tailWord_2269919 prefixEnd_2269919 777039662515473110115559 := by
  unfold tailWord_2269919
  simp only [CollatzResearch.WordTrace]
  refine ⟨82790747463478609146220811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55193831642319072764147207 82790747463478609146220811)
  ·
    refine ⟨124186121195217913719331217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82790747463478609146220811 124186121195217913719331217)
    ·
      refine ⟨93139590896413435289498413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124186121195217913719331217 93139590896413435289498413)
      ·
        refine ⟨34927346586155038233561905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93139590896413435289498413 34927346586155038233561905)
        ·
          refine ⟨26195509939616278675171429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34927346586155038233561905 26195509939616278675171429)
          ·
            refine ⟨4911658113678052251594643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26195509939616278675171429 4911658113678052251594643)
            ·
              refine ⟨7367487170517078377391965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4911658113678052251594643 7367487170517078377391965)
              ·
                refine ⟨2762807688943904391521987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7367487170517078377391965 2762807688943904391521987)
                ·
                  refine ⟨4144211533415856587282981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2762807688943904391521987 4144211533415856587282981)
                  ·
                    refine ⟨777039662515473110115559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4144211533415856587282981 777039662515473110115559)
                    ·
                      rfl

theorem cell22_2269919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 4].length) (baseStart_2269919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269919 prefixEnd_2269919 := by exact prefixLift 2269919
  have htrace : WordTrace (prefixWord ++ tailWord_2269919) baseStart_2269919 baseEnd_2269919 := by
    simpa [prefixWord, tailWord_2269919, baseEnd_2269919] using wordTrace_append hprefix tailTrace_2269919
  have hstable : (prefixWord ++ tailWord_2269919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269919).length < 2 ^ (prefixWord ++ tailWord_2269919).sum := by decide
  have hdescent : baseEnd_2269919 < baseStart_2269919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269934 : List Nat := [4, 1, 2, 1, 1, 4, 2, 1, 6]
def baseStart_2269934 : Nat := 118140960795 + 2269934 * 2 ^ 59
def prefixEnd_2269934 : Nat := 4983230072969 + 3 ^ 40 * 2269934 * 2
def baseEnd_2269934 : Nat := 259014932440672690330171

theorem tailTrace_2269934 : CollatzResearch.WordTrace tailWord_2269934 prefixEnd_2269934 259014932440672690330171 := by
  unfold tailWord_2269934
  simp only [CollatzResearch.WordTrace]
  refine ⟨10348911819803033338502107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55194196372282844472011237 10348911819803033338502107)
  ·
    refine ⟨15523367729704550007753161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10348911819803033338502107 15523367729704550007753161)
    ·
      refine ⟨11642525797278412505814871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15523367729704550007753161 11642525797278412505814871)
      ·
        refine ⟨17463788695917618758722307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11642525797278412505814871 17463788695917618758722307)
        ·
          refine ⟨26195683043876428138083461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17463788695917618758722307 26195683043876428138083461)
          ·
            refine ⟨4911690570726830275890649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26195683043876428138083461 4911690570726830275890649)
            ·
              refine ⟨3683767928045122706917987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4911690570726830275890649 3683767928045122706917987)
              ·
                refine ⟨5525651892067684060376981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3683767928045122706917987 5525651892067684060376981)
                ·
                  refine ⟨259014932440672690330171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5525651892067684060376981 259014932440672690330171)
                  ·
                    rfl

theorem cell22_2269934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_2269934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269934 prefixEnd_2269934 := by exact prefixLift 2269934
  have htrace : WordTrace (prefixWord ++ tailWord_2269934) baseStart_2269934 baseEnd_2269934 := by
    simpa [prefixWord, tailWord_2269934, baseEnd_2269934] using wordTrace_append hprefix tailTrace_2269934
  have hstable : (prefixWord ++ tailWord_2269934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269934).length < 2 ^ (prefixWord ++ tailWord_2269934).sum := by decide
  have hdescent : baseEnd_2269934 < baseStart_2269934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269940 : List Nat := [2, 6, 1, 1, 2, 1, 3, 1, 5]
def baseStart_2269940 : Nat := 118140960795 + 2269940 * 2 ^ 59
def prefixEnd_2269940 : Nat := 4983230072969 + 3 ^ 40 * 2269940 * 2
def baseEnd_2269940 : Nat := 259015617081545351780165

theorem tailTrace_2269940 : CollatzResearch.WordTrace tailWord_2269940 prefixEnd_2269940 259015617081545351780165 := by
  unfold tailWord_2269940
  simp only [CollatzResearch.WordTrace]
  refine ⟨41395756698201264866367637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55194342264268353155156849 41395756698201264866367637)
  ·
    refine ⟨1940426095228184290610983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41395756698201264866367637 1940426095228184290610983)
    ·
      refine ⟨2910639142842276435916475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1940426095228184290610983 2910639142842276435916475)
      ·
        refine ⟨4365958714263414653874713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2910639142842276435916475 4365958714263414653874713)
        ·
          refine ⟨3274469035697560990406035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4365958714263414653874713 3274469035697560990406035)
          ·
            refine ⟨4911703553546341485609053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3274469035697560990406035 4911703553546341485609053)
            ·
              refine ⟨1841888832579878057103395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4911703553546341485609053 1841888832579878057103395)
              ·
                refine ⟨2762833248869817085655093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1841888832579878057103395 2762833248869817085655093)
                ·
                  refine ⟨259015617081545351780165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2762833248869817085655093 259015617081545351780165)
                  ·
                    rfl

theorem cell22_2269940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_2269940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269940 prefixEnd_2269940 := by exact prefixLift 2269940
  have htrace : WordTrace (prefixWord ++ tailWord_2269940) baseStart_2269940 baseEnd_2269940 := by
    simpa [prefixWord, tailWord_2269940, baseEnd_2269940] using wordTrace_append hprefix tailTrace_2269940
  have hstable : (prefixWord ++ tailWord_2269940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269940).length < 2 ^ (prefixWord ++ tailWord_2269940).sum := by decide
  have hdescent : baseEnd_2269940 < baseStart_2269940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269962 : List Nat := [3, 1, 2, 2, 1, 2, 3, 8]
def baseStart_2269962 : Nat := 118140960795 + 2269962 * 2 ^ 59
def prefixEnd_2269962 : Nat := 4983230072969 + 3 ^ 40 * 2269962 * 2
def baseEnd_2269962 : Nat := 86339375810470592365603

theorem tailTrace_2269962 : CollatzResearch.WordTrace tailWord_2269962 prefixEnd_2269962 86339375810470592365603 := by
  unfold tailWord_2269962
  simp only [CollatzResearch.WordTrace]
  refine ⟨20698078950580706872509035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55194877201548551660024093 20698078950580706872509035)
  ·
    refine ⟨31047118425871060308763553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20698078950580706872509035 31047118425871060308763553)
    ·
      refine ⟨23285338819403295231572665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31047118425871060308763553 23285338819403295231572665)
      ·
        refine ⟨17464004114552471423679499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23285338819403295231572665 17464004114552471423679499)
        ·
          refine ⟨26196006171828707135519249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17464004114552471423679499 26196006171828707135519249)
          ·
            refine ⟨19647004628871530351639437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26196006171828707135519249 19647004628871530351639437)
            ·
              refine ⟨7367626735826823881864789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19647004628871530351639437 7367626735826823881864789)
              ·
                refine ⟨86339375810470592365603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7367626735826823881864789 86339375810470592365603)
                ·
                  rfl

theorem cell22_2269962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 8].length) (baseStart_2269962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2269962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2269962 prefixEnd_2269962 := by exact prefixLift 2269962
  have htrace : WordTrace (prefixWord ++ tailWord_2269962) baseStart_2269962 baseEnd_2269962 := by
    simpa [prefixWord, tailWord_2269962, baseEnd_2269962] using wordTrace_append hprefix tailTrace_2269962
  have hstable : (prefixWord ++ tailWord_2269962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269962).length < 2 ^ (prefixWord ++ tailWord_2269962).sum := by decide
  have hdescent : baseEnd_2269962 < baseStart_2269962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270069 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 8]
def baseStart_2270069 : Nat := 118140960795 + 2270069 * 2 ^ 59
def prefixEnd_2270069 : Nat := 4983230072969 + 3 ^ 40 * 2270069 * 2
def baseEnd_2270069 : Nat := 259030336860307572955033

theorem tailTrace_2270069 : CollatzResearch.WordTrace tailWord_2270069 prefixEnd_2270069 259030336860307572955033 := by
  unfold tailWord_2270069
  simp only [CollatzResearch.WordTrace]
  refine ⟨82796218412935184764181261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55197478941956789842787507 82796218412935184764181261)
  ·
    refine ⟨31048581904850694286567973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82796218412935184764181261 31048581904850694286567973)
    ·
      refine ⟨5821609107159505178731495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31048581904850694286567973 5821609107159505178731495)
      ·
        refine ⟨8732413660739257768097243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5821609107159505178731495 8732413660739257768097243)
        ·
          refine ⟨13098620491108886652145865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8732413660739257768097243 13098620491108886652145865)
          ·
            refine ⟨9823965368331664989109399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13098620491108886652145865 9823965368331664989109399)
            ·
              refine ⟨14735948052497497483664099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9823965368331664989109399 14735948052497497483664099)
              ·
                refine ⟨22103922078746246225496149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14735948052497497483664099 22103922078746246225496149)
                ·
                  refine ⟨259030336860307572955033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22103922078746246225496149 259030336860307572955033)
                  ·
                    rfl

theorem cell22_2270069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_2270069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270069 prefixEnd_2270069 := by exact prefixLift 2270069
  have htrace : WordTrace (prefixWord ++ tailWord_2270069) baseStart_2270069 baseEnd_2270069 := by
    simpa [prefixWord, tailWord_2270069, baseEnd_2270069] using wordTrace_append hprefix tailTrace_2270069
  have hstable : (prefixWord ++ tailWord_2270069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270069).length < 2 ^ (prefixWord ++ tailWord_2270069).sum := by decide
  have hdescent : baseEnd_2270069 < baseStart_2270069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270088 : List Nat := [2, 1, 3, 3, 2, 1, 4, 1, 1, 4]
def baseStart_2270088 : Nat := 118140960795 + 2270088 * 2 ^ 59
def prefixEnd_2270088 : Nat := 4983230072969 + 3 ^ 40 * 2270088 * 2
def baseEnd_2270088 : Nat := 777097514669213002640041

theorem tailTrace_2270088 : CollatzResearch.WordTrace tailWord_2270088 prefixEnd_2270088 777097514669213002640041 := by
  unfold tailWord_2270088
  simp only [CollatzResearch.WordTrace]
  refine ⟨41398455699933175504561459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55197940933244234006081945 41398455699933175504561459)
  ·
    refine ⟨62097683549899763256842189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41398455699933175504561459 62097683549899763256842189)
    ·
      refine ⟨23286631331212411221315821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62097683549899763256842189 23286631331212411221315821)
      ·
        refine ⟨8732486749204654207993433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23286631331212411221315821 8732486749204654207993433)
        ·
          refine ⟨6549365061903490655995075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8732486749204654207993433 6549365061903490655995075)
          ·
            refine ⟨9824047592855235983992613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6549365061903490655995075 9824047592855235983992613)
            ·
              refine ⟨1842008923660356746998615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9824047592855235983992613 1842008923660356746998615)
              ·
                refine ⟨2763013385490535120497923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1842008923660356746998615 2763013385490535120497923)
                ·
                  refine ⟨4144520078235802680746885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2763013385490535120497923 4144520078235802680746885)
                  ·
                    refine ⟨777097514669213002640041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4144520078235802680746885 777097514669213002640041)
                    ·
                      rfl

theorem cell22_2270088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_2270088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270088 prefixEnd_2270088 := by exact prefixLift 2270088
  have htrace : WordTrace (prefixWord ++ tailWord_2270088) baseStart_2270088 baseEnd_2270088 := by
    simpa [prefixWord, tailWord_2270088, baseEnd_2270088] using wordTrace_append hprefix tailTrace_2270088
  have hstable : (prefixWord ++ tailWord_2270088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270088).length < 2 ^ (prefixWord ++ tailWord_2270088).sum := by decide
  have hdescent : baseEnd_2270088 < baseStart_2270088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270101 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 4, 3]
def baseStart_2270101 : Nat := 118140960795 + 2270101 * 2 ^ 59
def prefixEnd_2270101 : Nat := 4983230072969 + 3 ^ 40 * 2270101 * 2
def baseEnd_2270101 : Nat := 777101964834885302065001

theorem tailTrace_2270101 : CollatzResearch.WordTrace tailWord_2270101 prefixEnd_2270101 777101964834885302065001 := by
  unfold tailWord_2270101
  simp only [CollatzResearch.WordTrace]
  refine ⟨82797385548819254229346157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55198257032546169486230771 82797385548819254229346157)
  ·
    refine ⟨31049019580807220336004809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82797385548819254229346157 31049019580807220336004809)
    ·
      refine ⟨23286764685605415252003607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31049019580807220336004809 23286764685605415252003607)
      ·
        refine ⟨34930147028408122878005411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23286764685605415252003607 34930147028408122878005411)
        ·
          refine ⟨52395220542612184317008117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34930147028408122878005411 52395220542612184317008117)
          ·
            refine ⟨4912051925869892279719511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52395220542612184317008117 4912051925869892279719511)
            ·
              refine ⟨7368077888804838419579267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4912051925869892279719511 7368077888804838419579267)
              ·
                refine ⟨11052116833207257629368901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7368077888804838419579267 11052116833207257629368901)
                ·
                  refine ⟨2072271906226360805506669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11052116833207257629368901 2072271906226360805506669)
                  ·
                    refine ⟨777101964834885302065001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2072271906226360805506669 777101964834885302065001)
                    ·
                      rfl

theorem cell22_2270101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_2270101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270101 prefixEnd_2270101 := by exact prefixLift 2270101
  have htrace : WordTrace (prefixWord ++ tailWord_2270101) baseStart_2270101 baseEnd_2270101 := by
    simpa [prefixWord, tailWord_2270101, baseEnd_2270101] using wordTrace_append hprefix tailTrace_2270101
  have hstable : (prefixWord ++ tailWord_2270101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270101).length < 2 ^ (prefixWord ++ tailWord_2270101).sum := by decide
  have hdescent : baseEnd_2270101 < baseStart_2270101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270148 : List Nat := [2, 3, 3, 3, 1, 2, 8]
def baseStart_2270148 : Nat := 118140960795 + 2270148 * 2 ^ 59
def prefixEnd_2270148 : Nat := 4983230072969 + 3 ^ 40 * 2270148 * 2
def baseEnd_2270148 : Nat := 28782150144273809116291

theorem tailTrace_2270148 : CollatzResearch.WordTrace tailWord_2270148 prefixEnd_2270148 28782150144273809116291 := by
  unfold tailWord_2270148
  simp only [CollatzResearch.WordTrace]
  refine ⟨41399549889824490628153549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55199399853099320837538065 41399549889824490628153549)
  ·
    refine ⟨15524831208684183985557581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41399549889824490628153549 15524831208684183985557581)
    ·
      refine ⟨5821811703256568994584093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15524831208684183985557581 5821811703256568994584093)
      ·
        refine ⟨2183179388721213372969035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5821811703256568994584093 2183179388721213372969035)
        ·
          refine ⟨3274769083081820059453553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2183179388721213372969035 3274769083081820059453553)
          ·
            refine ⟨2456076812311365044590165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3274769083081820059453553 2456076812311365044590165)
            ·
              refine ⟨28782150144273809116291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2456076812311365044590165 28782150144273809116291)
              ·
                rfl

theorem cell22_2270148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 8].length) (baseStart_2270148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270148 prefixEnd_2270148 := by exact prefixLift 2270148
  have htrace : WordTrace (prefixWord ++ tailWord_2270148) baseStart_2270148 baseEnd_2270148 := by
    simpa [prefixWord, tailWord_2270148, baseEnd_2270148] using wordTrace_append hprefix tailTrace_2270148
  have hstable : (prefixWord ++ tailWord_2270148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270148).length < 2 ^ (prefixWord ++ tailWord_2270148).sum := by decide
  have hdescent : baseEnd_2270148 < baseStart_2270148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270159 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 7]
def baseStart_2270159 : Nat := 118140960795 + 2270159 * 2 ^ 59
def prefixEnd_2270159 : Nat := 4983230072969 + 3 ^ 40 * 2270159 * 2
def baseEnd_2270159 : Nat := 259040606473397494704941

theorem tailTrace_2270159 : CollatzResearch.WordTrace tailWord_2270159 prefixEnd_2270159 259040606473397494704941 := by
  unfold tailWord_2270159
  simp only [CollatzResearch.WordTrace]
  refine ⟨82799500982609130134957531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55199667321739420089971687 82799500982609130134957531)
  ·
    refine ⟨124199251473913695202436297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82799500982609130134957531 124199251473913695202436297)
    ·
      refine ⟨93149438605435271401827223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124199251473913695202436297 93149438605435271401827223)
      ·
        refine ⟨139724157908152907102740835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93149438605435271401827223 139724157908152907102740835)
        ·
          refine ⟨209586236862229360654111253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139724157908152907102740835 209586236862229360654111253)
          ·
            refine ⟨9824354852917001280661465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 209586236862229360654111253 9824354852917001280661465)
            ·
              refine ⟨7368266139687750960496099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9824354852917001280661465 7368266139687750960496099)
              ·
                refine ⟨11052399209531626440744149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7368266139687750960496099 11052399209531626440744149)
                ·
                  refine ⟨259040606473397494704941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11052399209531626440744149 259040606473397494704941)
                  ·
                    rfl

theorem cell22_2270159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 7].length) (baseStart_2270159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270159 prefixEnd_2270159 := by exact prefixLift 2270159
  have htrace : WordTrace (prefixWord ++ tailWord_2270159) baseStart_2270159 baseEnd_2270159 := by
    simpa [prefixWord, tailWord_2270159, baseEnd_2270159] using wordTrace_append hprefix tailTrace_2270159
  have hstable : (prefixWord ++ tailWord_2270159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270159).length < 2 ^ (prefixWord ++ tailWord_2270159).sum := by decide
  have hdescent : baseEnd_2270159 < baseStart_2270159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270270 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_2270270 : Nat := 118140960795 + 2270270 * 2 ^ 59
def prefixEnd_2270270 : Nat := 4983230072969 + 3 ^ 40 * 2270270 * 2
def baseEnd_2270270 : Nat := 777159816988625194589483

theorem tailTrace_2270270 : CollatzResearch.WordTrace tailWord_2270270 prefixEnd_2270270 777159816988625194589483 := by
  unfold tailWord_2270270
  simp only [CollatzResearch.WordTrace]
  refine ⟨10350443685650874511531033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55202366323471330728165509 10350443685650874511531033)
  ·
    refine ⟨7762832764238155883648275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10350443685650874511531033 7762832764238155883648275)
    ·
      refine ⟨11644249146357233825472413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7762832764238155883648275 11644249146357233825472413)
      ·
        refine ⟨4366593429883962684552155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11644249146357233825472413 4366593429883962684552155)
        ·
          refine ⟨6549890144825944026828233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4366593429883962684552155 6549890144825944026828233)
          ·
            refine ⟨4912417608619458020121175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6549890144825944026828233 4912417608619458020121175)
            ·
              refine ⟨7368626412929187030181763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4912417608619458020121175 7368626412929187030181763)
              ·
                refine ⟨11052939619393780545272645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7368626412929187030181763 11052939619393780545272645)
                ·
                  refine ⟨2072426178636333852238621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11052939619393780545272645 2072426178636333852238621)
                  ·
                    refine ⟨777159816988625194589483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2072426178636333852238621 777159816988625194589483)
                    ·
                      rfl

theorem cell22_2270270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_2270270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270270 prefixEnd_2270270 := by exact prefixLift 2270270
  have htrace : WordTrace (prefixWord ++ tailWord_2270270) baseStart_2270270 baseEnd_2270270 := by
    simpa [prefixWord, tailWord_2270270, baseEnd_2270270] using wordTrace_append hprefix tailTrace_2270270
  have hstable : (prefixWord ++ tailWord_2270270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270270).length < 2 ^ (prefixWord ++ tailWord_2270270).sum := by decide
  have hdescent : baseEnd_2270270 < baseStart_2270270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270311 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 7]
def baseStart_2270311 : Nat := 118140960795 + 2270311 * 2 ^ 59
def prefixEnd_2270311 : Nat := 4983230072969 + 3 ^ 40 * 2270311 * 2
def baseEnd_2270311 : Nat := 259057950708838251438119

theorem tailTrace_2270311 : CollatzResearch.WordTrace tailWord_2270311 prefixEnd_2270311 259057950708838251438119 := by
  unfold tailWord_2270311
  simp only [CollatzResearch.WordTrace]
  refine ⟨82805044878058460094490787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55203363252038973396327191 82805044878058460094490787)
  ·
    refine ⟨124207567317087690141736181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82805044878058460094490787 124207567317087690141736181)
    ·
      refine ⟨11644459435976970950787767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124207567317087690141736181 11644459435976970950787767)
      ·
        refine ⟨17466689153965456426181651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11644459435976970950787767 17466689153965456426181651)
        ·
          refine ⟨26200033730948184639272477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17466689153965456426181651 26200033730948184639272477)
          ·
            refine ⟨9825012649105569239727179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26200033730948184639272477 9825012649105569239727179)
            ·
              refine ⟨14737518973658353859590769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9825012649105569239727179 14737518973658353859590769)
              ·
                refine ⟨11053139230243765394693077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14737518973658353859590769 11053139230243765394693077)
                ·
                  refine ⟨259057950708838251438119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11053139230243765394693077 259057950708838251438119)
                  ·
                    rfl

theorem cell22_2270311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 7].length) (baseStart_2270311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270311 prefixEnd_2270311 := by exact prefixLift 2270311
  have htrace : WordTrace (prefixWord ++ tailWord_2270311) baseStart_2270311 baseEnd_2270311 := by
    simpa [prefixWord, tailWord_2270311, baseEnd_2270311] using wordTrace_append hprefix tailTrace_2270311
  have hstable : (prefixWord ++ tailWord_2270311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270311).length < 2 ^ (prefixWord ++ tailWord_2270311).sum := by decide
  have hdescent : baseEnd_2270311 < baseStart_2270311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270332 : List Nat := [2, 2, 2, 1, 1, 3, 5, 2, 1, 3]
def baseStart_2270332 : Nat := 118140960795 + 2270332 * 2 ^ 59
def prefixEnd_2270332 : Nat := 4983230072969 + 3 ^ 40 * 2270332 * 2
def baseEnd_2270332 : Nat := 777181040855677699539293

theorem tailTrace_2270332 : CollatzResearch.WordTrace tailWord_2270332 prefixEnd_2270332 777181040855677699539293 := by
  unfold tailWord_2270332
  simp only [CollatzResearch.WordTrace]
  refine ⟨41402905405491190340502625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55203873873988253787336833 41402905405491190340502625)
  ·
    refine ⟨31052179054118392755376969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41402905405491190340502625 31052179054118392755376969)
    ·
      refine ⟨23289134290588794566532727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31052179054118392755376969 23289134290588794566532727)
      ·
        refine ⟨34933701435883191849799091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23289134290588794566532727 34933701435883191849799091)
        ·
          refine ⟨52400552153824787774698637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34933701435883191849799091 52400552153824787774698637)
          ·
            refine ⟨19650207057684295415511989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52400552153824787774698637 19650207057684295415511989)
            ·
              refine ⟨1842206911657902695204249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19650207057684295415511989 1842206911657902695204249)
              ·
                refine ⟨1381655183743427021403187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1842206911657902695204249 1381655183743427021403187)
                ·
                  refine ⟨2072482775615140532104781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1381655183743427021403187 2072482775615140532104781)
                  ·
                    refine ⟨777181040855677699539293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2072482775615140532104781 777181040855677699539293)
                    ·
                      rfl

theorem cell22_2270332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_2270332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270332 prefixEnd_2270332 := by exact prefixLift 2270332
  have htrace : WordTrace (prefixWord ++ tailWord_2270332) baseStart_2270332 baseEnd_2270332 := by
    simpa [prefixWord, tailWord_2270332, baseEnd_2270332] using wordTrace_append hprefix tailTrace_2270332
  have hstable : (prefixWord ++ tailWord_2270332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270332).length < 2 ^ (prefixWord ++ tailWord_2270332).sum := by decide
  have hdescent : baseEnd_2270332 < baseStart_2270332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270345 : List Nat := [1, 2, 1, 1, 4, 5, 2, 1, 5]
def baseStart_2270345 : Nat := 118140960795 + 2270345 * 2 ^ 59
def prefixEnd_2270345 : Nat := 4983230072969 + 3 ^ 40 * 2270345 * 2
def baseEnd_2270345 : Nat := 259061830340449999654751

theorem tailTrace_2270345 : CollatzResearch.WordTrace tailWord_2270345 prefixEnd_2270345 259061830340449999654751 := by
  unfold tailWord_2270345
  simp only [CollatzResearch.WordTrace]
  refine ⟨82806284959935283901228489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55204189973290189267485659 82806284959935283901228489)
  ·
    refine ⟨62104713719951462925921367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82806284959935283901228489 62104713719951462925921367)
    ·
      refine ⟨93157070579927194388882051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62104713719951462925921367 93157070579927194388882051)
      ·
        refine ⟨139735605869890791583323077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93157070579927194388882051 139735605869890791583323077)
        ·
          refine ⟨26200426100604523421873077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139735605869890791583323077 26200426100604523421873077)
          ·
            refine ⟨2456289946931674070800601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26200426100604523421873077 2456289946931674070800601)
            ·
              refine ⟨1842217460198755553100451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2456289946931674070800601 1842217460198755553100451)
              ·
                refine ⟨2763326190298133329650677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1842217460198755553100451 2763326190298133329650677)
                ·
                  refine ⟨259061830340449999654751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2763326190298133329650677 259061830340449999654751)
                  ·
                    rfl

theorem cell22_2270345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 5].length) (baseStart_2270345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270345 prefixEnd_2270345 := by exact prefixLift 2270345
  have htrace : WordTrace (prefixWord ++ tailWord_2270345) baseStart_2270345 baseEnd_2270345 := by
    simpa [prefixWord, tailWord_2270345, baseEnd_2270345] using wordTrace_append hprefix tailTrace_2270345
  have hstable : (prefixWord ++ tailWord_2270345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270345).length < 2 ^ (prefixWord ++ tailWord_2270345).sum := by decide
  have hdescent : baseEnd_2270345 < baseStart_2270345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270439 : List Nat := [1, 1, 5, 3, 2, 2, 1, 2, 2, 3]
def baseStart_2270439 : Nat := 118140960795 + 2270439 * 2 ^ 59
def prefixEnd_2270439 : Nat := 4983230072969 + 3 ^ 40 * 2270439 * 2
def baseEnd_2270439 : Nat := 777217669142365087113965

theorem tailTrace_2270439 : CollatzResearch.WordTrace tailWord_2270439 prefixEnd_2270439 777217669142365087113965 := by
  unfold tailWord_2270439
  simp only [CollatzResearch.WordTrace]
  refine ⟨82809713421594737955150371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55206475614396491970100247 82809713421594737955150371)
  ·
    refine ⟨124214570132392106932725557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82809713421594737955150371 124214570132392106932725557)
    ·
      refine ⟨11645115949911760024943021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124214570132392106932725557 11645115949911760024943021)
      ·
        refine ⟨4366918481216910009353633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11645115949911760024943021 4366918481216910009353633)
        ·
          refine ⟨3275188860912682507015225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4366918481216910009353633 3275188860912682507015225)
          ·
            refine ⟨2456391645684511880261419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3275188860912682507015225 2456391645684511880261419)
            ·
              refine ⟨3684587468526767820392129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2456391645684511880261419 3684587468526767820392129)
              ·
                refine ⟨2763440601395075865294097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3684587468526767820392129 2763440601395075865294097)
                ·
                  refine ⟨2072580451046306898970573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2763440601395075865294097 2072580451046306898970573)
                  ·
                    refine ⟨777217669142365087113965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2072580451046306898970573 777217669142365087113965)
                    ·
                      rfl

theorem cell22_2270439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_2270439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270439 prefixEnd_2270439 := by exact prefixLift 2270439
  have htrace : WordTrace (prefixWord ++ tailWord_2270439) baseStart_2270439 baseEnd_2270439 := by
    simpa [prefixWord, tailWord_2270439, baseEnd_2270439] using wordTrace_append hprefix tailTrace_2270439
  have hstable : (prefixWord ++ tailWord_2270439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270439).length < 2 ^ (prefixWord ++ tailWord_2270439).sum := by decide
  have hdescent : baseEnd_2270439 < baseStart_2270439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270527 : List Nat := [1, 1, 2, 2, 4, 4, 1, 2, 1, 4]
def baseStart_2270527 : Nat := 118140960795 + 2270527 * 2 ^ 59
def prefixEnd_2270527 : Nat := 4983230072969 + 3 ^ 40 * 2270527 * 2
def baseEnd_2270527 : Nat := 777247793340762190913695

theorem tailTrace_2270527 : CollatzResearch.WordTrace tailWord_2270527 prefixEnd_2270527 777247793340762190913695 := by
  unfold tailWord_2270527
  simp only [CollatzResearch.WordTrace]
  refine ⟨82812923045275928984353835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55208615363517285989569223 82812923045275928984353835)
  ·
    refine ⟨124219384567913893476530753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82812923045275928984353835 124219384567913893476530753)
    ·
      refine ⟨93164538425935420107398065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124219384567913893476530753 93164538425935420107398065)
      ·
        refine ⟨69873403819451565080548549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93164538425935420107398065 69873403819451565080548549)
        ·
          refine ⟨13101263216147168452602853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69873403819451565080548549 13101263216147168452602853)
          ·
            refine ⟨2456486853027594084863035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13101263216147168452602853 2456486853027594084863035)
            ·
              refine ⟨3684730279541391127294553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2456486853027594084863035 3684730279541391127294553)
              ·
                refine ⟨2763547709656043345470915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3684730279541391127294553 2763547709656043345470915)
                ·
                  refine ⟨4145321564484065018206373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2763547709656043345470915 4145321564484065018206373)
                  ·
                    refine ⟨777247793340762190913695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4145321564484065018206373 777247793340762190913695)
                    ·
                      rfl

theorem cell22_2270527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 4].length) (baseStart_2270527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270527 prefixEnd_2270527 := by exact prefixLift 2270527
  have htrace : WordTrace (prefixWord ++ tailWord_2270527) baseStart_2270527 baseEnd_2270527 := by
    simpa [prefixWord, tailWord_2270527, baseEnd_2270527] using wordTrace_append hprefix tailTrace_2270527
  have hstable : (prefixWord ++ tailWord_2270527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270527).length < 2 ^ (prefixWord ++ tailWord_2270527).sum := by decide
  have hdescent : baseEnd_2270527 < baseStart_2270527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270538 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 1, 6]
def baseStart_2270538 : Nat := 118140960795 + 2270538 * 2 ^ 59
def prefixEnd_2270538 : Nat := 4983230072969 + 3 ^ 40 * 2270538 * 2
def baseEnd_2270538 : Nat := 777251558865561828888661

theorem tailTrace_2270538 : CollatzResearch.WordTrace tailWord_2270538 prefixEnd_2270538 777251558865561828888661 := by
  unfold tailWord_2270538
  simp only [CollatzResearch.WordTrace]
  refine ⟨20703331062059019465751067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55208882832157385242002845 20703331062059019465751067)
  ·
    refine ⟨31054996593088529198626601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20703331062059019465751067 31054996593088529198626601)
    ·
      refine ⟨23291247444816396898969951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31054996593088529198626601 23291247444816396898969951)
      ·
        refine ⟨34936871167224595348454927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23291247444816396898969951 34936871167224595348454927)
        ·
          refine ⟨52405306750836893022682391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34936871167224595348454927 52405306750836893022682391)
          ·
            refine ⟨78607960126255339534023587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52405306750836893022682391 78607960126255339534023587)
            ·
              refine ⟨117911940189383009301035381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78607960126255339534023587 117911940189383009301035381)
              ·
                refine ⟨11054244392754657121972067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117911940189383009301035381 11054244392754657121972067)
                ·
                  refine ⟨16581366589131985682958101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11054244392754657121972067 16581366589131985682958101)
                  ·
                    refine ⟨777251558865561828888661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16581366589131985682958101 777251558865561828888661)
                    ·
                      rfl

theorem cell22_2270538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_2270538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270538 prefixEnd_2270538 := by exact prefixLift 2270538
  have htrace : WordTrace (prefixWord ++ tailWord_2270538) baseStart_2270538 baseEnd_2270538 := by
    simpa [prefixWord, tailWord_2270538, baseEnd_2270538] using wordTrace_append hprefix tailTrace_2270538
  have hstable : (prefixWord ++ tailWord_2270538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270538).length < 2 ^ (prefixWord ++ tailWord_2270538).sum := by decide
  have hdescent : baseEnd_2270538 < baseStart_2270538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270540 : List Nat := [2, 2, 1, 3, 2, 3, 1, 2, 1, 5]
def baseStart_2270540 : Nat := 118140960795 + 2270540 * 2 ^ 59
def prefixEnd_2270540 : Nat := 4983230072969 + 3 ^ 40 * 2270540 * 2
def baseEnd_2270540 : Nat := 777252243506434490338655

theorem tailTrace_2270540 : CollatzResearch.WordTrace tailWord_2270540 prefixEnd_2270540 777252243506434490338655 := by
  unfold tailWord_2270540
  simp only [CollatzResearch.WordTrace]
  refine ⟨41406698597114416102288537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55208931462819221469718049 41406698597114416102288537)
  ·
    refine ⟨31055023947835812076716403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41406698597114416102288537 31055023947835812076716403)
    ·
      refine ⟨46582535921753718115074605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31055023947835812076716403 46582535921753718115074605)
      ·
        refine ⟨17468450970657644293152977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46582535921753718115074605 17468450970657644293152977)
        ·
          refine ⟨13101338227993233219864733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17468450970657644293152977 13101338227993233219864733)
          ·
            refine ⟨4913001835497462457449275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13101338227993233219864733 4913001835497462457449275)
            ·
              refine ⟨7369502753246193686173913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4913001835497462457449275 7369502753246193686173913)
              ·
                refine ⟨5527127064934645264630435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7369502753246193686173913 5527127064934645264630435)
                ·
                  refine ⟨8290690597401967896945653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5527127064934645264630435 8290690597401967896945653)
                  ·
                    refine ⟨777252243506434490338655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8290690597401967896945653 777252243506434490338655)
                    ·
                      rfl

theorem cell22_2270540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_2270540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270540 prefixEnd_2270540 := by exact prefixLift 2270540
  have htrace : WordTrace (prefixWord ++ tailWord_2270540) baseStart_2270540 baseEnd_2270540 := by
    simpa [prefixWord, tailWord_2270540, baseEnd_2270540] using wordTrace_append hprefix tailTrace_2270540
  have hstable : (prefixWord ++ tailWord_2270540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270540).length < 2 ^ (prefixWord ++ tailWord_2270540).sum := by decide
  have hdescent : baseEnd_2270540 < baseStart_2270540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270574 : List Nat := [4, 1, 2, 4, 1, 1, 2, 1, 1, 5]
def baseStart_2270574 : Nat := 118140960795 + 2270574 * 2 ^ 59
def prefixEnd_2270574 : Nat := 4983230072969 + 3 ^ 40 * 2270574 * 2
def baseEnd_2270574 : Nat := 777263882401269734988551

theorem tailTrace_2270574 : CollatzResearch.WordTrace tailWord_2270574 prefixEnd_2270574 777263882401269734988551 := by
  unfold tailWord_2270574
  simp only [CollatzResearch.WordTrace]
  refine ⟨10351829659513207001414347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55209758184070437340876517 10351829659513207001414347)
  ·
    refine ⟨15527744489269810502121521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10351829659513207001414347 15527744489269810502121521)
    ·
      refine ⟨11645808366952357876591141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15527744489269810502121521 11645808366952357876591141)
      ·
        refine ⟨2183589068803567101860839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11645808366952357876591141 2183589068803567101860839)
        ·
          refine ⟨3275383603205350652791259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2183589068803567101860839 3275383603205350652791259)
          ·
            refine ⟨4913075404808025979186889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3275383603205350652791259 4913075404808025979186889)
            ·
              refine ⟨3684806553606019484390167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4913075404808025979186889 3684806553606019484390167)
              ·
                refine ⟨5527209830409029226585251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3684806553606019484390167 5527209830409029226585251)
                ·
                  refine ⟨8290814745613543839877877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5527209830409029226585251 8290814745613543839877877)
                  ·
                    refine ⟨777263882401269734988551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8290814745613543839877877 777263882401269734988551)
                    ·
                      rfl

theorem cell22_2270574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_2270574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270574 prefixEnd_2270574 := by exact prefixLift 2270574
  have htrace : WordTrace (prefixWord ++ tailWord_2270574) baseStart_2270574 baseEnd_2270574 := by
    simpa [prefixWord, tailWord_2270574, baseEnd_2270574] using wordTrace_append hprefix tailTrace_2270574
  have hstable : (prefixWord ++ tailWord_2270574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270574).length < 2 ^ (prefixWord ++ tailWord_2270574).sum := by decide
  have hdescent : baseEnd_2270574 < baseStart_2270574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270583 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 2, 6]
def baseStart_2270583 : Nat := 118140960795 + 2270583 * 2 ^ 59
def prefixEnd_2270583 : Nat := 4983230072969 + 3 ^ 40 * 2270583 * 2
def baseEnd_2270583 : Nat := 777266963285196711513523

theorem tailTrace_2270583 : CollatzResearch.WordTrace tailWord_2270583 prefixEnd_2270583 777266963285196711513523 := by
  unfold tailWord_2270583
  simp only [CollatzResearch.WordTrace]
  refine ⟨82814965533073050548392403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55209977022048700365594935 82814965533073050548392403)
  ·
    refine ⟨124222448299609575822588605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82814965533073050548392403 124222448299609575822588605)
    ·
      refine ⟨46583418112353590933470727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124222448299609575822588605 46583418112353590933470727)
      ·
        refine ⟨69875127168530386400206091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46583418112353590933470727 69875127168530386400206091)
        ·
          refine ⟨104812690752795579600309137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69875127168530386400206091 104812690752795579600309137)
          ·
            refine ⟨78609518064596684700231853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104812690752795579600309137 78609518064596684700231853)
            ·
              refine ⟨29478569274223756762586945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78609518064596684700231853 29478569274223756762586945)
              ·
                refine ⟨22108926955667817571940209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29478569274223756762586945 22108926955667817571940209)
                ·
                  refine ⟨16581695216750863178955157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22108926955667817571940209 16581695216750863178955157)
                  ·
                    refine ⟨777266963285196711513523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16581695216750863178955157 777266963285196711513523)
                    ·
                      rfl

theorem cell22_2270583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_2270583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270583 prefixEnd_2270583 := by exact prefixLift 2270583
  have htrace : WordTrace (prefixWord ++ tailWord_2270583) baseStart_2270583 baseEnd_2270583 := by
    simpa [prefixWord, tailWord_2270583, baseEnd_2270583] using wordTrace_append hprefix tailTrace_2270583
  have hstable : (prefixWord ++ tailWord_2270583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270583).length < 2 ^ (prefixWord ++ tailWord_2270583).sum := by decide
  have hdescent : baseEnd_2270583 < baseStart_2270583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270585 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 5, 3]
def baseStart_2270585 : Nat := 118140960795 + 2270585 * 2 ^ 59
def prefixEnd_2270585 : Nat := 4983230072969 + 3 ^ 40 * 2270585 * 2
def baseEnd_2270585 : Nat := 777267647926069372963517

theorem tailTrace_2270585 : CollatzResearch.WordTrace tailWord_2270585 prefixEnd_2270585 777267647926069372963517 := by
  unfold tailWord_2270585
  simp only [CollatzResearch.WordTrace]
  refine ⟨82815038479065804889965209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55210025652710536593310139 82815038479065804889965209)
  ·
    refine ⟨62111278859299353667473907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82815038479065804889965209 62111278859299353667473907)
    ·
      refine ⟨93166918288949030501210861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62111278859299353667473907 93166918288949030501210861)
      ·
        refine ⟨34937594358355886437954073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93166918288949030501210861 34937594358355886437954073)
        ·
          refine ⟨26203195768766914828465555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34937594358355886437954073 26203195768766914828465555)
          ·
            refine ⟨39304793653150372242698333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26203195768766914828465555 39304793653150372242698333)
            ·
              refine ⟨14739297619931389591011875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39304793653150372242698333 14739297619931389591011875)
              ·
                refine ⟨22108946429897084386517813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14739297619931389591011875 22108946429897084386517813)
                ·
                  refine ⟨2072713727802851661236045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22108946429897084386517813 2072713727802851661236045)
                  ·
                    refine ⟨777267647926069372963517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2072713727802851661236045 777267647926069372963517)
                    ·
                      rfl

theorem cell22_2270585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 3].length) (baseStart_2270585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270585 prefixEnd_2270585 := by exact prefixLift 2270585
  have htrace : WordTrace (prefixWord ++ tailWord_2270585) baseStart_2270585 baseEnd_2270585 := by
    simpa [prefixWord, tailWord_2270585, baseEnd_2270585] using wordTrace_append hprefix tailTrace_2270585
  have hstable : (prefixWord ++ tailWord_2270585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270585).length < 2 ^ (prefixWord ++ tailWord_2270585).sum := by decide
  have hdescent : baseEnd_2270585 < baseStart_2270585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270705 : List Nat := [1, 2, 2, 2, 3, 2, 2, 8]
def baseStart_2270705 : Nat := 118140960795 + 2270705 * 2 ^ 59
def prefixEnd_2270705 : Nat := 4983230072969 + 3 ^ 40 * 2270705 * 2
def baseEnd_2270705 : Nat := 86367636264269895551461

theorem tailTrace_2270705 : CollatzResearch.WordTrace tailWord_2270705 prefixEnd_2270705 86367636264269895551461 := by
  unfold tailWord_2270705
  simp only [CollatzResearch.WordTrace]
  refine ⟨82819415238631065384333569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55212943492420710256222379 82819415238631065384333569)
  ·
    refine ⟨62114561428973299038250177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82819415238631065384333569 62114561428973299038250177)
    ·
      refine ⟨46585921071729974278687633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62114561428973299038250177 46585921071729974278687633)
      ·
        refine ⟨34939440803797480709015725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46585921071729974278687633 34939440803797480709015725)
        ·
          refine ⟨13102290301424055265880897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34939440803797480709015725 13102290301424055265880897)
          ·
            refine ⟨9826717726068041449410673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13102290301424055265880897 9826717726068041449410673)
            ·
              refine ⟨7370038294551031087058005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9826717726068041449410673 7370038294551031087058005)
              ·
                refine ⟨86367636264269895551461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7370038294551031087058005 86367636264269895551461)
                ·
                  rfl

theorem cell22_2270705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 8].length) (baseStart_2270705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270705 prefixEnd_2270705 := by exact prefixLift 2270705
  have htrace : WordTrace (prefixWord ++ tailWord_2270705) baseStart_2270705 baseEnd_2270705 := by
    simpa [prefixWord, tailWord_2270705, baseEnd_2270705] using wordTrace_append hprefix tailTrace_2270705
  have hstable : (prefixWord ++ tailWord_2270705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270705).length < 2 ^ (prefixWord ++ tailWord_2270705).sum := by decide
  have hdescent : baseEnd_2270705 < baseStart_2270705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270709 : List Nat := [1, 3, 5, 1, 1, 2, 1, 2, 1, 5]
def baseStart_2270709 : Nat := 118140960795 + 2270709 * 2 ^ 59
def prefixEnd_2270709 : Nat := 4983230072969 + 3 ^ 40 * 2270709 * 2
def baseEnd_2270709 : Nat := 777310095660174382863137

theorem tailTrace_2270709 : CollatzResearch.WordTrace tailWord_2270709 prefixEnd_2270709 777310095660174382863137 := by
  unfold tailWord_2270709
  simp only [CollatzResearch.WordTrace]
  refine ⟨82819561130616574067479181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55213040753744382711652787 82819561130616574067479181)
  ·
    refine ⟨31057335423981215275304693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82819561130616574067479181 31057335423981215275304693)
    ·
      refine ⟨2911625195998238932059815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31057335423981215275304693 2911625195998238932059815)
      ·
        refine ⟨4367437793997358398089723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2911625195998238932059815 4367437793997358398089723)
        ·
          refine ⟨6551156690996037597134585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4367437793997358398089723 6551156690996037597134585)
          ·
            refine ⟨4913367518247028197850939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6551156690996037597134585 4913367518247028197850939)
            ·
              refine ⟨7370051277370542296776409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4913367518247028197850939 7370051277370542296776409)
              ·
                refine ⟨5527538458027906722582307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7370051277370542296776409 5527538458027906722582307)
                ·
                  refine ⟨8291307687041860083873461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5527538458027906722582307 8291307687041860083873461)
                  ·
                    refine ⟨777310095660174382863137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8291307687041860083873461 777310095660174382863137)
                    ·
                      rfl

theorem cell22_2270709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_2270709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270709 prefixEnd_2270709 := by exact prefixLift 2270709
  have htrace : WordTrace (prefixWord ++ tailWord_2270709) baseStart_2270709 baseEnd_2270709 := by
    simpa [prefixWord, tailWord_2270709, baseEnd_2270709] using wordTrace_append hprefix tailTrace_2270709
  have hstable : (prefixWord ++ tailWord_2270709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270709).length < 2 ^ (prefixWord ++ tailWord_2270709).sum := by decide
  have hdescent : baseEnd_2270709 < baseStart_2270709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270722 : List Nat := [3, 4, 1, 2, 1, 11]
def baseStart_2270722 : Nat := 118140960795 + 2270722 * 2 ^ 59
def prefixEnd_2270722 : Nat := 4983230072969 + 3 ^ 40 * 2270722 * 2
def baseEnd_2270722 : Nat := 9596475874393168917137

theorem tailTrace_2270722 : CollatzResearch.WordTrace tailWord_2270722 prefixEnd_2270722 9596475874393168917137 := by
  unfold tailWord_2270722
  simp only [CollatzResearch.WordTrace]
  refine ⟨20705008819892369321925605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55213356853046318191801613 20705008819892369321925605)
  ·
    refine ⟨3882189153729819247861051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20705008819892369321925605 3882189153729819247861051)
    ·
      refine ⟨5823283730594728871791577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3882189153729819247861051 5823283730594728871791577)
      ·
        refine ⟨4367462797946046653843683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5823283730594728871791577 4367462797946046653843683)
        ·
          refine ⟨6551194196919069980765525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4367462797946046653843683 6551194196919069980765525)
          ·
            refine ⟨9596475874393168917137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6551194196919069980765525 9596475874393168917137)
            ·
              rfl

theorem cell22_2270722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 11].length) (baseStart_2270722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270722 prefixEnd_2270722 := by exact prefixLift 2270722
  have htrace : WordTrace (prefixWord ++ tailWord_2270722) baseStart_2270722 baseEnd_2270722 := by
    simpa [prefixWord, tailWord_2270722, baseEnd_2270722] using wordTrace_append hprefix tailTrace_2270722
  have hstable : (prefixWord ++ tailWord_2270722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270722).length < 2 ^ (prefixWord ++ tailWord_2270722).sum := by decide
  have hdescent : baseEnd_2270722 < baseStart_2270722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270737 : List Nat := [1, 2, 2, 1, 1, 2, 4, 3, 3, 3]
def baseStart_2270737 : Nat := 118140960795 + 2270737 * 2 ^ 59
def prefixEnd_2270737 : Nat := 4983230072969 + 3 ^ 40 * 2270737 * 2
def baseEnd_2270737 : Nat := 777319680632391643163051

theorem tailTrace_2270737 : CollatzResearch.WordTrace tailWord_2270737 prefixEnd_2270737 777319680632391643163051 := by
  unfold tailWord_2270737
  simp only [CollatzResearch.WordTrace]
  refine ⟨82820582374515134849498465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55213721583010089899665643 82820582374515134849498465)
  ·
    refine ⟨62115436780886351137123849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82820582374515134849498465 62115436780886351137123849)
    ·
      refine ⟨46586577585664763352842887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62115436780886351137123849 46586577585664763352842887)
      ·
        refine ⟨69879866378497145029264331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46586577585664763352842887 69879866378497145029264331)
        ·
          refine ⟨104819799567745717543896497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69879866378497145029264331 104819799567745717543896497)
          ·
            refine ⟨78614849675809288157922373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104819799567745717543896497 78614849675809288157922373)
            ·
              refine ⟨14740284314214241529610445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78614849675809288157922373 14740284314214241529610445)
              ·
                refine ⟨5527606617830340573603917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14740284314214241529610445 5527606617830340573603917)
                ·
                  refine ⟨2072852481686377715101469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5527606617830340573603917 2072852481686377715101469)
                  ·
                    refine ⟨777319680632391643163051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2072852481686377715101469 777319680632391643163051)
                    ·
                      rfl

theorem cell22_2270737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_2270737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270737 prefixEnd_2270737 := by exact prefixLift 2270737
  have htrace : WordTrace (prefixWord ++ tailWord_2270737) baseStart_2270737 baseEnd_2270737 := by
    simpa [prefixWord, tailWord_2270737, baseEnd_2270737] using wordTrace_append hprefix tailTrace_2270737
  have hstable : (prefixWord ++ tailWord_2270737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270737).length < 2 ^ (prefixWord ++ tailWord_2270737).sum := by decide
  have hdescent : baseEnd_2270737 < baseStart_2270737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270771 : List Nat := [1, 1, 1, 2, 4, 4, 2, 3, 1, 3]
def baseStart_2270771 : Nat := 118140960795 + 2270771 * 2 ^ 59
def prefixEnd_2270771 : Nat := 4983230072969 + 3 ^ 40 * 2270771 * 2
def baseEnd_2270771 : Nat := 777331319527226887812947

theorem tailTrace_2270771 : CollatzResearch.WordTrace tailWord_2270771 prefixEnd_2270771 777331319527226887812947 := by
  unfold tailWord_2270771
  simp only [CollatzResearch.WordTrace]
  refine ⟨82821822456391958656236167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55214548304261305770824111 82821822456391958656236167)
  ·
    refine ⟨124232733684587937984354251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82821822456391958656236167 124232733684587937984354251)
    ·
      refine ⟨186349100526881906976531377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124232733684587937984354251 186349100526881906976531377)
      ·
        refine ⟨139761825395161430232398533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186349100526881906976531377 139761825395161430232398533)
        ·
          refine ⟨26205342261592768168574725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139761825395161430232398533 26205342261592768168574725)
          ·
            refine ⟨4913501674048644031607761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26205342261592768168574725 4913501674048644031607761)
            ·
              refine ⟨3685126255536483023705821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4913501674048644031607761 3685126255536483023705821)
              ·
                refine ⟨1381922345826181133889683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3685126255536483023705821 1381922345826181133889683)
                ·
                  refine ⟨2072883518739271700834525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1381922345826181133889683 2072883518739271700834525)
                  ·
                    refine ⟨777331319527226887812947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2072883518739271700834525 777331319527226887812947)
                    ·
                      rfl

theorem cell22_2270771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 1, 3].length) (baseStart_2270771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270771 prefixEnd_2270771 := by exact prefixLift 2270771
  have htrace : WordTrace (prefixWord ++ tailWord_2270771) baseStart_2270771 baseEnd_2270771 := by
    simpa [prefixWord, tailWord_2270771, baseEnd_2270771] using wordTrace_append hprefix tailTrace_2270771
  have hstable : (prefixWord ++ tailWord_2270771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270771).length < 2 ^ (prefixWord ++ tailWord_2270771).sum := by decide
  have hdescent : baseEnd_2270771 < baseStart_2270771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270844 : List Nat := [2, 2, 2, 1, 1, 2, 1, 6, 2, 3]
def baseStart_2270844 : Nat := 118140960795 + 2270844 * 2 ^ 59
def prefixEnd_2270844 : Nat := 4983230072969 + 3 ^ 40 * 2270844 * 2
def baseEnd_2270844 : Nat := 777356308919079030737723

theorem tailTrace_2270844 : CollatzResearch.WordTrace tailWord_2270844 prefixEnd_2270844 777356308919079030737723 := by
  unfold tailWord_2270844
  simp only [CollatzResearch.WordTrace]
  refine ⟨41412242492563746061821793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55216323323418328082429057 41412242492563746061821793)
  ·
    refine ⟨31059181869422809546366345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41412242492563746061821793 31059181869422809546366345)
    ·
      refine ⟨23294386402067107159774759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31059181869422809546366345 23294386402067107159774759)
      ·
        refine ⟨34941579603100660739662139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23294386402067107159774759 34941579603100660739662139)
        ·
          refine ⟨52412369404650991109493209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34941579603100660739662139 52412369404650991109493209)
          ·
            refine ⟨39309277053488243332119907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52412369404650991109493209 39309277053488243332119907)
            ·
              refine ⟨58963915580232364998179861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39309277053488243332119907 58963915580232364998179861)
              ·
                refine ⟨2763933542823392109289681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58963915580232364998179861 2763933542823392109289681)
                ·
                  refine ⟨2072950157117544081967261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2763933542823392109289681 2072950157117544081967261)
                  ·
                    refine ⟨777356308919079030737723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2072950157117544081967261 777356308919079030737723)
                    ·
                      rfl

theorem cell22_2270844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_2270844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270844 prefixEnd_2270844 := by exact prefixLift 2270844
  have htrace : WordTrace (prefixWord ++ tailWord_2270844) baseStart_2270844 baseEnd_2270844 := by
    simpa [prefixWord, tailWord_2270844, baseEnd_2270844] using wordTrace_append hprefix tailTrace_2270844
  have hstable : (prefixWord ++ tailWord_2270844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270844).length < 2 ^ (prefixWord ++ tailWord_2270844).sum := by decide
  have hdescent : baseEnd_2270844 < baseStart_2270844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270876 : List Nat := [2, 2, 3, 2, 3, 1, 2, 1, 2, 4]
def baseStart_2270876 : Nat := 118140960795 + 2270876 * 2 ^ 59
def prefixEnd_2270876 : Nat := 4983230072969 + 3 ^ 40 * 2270876 * 2
def baseEnd_2270876 : Nat := 777367263173041613937625

theorem tailTrace_2270876 : CollatzResearch.WordTrace tailWord_2270876 prefixEnd_2270876 777367263173041613937625 := by
  unfold tailWord_2270876
  simp only [CollatzResearch.WordTrace]
  refine ⟨41412826060505780794404241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55217101414007707725872321 41412826060505780794404241)
  ·
    refine ⟨31059619545379335595803181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41412826060505780794404241 31059619545379335595803181)
    ·
      refine ⟨11647357329517250848426193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31059619545379335595803181 11647357329517250848426193)
      ·
        refine ⟨8735517997137938136319645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11647357329517250848426193 8735517997137938136319645)
        ·
          refine ⟨3275819248926726801119867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8735517997137938136319645 3275819248926726801119867)
          ·
            refine ⟨4913728873390090201679801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3275819248926726801119867 4913728873390090201679801)
            ·
              refine ⟨3685296655042567651259851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4913728873390090201679801 3685296655042567651259851)
              ·
                refine ⟨5527944982563851476889777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3685296655042567651259851 5527944982563851476889777)
                ·
                  refine ⟨4145958736922888607667333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5527944982563851476889777 4145958736922888607667333)
                  ·
                    refine ⟨777367263173041613937625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4145958736922888607667333 777367263173041613937625)
                    ·
                      rfl

theorem cell22_2270876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_2270876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270876 prefixEnd_2270876 := by exact prefixLift 2270876
  have htrace : WordTrace (prefixWord ++ tailWord_2270876) baseStart_2270876 baseEnd_2270876 := by
    simpa [prefixWord, tailWord_2270876, baseEnd_2270876] using wordTrace_append hprefix tailTrace_2270876
  have hstable : (prefixWord ++ tailWord_2270876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270876).length < 2 ^ (prefixWord ++ tailWord_2270876).sum := by decide
  have hdescent : baseEnd_2270876 < baseStart_2270876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270917 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 2, 5]
def baseStart_2270917 : Nat := 118140960795 + 2270917 * 2 ^ 59
def prefixEnd_2270917 : Nat := 4983230072969 + 3 ^ 40 * 2270917 * 2
def baseEnd_2270917 : Nat := 777381298310931173662499

theorem tailTrace_2270917 : CollatzResearch.WordTrace tailWord_2270917 prefixEnd_2270917 777381298310931173662499 := by
  unfold tailWord_2270917
  simp only [CollatzResearch.WordTrace]
  refine ⟨82827147513863025591051005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55218098342575350394034003 82827147513863025591051005)
  ·
    refine ⟨31060180317698634596644127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82827147513863025591051005 31060180317698634596644127)
    ·
      refine ⟨46590270476547951894966191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31060180317698634596644127 46590270476547951894966191)
      ·
        refine ⟨69885405714821927842449287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46590270476547951894966191 69885405714821927842449287)
        ·
          refine ⟨104828108572232891763673931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69885405714821927842449287 104828108572232891763673931)
          ·
            refine ⟨157242162858349337645510897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104828108572232891763673931 157242162858349337645510897)
            ·
              refine ⟨117931622143762003234133173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157242162858349337645510897 117931622143762003234133173)
              ·
                refine ⟨11056089575977687803199985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117931622143762003234133173 11056089575977687803199985)
                ·
                  refine ⟨8292067181983265852399989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11056089575977687803199985 8292067181983265852399989)
                  ·
                    refine ⟨777381298310931173662499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8292067181983265852399989 777381298310931173662499)
                    ·
                      rfl

theorem cell22_2270917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_2270917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270917 prefixEnd_2270917 := by exact prefixLift 2270917
  have htrace : WordTrace (prefixWord ++ tailWord_2270917) baseStart_2270917 baseEnd_2270917 := by
    simpa [prefixWord, tailWord_2270917, baseEnd_2270917] using wordTrace_append hprefix tailTrace_2270917
  have hstable : (prefixWord ++ tailWord_2270917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270917).length < 2 ^ (prefixWord ++ tailWord_2270917).sum := by decide
  have hdescent : baseEnd_2270917 < baseStart_2270917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270979 : List Nat := [1, 1, 1, 3, 2, 2, 5, 1, 1, 5]
def baseStart_2270979 : Nat := 118140960795 + 2270979 * 2 ^ 59
def prefixEnd_2270979 : Nat := 4983230072969 + 3 ^ 40 * 2270979 * 2
def baseEnd_2270979 : Nat := 777402522177983678612309

theorem tailTrace_2270979 : CollatzResearch.WordTrace tailWord_2270979 prefixEnd_2270979 777402522177983678612309 := by
  unfold tailWord_2270979
  simp only [CollatzResearch.WordTrace]
  refine ⟨82829408839638410179807991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55219605893092273453205327 82829408839638410179807991)
  ·
    refine ⟨124244113259457615269711987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82829408839638410179807991 124244113259457615269711987)
    ·
      refine ⟨186366169889186422904567981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124244113259457615269711987 186366169889186422904567981)
      ·
        refine ⟨69887313708444908589212993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186366169889186422904567981 69887313708444908589212993)
        ·
          refine ⟨52415485281333681441909745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69887313708444908589212993 52415485281333681441909745)
          ·
            refine ⟨39311613961000261081432309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52415485281333681441909745 39311613961000261081432309)
            ·
              refine ⟨3685463808843774476384279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39311613961000261081432309 3685463808843774476384279)
              ·
                refine ⟨5528195713265661714576419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3685463808843774476384279 5528195713265661714576419)
                ·
                  refine ⟨8292293569898492571864629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5528195713265661714576419 8292293569898492571864629)
                  ·
                    refine ⟨777402522177983678612309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8292293569898492571864629 777402522177983678612309)
                    ·
                      rfl

theorem cell22_2270979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 5].length) (baseStart_2270979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270979 prefixEnd_2270979 := by exact prefixLift 2270979
  have htrace : WordTrace (prefixWord ++ tailWord_2270979) baseStart_2270979 baseEnd_2270979 := by
    simpa [prefixWord, tailWord_2270979, baseEnd_2270979] using wordTrace_append hprefix tailTrace_2270979
  have hstable : (prefixWord ++ tailWord_2270979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270979).length < 2 ^ (prefixWord ++ tailWord_2270979).sum := by decide
  have hdescent : baseEnd_2270979 < baseStart_2270979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270983 : List Nat := [1, 1, 4, 4, 2, 1, 2, 2, 1, 4]
def baseStart_2270983 : Nat := 118140960795 + 2270983 * 2 ^ 59
def prefixEnd_2270983 : Nat := 4983230072969 + 3 ^ 40 * 2270983 * 2
def baseEnd_2270983 : Nat := 777403891459729001512297

theorem tailTrace_2270983 : CollatzResearch.WordTrace tailWord_2270983 prefixEnd_2270983 777403891459729001512297 := by
  unfold tailWord_2270983
  simp only [CollatzResearch.WordTrace]
  refine ⟨82829554731623918862953603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55219703154415945908635735 82829554731623918862953603)
  ·
    refine ⟨124244332097435878294430405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82829554731623918862953603 124244332097435878294430405)
    ·
      refine ⟨23295812268269227180205701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124244332097435878294430405 23295812268269227180205701)
      ·
        refine ⟨4367964800300480096288569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23295812268269227180205701 4367964800300480096288569)
        ·
          refine ⟨3275973600225360072216427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4367964800300480096288569 3275973600225360072216427)
          ·
            refine ⟨4913960400338040108324641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3275973600225360072216427 4913960400338040108324641)
            ·
              refine ⟨3685470300253530081243481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4913960400338040108324641 3685470300253530081243481)
              ·
                refine ⟨2764102725190147560932611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3685470300253530081243481 2764102725190147560932611)
                ·
                  refine ⟨4146154087785221341398917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2764102725190147560932611 4146154087785221341398917)
                  ·
                    refine ⟨777403891459729001512297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4146154087785221341398917 777403891459729001512297)
                    ·
                      rfl

theorem cell22_2270983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_2270983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2270983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2270983 prefixEnd_2270983 := by exact prefixLift 2270983
  have htrace : WordTrace (prefixWord ++ tailWord_2270983) baseStart_2270983 baseEnd_2270983 := by
    simpa [prefixWord, tailWord_2270983, baseEnd_2270983] using wordTrace_append hprefix tailTrace_2270983
  have hstable : (prefixWord ++ tailWord_2270983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270983).length < 2 ^ (prefixWord ++ tailWord_2270983).sum := by decide
  have hdescent : baseEnd_2270983 < baseStart_2270983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271009 : List Nat := [1, 2, 3, 2, 1, 5, 8]
def baseStart_2271009 : Nat := 118140960795 + 2271009 * 2 ^ 59
def prefixEnd_2271009 : Nat := 4983230072969 + 3 ^ 40 * 2271009 * 2
def baseEnd_2271009 : Nat := 28793066362632355568971

theorem tailTrace_2271009 : CollatzResearch.WordTrace tailWord_2271009 prefixEnd_2271009 28793066362632355568971 := by
  unfold tailWord_2271009
  simp only [CollatzResearch.WordTrace]
  refine ⟨82830503029529725303400081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55220335353019816868933387 82830503029529725303400081)
  ·
    refine ⟨62122877272147293977550061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82830503029529725303400081 62122877272147293977550061)
    ·
      refine ⟨23296078977055235241581273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62122877272147293977550061 23296078977055235241581273)
      ·
        refine ⟨17472059232791426431185955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23296078977055235241581273 17472059232791426431185955)
        ·
          refine ⟨26208088849187139646778933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17472059232791426431185955 26208088849187139646778933)
          ·
            refine ⟨2457008329611294341885525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26208088849187139646778933 2457008329611294341885525)
            ·
              refine ⟨28793066362632355568971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2457008329611294341885525 28793066362632355568971)
              ·
                rfl

theorem cell22_2271009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 8].length) (baseStart_2271009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271009 prefixEnd_2271009 := by exact prefixLift 2271009
  have htrace : WordTrace (prefixWord ++ tailWord_2271009) baseStart_2271009 baseEnd_2271009 := by
    simpa [prefixWord, tailWord_2271009, baseEnd_2271009] using wordTrace_append hprefix tailTrace_2271009
  have hstable : (prefixWord ++ tailWord_2271009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271009).length < 2 ^ (prefixWord ++ tailWord_2271009).sum := by decide
  have hdescent : baseEnd_2271009 < baseStart_2271009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271030 : List Nat := [5, 1, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_2271030 : Nat := 118140960795 + 2271030 * 2 ^ 59
def prefixEnd_2271030 : Nat := 4983230072969 + 3 ^ 40 * 2271030 * 2
def baseEnd_2271030 : Nat := 777419980520236545587153

theorem tailTrace_2271030 : CollatzResearch.WordTrace tailWord_2271030 prefixEnd_2271030 777419980520236545587153 := by
  unfold tailWord_2271030
  simp only [CollatzResearch.WordTrace]
  refine ⟨5176954310153352868119659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55220845974969097259943029 5176954310153352868119659)
  ·
    refine ⟨7765431465230029302179489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5176954310153352868119659 7765431465230029302179489)
    ·
      refine ⟨5824073598922521976634617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7765431465230029302179489 5824073598922521976634617)
      ·
        refine ⟨4368055199191891482475963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5824073598922521976634617 4368055199191891482475963)
        ·
          refine ⟨6552082798787837223713945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4368055199191891482475963 6552082798787837223713945)
          ·
            refine ⟨4914062099090877917785459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6552082798787837223713945 4914062099090877917785459)
            ·
              refine ⟨7371093148636316876678189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4914062099090877917785459 7371093148636316876678189)
              ·
                refine ⟨2764159930738618828754321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7371093148636316876678189 2764159930738618828754321)
                ·
                  refine ⟨2073119948053964121565741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2764159930738618828754321 2073119948053964121565741)
                  ·
                    refine ⟨777419980520236545587153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2073119948053964121565741 777419980520236545587153)
                    ·
                      rfl

theorem cell22_2271030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_2271030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271030 prefixEnd_2271030 := by exact prefixLift 2271030
  have htrace : WordTrace (prefixWord ++ tailWord_2271030) baseStart_2271030 baseEnd_2271030 := by
    simpa [prefixWord, tailWord_2271030, baseEnd_2271030] using wordTrace_append hprefix tailTrace_2271030
  have hstable : (prefixWord ++ tailWord_2271030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271030).length < 2 ^ (prefixWord ++ tailWord_2271030).sum := by decide
  have hdescent : baseEnd_2271030 < baseStart_2271030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271071 : List Nat := [1, 1, 2, 3, 1, 5, 2, 2, 5]
def baseStart_2271071 : Nat := 118140960795 + 2271071 * 2 ^ 59
def prefixEnd_2271071 : Nat := 4983230072969 + 3 ^ 40 * 2271071 * 2
def baseEnd_2271071 : Nat := 259144671886042035104009

theorem tailTrace_2271071 : CollatzResearch.WordTrace tailWord_2271071 prefixEnd_2271071 259144671886042035104009 := by
  unfold tailWord_2271071
  simp only [CollatzResearch.WordTrace]
  refine ⟨82832764355305109892157067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55221842903536739928104711 82832764355305109892157067)
  ·
    refine ⟨124249146532957664838235601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82832764355305109892157067 124249146532957664838235601)
    ·
      refine ⟨93186859899718248628676701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124249146532957664838235601 93186859899718248628676701)
      ·
        refine ⟨34945072462394343235753763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93186859899718248628676701 34945072462394343235753763)
        ·
          refine ⟨52417608693591514853630645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34945072462394343235753763 52417608693591514853630645)
          ·
            refine ⟨4914150815024204517527873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52417608693591514853630645 4914150815024204517527873)
            ·
              refine ⟨3685613111268153388145905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4914150815024204517527873 3685613111268153388145905)
              ·
                refine ⟨2764209833451115041109429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3685613111268153388145905 2764209833451115041109429)
                ·
                  refine ⟨259144671886042035104009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2764209833451115041109429 259144671886042035104009)
                  ·
                    rfl

theorem cell22_2271071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 5].length) (baseStart_2271071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271071 prefixEnd_2271071 := by exact prefixLift 2271071
  have htrace : WordTrace (prefixWord ++ tailWord_2271071) baseStart_2271071 baseEnd_2271071 := by
    simpa [prefixWord, tailWord_2271071, baseEnd_2271071] using wordTrace_append hprefix tailTrace_2271071
  have hstable : (prefixWord ++ tailWord_2271071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271071).length < 2 ^ (prefixWord ++ tailWord_2271071).sum := by decide
  have hdescent : baseEnd_2271071 < baseStart_2271071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271075 : List Nat := [1, 1, 1, 5, 4, 1, 1, 4, 1, 3]
def baseStart_2271075 : Nat := 118140960795 + 2271075 * 2 ^ 59
def prefixEnd_2271075 : Nat := 4983230072969 + 3 ^ 40 * 2271075 * 2
def baseEnd_2271075 : Nat := 777435384939871428212015

theorem tailTrace_2271075 : CollatzResearch.WordTrace tailWord_2271075 prefixEnd_2271075 777435384939871428212015 := by
  unfold tailWord_2271075
  simp only [CollatzResearch.WordTrace]
  refine ⟨82832910247290618575302679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55221940164860412383535119 82832910247290618575302679)
  ·
    refine ⟨124249365370935927862954019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82832910247290618575302679 124249365370935927862954019)
    ·
      refine ⟨186374048056403891794431029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124249365370935927862954019 186374048056403891794431029)
      ·
        refine ⟨17472567005287864855727909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 186374048056403891794431029 17472567005287864855727909)
        ·
          refine ⟨3276106313491474660448983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17472567005287864855727909 3276106313491474660448983)
          ·
            refine ⟨4914159470237211990673475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3276106313491474660448983 4914159470237211990673475)
            ·
              refine ⟨7371239205355817986010213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4914159470237211990673475 7371239205355817986010213)
              ·
                refine ⟨1382107351004215872376915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7371239205355817986010213 1382107351004215872376915)
                ·
                  refine ⟨2073161026506323808565373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382107351004215872376915 2073161026506323808565373)
                  ·
                    refine ⟨777435384939871428212015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2073161026506323808565373 777435384939871428212015)
                    ·
                      rfl

theorem cell22_2271075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 1, 3].length) (baseStart_2271075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271075 prefixEnd_2271075 := by exact prefixLift 2271075
  have htrace : WordTrace (prefixWord ++ tailWord_2271075) baseStart_2271075 baseEnd_2271075 := by
    simpa [prefixWord, tailWord_2271075, baseEnd_2271075] using wordTrace_append hprefix tailTrace_2271075
  have hstable : (prefixWord ++ tailWord_2271075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271075).length < 2 ^ (prefixWord ++ tailWord_2271075).sum := by decide
  have hdescent : baseEnd_2271075 < baseStart_2271075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271086 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_2271086 : Nat := 118140960795 + 2271086 * 2 ^ 59
def prefixEnd_2271086 : Nat := 4983230072969 + 3 ^ 40 * 2271086 * 2
def baseEnd_2271086 : Nat := 777439150464671066186981

theorem tailTrace_2271086 : CollatzResearch.WordTrace tailWord_2271086 prefixEnd_2271086 777439150464671066186981 := by
  unfold tailWord_2271086
  simp only [CollatzResearch.WordTrace]
  refine ⟨10354163931281345931744139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55222207633500511635968741 10354163931281345931744139)
  ·
    refine ⟨15531245896922018897616209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10354163931281345931744139 15531245896922018897616209)
    ·
      refine ⟨11648434422691514173212157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15531245896922018897616209 11648434422691514173212157)
      ·
        refine ⟨4368162908509317814954559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11648434422691514173212157 4368162908509317814954559)
        ·
          refine ⟨6552244362763976722431839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4368162908509317814954559 6552244362763976722431839)
          ·
            refine ⟨9828366544145965083647759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6552244362763976722431839 9828366544145965083647759)
            ·
              refine ⟨14742549816218947625471639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9828366544145965083647759 14742549816218947625471639)
              ·
                refine ⟨22113824724328421438207459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14742549816218947625471639 22113824724328421438207459)
                ·
                  refine ⟨33170737086492632157311189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22113824724328421438207459 33170737086492632157311189)
                  ·
                    refine ⟨777439150464671066186981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33170737086492632157311189 777439150464671066186981)
                    ·
                      rfl

theorem cell22_2271086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_2271086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271086 prefixEnd_2271086 := by exact prefixLift 2271086
  have htrace : WordTrace (prefixWord ++ tailWord_2271086) baseStart_2271086 baseEnd_2271086 := by
    simpa [prefixWord, tailWord_2271086, baseEnd_2271086] using wordTrace_append hprefix tailTrace_2271086
  have hstable : (prefixWord ++ tailWord_2271086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271086).length < 2 ^ (prefixWord ++ tailWord_2271086).sum := by decide
  have hdescent : baseEnd_2271086 < baseStart_2271086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271101 : List Nat := [1, 4, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_2271101 : Nat := 118140960795 + 2271101 * 2 ^ 59
def prefixEnd_2271101 : Nat := 4983230072969 + 3 ^ 40 * 2271101 * 2
def baseEnd_2271101 : Nat := 777444285271216027061935

theorem tailTrace_2271101 : CollatzResearch.WordTrace tailWord_2271101 prefixEnd_2271101 777444285271216027061935 := by
  unfold tailWord_2271101
  simp only [CollatzResearch.WordTrace]
  refine ⟨82833858545196425015749157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55222572363464283343832771 82833858545196425015749157)
  ·
    refine ⟨15531348477224329690452967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82833858545196425015749157 15531348477224329690452967)
    ·
      refine ⟨23297022715836494535679451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15531348477224329690452967 23297022715836494535679451)
      ·
        refine ⟨34945534073754741803519177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23297022715836494535679451 34945534073754741803519177)
        ·
          refine ⟨26209150555316056352639383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34945534073754741803519177 26209150555316056352639383)
          ·
            refine ⟨39313725832974084528959075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26209150555316056352639383 39313725832974084528959075)
            ·
              refine ⟨58970588749461126793438613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39313725832974084528959075 58970588749461126793438613)
              ·
                refine ⟨2764246347630990318442435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58970588749461126793438613 2764246347630990318442435)
                ·
                  refine ⟨4146369521446485477663653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2764246347630990318442435 4146369521446485477663653)
                  ·
                    refine ⟨777444285271216027061935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4146369521446485477663653 777444285271216027061935)
                    ·
                      rfl

theorem cell22_2271101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_2271101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271101 prefixEnd_2271101 := by exact prefixLift 2271101
  have htrace : WordTrace (prefixWord ++ tailWord_2271101) baseStart_2271101 baseEnd_2271101 := by
    simpa [prefixWord, tailWord_2271101, baseEnd_2271101] using wordTrace_append hprefix tailTrace_2271101
  have hstable : (prefixWord ++ tailWord_2271101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271101).length < 2 ^ (prefixWord ++ tailWord_2271101).sum := by decide
  have hdescent : baseEnd_2271101 < baseStart_2271101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271133 : List Nat := [1, 4, 2, 1, 2, 2, 2, 4, 4]
def baseStart_2271133 : Nat := 118140960795 + 2271133 * 2 ^ 59
def prefixEnd_2271133 : Nat := 4983230072969 + 3 ^ 40 * 2271133 * 2
def baseEnd_2271133 : Nat := 259151746508392870087279

theorem tailTrace_2271133 : CollatzResearch.WordTrace tailWord_2271133 prefixEnd_2271133 259151746508392870087279 := by
  unfold tailWord_2271133
  simp only [CollatzResearch.WordTrace]
  refine ⟨82835025681080494480914053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55223350454053662987276035 82835025681080494480914053)
  ·
    refine ⟨15531567315202592715171385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82835025681080494480914053 15531567315202592715171385)
    ·
      refine ⟨11648675486401944536378539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15531567315202592715171385 11648675486401944536378539)
      ·
        refine ⟨17473013229602916804567809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11648675486401944536378539 17473013229602916804567809)
        ·
          refine ⟨13104759922202187603425857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17473013229602916804567809 13104759922202187603425857)
          ·
            refine ⟨9828569941651640702569393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13104759922202187603425857 9828569941651640702569393)
            ·
              refine ⟨7371427456238730526927045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9828569941651640702569393 7371427456238730526927045)
              ·
                refine ⟨1382142648044761973798821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7371427456238730526927045 1382142648044761973798821)
                ·
                  refine ⟨259151746508392870087279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1382142648044761973798821 259151746508392870087279)
                  ·
                    rfl

theorem cell22_2271133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_2271133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271133 prefixEnd_2271133 := by exact prefixLift 2271133
  have htrace : WordTrace (prefixWord ++ tailWord_2271133) baseStart_2271133 baseEnd_2271133 := by
    simpa [prefixWord, tailWord_2271133, baseEnd_2271133] using wordTrace_append hprefix tailTrace_2271133
  have hstable : (prefixWord ++ tailWord_2271133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271133).length < 2 ^ (prefixWord ++ tailWord_2271133).sum := by decide
  have hdescent : baseEnd_2271133 < baseStart_2271133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271159 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 1, 9]
def baseStart_2271159 : Nat := 118140960795 + 2271159 * 2 ^ 59
def prefixEnd_2271159 : Nat := 4983230072969 + 3 ^ 40 * 2271159 * 2
def baseEnd_2271159 : Nat := 777464139856523209111757

theorem tailTrace_2271159 : CollatzResearch.WordTrace tailWord_2271159 prefixEnd_2271159 777464139856523209111757 := by
  unfold tailWord_2271159
  simp only [CollatzResearch.WordTrace]
  refine ⟨82835973978986300921360531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55223982652657533947573687 82835973978986300921360531)
  ·
    refine ⟨124253960968479451382040797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82835973978986300921360531 124253960968479451382040797)
    ·
      refine ⟨46595235363179794268265299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124253960968479451382040797 46595235363179794268265299)
      ·
        refine ⟨69892853044769691402397949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46595235363179794268265299 69892853044769691402397949)
        ·
          refine ⟨26209819891788634275899231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69892853044769691402397949 26209819891788634275899231)
          ·
            refine ⟨39314729837682951413848847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26209819891788634275899231 39314729837682951413848847)
            ·
              refine ⟨58972094756524427120773271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39314729837682951413848847 58972094756524427120773271)
              ·
                refine ⟨88458142134786640681159907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58972094756524427120773271 88458142134786640681159907)
                ·
                  refine ⟨132687213202179961021739861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88458142134786640681159907 132687213202179961021739861)
                  ·
                    refine ⟨777464139856523209111757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 132687213202179961021739861 777464139856523209111757)
                    ·
                      rfl

theorem cell22_2271159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_2271159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271159 prefixEnd_2271159 := by exact prefixLift 2271159
  have htrace : WordTrace (prefixWord ++ tailWord_2271159) baseStart_2271159 baseEnd_2271159 := by
    simpa [prefixWord, tailWord_2271159, baseEnd_2271159] using wordTrace_append hprefix tailTrace_2271159
  have hstable : (prefixWord ++ tailWord_2271159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271159).length < 2 ^ (prefixWord ++ tailWord_2271159).sum := by decide
  have hdescent : baseEnd_2271159 < baseStart_2271159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271296 : List Nat := [2, 1, 1, 2, 2, 5, 9]
def baseStart_2271296 : Nat := 118140960795 + 2271296 * 2 ^ 59
def prefixEnd_2271296 : Nat := 4983230072969 + 3 ^ 40 * 2271296 * 2
def baseEnd_2271296 : Nat := 28796705102085204386531

theorem tailTrace_2271296 : CollatzResearch.WordTrace tailWord_2271296 prefixEnd_2271296 28796705102085204386531 := by
  unfold tailWord_2271296
  simp only [CollatzResearch.WordTrace]
  refine ⟨41420485389744986659548871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55227313852993315546065161 41420485389744986659548871)
  ·
    refine ⟨62130728084617479989323307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41420485389744986659548871 62130728084617479989323307)
    ·
      refine ⟨93196092126926219983984961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62130728084617479989323307 93196092126926219983984961)
      ·
        refine ⟨69897069095194664987988721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93196092126926219983984961 69897069095194664987988721)
        ·
          refine ⟨52422801821395998740991541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69897069095194664987988721 52422801821395998740991541)
          ·
            refine ⟨4914637670755874881967957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52422801821395998740991541 4914637670755874881967957)
            ·
              refine ⟨28796705102085204386531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4914637670755874881967957 28796705102085204386531)
              ·
                rfl

theorem cell22_2271296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 9].length) (baseStart_2271296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271296 prefixEnd_2271296 := by exact prefixLift 2271296
  have htrace : WordTrace (prefixWord ++ tailWord_2271296) baseStart_2271296 baseEnd_2271296 := by
    simpa [prefixWord, tailWord_2271296, baseEnd_2271296] using wordTrace_append hprefix tailTrace_2271296
  have hstable : (prefixWord ++ tailWord_2271296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271296).length < 2 ^ (prefixWord ++ tailWord_2271296).sum := by decide
  have hdescent : baseEnd_2271296 < baseStart_2271296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271302 : List Nat := [6, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_2271302 : Nat := 118140960795 + 2271302 * 2 ^ 59
def prefixEnd_2271302 : Nat := 4983230072969 + 3 ^ 40 * 2271302 * 2
def baseEnd_2271302 : Nat := 259171030559639500928773

theorem tailTrace_2271302 : CollatzResearch.WordTrace tailWord_2271302 prefixEnd_2271302 259171030559639500928773 := by
  unfold tailWord_2271302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2588787175545882385744255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55227459744978824229210773 2588787175545882385744255)
  ·
    refine ⟨3883180763318823578616383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2588787175545882385744255 3883180763318823578616383)
    ·
      refine ⟨5824771144978235367924575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3883180763318823578616383 5824771144978235367924575)
      ·
        refine ⟨8737156717467353051886863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5824771144978235367924575 8737156717467353051886863)
        ·
          refine ⟨13105735076201029577830295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8737156717467353051886863 13105735076201029577830295)
          ·
            refine ⟨19658602614301544366745443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13105735076201029577830295 19658602614301544366745443)
            ·
              refine ⟨29487903921452316550118165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19658602614301544366745443 29487903921452316550118165)
              ·
                refine ⟨1382245496318077338286789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29487903921452316550118165 1382245496318077338286789)
                ·
                  refine ⟨259171030559639500928773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1382245496318077338286789 259171030559639500928773)
                  ·
                    rfl

theorem cell22_2271302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_2271302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271302 prefixEnd_2271302 := by exact prefixLift 2271302
  have htrace : WordTrace (prefixWord ++ tailWord_2271302) baseStart_2271302 baseEnd_2271302 := by
    simpa [prefixWord, tailWord_2271302, baseEnd_2271302] using wordTrace_append hprefix tailTrace_2271302
  have hstable : (prefixWord ++ tailWord_2271302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271302).length < 2 ^ (prefixWord ++ tailWord_2271302).sum := by decide
  have hdescent : baseEnd_2271302 < baseStart_2271302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271317 : List Nat := [1, 3, 2, 2, 1, 4, 3, 1, 2, 3]
def baseStart_2271317 : Nat := 118140960795 + 2271317 * 2 ^ 59
def prefixEnd_2271317 : Nat := 4983230072969 + 3 ^ 40 * 2271317 * 2
def baseEnd_2271317 : Nat := 777518226485463463661273

theorem tailTrace_2271317 : CollatzResearch.WordTrace tailWord_2271317 prefixEnd_2271317 777518226485463463661273 := by
  unfold tailWord_2271317
  simp only [CollatzResearch.WordTrace]
  refine ⟨82841736712413893905612205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55227824474942595937074803 82841736712413893905612205)
  ·
    refine ⟨31065651267155210214604577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82841736712413893905612205 31065651267155210214604577)
    ·
      refine ⟨23299238450366407660953433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31065651267155210214604577 23299238450366407660953433)
      ·
        refine ⟨17474428837774805745715075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23299238450366407660953433 17474428837774805745715075)
        ·
          refine ⟨26211643256662208618572613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17474428837774805745715075 26211643256662208618572613)
          ·
            refine ⟨4914683110624164115982365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26211643256662208618572613 4914683110624164115982365)
            ·
              refine ⟨1843006166484061543493387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4914683110624164115982365 1843006166484061543493387)
              ·
                refine ⟨2764509249726092315240081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1843006166484061543493387 2764509249726092315240081)
                ·
                  refine ⟨2073381937294569236430061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2764509249726092315240081 2073381937294569236430061)
                  ·
                    refine ⟨777518226485463463661273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2073381937294569236430061 777518226485463463661273)
                    ·
                      rfl

theorem cell22_2271317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_2271317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271317 prefixEnd_2271317 := by exact prefixLift 2271317
  have htrace : WordTrace (prefixWord ++ tailWord_2271317) baseStart_2271317 baseEnd_2271317 := by
    simpa [prefixWord, tailWord_2271317, baseEnd_2271317] using wordTrace_append hprefix tailTrace_2271317
  have hstable : (prefixWord ++ tailWord_2271317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271317).length < 2 ^ (prefixWord ++ tailWord_2271317).sum := by decide
  have hdescent : baseEnd_2271317 < baseStart_2271317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271330 : List Nat := [3, 3, 2, 2, 2, 1, 1, 8]
def baseStart_2271330 : Nat := 118140960795 + 2271330 * 2 ^ 59
def prefixEnd_2271330 : Nat := 4983230072969 + 3 ^ 40 * 2271330 * 2
def baseEnd_2271330 : Nat := 86391408516792862565137

theorem tailTrace_2271330 : CollatzResearch.WordTrace tailWord_2271330 prefixEnd_2271330 86391408516792862565137 := by
  unfold tailWord_2271330
  simp only [CollatzResearch.WordTrace]
  refine ⟨20710552715341699281458861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55228140574244531417223629 20710552715341699281458861)
  ·
    refine ⟨7766457268253137230547073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20710552715341699281458861 7766457268253137230547073)
    ·
      refine ⟨5824842951189852922910305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7766457268253137230547073 5824842951189852922910305)
      ·
        refine ⟨4368632213392389692182729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5824842951189852922910305 4368632213392389692182729)
        ·
          refine ⟨3276474160044292269137047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4368632213392389692182729 3276474160044292269137047)
          ·
            refine ⟨4914711240066438403705571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3276474160044292269137047 4914711240066438403705571)
            ·
              refine ⟨7372066860099657605558357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4914711240066438403705571 7372066860099657605558357)
              ·
                refine ⟨86391408516792862565137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7372066860099657605558357 86391408516792862565137)
                ·
                  rfl

theorem cell22_2271330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 8].length) (baseStart_2271330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271330 prefixEnd_2271330 := by exact prefixLift 2271330
  have htrace : WordTrace (prefixWord ++ tailWord_2271330) baseStart_2271330 baseEnd_2271330 := by
    simpa [prefixWord, tailWord_2271330, baseEnd_2271330] using wordTrace_append hprefix tailTrace_2271330
  have hstable : (prefixWord ++ tailWord_2271330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271330).length < 2 ^ (prefixWord ++ tailWord_2271330).sum := by decide
  have hdescent : baseEnd_2271330 < baseStart_2271330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271371 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 1, 10]
def baseStart_2271371 : Nat := 118140960795 + 2271371 * 2 ^ 59
def prefixEnd_2271371 : Nat := 4983230072969 + 3 ^ 40 * 2271371 * 2
def baseEnd_2271371 : Nat := 777536711789025322811107

theorem tailTrace_2271371 : CollatzResearch.WordTrace tailWord_2271371 prefixEnd_2271371 777536711789025322811107 := by
  unfold tailWord_2271371
  simp only [CollatzResearch.WordTrace]
  refine ⟨82843706254218261128077967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55229137502812174085385311 82843706254218261128077967)
  ·
    refine ⟨124265559381327391692116951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82843706254218261128077967 124265559381327391692116951)
    ·
      refine ⟨186398339071991087538175427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124265559381327391692116951 186398339071991087538175427)
      ·
        refine ⟨279597508607986631307263141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186398339071991087538175427 279597508607986631307263141)
        ·
          refine ⟨52424532863997493370111839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 279597508607986631307263141 52424532863997493370111839)
          ·
            refine ⟨78636799295996240055167759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52424532863997493370111839 78636799295996240055167759)
            ·
              refine ⟨117955198943994360082751639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78636799295996240055167759 117955198943994360082751639)
              ·
                refine ⟨176932798415991540124127459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117955198943994360082751639 176932798415991540124127459)
                ·
                  refine ⟨265399197623987310186191189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176932798415991540124127459 265399197623987310186191189)
                  ·
                    refine ⟨777536711789025322811107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 265399197623987310186191189 777536711789025322811107)
                    ·
                      rfl

theorem cell22_2271371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 10].length) (baseStart_2271371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271371 prefixEnd_2271371 := by exact prefixLift 2271371
  have htrace : WordTrace (prefixWord ++ tailWord_2271371) baseStart_2271371 baseEnd_2271371 := by
    simpa [prefixWord, tailWord_2271371, baseEnd_2271371] using wordTrace_append hprefix tailTrace_2271371
  have hstable : (prefixWord ++ tailWord_2271371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271371).length < 2 ^ (prefixWord ++ tailWord_2271371).sum := by decide
  have hdescent : baseEnd_2271371 < baseStart_2271371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271413 : List Nat := [1, 3, 3, 4, 1, 2, 2, 2, 1, 3]
def baseStart_2271413 : Nat := 118140960795 + 2271413 * 2 ^ 59
def prefixEnd_2271413 : Nat := 4983230072969 + 3 ^ 40 * 2271413 * 2
def baseEnd_2271413 : Nat := 777551089247351213260979

theorem tailTrace_2271413 : CollatzResearch.WordTrace tailWord_2271413 prefixEnd_2271413 777551089247351213260979 := by
  unfold tailWord_2271413
  simp only [CollatzResearch.WordTrace]
  refine ⟨82845238120066102301106893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55230158746710734867404595 82845238120066102301106893)
  ·
    refine ⟨31066964295024788362915085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82845238120066102301106893 31066964295024788362915085)
    ·
      refine ⟨11650111610634295636093157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31066964295024788362915085 11650111610634295636093157)
      ·
        refine ⟨2184395926993930431767467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11650111610634295636093157 2184395926993930431767467)
        ·
          refine ⟨3276593890490895647651201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2184395926993930431767467 3276593890490895647651201)
          ·
            refine ⟨2457445417868171735738401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3276593890490895647651201 2457445417868171735738401)
            ·
              refine ⟨1843084063401128801803801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2457445417868171735738401 1843084063401128801803801)
              ·
                refine ⟨1382313047550846601352851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1843084063401128801803801 1382313047550846601352851)
                ·
                  refine ⟨2073469571326269902029277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382313047550846601352851 2073469571326269902029277)
                  ·
                    refine ⟨777551089247351213260979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2073469571326269902029277 777551089247351213260979)
                    ·
                      rfl

theorem cell22_2271413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_2271413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271413 prefixEnd_2271413 := by exact prefixLift 2271413
  have htrace : WordTrace (prefixWord ++ tailWord_2271413) baseStart_2271413 baseEnd_2271413 := by
    simpa [prefixWord, tailWord_2271413, baseEnd_2271413] using wordTrace_append hprefix tailTrace_2271413
  have hstable : (prefixWord ++ tailWord_2271413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271413).length < 2 ^ (prefixWord ++ tailWord_2271413).sum := by decide
  have hdescent : baseEnd_2271413 < baseStart_2271413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271435 : List Nat := [1, 1, 1, 1, 3, 2, 3, 5, 2, 3]
def baseStart_2271435 : Nat := 118140960795 + 2271435 * 2 ^ 59
def prefixEnd_2271435 : Nat := 4983230072969 + 3 ^ 40 * 2271435 * 2
def baseEnd_2271435 : Nat := 777558620296950489210911

theorem tailTrace_2271435 : CollatzResearch.WordTrace tailWord_2271435 prefixEnd_2271435 777558620296950489210911 := by
  unfold tailWord_2271435
  simp only [CollatzResearch.WordTrace]
  refine ⟨82846040525986400058407759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55230693683990933372271839 82846040525986400058407759)
  ·
    refine ⟨124269060788979600087611639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82846040525986400058407759 124269060788979600087611639)
    ·
      refine ⟨186403591183469400131417459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124269060788979600087611639 186403591183469400131417459)
      ·
        refine ⟨279605386775204100197126189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186403591183469400131417459 279605386775204100197126189)
        ·
          refine ⟨104852020040701537573922321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 279605386775204100197126189 104852020040701537573922321)
          ·
            refine ⟨78639015030526153180441741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104852020040701537573922321 78639015030526153180441741)
            ·
              refine ⟨29489630636447307442665653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78639015030526153180441741 29489630636447307442665653)
              ·
                refine ⟨2764652872166935072749905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29489630636447307442665653 2764652872166935072749905)
                ·
                  refine ⟨2073489654125201304562429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2764652872166935072749905 2073489654125201304562429)
                  ·
                    refine ⟨777558620296950489210911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2073489654125201304562429 777558620296950489210911)
                    ·
                      rfl

theorem cell22_2271435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 3].length) (baseStart_2271435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271435 prefixEnd_2271435 := by exact prefixLift 2271435
  have htrace : WordTrace (prefixWord ++ tailWord_2271435) baseStart_2271435 baseEnd_2271435 := by
    simpa [prefixWord, tailWord_2271435, baseEnd_2271435] using wordTrace_append hprefix tailTrace_2271435
  have hstable : (prefixWord ++ tailWord_2271435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271435).length < 2 ^ (prefixWord ++ tailWord_2271435).sum := by decide
  have hdescent : baseEnd_2271435 < baseStart_2271435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271450 : List Nat := [3, 1, 1, 2, 2, 1, 5, 1, 2, 4]
def baseStart_2271450 : Nat := 118140960795 + 2271450 * 2 ^ 59
def prefixEnd_2271450 : Nat := 4983230072969 + 3 ^ 40 * 2271450 * 2
def baseEnd_2271450 : Nat := 777563755103495450085865

theorem tailTrace_2271450 : CollatzResearch.WordTrace tailWord_2271450 prefixEnd_2271450 777563755103495450085865 := by
  unfold tailWord_2271450
  simp only [CollatzResearch.WordTrace]
  refine ⟨20711646905233014405050951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55231058413954705080135869 20711646905233014405050951)
  ·
    refine ⟨31067470357849521607576427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20711646905233014405050951 31067470357849521607576427)
    ·
      refine ⟨46601205536774282411364641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31067470357849521607576427 46601205536774282411364641)
      ·
        refine ⟨34950904152580711808523481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46601205536774282411364641 34950904152580711808523481)
        ·
          refine ⟨26213178114435533856392611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34950904152580711808523481 26213178114435533856392611)
          ·
            refine ⟨39319767171653300784588917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26213178114435533856392611 39319767171653300784588917)
            ·
              refine ⟨3686228172342496948555211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39319767171653300784588917 3686228172342496948555211)
              ·
                refine ⟨5529342258513745422832817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3686228172342496948555211 5529342258513745422832817)
                ·
                  refine ⟨4147006693885309067124613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5529342258513745422832817 4147006693885309067124613)
                  ·
                    refine ⟨777563755103495450085865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4147006693885309067124613 777563755103495450085865)
                    ·
                      rfl

theorem cell22_2271450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_2271450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271450 prefixEnd_2271450 := by exact prefixLift 2271450
  have htrace : WordTrace (prefixWord ++ tailWord_2271450) baseStart_2271450 baseEnd_2271450 := by
    simpa [prefixWord, tailWord_2271450, baseEnd_2271450] using wordTrace_append hprefix tailTrace_2271450
  have hstable : (prefixWord ++ tailWord_2271450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271450).length < 2 ^ (prefixWord ++ tailWord_2271450).sum := by decide
  have hdescent : baseEnd_2271450 < baseStart_2271450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271570 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_2271570 : Nat := 118140960795 + 2271570 * 2 ^ 59
def prefixEnd_2271570 : Nat := 4983230072969 + 3 ^ 40 * 2271570 * 2
def baseEnd_2271570 : Nat := 777604833555855137085497

theorem tailTrace_2271570 : CollatzResearch.WordTrace tailWord_2271570 prefixEnd_2271570 777604833555855137085497 := by
  unfold tailWord_2271570
  simp only [CollatzResearch.WordTrace]
  refine ⟨20712741095124329528643041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55233976253664878743048109 20712741095124329528643041)
  ·
    refine ⟨15534555821343247146482281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20712741095124329528643041 15534555821343247146482281)
    ·
      refine ⟨11650916866007435359861711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15534555821343247146482281 11650916866007435359861711)
      ·
        refine ⟨17476375299011153039792567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11650916866007435359861711 17476375299011153039792567)
        ·
          refine ⟨26214562948516729559688851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17476375299011153039792567 26214562948516729559688851)
          ·
            refine ⟨39321844422775094339533277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26214562948516729559688851 39321844422775094339533277)
            ·
              refine ⟨14745691658540660377324979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39321844422775094339533277 14745691658540660377324979)
              ·
                refine ⟨22118537487810990565987469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14745691658540660377324979 22118537487810990565987469)
                ·
                  refine ⟨8294451557929121462245301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22118537487810990565987469 8294451557929121462245301)
                  ·
                    refine ⟨777604833555855137085497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8294451557929121462245301 777604833555855137085497)
                    ·
                      rfl

theorem cell22_2271570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_2271570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271570 prefixEnd_2271570 := by exact prefixLift 2271570
  have htrace : WordTrace (prefixWord ++ tailWord_2271570) baseStart_2271570 baseEnd_2271570 := by
    simpa [prefixWord, tailWord_2271570, baseEnd_2271570] using wordTrace_append hprefix tailTrace_2271570
  have hstable : (prefixWord ++ tailWord_2271570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271570).length < 2 ^ (prefixWord ++ tailWord_2271570).sum := by decide
  have hdescent : baseEnd_2271570 < baseStart_2271570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271582 : List Nat := [4, 4, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_2271582 : Nat := 118140960795 + 2271582 * 2 ^ 59
def prefixEnd_2271582 : Nat := 4983230072969 + 3 ^ 40 * 2271582 * 2
def baseEnd_2271582 : Nat := 777608941401091105785461

theorem tailTrace_2271582 : CollatzResearch.WordTrace tailWord_2271582 prefixEnd_2271582 777608941401091105785461 := by
  unfold tailWord_2271582
  simp only [CollatzResearch.WordTrace]
  refine ⟨10356425257056730520501125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55234268037635896109339333 10356425257056730520501125)
  ·
    refine ⟨1941829735698136972593961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10356425257056730520501125 1941829735698136972593961)
    ·
      refine ⟨1456372301773602729445471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1941829735698136972593961 1456372301773602729445471)
      ·
        refine ⟨2184558452660404094168207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1456372301773602729445471 2184558452660404094168207)
        ·
          refine ⟨3276837678990606141252311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2184558452660404094168207 3276837678990606141252311)
          ·
            refine ⟨4915256518485909211878467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3276837678990606141252311 4915256518485909211878467)
            ·
              refine ⟨7372884777728863817817701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4915256518485909211878467 7372884777728863817817701)
              ·
                refine ⟨1382415895824161965840819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7372884777728863817817701 1382415895824161965840819)
                ·
                  refine ⟨2073623843736242948761229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382415895824161965840819 2073623843736242948761229)
                  ·
                    refine ⟨777608941401091105785461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2073623843736242948761229 777608941401091105785461)
                    ·
                      rfl

theorem cell22_2271582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_2271582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271582 prefixEnd_2271582 := by exact prefixLift 2271582
  have htrace : WordTrace (prefixWord ++ tailWord_2271582) baseStart_2271582 baseEnd_2271582 := by
    simpa [prefixWord, tailWord_2271582, baseEnd_2271582] using wordTrace_append hprefix tailTrace_2271582
  have hstable : (prefixWord ++ tailWord_2271582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271582).length < 2 ^ (prefixWord ++ tailWord_2271582).sum := by decide
  have hdescent : baseEnd_2271582 < baseStart_2271582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271589 : List Nat := [1, 3, 1, 3, 1, 3, 4, 2, 4]
def baseStart_2271589 : Nat := 118140960795 + 2271589 * 2 ^ 59
def prefixEnd_2271589 : Nat := 4983230072969 + 3 ^ 40 * 2271589 * 2
def baseEnd_2271589 : Nat := 259203779214715140286813

theorem tailTrace_2271589 : CollatzResearch.WordTrace tailWord_2271589 prefixEnd_2271589 259203779214715140286813 := by
  unfold tailWord_2271589
  simp only [CollatzResearch.WordTrace]
  refine ⟨82851657367428484359513821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55234438244952322906342547 82851657367428484359513821)
  ·
    refine ⟨31069371512785681634817683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82851657367428484359513821 31069371512785681634817683)
    ·
      refine ⟨46604057269178522452226525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31069371512785681634817683 46604057269178522452226525)
      ·
        refine ⟨17476521475941945919584947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46604057269178522452226525 17476521475941945919584947)
        ·
          refine ⟨26214782213912918879377421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17476521475941945919584947 26214782213912918879377421)
          ·
            refine ⟨9830543330217344579766533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26214782213912918879377421 9830543330217344579766533)
            ·
              refine ⟨1843226874415752108706225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9830543330217344579766533 1843226874415752108706225)
              ·
                refine ⟨1382420155811814081529669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1843226874415752108706225 1382420155811814081529669)
                ·
                  refine ⟨259203779214715140286813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1382420155811814081529669 259203779214715140286813)
                  ·
                    rfl

theorem cell22_2271589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_2271589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271589 prefixEnd_2271589 := by exact prefixLift 2271589
  have htrace : WordTrace (prefixWord ++ tailWord_2271589) baseStart_2271589 baseEnd_2271589 := by
    simpa [prefixWord, tailWord_2271589, baseEnd_2271589] using wordTrace_append hprefix tailTrace_2271589
  have hstable : (prefixWord ++ tailWord_2271589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271589).length < 2 ^ (prefixWord ++ tailWord_2271589).sum := by decide
  have hdescent : baseEnd_2271589 < baseStart_2271589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271600 : List Nat := [2, 1, 1, 1, 4, 3, 3, 7]
def baseStart_2271600 : Nat := 118140960795 + 2271600 * 2 ^ 59
def prefixEnd_2271600 : Nat := 4983230072969 + 3 ^ 40 * 2271600 * 2
def baseEnd_2271600 : Nat := 86401678129882784315045

theorem tailTrace_2271600 : CollatzResearch.WordTrace tailWord_2271600 prefixEnd_2271600 86401678129882784315045 := by
  unfold tailWord_2271600
  simp only [CollatzResearch.WordTrace]
  refine ⟨41426029285194316619082127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55234705713592422158776169 41426029285194316619082127)
  ·
    refine ⟨62139043927791474928623191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41426029285194316619082127 62139043927791474928623191)
    ·
      refine ⟨93208565891687212392934787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62139043927791474928623191 93208565891687212392934787)
      ·
        refine ⟨139812848837530818589402181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93208565891687212392934787 139812848837530818589402181)
        ·
          refine ⟨26214909157037028485512909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139812848837530818589402181 26214909157037028485512909)
          ·
            refine ⟨9830590933888885682067341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26214909157037028485512909 9830590933888885682067341)
            ·
              refine ⟨3686471600208332130775253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9830590933888885682067341 3686471600208332130775253)
              ·
                refine ⟨86401678129882784315045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3686471600208332130775253 86401678129882784315045)
                ·
                  rfl

theorem cell22_2271600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 7].length) (baseStart_2271600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271600 prefixEnd_2271600 := by exact prefixLift 2271600
  have htrace : WordTrace (prefixWord ++ tailWord_2271600) baseStart_2271600 baseEnd_2271600 := by
    simpa [prefixWord, tailWord_2271600, baseEnd_2271600] using wordTrace_append hprefix tailTrace_2271600
  have hstable : (prefixWord ++ tailWord_2271600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271600).length < 2 ^ (prefixWord ++ tailWord_2271600).sum := by decide
  have hdescent : baseEnd_2271600 < baseStart_2271600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271619 : List Nat := [1, 1, 1, 3, 6, 2, 1, 1, 2, 4]
def baseStart_2271619 : Nat := 118140960795 + 2271619 * 2 ^ 59
def prefixEnd_2271619 : Nat := 4983230072969 + 3 ^ 40 * 2271619 * 2
def baseEnd_2271619 : Nat := 777621607257235342610347

theorem tailTrace_2271619 : CollatzResearch.WordTrace tailWord_2271619 prefixEnd_2271619 777621607257235342610347 := by
  unfold tailWord_2271619
  simp only [CollatzResearch.WordTrace]
  refine ⟨82852751557319799483105911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55235167704879866322070607 82852751557319799483105911)
  ·
    refine ⟨124279127335979699224658867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82852751557319799483105911 124279127335979699224658867)
    ·
      refine ⟨186418691003969548836988301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124279127335979699224658867 186418691003969548836988301)
      ·
        refine ⟨69907009126488580813870613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186418691003969548836988301 69907009126488580813870613)
        ·
          refine ⟨3276891052804152225650185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69907009126488580813870613 3276891052804152225650185)
          ·
            refine ⟨2457668289603114169237639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3276891052804152225650185 2457668289603114169237639)
            ·
              refine ⟨3686502434404671253856459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2457668289603114169237639 3686502434404671253856459)
              ·
                refine ⟨5529753651607006880784689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3686502434404671253856459 5529753651607006880784689)
                ·
                  refine ⟨4147315238705255160588517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5529753651607006880784689 4147315238705255160588517)
                  ·
                    refine ⟨777621607257235342610347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4147315238705255160588517 777621607257235342610347)
                    ·
                      rfl

theorem cell22_2271619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 4].length) (baseStart_2271619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271619 prefixEnd_2271619 := by exact prefixLift 2271619
  have htrace : WordTrace (prefixWord ++ tailWord_2271619) baseStart_2271619 baseEnd_2271619 := by
    simpa [prefixWord, tailWord_2271619, baseEnd_2271619] using wordTrace_append hprefix tailTrace_2271619
  have hstable : (prefixWord ++ tailWord_2271619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271619).length < 2 ^ (prefixWord ++ tailWord_2271619).sum := by decide
  have hdescent : baseEnd_2271619 < baseStart_2271619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271668 : List Nat := [2, 5, 2, 2, 1, 2, 2, 6]
def baseStart_2271668 : Nat := 118140960795 + 2271668 * 2 ^ 59
def prefixEnd_2271668 : Nat := 4983230072969 + 3 ^ 40 * 2271668 * 2
def baseEnd_2271668 : Nat := 86404264550957283126133

theorem tailTrace_2271668 : CollatzResearch.WordTrace tailWord_2271668 prefixEnd_2271668 86404264550957283126133 := by
  unfold tailWord_2271668
  simp only [CollatzResearch.WordTrace]
  refine ⟨41427269367071140425819829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55236359156094853901093105 41427269367071140425819829)
  ·
    refine ⟨3883806503162919414920609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41427269367071140425819829 3883806503162919414920609)
    ·
      refine ⟨2912854877372189561190457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3883806503162919414920609 2912854877372189561190457)
      ·
        refine ⟨2184641158029142170892843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2912854877372189561190457 2184641158029142170892843)
        ·
          refine ⟨3276961737043713256339265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2184641158029142170892843 3276961737043713256339265)
          ·
            refine ⟨2457721302782784942254449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3276961737043713256339265 2457721302782784942254449)
            ·
              refine ⟨1843290977087088706690837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2457721302782784942254449 1843290977087088706690837)
              ·
                refine ⟨86404264550957283126133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1843290977087088706690837 86404264550957283126133)
                ·
                  rfl

theorem cell22_2271668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 6].length) (baseStart_2271668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271668 prefixEnd_2271668 := by exact prefixLift 2271668
  have htrace : WordTrace (prefixWord ++ tailWord_2271668) baseStart_2271668 baseEnd_2271668 := by
    simpa [prefixWord, tailWord_2271668, baseEnd_2271668] using wordTrace_append hprefix tailTrace_2271668
  have hstable : (prefixWord ++ tailWord_2271668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271668).length < 2 ^ (prefixWord ++ tailWord_2271668).sum := by decide
  have hdescent : baseEnd_2271668 < baseStart_2271668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271726 : List Nat := [4, 1, 2, 1, 2, 4, 1, 2, 1, 4]
def baseStart_2271726 : Nat := 118140960795 + 2271726 * 2 ^ 59
def prefixEnd_2271726 : Nat := 4983230072969 + 3 ^ 40 * 2271726 * 2
def baseEnd_2271726 : Nat := 777658235543922730185019

theorem tailTrace_2271726 : CollatzResearch.WordTrace tailWord_2271726 prefixEnd_2271726 777658235543922730185019 := by
  unfold tailWord_2271726
  simp only [CollatzResearch.WordTrace]
  refine ⟨10357081770991519594656379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55237769445288104504834021 10357081770991519594656379)
  ·
    refine ⟨15535622656487279391984569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10357081770991519594656379 15535622656487279391984569)
    ·
      refine ⟨11651716992365459543988427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15535622656487279391984569 11651716992365459543988427)
      ·
        refine ⟨17477575488548189315982641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11651716992365459543988427 17477575488548189315982641)
        ·
          refine ⟨13108181616411141986986981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17477575488548189315982641 13108181616411141986986981)
          ·
            refine ⟨2457784053077089122560059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13108181616411141986986981 2457784053077089122560059)
            ·
              refine ⟨3686676079615633683840089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2457784053077089122560059 3686676079615633683840089)
              ·
                refine ⟨2765007059711725262880067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3686676079615633683840089 2765007059711725262880067)
                ·
                  refine ⟨4147510589567587894320101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2765007059711725262880067 4147510589567587894320101)
                  ·
                    refine ⟨777658235543922730185019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4147510589567587894320101 777658235543922730185019)
                    ·
                      rfl

theorem cell22_2271726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_2271726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271726 prefixEnd_2271726 := by exact prefixLift 2271726
  have htrace : WordTrace (prefixWord ++ tailWord_2271726) baseStart_2271726 baseEnd_2271726 := by
    simpa [prefixWord, tailWord_2271726, baseEnd_2271726] using wordTrace_append hprefix tailTrace_2271726
  have hstable : (prefixWord ++ tailWord_2271726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271726).length < 2 ^ (prefixWord ++ tailWord_2271726).sum := by decide
  have hdescent : baseEnd_2271726 < baseStart_2271726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271737 : List Nat := [1, 2, 1, 3, 1, 2, 3, 3, 2, 4]
def baseStart_2271737 : Nat := 118140960795 + 2271737 * 2 ^ 59
def prefixEnd_2271737 : Nat := 4983230072969 + 3 ^ 40 * 2271737 * 2
def baseEnd_2271737 : Nat := 777662001068722368159985

theorem tailTrace_2271737 : CollatzResearch.WordTrace tailWord_2271737 prefixEnd_2271737 777662001068722368159985 := by
  unfold tailWord_2271737
  simp only [CollatzResearch.WordTrace]
  refine ⟨82857055370892305635901465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55238036913928203757267643 82857055370892305635901465)
  ·
    refine ⟨62142791528169229226926099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82857055370892305635901465 62142791528169229226926099)
    ·
      refine ⟨93214187292253843840389149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62142791528169229226926099 93214187292253843840389149)
      ·
        refine ⟨34955320234595191440145931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93214187292253843840389149 34955320234595191440145931)
        ·
          refine ⟨52432980351892787160218897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34955320234595191440145931 52432980351892787160218897)
          ·
            refine ⟨39324735263919590370164173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52432980351892787160218897 39324735263919590370164173)
            ·
              refine ⟨14746775723969846388811565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39324735263919590370164173 14746775723969846388811565)
              ·
                refine ⟨5530040896488692395804337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14746775723969846388811565 5530040896488692395804337)
                ·
                  refine ⟨4147530672366519296853253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5530040896488692395804337 4147530672366519296853253)
                  ·
                    refine ⟨777662001068722368159985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4147530672366519296853253 777662001068722368159985)
                    ·
                      rfl

theorem cell22_2271737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_2271737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271737 prefixEnd_2271737 := by exact prefixLift 2271737
  have htrace : WordTrace (prefixWord ++ tailWord_2271737) baseStart_2271737 baseEnd_2271737 := by
    simpa [prefixWord, tailWord_2271737, baseEnd_2271737] using wordTrace_append hprefix tailTrace_2271737
  have hstable : (prefixWord ++ tailWord_2271737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271737).length < 2 ^ (prefixWord ++ tailWord_2271737).sum := by decide
  have hdescent : baseEnd_2271737 < baseStart_2271737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271756 : List Nat := [2, 2, 1, 2, 4, 2, 2, 2, 2, 3]
def baseStart_2271756 : Nat := 118140960795 + 2271756 * 2 ^ 59
def prefixEnd_2271756 : Nat := 4983230072969 + 3 ^ 40 * 2271756 * 2
def baseEnd_2271756 : Nat := 777668505157012651934927

theorem tailTrace_2271756 : CollatzResearch.WordTrace tailWord_2271756 prefixEnd_2271756 777668505157012651934927 := by
  unfold tailWord_2271756
  simp only [CollatzResearch.WordTrace]
  refine ⟨41428874178911735940421561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55238498905215647920562081 41428874178911735940421561)
  ·
    refine ⟨31071655634183801955316171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41428874178911735940421561 31071655634183801955316171)
    ·
      refine ⟨46607483451275702932974257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31071655634183801955316171 46607483451275702932974257)
      ·
        refine ⟨34955612588456777199730693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46607483451275702932974257 34955612588456777199730693)
        ·
          refine ⟨6554177360335645724949505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34955612588456777199730693 6554177360335645724949505)
          ·
            refine ⟨4915633020251734293712129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6554177360335645724949505 4915633020251734293712129)
            ·
              refine ⟨3686724765188800720284097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4915633020251734293712129 3686724765188800720284097)
              ·
                refine ⟨2765043573891600540213073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3686724765188800720284097 2765043573891600540213073)
                ·
                  refine ⟨2073782680418700405159805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2765043573891600540213073 2073782680418700405159805)
                  ·
                    refine ⟨777668505157012651934927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2073782680418700405159805 777668505157012651934927)
                    ·
                      rfl

theorem cell22_2271756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_2271756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271756 prefixEnd_2271756 := by exact prefixLift 2271756
  have htrace : WordTrace (prefixWord ++ tailWord_2271756) baseStart_2271756 baseEnd_2271756 := by
    simpa [prefixWord, tailWord_2271756, baseEnd_2271756] using wordTrace_append hprefix tailTrace_2271756
  have hstable : (prefixWord ++ tailWord_2271756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271756).length < 2 ^ (prefixWord ++ tailWord_2271756).sum := by decide
  have hdescent : baseEnd_2271756 < baseStart_2271756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271758 : List Nat := [4, 1, 1, 2, 3, 3, 2, 2, 4]
def baseStart_2271758 : Nat := 118140960795 + 2271758 * 2 ^ 59
def prefixEnd_2271758 : Nat := 4983230072969 + 3 ^ 40 * 2271758 * 2
def baseEnd_2271758 : Nat := 259223063265961771128307

theorem tailTrace_2271758 : CollatzResearch.WordTrace tailWord_2271758 prefixEnd_2271758 259223063265961771128307 := by
  unfold tailWord_2271758
  simp only [CollatzResearch.WordTrace]
  refine ⟨10357227662977028277801991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55238547535877484148277285 10357227662977028277801991)
  ·
    refine ⟨15535841494465542416702987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10357227662977028277801991 15535841494465542416702987)
    ·
      refine ⟨23303762241698313625054481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15535841494465542416702987 23303762241698313625054481)
      ·
        refine ⟨17477821681273735218790861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23303762241698313625054481 17477821681273735218790861)
        ·
          refine ⟨6554183130477650707046573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17477821681273735218790861 6554183130477650707046573)
          ·
            refine ⟨2457818673929119015142465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6554183130477650707046573 2457818673929119015142465)
            ·
              refine ⟨1843364005446839261356849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2457818673929119015142465 1843364005446839261356849)
              ·
                refine ⟨1382523004085129446017637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1843364005446839261356849 1382523004085129446017637)
                ·
                  refine ⟨259223063265961771128307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1382523004085129446017637 259223063265961771128307)
                  ·
                    rfl

theorem cell22_2271758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_2271758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271758 prefixEnd_2271758 := by exact prefixLift 2271758
  have htrace : WordTrace (prefixWord ++ tailWord_2271758) baseStart_2271758 baseEnd_2271758 := by
    simpa [prefixWord, tailWord_2271758, baseEnd_2271758] using wordTrace_append hprefix tailTrace_2271758
  have hstable : (prefixWord ++ tailWord_2271758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271758).length < 2 ^ (prefixWord ++ tailWord_2271758).sum := by decide
  have hdescent : baseEnd_2271758 < baseStart_2271758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271797 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 7]
def baseStart_2271797 : Nat := 118140960795 + 2271797 * 2 ^ 59
def prefixEnd_2271797 : Nat := 4983230072969 + 3 ^ 40 * 2271797 * 2
def baseEnd_2271797 : Nat := 259227513431634070553267

theorem tailTrace_2271797 : CollatzResearch.WordTrace tailWord_2271797 prefixEnd_2271797 259227513431634070553267 := by
  unfold tailWord_2271797
  simp only [CollatzResearch.WordTrace]
  refine ⟨82859243750674935883085645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55239495833783290588723763 82859243750674935883085645)
  ·
    refine ⟨31072216406503100956157117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82859243750674935883085645 31072216406503100956157117)
    ·
      refine ⟨11652081152438662858558919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31072216406503100956157117 11652081152438662858558919)
      ·
        refine ⟨17478121728657994287838379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11652081152438662858558919 17478121728657994287838379)
        ·
          refine ⟨26217182592986991431757569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17478121728657994287838379 26217182592986991431757569)
          ·
            refine ⟨19662886944740243573818177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26217182592986991431757569 19662886944740243573818177)
            ·
              refine ⟨14747165208555182680363633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19662886944740243573818177 14747165208555182680363633)
              ·
                refine ⟨11060373906416387010272725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14747165208555182680363633 11060373906416387010272725)
                ·
                  refine ⟨259227513431634070553267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11060373906416387010272725 259227513431634070553267)
                  ·
                    rfl

theorem cell22_2271797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_2271797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271797 prefixEnd_2271797 := by exact prefixLift 2271797
  have htrace : WordTrace (prefixWord ++ tailWord_2271797) baseStart_2271797 baseEnd_2271797 := by
    simpa [prefixWord, tailWord_2271797, baseEnd_2271797] using wordTrace_append hprefix tailTrace_2271797
  have hstable : (prefixWord ++ tailWord_2271797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271797).length < 2 ^ (prefixWord ++ tailWord_2271797).sum := by decide
  have hdescent : baseEnd_2271797 < baseStart_2271797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271859 : List Nat := [1, 1, 1, 2, 2, 1, 1, 9, 4]
def baseStart_2271859 : Nat := 118140960795 + 2271859 * 2 ^ 59
def prefixEnd_2271859 : Nat := 4983230072969 + 3 ^ 40 * 2271859 * 2
def baseEnd_2271859 : Nat := 259234588053984905536537

theorem tailTrace_2271859 : CollatzResearch.WordTrace tailWord_2271859 prefixEnd_2271859 259234588053984905536537 := by
  unfold tailWord_2271859
  simp only [CollatzResearch.WordTrace]
  refine ⟨82861505076450320471842631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55241003384300213647895087 82861505076450320471842631)
  ·
    refine ⟨124292257614675480707763947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82861505076450320471842631 124292257614675480707763947)
    ·
      refine ⟨186438386422013221061645921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124292257614675480707763947 186438386422013221061645921)
      ·
        refine ⟨139828789816509915796234441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186438386422013221061645921 139828789816509915796234441)
        ·
          refine ⟨104871592362382436847175831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139828789816509915796234441 104871592362382436847175831)
          ·
            refine ⟨157307388543573655270763747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104871592362382436847175831 157307388543573655270763747)
            ·
              refine ⟨235961082815360482906145621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157307388543573655270763747 235961082815360482906145621)
              ·
                refine ⟨1382584469621252829528197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 235961082815360482906145621 1382584469621252829528197)
                ·
                  refine ⟨259234588053984905536537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1382584469621252829528197 259234588053984905536537)
                  ·
                    rfl

theorem cell22_2271859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 4].length) (baseStart_2271859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271859 prefixEnd_2271859 := by exact prefixLift 2271859
  have htrace : WordTrace (prefixWord ++ tailWord_2271859) baseStart_2271859 baseEnd_2271859 := by
    simpa [prefixWord, tailWord_2271859, baseEnd_2271859] using wordTrace_append hprefix tailTrace_2271859
  have hstable : (prefixWord ++ tailWord_2271859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271859).length < 2 ^ (prefixWord ++ tailWord_2271859).sum := by decide
  have hdescent : baseEnd_2271859 < baseStart_2271859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271876 : List Nat := [2, 3, 2, 1, 3, 3, 1, 1, 6]
def baseStart_2271876 : Nat := 118140960795 + 2271876 * 2 ^ 59
def prefixEnd_2271876 : Nat := 4983230072969 + 3 ^ 40 * 2271876 * 2
def baseEnd_2271876 : Nat := 259236527869790779644853

theorem tailTrace_2271876 : CollatzResearch.WordTrace tailWord_2271876 prefixEnd_2271876 259236527869790779644853 := by
  unfold tailWord_2271876
  simp only [CollatzResearch.WordTrace]
  refine ⟨41431062558694366187605741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55241416744925821583474321 41431062558694366187605741)
  ·
    refine ⟨15536648459510387320352153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41431062558694366187605741 15536648459510387320352153)
    ·
      refine ⟨11652486344632790490264115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15536648459510387320352153 11652486344632790490264115)
      ·
        refine ⟨17478729516949185735396173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11652486344632790490264115 17478729516949185735396173)
        ·
          refine ⟨6554523568855944650773565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17478729516949185735396173 6554523568855944650773565)
          ·
            refine ⟨2457946338320979244040087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6554523568855944650773565 2457946338320979244040087)
            ·
              refine ⟨3686919507481468866060131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2457946338320979244040087 3686919507481468866060131)
              ·
                refine ⟨5530379261222203299090197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3686919507481468866060131 5530379261222203299090197)
                ·
                  refine ⟨259236527869790779644853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5530379261222203299090197 259236527869790779644853)
                  ·
                    rfl

theorem cell22_2271876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_2271876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271876 prefixEnd_2271876 := by exact prefixLift 2271876
  have htrace : WordTrace (prefixWord ++ tailWord_2271876) baseStart_2271876 baseEnd_2271876 := by
    simpa [prefixWord, tailWord_2271876, baseEnd_2271876] using wordTrace_append hprefix tailTrace_2271876
  have hstable : (prefixWord ++ tailWord_2271876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271876).length < 2 ^ (prefixWord ++ tailWord_2271876).sum := by decide
  have hdescent : baseEnd_2271876 < baseStart_2271876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271921 : List Nat := [1, 2, 2, 6, 2, 9]
def baseStart_2271921 : Nat := 118140960795 + 2271921 * 2 ^ 59
def prefixEnd_2271921 : Nat := 4983230072969 + 3 ^ 40 * 2271921 * 2
def baseEnd_2271921 : Nat := 9601543062086508908141

theorem tailTrace_2271921 : CollatzResearch.WordTrace tailWord_2271921 prefixEnd_2271921 9601543062086508908141 := by
  unfold tailWord_2271921
  simp only [CollatzResearch.WordTrace]
  refine ⟨82863766402225705060599617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55242510934817136707066411 82863766402225705060599617)
  ·
    refine ⟨62147824801669278795449713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82863766402225705060599617 62147824801669278795449713)
    ·
      refine ⟨46610868601251959096587285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62147824801669278795449713 46610868601251959096587285)
      ·
        refine ⟨2184884465683685582652529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46610868601251959096587285 2184884465683685582652529)
        ·
          refine ⟨1638663349262764186989397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2184884465683685582652529 1638663349262764186989397)
          ·
            refine ⟨9601543062086508908141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1638663349262764186989397 9601543062086508908141)
            ·
              rfl

theorem cell22_2271921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 9].length) (baseStart_2271921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271921 prefixEnd_2271921 := by exact prefixLift 2271921
  have htrace : WordTrace (prefixWord ++ tailWord_2271921) baseStart_2271921 baseEnd_2271921 := by
    simpa [prefixWord, tailWord_2271921, baseEnd_2271921] using wordTrace_append hprefix tailTrace_2271921
  have hstable : (prefixWord ++ tailWord_2271921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271921).length < 2 ^ (prefixWord ++ tailWord_2271921).sum := by decide
  have hdescent : baseEnd_2271921 < baseStart_2271921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271934 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_2271934 : Nat := 118140960795 + 2271934 * 2 ^ 59
def prefixEnd_2271934 : Nat := 4983230072969 + 3 ^ 40 * 2271934 * 2
def baseEnd_2271934 : Nat := 777729438194679520984381

theorem tailTrace_2271934 : CollatzResearch.WordTrace tailWord_2271934 prefixEnd_2271934 777729438194679520984381 := by
  unfold tailWord_2271934
  simp only [CollatzResearch.WordTrace]
  refine ⟨10358030068897326035102857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55242827034119072187215237 10358030068897326035102857)
  ·
    refine ⟨7768522551672994526327143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10358030068897326035102857 7768522551672994526327143)
    ·
      refine ⟨11652783827509491789490715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7768522551672994526327143 11652783827509491789490715)
      ·
        refine ⟨17479175741264237684236073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11652783827509491789490715 17479175741264237684236073)
        ·
          refine ⟨13109381805948178263177055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17479175741264237684236073 13109381805948178263177055)
          ·
            refine ⟨19664072708922267394765583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13109381805948178263177055 19664072708922267394765583)
            ·
              refine ⟨29496109063383401092148375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19664072708922267394765583 29496109063383401092148375)
              ·
                refine ⟨44244163595075101638222563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29496109063383401092148375 44244163595075101638222563)
                ·
                  refine ⟨66366245392612652457333845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44244163595075101638222563 66366245392612652457333845)
                  ·
                    refine ⟨777729438194679520984381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66366245392612652457333845 777729438194679520984381)
                    ·
                      rfl

theorem cell22_2271934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_2271934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271934 prefixEnd_2271934 := by exact prefixLift 2271934
  have htrace : WordTrace (prefixWord ++ tailWord_2271934) baseStart_2271934 baseEnd_2271934 := by
    simpa [prefixWord, tailWord_2271934, baseEnd_2271934] using wordTrace_append hprefix tailTrace_2271934
  have hstable : (prefixWord ++ tailWord_2271934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271934).length < 2 ^ (prefixWord ++ tailWord_2271934).sum := by decide
  have hdescent : baseEnd_2271934 < baseStart_2271934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2271994 : List Nat := [3, 1, 1, 1, 1, 3, 3, 3, 6]
def baseStart_2271994 : Nat := 118140960795 + 2271994 * 2 ^ 59
def prefixEnd_2271994 : Nat := 4983230072969 + 3 ^ 40 * 2271994 * 2
def baseEnd_2271994 : Nat := 259249992473619788161399

theorem tailTrace_2271994 : CollatzResearch.WordTrace tailWord_2271994 prefixEnd_2271994 259249992473619788161399 := by
  unfold tailWord_2271994
  simp only [CollatzResearch.WordTrace]
  refine ⟨20716607232740309632001759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55244285953974159018671357 20716607232740309632001759)
  ·
    refine ⟨31074910849110464448002639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20716607232740309632001759 31074910849110464448002639)
    ·
      refine ⟨46612366273665696672003959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31074910849110464448002639 46612366273665696672003959)
      ·
        refine ⟨69918549410498545008005939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46612366273665696672003959 69918549410498545008005939)
        ·
          refine ⟨104877824115747817512008909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69918549410498545008005939 104877824115747817512008909)
          ·
            refine ⟨39329184043405431567003341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104877824115747817512008909 39329184043405431567003341)
            ·
              refine ⟨14748444016277036837626253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39329184043405431567003341 14748444016277036837626253)
              ·
                refine ⟨5530666506103888814109845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14748444016277036837626253 5530666506103888814109845)
                ·
                  refine ⟨259249992473619788161399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5530666506103888814109845 259249992473619788161399)
                  ·
                    rfl

theorem cell22_2271994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_2271994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2271994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2271994 prefixEnd_2271994 := by exact prefixLift 2271994
  have htrace : WordTrace (prefixWord ++ tailWord_2271994) baseStart_2271994 baseEnd_2271994 := by
    simpa [prefixWord, tailWord_2271994, baseEnd_2271994] using wordTrace_append hprefix tailTrace_2271994
  have hstable : (prefixWord ++ tailWord_2271994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2271994).length < 2 ^ (prefixWord ++ tailWord_2271994).sum := by decide
  have hdescent : baseEnd_2271994 < baseStart_2271994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2271994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272026 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 6, 3]
def baseStart_2272026 : Nat := 118140960795 + 2272026 * 2 ^ 59
def prefixEnd_2272026 : Nat := 4983230072969 + 3 ^ 40 * 2272026 * 2
def baseEnd_2272026 : Nat := 777760931674821947684099

theorem tailTrace_2272026 : CollatzResearch.WordTrace tailWord_2272026 prefixEnd_2272026 777760931674821947684099 := by
  unfold tailWord_2272026
  simp only [CollatzResearch.WordTrace]
  refine ⟨20716899016711326998292983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55245064044563538662114621 20716899016711326998292983)
  ·
    refine ⟨31075348525066990497439475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20716899016711326998292983 31075348525066990497439475)
    ·
      refine ⟨46613022787600485746159213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31075348525066990497439475 46613022787600485746159213)
      ·
        refine ⟨17479883545350182154809705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46613022787600485746159213 17479883545350182154809705)
        ·
          refine ⟨13109912659012636616107279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17479883545350182154809705 13109912659012636616107279)
          ·
            refine ⟨19664868988518954924160919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13109912659012636616107279 19664868988518954924160919)
            ·
              refine ⟨29497303482778432386241379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19664868988518954924160919 29497303482778432386241379)
              ·
                refine ⟨44245955224167648579362069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29497303482778432386241379 44245955224167648579362069)
                ·
                  refine ⟨2074029151132858527157597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44245955224167648579362069 2074029151132858527157597)
                  ·
                    refine ⟨777760931674821947684099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2074029151132858527157597 777760931674821947684099)
                    ·
                      rfl

theorem cell22_2272026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_2272026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272026 prefixEnd_2272026 := by exact prefixLift 2272026
  have htrace : WordTrace (prefixWord ++ tailWord_2272026) baseStart_2272026 baseEnd_2272026 := by
    simpa [prefixWord, tailWord_2272026, baseEnd_2272026] using wordTrace_append hprefix tailTrace_2272026
  have hstable : (prefixWord ++ tailWord_2272026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272026).length < 2 ^ (prefixWord ++ tailWord_2272026).sum := by decide
  have hdescent : baseEnd_2272026 < baseStart_2272026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272028 : List Nat := [2, 2, 3, 1, 1, 3, 3, 3, 4]
def baseStart_2272028 : Nat := 118140960795 + 2272028 * 2 ^ 59
def prefixEnd_2272028 : Nat := 4983230072969 + 3 ^ 40 * 2272028 * 2
def baseEnd_2272028 : Nat := 259253872105231536378031

theorem tailTrace_2272028 : CollatzResearch.WordTrace tailWord_2272028 prefixEnd_2272028 259253872105231536378031 := by
  unfold tailWord_2272028
  simp only [CollatzResearch.WordTrace]
  refine ⟨41433834506419031167372369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55245112675225374889829825 41433834506419031167372369)
  ·
    refine ⟨31075375879814273375529277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41433834506419031167372369 31075375879814273375529277)
    ·
      refine ⟨11653265954930352515823479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31075375879814273375529277 11653265954930352515823479)
      ·
        refine ⟨17479898932395528773735219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11653265954930352515823479 17479898932395528773735219)
        ·
          refine ⟨26219848398593293160602829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17479898932395528773735219 26219848398593293160602829)
          ·
            refine ⟨9832443149472484935226061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26219848398593293160602829 9832443149472484935226061)
            ·
              refine ⟨3687166181052181850709773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9832443149472484935226061 3687166181052181850709773)
              ·
                refine ⟨1382687317894568194016165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3687166181052181850709773 1382687317894568194016165)
                ·
                  refine ⟨259253872105231536378031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1382687317894568194016165 259253872105231536378031)
                  ·
                    rfl

theorem cell22_2272028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_2272028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272028 prefixEnd_2272028 := by exact prefixLift 2272028
  have htrace : WordTrace (prefixWord ++ tailWord_2272028) baseStart_2272028 baseEnd_2272028 := by
    simpa [prefixWord, tailWord_2272028, baseEnd_2272028] using wordTrace_append hprefix tailTrace_2272028
  have hstable : (prefixWord ++ tailWord_2272028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272028).length < 2 ^ (prefixWord ++ tailWord_2272028).sum := by decide
  have hdescent : baseEnd_2272028 < baseStart_2272028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272069 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 4, 6]
def baseStart_2272069 : Nat := 118140960795 + 2272069 * 2 ^ 59
def prefixEnd_2272069 : Nat := 4983230072969 + 3 ^ 40 * 2272069 * 2
def baseEnd_2272069 : Nat := 777775651453584168858967

theorem tailTrace_2272069 : CollatzResearch.WordTrace tailWord_2272069 prefixEnd_2272069 777775651453584168858967 := by
  unfold tailWord_2272069
  simp only [CollatzResearch.WordTrace]
  refine ⟨82869164405689526336987261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55246109603793017557991507 82869164405689526336987261)
  ·
    refine ⟨31075936652133572376370223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82869164405689526336987261 31075936652133572376370223)
    ·
      refine ⟨46613904978200358564555335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31075936652133572376370223 46613904978200358564555335)
      ·
        refine ⟨69920857467300537846833003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46613904978200358564555335 69920857467300537846833003)
        ·
          refine ⟨104881286200950806770249505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69920857467300537846833003 104881286200950806770249505)
          ·
            refine ⟨78660964650713105077687129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104881286200950806770249505 78660964650713105077687129)
            ·
              refine ⟨58995723488034828808265347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78660964650713105077687129 58995723488034828808265347)
              ·
                refine ⟨88493585232052243212398021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58995723488034828808265347 88493585232052243212398021)
                ·
                  refine ⟨16592547231009795602324629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88493585232052243212398021 16592547231009795602324629)
                  ·
                    refine ⟨777775651453584168858967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16592547231009795602324629 777775651453584168858967)
                    ·
                      rfl

theorem cell22_2272069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_2272069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272069 prefixEnd_2272069 := by exact prefixLift 2272069
  have htrace : WordTrace (prefixWord ++ tailWord_2272069) baseStart_2272069 baseEnd_2272069 := by
    simpa [prefixWord, tailWord_2272069, baseEnd_2272069] using wordTrace_append hprefix tailTrace_2272069
  have hstable : (prefixWord ++ tailWord_2272069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272069).length < 2 ^ (prefixWord ++ tailWord_2272069).sum := by decide
  have hdescent : baseEnd_2272069 < baseStart_2272069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272071 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 5, 3]
def baseStart_2272071 : Nat := 118140960795 + 2272071 * 2 ^ 59
def prefixEnd_2272071 : Nat := 4983230072969 + 3 ^ 40 * 2272071 * 2
def baseEnd_2272071 : Nat := 777776336094456830308961

theorem tailTrace_2272071 : CollatzResearch.WordTrace tailWord_2272071 prefixEnd_2272071 777776336094456830308961 := by
  unfold tailWord_2272071
  simp only [CollatzResearch.WordTrace]
  refine ⟨82869237351682280678560067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55246158234454853785706711 82869237351682280678560067)
  ·
    refine ⟨124303856027523421017840101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82869237351682280678560067 124303856027523421017840101)
    ·
      refine ⟨23306973005160641440845019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124303856027523421017840101 23306973005160641440845019)
      ·
        refine ⟨34960459507740962161267529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23306973005160641440845019 34960459507740962161267529)
        ·
          refine ⟨26220344630805721620950647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34960459507740962161267529 26220344630805721620950647)
          ·
            refine ⟨39330516946208582431425971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26220344630805721620950647 39330516946208582431425971)
            ·
              refine ⟨58995775419312873647138957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39330516946208582431425971 58995775419312873647138957)
              ·
                refine ⟨22123415782242327617677109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58995775419312873647138957 22123415782242327617677109)
                ·
                  refine ⟨2074070229585218214157229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22123415782242327617677109 2074070229585218214157229)
                  ·
                    refine ⟨777776336094456830308961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2074070229585218214157229 777776336094456830308961)
                    ·
                      rfl

theorem cell22_2272071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_2272071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272071 prefixEnd_2272071 := by exact prefixLift 2272071
  have htrace : WordTrace (prefixWord ++ tailWord_2272071) baseStart_2272071 baseEnd_2272071 := by
    simpa [prefixWord, tailWord_2272071, baseEnd_2272071] using wordTrace_append hprefix tailTrace_2272071
  have hstable : (prefixWord ++ tailWord_2272071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272071).length < 2 ^ (prefixWord ++ tailWord_2272071).sum := by decide
  have hdescent : baseEnd_2272071 < baseStart_2272071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272101 : List Nat := [1, 3, 1, 3, 1, 1, 3, 4, 5]
def baseStart_2272101 : Nat := 118140960795 + 2272101 * 2 ^ 59
def prefixEnd_2272101 : Nat := 4983230072969 + 3 ^ 40 * 2272101 * 2
def baseEnd_2272101 : Nat := 259262201902515584019623

theorem tailTrace_2272101 : CollatzResearch.WordTrace tailWord_2272101 prefixEnd_2272101 259262201902515584019623 := by
  unfold tailWord_2272101
  simp only [CollatzResearch.WordTrace]
  refine ⟨82870331541573595802152157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55246887694382397201434771 82870331541573595802152157)
  ·
    refine ⟨31076374328090098425807059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82870331541573595802152157 31076374328090098425807059)
    ·
      refine ⟨46614561492135147638710589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31076374328090098425807059 46614561492135147638710589)
      ·
        refine ⟨17480460559550680364516471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46614561492135147638710589 17480460559550680364516471)
        ·
          refine ⟨26220690839326020546774707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17480460559550680364516471 26220690839326020546774707)
          ·
            refine ⟨39331036258989030820162061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26220690839326020546774707 39331036258989030820162061)
            ·
              refine ⟨14749138597120886557560773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39331036258989030820162061 14749138597120886557560773)
              ·
                refine ⟨2765463486960166229542645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14749138597120886557560773 2765463486960166229542645)
                ·
                  refine ⟨259262201902515584019623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2765463486960166229542645 259262201902515584019623)
                  ·
                    rfl

theorem cell22_2272101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_2272101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272101 prefixEnd_2272101 := by exact prefixLift 2272101
  have htrace : WordTrace (prefixWord ++ tailWord_2272101) baseStart_2272101 baseEnd_2272101 := by
    simpa [prefixWord, tailWord_2272101, baseEnd_2272101] using wordTrace_append hprefix tailTrace_2272101
  have hstable : (prefixWord ++ tailWord_2272101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272101).length < 2 ^ (prefixWord ++ tailWord_2272101).sum := by decide
  have hdescent : baseEnd_2272101 < baseStart_2272101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272131 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 3, 4]
def baseStart_2272131 : Nat := 118140960795 + 2272131 * 2 ^ 59
def prefixEnd_2272131 : Nat := 4983230072969 + 3 ^ 40 * 2272131 * 2
def baseEnd_2272131 : Nat := 777796875320636673808777

theorem tailTrace_2272131 : CollatzResearch.WordTrace tailWord_2272131 prefixEnd_2272131 777796875320636673808777 := by
  unfold tailWord_2272131
  simp only [CollatzResearch.WordTrace]
  refine ⟨82871425731464910925744247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55247617154309940617162831 82871425731464910925744247)
  ·
    refine ⟨124307138597197366388616371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82871425731464910925744247 124307138597197366388616371)
    ·
      refine ⟨186460707895796049582924557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124307138597197366388616371 186460707895796049582924557)
      ·
        refine ⟨69922765460923518593596709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186460707895796049582924557 69922765460923518593596709)
        ·
          refine ⟨13110518523923159736299383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69922765460923518593596709 13110518523923159736299383)
          ·
            refine ⟨19665777785884739604449075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13110518523923159736299383 19665777785884739604449075)
            ·
              refine ⟨29498666678827109406673613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19665777785884739604449075 29498666678827109406673613)
              ·
                refine ⟨11062000004560166027502605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29498666678827109406673613 11062000004560166027502605)
                ·
                  refine ⟨4148250001710062260313477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11062000004560166027502605 4148250001710062260313477)
                  ·
                    refine ⟨777796875320636673808777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4148250001710062260313477 777796875320636673808777)
                    ·
                      rfl

theorem cell22_2272131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 4].length) (baseStart_2272131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272131 prefixEnd_2272131 := by exact prefixLift 2272131
  have htrace : WordTrace (prefixWord ++ tailWord_2272131) baseStart_2272131 baseEnd_2272131 := by
    simpa [prefixWord, tailWord_2272131, baseEnd_2272131] using wordTrace_append hprefix tailTrace_2272131
  have hstable : (prefixWord ++ tailWord_2272131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272131).length < 2 ^ (prefixWord ++ tailWord_2272131).sum := by decide
  have hdescent : baseEnd_2272131 < baseStart_2272131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272163 : List Nat := [1, 1, 1, 4, 1, 2, 4, 4, 4]
def baseStart_2272163 : Nat := 118140960795 + 2272163 * 2 ^ 59
def prefixEnd_2272163 : Nat := 4983230072969 + 3 ^ 40 * 2272163 * 2
def baseEnd_2272163 : Nat := 259269276524866419002893

theorem tailTrace_2272163 : CollatzResearch.WordTrace tailWord_2272163 prefixEnd_2272163 259269276524866419002893 := by
  unfold tailWord_2272163
  simp only [CollatzResearch.WordTrace]
  refine ⟨82872592867348980390909143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55248395244899320260606095 82872592867348980390909143)
  ·
    refine ⟨124308889301023470586363715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82872592867348980390909143 124308889301023470586363715)
    ·
      refine ⟨186463333951535205879545573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124308889301023470586363715 186463333951535205879545573)
      ·
        refine ⟨34961875115912851102414795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186463333951535205879545573 34961875115912851102414795)
        ·
          refine ⟨52442812673869276653622193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34961875115912851102414795 52442812673869276653622193)
          ·
            refine ⟨39332109505401957490216645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52442812673869276653622193 39332109505401957490216645)
            ·
              refine ⟨7374770532262867029415621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39332109505401957490216645 7374770532262867029415621)
              ·
                refine ⟨1382769474799287568015429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7374770532262867029415621 1382769474799287568015429)
                ·
                  refine ⟨259269276524866419002893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1382769474799287568015429 259269276524866419002893)
                  ·
                    rfl

theorem cell22_2272163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 4].length) (baseStart_2272163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272163 prefixEnd_2272163 := by exact prefixLift 2272163
  have htrace : WordTrace (prefixWord ++ tailWord_2272163) baseStart_2272163 baseEnd_2272163 := by
    simpa [prefixWord, tailWord_2272163, baseEnd_2272163] using wordTrace_append hprefix tailTrace_2272163
  have hstable : (prefixWord ++ tailWord_2272163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272163).length < 2 ^ (prefixWord ++ tailWord_2272163).sum := by decide
  have hdescent : baseEnd_2272163 < baseStart_2272163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272180 : List Nat := [2, 5, 2, 1, 1, 1, 2, 2, 6]
def baseStart_2272180 : Nat := 118140960795 + 2272180 * 2 ^ 59
def prefixEnd_2272180 : Nat := 4983230072969 + 3 ^ 40 * 2272180 * 2
def baseEnd_2272180 : Nat := 259271216340672293111209

theorem tailTrace_2272180 : CollatzResearch.WordTrace tailWord_2272180 prefixEnd_2272180 259271216340672293111209 := by
  unfold tailWord_2272180
  simp only [CollatzResearch.WordTrace]
  refine ⟨41436606454143696147138997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55248808605524928196185329 41436606454143696147138997)
  ·
    refine ⟨3884681855075971513794281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41436606454143696147138997 3884681855075971513794281)
    ·
      refine ⟨2913511391306978635345711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3884681855075971513794281 2913511391306978635345711)
      ·
        refine ⟨4370267086960467953018567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2913511391306978635345711 4370267086960467953018567)
        ·
          refine ⟨6555400630440701929527851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4370267086960467953018567 6555400630440701929527851)
          ·
            refine ⟨9833100945661052894291777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6555400630440701929527851 9833100945661052894291777)
            ·
              refine ⟨7374825709245789670718833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9833100945661052894291777 7374825709245789670718833)
              ·
                refine ⟨5531119281934342253039125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7374825709245789670718833 5531119281934342253039125)
                ·
                  refine ⟨259271216340672293111209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5531119281934342253039125 259271216340672293111209)
                  ·
                    rfl

theorem cell22_2272180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_2272180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272180 prefixEnd_2272180 := by exact prefixLift 2272180
  have htrace : WordTrace (prefixWord ++ tailWord_2272180) baseStart_2272180 baseEnd_2272180 := by
    simpa [prefixWord, tailWord_2272180, baseEnd_2272180] using wordTrace_append hprefix tailTrace_2272180
  have hstable : (prefixWord ++ tailWord_2272180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272180).length < 2 ^ (prefixWord ++ tailWord_2272180).sum := by decide
  have hdescent : baseEnd_2272180 < baseStart_2272180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272210 : List Nat := [3, 2, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_2272210 : Nat := 118140960795 + 2272210 * 2 ^ 59
def prefixEnd_2272210 : Nat := 4983230072969 + 3 ^ 40 * 2272210 * 2
def baseEnd_2272210 : Nat := 777823918635106801083535

theorem tailTrace_2272210 : CollatzResearch.WordTrace tailWord_2272210 prefixEnd_2272210 777823918635106801083535 := by
  unfold tailWord_2272210
  simp only [CollatzResearch.WordTrace]
  refine ⟨20718576774544676854467521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55249538065452471611913389 20718576774544676854467521)
  ·
    refine ⟨15538932580908507640850641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20718576774544676854467521 15538932580908507640850641)
    ·
      refine ⟨11654199435681380730637981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15538932580908507640850641 11654199435681380730637981)
      ·
        refine ⟨4370324788380517773989243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11654199435681380730637981 4370324788380517773989243)
        ·
          refine ⟨6555487182570776660983865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4370324788380517773989243 6555487182570776660983865)
          ·
            refine ⟨4916615386928082495737899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6555487182570776660983865 4916615386928082495737899)
            ·
              refine ⟨7374923080392123743606849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4916615386928082495737899 7374923080392123743606849)
              ·
                refine ⟨5531192310294092807705137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7374923080392123743606849 5531192310294092807705137)
                ·
                  refine ⟨4148394232720569605778853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5531192310294092807705137 4148394232720569605778853)
                  ·
                    refine ⟨777823918635106801083535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4148394232720569605778853 777823918635106801083535)
                    ·
                      rfl

theorem cell22_2272210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_2272210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272210 prefixEnd_2272210 := by exact prefixLift 2272210
  have htrace : WordTrace (prefixWord ++ tailWord_2272210) baseStart_2272210 baseEnd_2272210 := by
    simpa [prefixWord, tailWord_2272210, baseEnd_2272210] using wordTrace_append hprefix tailTrace_2272210
  have hstable : (prefixWord ++ tailWord_2272210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272210).length < 2 ^ (prefixWord ++ tailWord_2272210).sum := by decide
  have hdescent : baseEnd_2272210 < baseStart_2272210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272214 : List Nat := [5, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_2272214 : Nat := 118140960795 + 2272214 * 2 ^ 59
def prefixEnd_2272214 : Nat := 4983230072969 + 3 ^ 40 * 2272214 * 2
def baseEnd_2272214 : Nat := 259275095972284041327841

theorem tailTrace_2272214 : CollatzResearch.WordTrace tailWord_2272214 prefixEnd_2272214 259275095972284041327841 := by
  unfold tailWord_2272214
  simp only [CollatzResearch.WordTrace]
  refine ⟨5179653311885263506313481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55249635326776144067343797 5179653311885263506313481)
  ·
    refine ⟨3884739983913947629735111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5179653311885263506313481 3884739983913947629735111)
    ·
      refine ⟨5827109975870921444602667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3884739983913947629735111 5827109975870921444602667)
      ·
        refine ⟨8740664963806382166904001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5827109975870921444602667 8740664963806382166904001)
        ·
          refine ⟨6555498722854786625178001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8740664963806382166904001 6555498722854786625178001)
          ·
            refine ⟨4916624042141089968883501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6555498722854786625178001 4916624042141089968883501)
            ·
              refine ⟨1843734015802908738331313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4916624042141089968883501 1843734015802908738331313)
              ·
                refine ⟨1382800511852181553748485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1843734015802908738331313 1382800511852181553748485)
                ·
                  refine ⟨259275095972284041327841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1382800511852181553748485 259275095972284041327841)
                  ·
                    rfl

theorem cell22_2272214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_2272214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272214 prefixEnd_2272214 := by exact prefixLift 2272214
  have htrace : WordTrace (prefixWord ++ tailWord_2272214) baseStart_2272214 baseEnd_2272214 := by
    simpa [prefixWord, tailWord_2272214, baseEnd_2272214] using wordTrace_append hprefix tailTrace_2272214
  have hstable : (prefixWord ++ tailWord_2272214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272214).length < 2 ^ (prefixWord ++ tailWord_2272214).sum := by decide
  have hdescent : baseEnd_2272214 < baseStart_2272214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272251 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 4, 5]
def baseStart_2272251 : Nat := 118140960795 + 2272251 * 2 ^ 59
def prefixEnd_2272251 : Nat := 4983230072969 + 3 ^ 40 * 2272251 * 2
def baseEnd_2272251 : Nat := 777837953772996360808409

theorem tailTrace_2272251 : CollatzResearch.WordTrace tailWord_2272251 prefixEnd_2272251 777837953772996360808409 := by
  unfold tailWord_2272251
  simp only [CollatzResearch.WordTrace]
  refine ⟨82875802491030171420112607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55250534994020114280075071 82875802491030171420112607)
  ·
    refine ⟨124313703736545257130168911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82875802491030171420112607 124313703736545257130168911)
    ·
      refine ⟨186470555604817885695253367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124313703736545257130168911 186470555604817885695253367)
      ·
        refine ⟨279705833407226828542880051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186470555604817885695253367 279705833407226828542880051)
        ·
          refine ⟨419558750110840242814320077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279705833407226828542880051 419558750110840242814320077)
          ·
            refine ⟨157334531291565091055370029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 419558750110840242814320077 157334531291565091055370029)
            ·
              refine ⟨59000449234336909145763761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157334531291565091055370029 59000449234336909145763761)
              ·
                refine ⟨44250336925752681859322821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59000449234336909145763761 44250336925752681859322821)
                ·
                  refine ⟨8296938173578627848623029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44250336925752681859322821 8296938173578627848623029)
                  ·
                    refine ⟨777837953772996360808409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8296938173578627848623029 777837953772996360808409)
                    ·
                      rfl

theorem cell22_2272251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 5].length) (baseStart_2272251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272251 prefixEnd_2272251 := by exact prefixLift 2272251
  have htrace : WordTrace (prefixWord ++ tailWord_2272251) baseStart_2272251 baseEnd_2272251 := by
    simpa [prefixWord, tailWord_2272251, baseEnd_2272251] using wordTrace_append hprefix tailTrace_2272251
  have hstable : (prefixWord ++ tailWord_2272251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272251).length < 2 ^ (prefixWord ++ tailWord_2272251).sum := by decide
  have hdescent : baseEnd_2272251 < baseStart_2272251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272270 : List Nat := [4, 1, 1, 2, 2, 3, 2, 2, 5]
def baseStart_2272270 : Nat := 118140960795 + 2272270 * 2 ^ 59
def prefixEnd_2272270 : Nat := 4983230072969 + 3 ^ 40 * 2272270 * 2
def baseEnd_2272270 : Nat := 259281485953762214861117

theorem tailTrace_2272270 : CollatzResearch.WordTrace tailWord_2272270 prefixEnd_2272270 259281485953762214861117 := by
  unfold tailWord_2272270
  simp only [CollatzResearch.WordTrace]
  refine ⟨10359561934745167208131783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55250996985307558443369509 10359561934745167208131783)
  ·
    refine ⟨15539342902117750812197675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10359561934745167208131783 15539342902117750812197675)
    ·
      refine ⟨23309014353176626218296513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15539342902117750812197675 23309014353176626218296513)
      ·
        refine ⟨17481760764882469663722385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23309014353176626218296513 17481760764882469663722385)
        ·
          refine ⟨13111320573661852247791789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17481760764882469663722385 13111320573661852247791789)
          ·
            refine ⟨4916745215123194592921921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13111320573661852247791789 4916745215123194592921921)
            ·
              refine ⟨3687558911342395944691441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4916745215123194592921921 3687558911342395944691441)
              ·
                refine ⟨2765669183506796958518581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3687558911342395944691441 2765669183506796958518581)
                ·
                  refine ⟨259281485953762214861117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2765669183506796958518581 259281485953762214861117)
                  ·
                    rfl

theorem cell22_2272270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_2272270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272270 prefixEnd_2272270 := by exact prefixLift 2272270
  have htrace : WordTrace (prefixWord ++ tailWord_2272270) baseStart_2272270 baseEnd_2272270 := by
    simpa [prefixWord, tailWord_2272270, baseEnd_2272270] using wordTrace_append hprefix tailTrace_2272270
  have hstable : (prefixWord ++ tailWord_2272270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272270).length < 2 ^ (prefixWord ++ tailWord_2272270).sum := by decide
  have hdescent : baseEnd_2272270 < baseStart_2272270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272285 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_2272285 : Nat := 118140960795 + 2272285 * 2 ^ 59
def prefixEnd_2272285 : Nat := 4983230072969 + 3 ^ 40 * 2272285 * 2
def baseEnd_2272285 : Nat := 777849592667831605458305

theorem tailTrace_2272285 : CollatzResearch.WordTrace tailWord_2272285 prefixEnd_2272285 777849592667831605458305 := by
  unfold tailWord_2272285
  simp only [CollatzResearch.WordTrace]
  refine ⟨82877042572906995226850309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55251361715271330151233539 82877042572906995226850309)
  ·
    refine ⟨15539445482420061605034433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82877042572906995226850309 15539445482420061605034433)
    ·
      refine ⟨11654584111815046203775825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15539445482420061605034433 11654584111815046203775825)
      ·
        refine ⟨8740938083861284652831869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11654584111815046203775825 8740938083861284652831869)
        ·
          refine ⟨3277851781447981744811951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8740938083861284652831869 3277851781447981744811951)
          ·
            refine ⟨4916777672171972617217927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3277851781447981744811951 4916777672171972617217927)
            ·
              refine ⟨7375166508257958925826891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4916777672171972617217927 7375166508257958925826891)
              ·
                refine ⟨11062749762386938388740337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7375166508257958925826891 11062749762386938388740337)
                ·
                  refine ⟨8297062321790203791555253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11062749762386938388740337 8297062321790203791555253)
                  ·
                    refine ⟨777849592667831605458305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8297062321790203791555253 777849592667831605458305)
                    ·
                      rfl

theorem cell22_2272285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_2272285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272285 prefixEnd_2272285 := by exact prefixLift 2272285
  have htrace : WordTrace (prefixWord ++ tailWord_2272285) baseStart_2272285 baseEnd_2272285 := by
    simpa [prefixWord, tailWord_2272285, baseEnd_2272285] using wordTrace_append hprefix tailTrace_2272285
  have hstable : (prefixWord ++ tailWord_2272285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272285).length < 2 ^ (prefixWord ++ tailWord_2272285).sum := by decide
  have hdescent : baseEnd_2272285 < baseStart_2272285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272317 : List Nat := [1, 4, 1, 3, 1, 2, 4, 1, 1, 4]
def baseStart_2272317 : Nat := 118140960795 + 2272317 * 2 ^ 59
def prefixEnd_2272317 : Nat := 4983230072969 + 3 ^ 40 * 2272317 * 2
def baseEnd_2272317 : Nat := 777860546921794188658207

theorem tailTrace_2272317 : CollatzResearch.WordTrace tailWord_2272317 prefixEnd_2272317 777860546921794188658207 := by
  unfold tailWord_2272317
  simp only [CollatzResearch.WordTrace]
  refine ⟨82878209708791064692015205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55252139805860709794676803 82878209708791064692015205)
  ·
    refine ⟨15539664320398324629752851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82878209708791064692015205 15539664320398324629752851)
    ·
      refine ⟨23309496480597486944629277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15539664320398324629752851 23309496480597486944629277)
      ·
        refine ⟨8741061180224057604235979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23309496480597486944629277 8741061180224057604235979)
        ·
          refine ⟨13111591770336086406353969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8741061180224057604235979 13111591770336086406353969)
          ·
            refine ⟨9833693827752064804765477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13111591770336086406353969 9833693827752064804765477)
            ·
              refine ⟨1843817592703512150893527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9833693827752064804765477 1843817592703512150893527)
              ·
                refine ⟨2765726389055268226340291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1843817592703512150893527 2765726389055268226340291)
                ·
                  refine ⟨4148589583582902339510437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2765726389055268226340291 4148589583582902339510437)
                  ·
                    refine ⟨777860546921794188658207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4148589583582902339510437 777860546921794188658207)
                    ·
                      rfl

theorem cell22_2272317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_2272317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272317 prefixEnd_2272317 := by exact prefixLift 2272317
  have htrace : WordTrace (prefixWord ++ tailWord_2272317) baseStart_2272317 baseEnd_2272317 := by
    simpa [prefixWord, tailWord_2272317, baseEnd_2272317] using wordTrace_append hprefix tailTrace_2272317
  have hstable : (prefixWord ++ tailWord_2272317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272317).length < 2 ^ (prefixWord ++ tailWord_2272317).sum := by decide
  have hdescent : baseEnd_2272317 < baseStart_2272317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272328 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 4, 4]
def baseStart_2272328 : Nat := 118140960795 + 2272328 * 2 ^ 59
def prefixEnd_2272328 : Nat := 4983230072969 + 3 ^ 40 * 2272328 * 2
def baseEnd_2272328 : Nat := 777864312446593826633173

theorem tailTrace_2272328 : CollatzResearch.WordTrace tailWord_2272328 prefixEnd_2272328 777864312446593826633173 := by
  unfold tailWord_2272328
  simp only [CollatzResearch.WordTrace]
  refine ⟨41439305455875606785332819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55252407274500809047110425 41439305455875606785332819)
  ·
    refine ⟨62158958183813410177999229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41439305455875606785332819 62158958183813410177999229)
    ·
      refine ⟨23309609318930028816749711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62158958183813410177999229 23309609318930028816749711)
      ·
        refine ⟨34964413978395043225124567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23309609318930028816749711 34964413978395043225124567)
        ·
          refine ⟨52446620967592564837686851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34964413978395043225124567 52446620967592564837686851)
          ·
            refine ⟨78669931451388847256530277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52446620967592564837686851 78669931451388847256530277)
            ·
              refine ⟨14750612147135408860599427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78669931451388847256530277 14750612147135408860599427)
              ·
                refine ⟨22125918220703113290899141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14750612147135408860599427 22125918220703113290899141)
                ·
                  refine ⟨4148609666381833742043589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22125918220703113290899141 4148609666381833742043589)
                  ·
                    refine ⟨777864312446593826633173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4148609666381833742043589 777864312446593826633173)
                    ·
                      rfl

theorem cell22_2272328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_2272328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272328 prefixEnd_2272328 := by exact prefixLift 2272328
  have htrace : WordTrace (prefixWord ++ tailWord_2272328) baseStart_2272328 baseEnd_2272328 := by
    simpa [prefixWord, tailWord_2272328, baseEnd_2272328] using wordTrace_append hprefix tailTrace_2272328
  have hstable : (prefixWord ++ tailWord_2272328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272328).length < 2 ^ (prefixWord ++ tailWord_2272328).sum := by decide
  have hdescent : baseEnd_2272328 < baseStart_2272328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272403 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 2, 5]
def baseStart_2272403 : Nat := 118140960795 + 2272403 * 2 ^ 59
def prefixEnd_2272403 : Nat := 4983230072969 + 3 ^ 40 * 2272403 * 2
def baseEnd_2272403 : Nat := 777889986479318631007943

theorem tailTrace_2272403 : CollatzResearch.WordTrace tailWord_2272403 prefixEnd_2272403 777889986479318631007943 := by
  unfold tailWord_2272403
  simp only [CollatzResearch.WordTrace]
  refine ⟨82881346386479501379645863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55254230924319667586430575 82881346386479501379645863)
  ·
    refine ⟨124322019579719252069468795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82881346386479501379645863 124322019579719252069468795)
    ·
      refine ⟨186483029369578878104203193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124322019579719252069468795 186483029369578878104203193)
      ·
        refine ⟨139862272027184158578152395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186483029369578878104203193 139862272027184158578152395)
        ·
          refine ⟨209793408040776237867228593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139862272027184158578152395 209793408040776237867228593)
          ·
            refine ⟨157345056030582178400421445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209793408040776237867228593 157345056030582178400421445)
            ·
              refine ⟨29502198005734158450079021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157345056030582178400421445 29502198005734158450079021)
              ·
                refine ⟨11063324252150309418779633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29502198005734158450079021 11063324252150309418779633)
                ·
                  refine ⟨8297493189112732064084725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11063324252150309418779633 8297493189112732064084725)
                  ·
                    refine ⟨777889986479318631007943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8297493189112732064084725 777889986479318631007943)
                    ·
                      rfl

theorem cell22_2272403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 5].length) (baseStart_2272403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272403 prefixEnd_2272403 := by exact prefixLift 2272403
  have htrace : WordTrace (prefixWord ++ tailWord_2272403) baseStart_2272403 baseEnd_2272403 := by
    simpa [prefixWord, tailWord_2272403, baseEnd_2272403] using wordTrace_append hprefix tailTrace_2272403
  have hstable : (prefixWord ++ tailWord_2272403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272403).length < 2 ^ (prefixWord ++ tailWord_2272403).sum := by decide
  have hdescent : baseEnd_2272403 < baseStart_2272403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272435 : List Nat := [1, 1, 1, 2, 3, 2, 2, 5, 1, 4]
def baseStart_2272435 : Nat := 118140960795 + 2272435 * 2 ^ 59
def prefixEnd_2272435 : Nat := 4983230072969 + 3 ^ 40 * 2272435 * 2
def baseEnd_2272435 : Nat := 777900940733281214207845

theorem tailTrace_2272435 : CollatzResearch.WordTrace tailWord_2272435 prefixEnd_2272435 777900940733281214207845 := by
  unfold tailWord_2272435
  simp only [CollatzResearch.WordTrace]
  refine ⟨82882513522363570844810759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55255009014909047229873839 82882513522363570844810759)
  ·
    refine ⟨124323770283545356267216139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82882513522363570844810759 124323770283545356267216139)
    ·
      refine ⟨186485655425318034400824209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124323770283545356267216139 186485655425318034400824209)
      ·
        refine ⟨139864241568988525800618157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186485655425318034400824209 139864241568988525800618157)
        ·
          refine ⟨52449090588370697175231809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139864241568988525800618157 52449090588370697175231809)
          ·
            refine ⟨39336817941278022881423857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52449090588370697175231809 39336817941278022881423857)
            ·
              refine ⟨29502613455958517161067893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39336817941278022881423857 29502613455958517161067893)
              ·
                refine ⟨2765870011496110983850115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29502613455958517161067893 2765870011496110983850115)
                ·
                  refine ⟨4148805017244166475775173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2765870011496110983850115 4148805017244166475775173)
                  ·
                    refine ⟨777900940733281214207845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4148805017244166475775173 777900940733281214207845)
                    ·
                      rfl

theorem cell22_2272435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 4].length) (baseStart_2272435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272435 prefixEnd_2272435 := by exact prefixLift 2272435
  have htrace : WordTrace (prefixWord ++ tailWord_2272435) baseStart_2272435 baseEnd_2272435 := by
    simpa [prefixWord, tailWord_2272435, baseEnd_2272435] using wordTrace_append hprefix tailTrace_2272435
  have hstable : (prefixWord ++ tailWord_2272435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272435).length < 2 ^ (prefixWord ++ tailWord_2272435).sum := by decide
  have hdescent : baseEnd_2272435 < baseStart_2272435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272465 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 6, 3]
def baseStart_2272465 : Nat := 118140960795 + 2272465 * 2 ^ 59
def prefixEnd_2272465 : Nat := 4983230072969 + 3 ^ 40 * 2272465 * 2
def baseEnd_2272465 : Nat := 777911210346371135957753

theorem tailTrace_2272465 : CollatzResearch.WordTrace tailWord_2272465 prefixEnd_2272465 777911210346371135957753 := by
  unfold tailWord_2272465
  simp only [CollatzResearch.WordTrace]
  refine ⟨82883607712254885968402849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55255738474836590645601899 82883607712254885968402849)
  ·
    refine ⟨62162705784191164476302137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82883607712254885968402849 62162705784191164476302137)
    ·
      refine ⟨46622029338143373357226603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62162705784191164476302137 46622029338143373357226603)
      ·
        refine ⟨69933044007215060035839905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46622029338143373357226603 69933044007215060035839905)
        ·
          refine ⟨52449783005411295026879929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69933044007215060035839905 52449783005411295026879929)
          ·
            refine ⟨39337337254058471270159947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52449783005411295026879929 39337337254058471270159947)
            ·
              refine ⟨59006005881087706905239921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39337337254058471270159947 59006005881087706905239921)
              ·
                refine ⟨44254504410815780178929941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59006005881087706905239921 44254504410815780178929941)
                ·
                  refine ⟨2074429894256989695887341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44254504410815780178929941 2074429894256989695887341)
                  ·
                    refine ⟨777911210346371135957753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2074429894256989695887341 777911210346371135957753)
                    ·
                      rfl

theorem cell22_2272465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_2272465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272465 prefixEnd_2272465 := by exact prefixLift 2272465
  have htrace : WordTrace (prefixWord ++ tailWord_2272465) baseStart_2272465 baseEnd_2272465 := by
    simpa [prefixWord, tailWord_2272465, baseEnd_2272465] using wordTrace_append hprefix tailTrace_2272465
  have hstable : (prefixWord ++ tailWord_2272465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272465).length < 2 ^ (prefixWord ++ tailWord_2272465).sum := by decide
  have hdescent : baseEnd_2272465 < baseStart_2272465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272480 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 1, 6]
def baseStart_2272480 : Nat := 118140960795 + 2272480 * 2 ^ 59
def prefixEnd_2272480 : Nat := 4983230072969 + 3 ^ 40 * 2272480 * 2
def baseEnd_2272480 : Nat := 777916345152916096832707

theorem tailTrace_2272480 : CollatzResearch.WordTrace tailWord_2272480 prefixEnd_2272480 777916345152916096832707 := by
  unfold tailWord_2272480
  simp only [CollatzResearch.WordTrace]
  refine ⟨41442077403600271765099447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55256103204800362353465929 41442077403600271765099447)
  ·
    refine ⟨62163116105400407647649171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41442077403600271765099447 62163116105400407647649171)
    ·
      refine ⟨93244674158100611471473757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62163116105400407647649171 93244674158100611471473757)
      ·
        refine ⟨34966752809287729301802659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93244674158100611471473757 34966752809287729301802659)
        ·
          refine ⟨52450129213931593952703989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34966752809287729301802659 52450129213931593952703989)
          ·
            refine ⟨4917199613806086933065999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52450129213931593952703989 4917199613806086933065999)
            ·
              refine ⟨7375799420709130399598999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4917199613806086933065999 7375799420709130399598999)
              ·
                refine ⟨11063699131063695599398499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7375799420709130399598999 11063699131063695599398499)
                ·
                  refine ⟨16595548696595543399097749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11063699131063695599398499 16595548696595543399097749)
                  ·
                    refine ⟨777916345152916096832707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16595548696595543399097749 777916345152916096832707)
                    ·
                      rfl

theorem cell22_2272480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_2272480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272480 prefixEnd_2272480 := by exact prefixLift 2272480
  have htrace : WordTrace (prefixWord ++ tailWord_2272480) baseStart_2272480 baseEnd_2272480 := by
    simpa [prefixWord, tailWord_2272480, baseEnd_2272480] using wordTrace_append hprefix tailTrace_2272480
  have hstable : (prefixWord ++ tailWord_2272480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272480).length < 2 ^ (prefixWord ++ tailWord_2272480).sum := by decide
  have hdescent : baseEnd_2272480 < baseStart_2272480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272495 : List Nat := [1, 1, 2, 1, 7, 1, 9]
def baseStart_2272495 : Nat := 118140960795 + 2272495 * 2 ^ 59
def prefixEnd_2272495 : Nat := 4983230072969 + 3 ^ 40 * 2272495 * 2
def baseEnd_2272495 : Nat := 28811906665165224359543

theorem tailTrace_2272495 : CollatzResearch.WordTrace tailWord_2272495 prefixEnd_2272495 28811906665165224359543 := by
  unfold tailWord_2272495
  simp only [CollatzResearch.WordTrace]
  refine ⟨82884701902146201091994939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55256467934764134061329959 82884701902146201091994939)
  ·
    refine ⟨124327052853219301637992409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82884701902146201091994939 124327052853219301637992409)
    ·
      refine ⟨93245289639914476228494307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124327052853219301637992409 93245289639914476228494307)
      ·
        refine ⟨139867934459871714342741461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93245289639914476228494307 139867934459871714342741461)
        ·
          refine ⟨3278154713903243304908003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 139867934459871714342741461 3278154713903243304908003)
          ·
            refine ⟨4917232070854864957362005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3278154713903243304908003 4917232070854864957362005)
            ·
              refine ⟨28811906665165224359543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4917232070854864957362005 28811906665165224359543)
              ·
                rfl

theorem cell22_2272495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 9].length) (baseStart_2272495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272495 prefixEnd_2272495 := by exact prefixLift 2272495
  have htrace : WordTrace (prefixWord ++ tailWord_2272495) baseStart_2272495 baseEnd_2272495 := by
    simpa [prefixWord, tailWord_2272495, baseEnd_2272495] using wordTrace_append hprefix tailTrace_2272495
  have hstable : (prefixWord ++ tailWord_2272495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272495).length < 2 ^ (prefixWord ++ tailWord_2272495).sum := by decide
  have hdescent : baseEnd_2272495 < baseStart_2272495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272499 : List Nat := [1, 1, 1, 2, 2, 7, 1, 2, 2, 3]
def baseStart_2272499 : Nat := 118140960795 + 2272499 * 2 ^ 59
def prefixEnd_2272499 : Nat := 4983230072969 + 3 ^ 40 * 2272499 * 2
def baseEnd_2272499 : Nat := 777922849241206380607649

theorem tailTrace_2272499 : CollatzResearch.WordTrace tailWord_2272499 prefixEnd_2272499 777922849241206380607649 := by
  unfold tailWord_2272499
  simp only [CollatzResearch.WordTrace]
  refine ⟨82884847794131709775140551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55256565196087806516760367 82884847794131709775140551)
  ·
    refine ⟨124327271691197564662710827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82884847794131709775140551 124327271691197564662710827)
    ·
      refine ⟨186490907536796346994066241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124327271691197564662710827 186490907536796346994066241)
      ·
        refine ⟨139868180652597260245549681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186490907536796346994066241 139868180652597260245549681)
        ·
          refine ⟨104901135489447945184162261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139868180652597260245549681 104901135489447945184162261)
          ·
            refine ⟨2458620363033936215253803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 104901135489447945184162261 2458620363033936215253803)
            ·
              refine ⟨3687930544550904322880705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2458620363033936215253803 3687930544550904322880705)
              ·
                refine ⟨2765947908413178242160529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3687930544550904322880705 2765947908413178242160529)
                ·
                  refine ⟨2074460931309883681620397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2765947908413178242160529 2074460931309883681620397)
                  ·
                    refine ⟨777922849241206380607649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2074460931309883681620397 777922849241206380607649)
                    ·
                      rfl

theorem cell22_2272499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 3].length) (baseStart_2272499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272499 prefixEnd_2272499 := by exact prefixLift 2272499
  have htrace : WordTrace (prefixWord ++ tailWord_2272499) baseStart_2272499 baseEnd_2272499 := by
    simpa [prefixWord, tailWord_2272499, baseEnd_2272499] using wordTrace_append hprefix tailTrace_2272499
  have hstable : (prefixWord ++ tailWord_2272499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272499).length < 2 ^ (prefixWord ++ tailWord_2272499).sum := by decide
  have hdescent : baseEnd_2272499 < baseStart_2272499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272516 : List Nat := [2, 3, 2, 2, 2, 2, 3, 1, 2, 3]
def baseStart_2272516 : Nat := 118140960795 + 2272516 * 2 ^ 59
def prefixEnd_2272516 : Nat := 4983230072969 + 3 ^ 40 * 2272516 * 2
def baseEnd_2272516 : Nat := 777928668688624002932597

theorem tailTrace_2272516 : CollatzResearch.WordTrace tailWord_2272516 prefixEnd_2272516 777928668688624002932597 := by
  unfold tailWord_2272516
  simp only [CollatzResearch.WordTrace]
  refine ⟨41442733917535060839254701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55256978556713414452339601 41442733917535060839254701)
  ·
    refine ⟨15541025219075647814720513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41442733917535060839254701 15541025219075647814720513)
    ·
      refine ⟨11655768914306735861040385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15541025219075647814720513 11655768914306735861040385)
      ·
        refine ⟨8741826685730051895780289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11655768914306735861040385 8741826685730051895780289)
        ·
          refine ⟨6556370014297538921835217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8741826685730051895780289 6556370014297538921835217)
          ·
            refine ⟨4917277510723154191376413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6556370014297538921835217 4917277510723154191376413)
            ·
              refine ⟨1843979066521182821766155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4917277510723154191376413 1843979066521182821766155)
              ·
                refine ⟨2765968599781774232649233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1843979066521182821766155 2765968599781774232649233)
                ·
                  refine ⟨2074476449836330674486925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2765968599781774232649233 2074476449836330674486925)
                  ·
                    refine ⟨777928668688624002932597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2074476449836330674486925 777928668688624002932597)
                    ·
                      rfl

theorem cell22_2272516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_2272516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272516 prefixEnd_2272516 := by exact prefixLift 2272516
  have htrace : WordTrace (prefixWord ++ tailWord_2272516) baseStart_2272516 baseEnd_2272516 := by
    simpa [prefixWord, tailWord_2272516, baseEnd_2272516] using wordTrace_append hprefix tailTrace_2272516
  have hstable : (prefixWord ++ tailWord_2272516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272516).length < 2 ^ (prefixWord ++ tailWord_2272516).sum := by decide
  have hdescent : baseEnd_2272516 < baseStart_2272516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272540 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 7]
def baseStart_2272540 : Nat := 118140960795 + 2272540 * 2 ^ 59
def prefixEnd_2272540 : Nat := 4983230072969 + 3 ^ 40 * 2272540 * 2
def baseEnd_2272540 : Nat := 259312294793031980110841

theorem tailTrace_2272540 : CollatzResearch.WordTrace tailWord_2272540 prefixEnd_2272540 259312294793031980110841 := by
  unfold tailWord_2272540
  simp only [CollatzResearch.WordTrace]
  refine ⟨41443171593491586888691537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55257562124655449184922049 41443171593491586888691537)
  ·
    refine ⟨31082378695118690166518653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41443171593491586888691537 31082378695118690166518653)
    ·
      refine ⟨11655892010669508812444495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31082378695118690166518653 11655892010669508812444495)
      ·
        refine ⟨17483838016004263218666743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11655892010669508812444495 17483838016004263218666743)
        ·
          refine ⟨26225757024006394828000115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17483838016004263218666743 26225757024006394828000115)
          ·
            refine ⟨39338635536009592242000173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26225757024006394828000115 39338635536009592242000173)
            ·
              refine ⟨14751988326003597090750065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39338635536009592242000173 14751988326003597090750065)
              ·
                refine ⟨11063991244502697818062549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14751988326003597090750065 11063991244502697818062549)
                ·
                  refine ⟨259312294793031980110841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11063991244502697818062549 259312294793031980110841)
                  ·
                    rfl

theorem cell22_2272540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_2272540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272540 prefixEnd_2272540 := by exact prefixLift 2272540
  have htrace : WordTrace (prefixWord ++ tailWord_2272540) baseStart_2272540 baseEnd_2272540 := by
    simpa [prefixWord, tailWord_2272540, baseEnd_2272540] using wordTrace_append hprefix tailTrace_2272540
  have hstable : (prefixWord ++ tailWord_2272540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272540).length < 2 ^ (prefixWord ++ tailWord_2272540).sum := by decide
  have hdescent : baseEnd_2272540 < baseStart_2272540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272585 : List Nat := [1, 2, 1, 1, 2, 3, 2, 4, 6]
def baseStart_2272585 : Nat := 118140960795 + 2272585 * 2 ^ 59
def prefixEnd_2272585 : Nat := 4983230072969 + 3 ^ 40 * 2272585 * 2
def baseEnd_2272585 : Nat := 259317429599576940985795

theorem tailTrace_2272585 : CollatzResearch.WordTrace tailWord_2272585 prefixEnd_2272585 259317429599576940985795 := by
  unfold tailWord_2272585
  simp only [CollatzResearch.WordTrace]
  refine ⟨82887984471820146462771209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55258656314546764308514139 82887984471820146462771209)
  ·
    refine ⟨62165988353865109847078407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82887984471820146462771209 62165988353865109847078407)
    ·
      refine ⟨93248982530797664770617611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62165988353865109847078407 93248982530797664770617611)
      ·
        refine ⟨139873473796196497155926417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93248982530797664770617611 139873473796196497155926417)
        ·
          refine ⟨104905105347147372866944813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139873473796196497155926417 104905105347147372866944813)
          ·
            refine ⟨39339414505180264825104305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104905105347147372866944813 39339414505180264825104305)
            ·
              refine ⟨29504560878885198618828229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39339414505180264825104305 29504560878885198618828229)
              ·
                refine ⟨5532105164790974741030293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29504560878885198618828229 5532105164790974741030293)
                ·
                  refine ⟨259317429599576940985795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5532105164790974741030293 259317429599576940985795)
                  ·
                    rfl

theorem cell22_2272585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 6].length) (baseStart_2272585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272585 prefixEnd_2272585 := by exact prefixLift 2272585
  have htrace : WordTrace (prefixWord ++ tailWord_2272585) baseStart_2272585 baseEnd_2272585 := by
    simpa [prefixWord, tailWord_2272585, baseEnd_2272585] using wordTrace_append hprefix tailTrace_2272585
  have hstable : (prefixWord ++ tailWord_2272585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272585).length < 2 ^ (prefixWord ++ tailWord_2272585).sum := by decide
  have hdescent : baseEnd_2272585 < baseStart_2272585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272781 : List Nat := [1, 7, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_2272781 : Nat := 118140960795 + 2272781 * 2 ^ 59
def prefixEnd_2272781 : Nat := 4983230072969 + 3 ^ 40 * 2272781 * 2
def baseEnd_2272781 : Nat := 778019383604251645056785

theorem tailTrace_2272781 : CollatzResearch.WordTrace tailWord_2272781 prefixEnd_2272781 778019383604251645056785 := by
  unfold tailWord_2272781
  simp only [CollatzResearch.WordTrace]
  refine ⟨82895133179110071936906197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55263422119406714624604131 82895133179110071936906197)
  ·
    refine ⟨1942854683885392311021239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 82895133179110071936906197 1942854683885392311021239)
    ·
      refine ⟨2914282025828088466531859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1942854683885392311021239 2914282025828088466531859)
      ·
        refine ⟨4371423038742132699797789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2914282025828088466531859 4371423038742132699797789)
        ·
          refine ⟨1639283639528299762424171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4371423038742132699797789 1639283639528299762424171)
          ·
            refine ⟨2458925459292449643636257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1639283639528299762424171 2458925459292449643636257)
            ·
              refine ⟨1844194094469337232727193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2458925459292449643636257 1844194094469337232727193)
              ·
                refine ⟨1383145570852002924545395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1844194094469337232727193 1383145570852002924545395)
                ·
                  refine ⟨2074718356278004386818093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383145570852002924545395 2074718356278004386818093)
                  ·
                    refine ⟨778019383604251645056785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2074718356278004386818093 778019383604251645056785)
                    ·
                      rfl

theorem cell22_2272781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_2272781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272781 prefixEnd_2272781 := by exact prefixLift 2272781
  have htrace : WordTrace (prefixWord ++ tailWord_2272781) baseStart_2272781 baseEnd_2272781 := by
    simpa [prefixWord, tailWord_2272781, baseEnd_2272781] using wordTrace_append hprefix tailTrace_2272781
  have hstable : (prefixWord ++ tailWord_2272781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272781).length < 2 ^ (prefixWord ++ tailWord_2272781).sum := by decide
  have hdescent : baseEnd_2272781 < baseStart_2272781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272782 : List Nat := [4, 1, 1, 2, 14]
def baseStart_2272782 : Nat := 118140960795 + 2272782 * 2 ^ 59
def prefixEnd_2272782 : Nat := 4983230072969 + 3 ^ 40 * 2272782 * 2
def baseEnd_2272782 : Nat := 3201727267179785908567

theorem tailTrace_2272782 : CollatzResearch.WordTrace tailWord_2272782 prefixEnd_2272782 3201727267179785908567 := by
  unfold tailWord_2272782
  simp only [CollatzResearch.WordTrace]
  refine ⟨10361896206513306138461575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55263446434737632738461733 10361896206513306138461575)
  ·
    refine ⟨15542844309769959207692363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10361896206513306138461575 15542844309769959207692363)
    ·
      refine ⟨23314266464654938811538545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15542844309769959207692363 23314266464654938811538545)
      ·
        refine ⟨17485699848491204108653909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23314266464654938811538545 17485699848491204108653909)
        ·
          refine ⟨3201727267179785908567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 17485699848491204108653909 3201727267179785908567)
          ·
            rfl

theorem cell22_2272782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 14].length) (baseStart_2272782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272782 prefixEnd_2272782 := by exact prefixLift 2272782
  have htrace : WordTrace (prefixWord ++ tailWord_2272782) baseStart_2272782 baseEnd_2272782 := by
    simpa [prefixWord, tailWord_2272782, baseEnd_2272782] using wordTrace_append hprefix tailTrace_2272782
  have hstable : (prefixWord ++ tailWord_2272782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272782).length < 2 ^ (prefixWord ++ tailWord_2272782).sum := by decide
  have hdescent : baseEnd_2272782 < baseStart_2272782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272844 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 7]
def baseStart_2272844 : Nat := 118140960795 + 2272844 * 2 ^ 59
def prefixEnd_2272844 : Nat := 4983230072969 + 3 ^ 40 * 2272844 * 2
def baseEnd_2272844 : Nat := 259346983263913493577197

theorem tailTrace_2272844 : CollatzResearch.WordTrace tailWord_2272844 prefixEnd_2272844 259346983263913493577197 := by
  unfold tailWord_2272844
  simp only [CollatzResearch.WordTrace]
  refine ⟨41448715488940916848224793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55264953985254555797633057 41448715488940916848224793)
  ·
    refine ⟨31086536616705687636168595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41448715488940916848224793 31086536616705687636168595)
    ·
      refine ⟨46629804925058531454252893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31086536616705687636168595 46629804925058531454252893)
      ·
        refine ⟨17486176846896949295344835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46629804925058531454252893 17486176846896949295344835)
        ·
          refine ⟨26229265270345423943017253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17486176846896949295344835 26229265270345423943017253)
          ·
            refine ⟨4917987238189766989315735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26229265270345423943017253 4917987238189766989315735)
            ·
              refine ⟨7376980857284650483973603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4917987238189766989315735 7376980857284650483973603)
              ·
                refine ⟨11065471285926975725960405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7376980857284650483973603 11065471285926975725960405)
                ·
                  refine ⟨259346983263913493577197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11065471285926975725960405 259346983263913493577197)
                  ·
                    rfl

theorem cell22_2272844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_2272844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272844 prefixEnd_2272844 := by exact prefixLift 2272844
  have htrace : WordTrace (prefixWord ++ tailWord_2272844) baseStart_2272844 baseEnd_2272844 := by
    simpa [prefixWord, tailWord_2272844, baseEnd_2272844] using wordTrace_append hprefix tailTrace_2272844
  have hstable : (prefixWord ++ tailWord_2272844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272844).length < 2 ^ (prefixWord ++ tailWord_2272844).sum := by decide
  have hdescent : baseEnd_2272844 < baseStart_2272844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272854 : List Nat := [5, 2, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_2272854 : Nat := 118140960795 + 2272854 * 2 ^ 59
def prefixEnd_2272854 : Nat := 4983230072969 + 3 ^ 40 * 2272854 * 2
def baseEnd_2272854 : Nat := 778044372996103787981561

theorem tailTrace_2272854 : CollatzResearch.WordTrace tailWord_2272854 prefixEnd_2272854 778044372996103787981561 := by
  unfold tailWord_2272854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5181112231740350337769601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55265197138563736936209077 5181112231740350337769601)
  ·
    refine ⟨3885834173805262753327201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5181112231740350337769601 3885834173805262753327201)
    ·
      refine ⟨2914375630353947064995401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3885834173805262753327201 2914375630353947064995401)
      ·
        refine ⟨2185781722765460298746551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2914375630353947064995401 2185781722765460298746551)
        ·
          refine ⟨3278672584148190448119827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2185781722765460298746551 3278672584148190448119827)
          ·
            refine ⟨4918008876222285672179741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3278672584148190448119827 4918008876222285672179741)
            ·
              refine ⟨1844253328583357127067403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4918008876222285672179741 1844253328583357127067403)
              ·
                refine ⟨2766379992875035690601105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1844253328583357127067403 2766379992875035690601105)
                ·
                  refine ⟨2074784994656276767950829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2766379992875035690601105 2074784994656276767950829)
                  ·
                    refine ⟨778044372996103787981561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2074784994656276767950829 778044372996103787981561)
                    ·
                      rfl

theorem cell22_2272854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_2272854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272854 prefixEnd_2272854 := by exact prefixLift 2272854
  have htrace : WordTrace (prefixWord ++ tailWord_2272854) baseStart_2272854 baseEnd_2272854 := by
    simpa [prefixWord, tailWord_2272854, baseEnd_2272854] using wordTrace_append hprefix tailTrace_2272854
  have hstable : (prefixWord ++ tailWord_2272854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272854).length < 2 ^ (prefixWord ++ tailWord_2272854).sum := by decide
  have hdescent : baseEnd_2272854 < baseStart_2272854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272906 : List Nat := [3, 1, 2, 3, 2, 1, 3, 1, 6]
def baseStart_2272906 : Nat := 118140960795 + 2272906 * 2 ^ 59
def prefixEnd_2272906 : Nat := 4983230072969 + 3 ^ 40 * 2272906 * 2
def baseEnd_2272906 : Nat := 259354057886264328560467

theorem tailTrace_2272906 : CollatzResearch.WordTrace tailWord_2272906 prefixEnd_2272906 259354057886264328560467 := by
  unfold tailWord_2272906
  simp only [CollatzResearch.WordTrace]
  refine ⟨20724923075914304571301643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55266461535771478856804381 20724923075914304571301643)
  ·
    refine ⟨31087384613871456856952465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20724923075914304571301643 31087384613871456856952465)
    ·
      refine ⟨23315538460403592642714349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31087384613871456856952465 23315538460403592642714349)
      ·
        refine ⟨8743326922651347241017881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23315538460403592642714349 8743326922651347241017881)
        ·
          refine ⟨6557495191988510430763411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8743326922651347241017881 6557495191988510430763411)
          ·
            refine ⟨9836242787982765646145117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6557495191988510430763411 9836242787982765646145117)
            ·
              refine ⟨3688591045493537117304419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9836242787982765646145117 3688591045493537117304419)
              ·
                refine ⟨5532886568240305675956629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3688591045493537117304419 5532886568240305675956629)
                ·
                  refine ⟨259354057886264328560467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5532886568240305675956629 259354057886264328560467)
                  ·
                    rfl

theorem cell22_2272906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_2272906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272906 prefixEnd_2272906 := by exact prefixLift 2272906
  have htrace : WordTrace (prefixWord ++ tailWord_2272906) baseStart_2272906 baseEnd_2272906 := by
    simpa [prefixWord, tailWord_2272906, baseEnd_2272906] using wordTrace_append hprefix tailTrace_2272906
  have hstable : (prefixWord ++ tailWord_2272906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272906).length < 2 ^ (prefixWord ++ tailWord_2272906).sum := by decide
  have hdescent : baseEnd_2272906 < baseStart_2272906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2272942 : List Nat := [4, 1, 4, 1, 2, 1, 3, 1, 1, 4]
def baseStart_2272942 : Nat := 118140960795 + 2272942 * 2 ^ 59
def prefixEnd_2272942 : Nat := 4983230072969 + 3 ^ 40 * 2272942 * 2
def baseEnd_2272942 : Nat := 778074497194500891781291

theorem tailTrace_2272942 : CollatzResearch.WordTrace tailWord_2272942 prefixEnd_2272942 778074497194500891781291 := by
  unfold tailWord_2272942
  simp only [CollatzResearch.WordTrace]
  refine ⟨10362625666440849554189635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55267336887684530955678053 10362625666440849554189635)
  ·
    refine ⟨15543938499661274331284453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10362625666440849554189635 15543938499661274331284453)
    ·
      refine ⟨2914488468686488937115835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15543938499661274331284453 2914488468686488937115835)
      ·
        refine ⟨4371732703029733405673753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2914488468686488937115835 4371732703029733405673753)
        ·
          refine ⟨3278799527272300054255315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4371732703029733405673753 3278799527272300054255315)
          ·
            refine ⟨4918199290908450081382973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3278799527272300054255315 4918199290908450081382973)
            ·
              refine ⟨1844324734090668780518615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4918199290908450081382973 1844324734090668780518615)
              ·
                refine ⟨2766487101136003170777923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1844324734090668780518615 2766487101136003170777923)
                ·
                  refine ⟨4149730651704004756166885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766487101136003170777923 4149730651704004756166885)
                  ·
                    refine ⟨778074497194500891781291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4149730651704004756166885 778074497194500891781291)
                    ·
                      rfl

theorem cell22_2272942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_2272942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2272942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2272942 prefixEnd_2272942 := by exact prefixLift 2272942
  have htrace : WordTrace (prefixWord ++ tailWord_2272942) baseStart_2272942 baseEnd_2272942 := by
    simpa [prefixWord, tailWord_2272942, baseEnd_2272942] using wordTrace_append hprefix tailTrace_2272942
  have hstable : (prefixWord ++ tailWord_2272942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2272942).length < 2 ^ (prefixWord ++ tailWord_2272942).sum := by decide
  have hdescent : baseEnd_2272942 < baseStart_2272942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2272942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273000 : List Nat := [2, 1, 4, 1, 3, 1, 1, 5, 1, 3]
def baseStart_2273000 : Nat := 118140960795 + 2273000 * 2 ^ 59
def prefixEnd_2273000 : Nat := 4983230072969 + 3 ^ 40 * 2273000 * 2
def baseEnd_2273000 : Nat := 778094351779808073831113

theorem tailTrace_2273000 : CollatzResearch.WordTrace tailWord_2273000 prefixEnd_2273000 778094351779808073831113 := by
  unfold tailWord_2273000
  simp only [CollatzResearch.WordTrace]
  refine ⟨41451560382658336169564227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55268747176877781559418969 41451560382658336169564227)
  ·
    refine ⟨62177340573987504254346341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41451560382658336169564227 62177340573987504254346341)
    ·
      refine ⟨11658251357622657047689939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62177340573987504254346341 11658251357622657047689939)
      ·
        refine ⟨17487377036433985571534909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11658251357622657047689939 17487377036433985571534909)
        ·
          refine ⟨6557766388662744589325591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17487377036433985571534909 6557766388662744589325591)
          ·
            refine ⟨9836649582994116883988387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6557766388662744589325591 9836649582994116883988387)
            ·
              refine ⟨14754974374491175325982581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9836649582994116883988387 14754974374491175325982581)
              ·
                refine ⟨1383278847608547686810867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14754974374491175325982581 1383278847608547686810867)
                ·
                  refine ⟨2074918271412821530216301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383278847608547686810867 2074918271412821530216301)
                  ·
                    refine ⟨778094351779808073831113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2074918271412821530216301 778094351779808073831113)
                    ·
                      rfl

theorem cell22_2273000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_2273000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273000 prefixEnd_2273000 := by exact prefixLift 2273000
  have htrace : WordTrace (prefixWord ++ tailWord_2273000) baseStart_2273000 baseEnd_2273000 := by
    simpa [prefixWord, tailWord_2273000, baseEnd_2273000] using wordTrace_append hprefix tailTrace_2273000
  have hstable : (prefixWord ++ tailWord_2273000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273000).length < 2 ^ (prefixWord ++ tailWord_2273000).sum := by decide
  have hdescent : baseEnd_2273000 < baseStart_2273000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273024 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 10]
def baseStart_2273024 : Nat := 118140960795 + 2273024 * 2 ^ 59
def prefixEnd_2273024 : Nat := 4983230072969 + 3 ^ 40 * 2273024 * 2
def baseEnd_2273024 : Nat := 259367522490093337077013

theorem tailTrace_2273024 : CollatzResearch.WordTrace tailWord_2273024 prefixEnd_2273024 259367522490093337077013 := by
  unfold tailWord_2273024
  simp only [CollatzResearch.WordTrace]
  refine ⟨41451998058614862219001063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55269330744819816292001417 41451998058614862219001063)
  ·
    refine ⟨62177997087922293328501595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41451998058614862219001063 62177997087922293328501595)
    ·
      refine ⟨93266995631883439992752393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62177997087922293328501595 93266995631883439992752393)
      ·
        refine ⟨69950246723912579994564295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93266995631883439992752393 69950246723912579994564295)
        ·
          refine ⟨104925370085868869991846443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69950246723912579994564295 104925370085868869991846443)
          ·
            refine ⟨157388055128803304987769665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104925370085868869991846443 157388055128803304987769665)
            ·
              refine ⟨118041041346602478740827249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157388055128803304987769665 118041041346602478740827249)
              ·
                refine ⟨88530781009951859055620437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118041041346602478740827249 88530781009951859055620437)
                ·
                  refine ⟨259367522490093337077013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 88530781009951859055620437 259367522490093337077013)
                  ·
                    rfl

theorem cell22_2273024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 10].length) (baseStart_2273024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273024 prefixEnd_2273024 := by exact prefixLift 2273024
  have htrace : WordTrace (prefixWord ++ tailWord_2273024) baseStart_2273024 baseEnd_2273024 := by
    simpa [prefixWord, tailWord_2273024, baseEnd_2273024] using wordTrace_append hprefix tailTrace_2273024
  have hstable : (prefixWord ++ tailWord_2273024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273024).length < 2 ^ (prefixWord ++ tailWord_2273024).sum := by decide
  have hdescent : baseEnd_2273024 < baseStart_2273024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273056 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 3, 5]
def baseStart_2273056 : Nat := 118140960795 + 2273056 * 2 ^ 59
def prefixEnd_2273056 : Nat := 4983230072969 + 3 ^ 40 * 2273056 * 2
def baseEnd_2273056 : Nat := 778113521724242594430941

theorem tailTrace_2273056 : CollatzResearch.WordTrace tailWord_2273056 prefixEnd_2273056 778113521724242594430941 := by
  unfold tailWord_2273056
  simp only [CollatzResearch.WordTrace]
  refine ⟨41452581626556896951583511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55270108835409195935444681 41452581626556896951583511)
  ·
    refine ⟨62178872439835345427375267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41452581626556896951583511 62178872439835345427375267)
    ·
      refine ⟨93268308659753018141062901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62178872439835345427375267 93268308659753018141062901)
      ·
        refine ⟨8743903936851845450724647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93268308659753018141062901 8743903936851845450724647)
        ·
          refine ⟨13115855905277768176086971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8743903936851845450724647 13115855905277768176086971)
          ·
            refine ⟨19673783857916652264130457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13115855905277768176086971 19673783857916652264130457)
            ·
              refine ⟨14755337893437489198097843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19673783857916652264130457 14755337893437489198097843)
              ·
                refine ⟨22133006840156233797146765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14755337893437489198097843 22133006840156233797146765)
                ·
                  refine ⟨8299877565058587673930037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22133006840156233797146765 8299877565058587673930037)
                  ·
                    refine ⟨778113521724242594430941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8299877565058587673930037 778113521724242594430941)
                    ·
                      rfl

theorem cell22_2273056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_2273056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273056 prefixEnd_2273056 := by exact prefixLift 2273056
  have htrace : WordTrace (prefixWord ++ tailWord_2273056) baseStart_2273056 baseEnd_2273056 := by
    simpa [prefixWord, tailWord_2273056, baseEnd_2273056] using wordTrace_append hprefix tailTrace_2273056
  have hstable : (prefixWord ++ tailWord_2273056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273056).length < 2 ^ (prefixWord ++ tailWord_2273056).sum := by decide
  have hdescent : baseEnd_2273056 < baseStart_2273056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273071 : List Nat := [1, 1, 2, 1, 2, 1, 2, 6, 2, 4]
def baseStart_2273071 : Nat := 118140960795 + 2273071 * 2 ^ 59
def prefixEnd_2273071 : Nat := 4983230072969 + 3 ^ 40 * 2273071 * 2
def baseEnd_2273071 : Nat := 778118656530787555305895

theorem tailTrace_2273071 : CollatzResearch.WordTrace tailWord_2273071 prefixEnd_2273071 778118656530787555305895 := by
  unfold tailWord_2273071
  simp only [CollatzResearch.WordTrace]
  refine ⟨82905710348059451464963067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55270473565372967643308711 82905710348059451464963067)
  ·
    refine ⟨124358565522089177197444601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82905710348059451464963067 124358565522089177197444601)
    ·
      refine ⟨93268924141566882898083451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124358565522089177197444601 93268924141566882898083451)
      ·
        refine ⟨139903386212350324347125177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93268924141566882898083451 139903386212350324347125177)
        ·
          refine ⟨104927539659262743260343883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139903386212350324347125177 104927539659262743260343883)
          ·
            refine ⟨157391309488894114890515825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104927539659262743260343883 157391309488894114890515825)
            ·
              refine ⟨118043482116670586167886869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157391309488894114890515825 118043482116670586167886869)
              ·
                refine ⟨5533288224218933726619697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 118043482116670586167886869 5533288224218933726619697)
                ·
                  refine ⟨4149966168164200294964773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5533288224218933726619697 4149966168164200294964773)
                  ·
                    refine ⟨778118656530787555305895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4149966168164200294964773 778118656530787555305895)
                    ·
                      rfl

theorem cell22_2273071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_2273071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273071 prefixEnd_2273071 := by exact prefixLift 2273071
  have htrace : WordTrace (prefixWord ++ tailWord_2273071) baseStart_2273071 baseEnd_2273071 := by
    simpa [prefixWord, tailWord_2273071, baseEnd_2273071] using wordTrace_append hprefix tailTrace_2273071
  have hstable : (prefixWord ++ tailWord_2273071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273071).length < 2 ^ (prefixWord ++ tailWord_2273071).sum := by decide
  have hdescent : baseEnd_2273071 < baseStart_2273071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273073 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 4, 3]
def baseStart_2273073 : Nat := 118140960795 + 2273073 * 2 ^ 59
def prefixEnd_2273073 : Nat := 4983230072969 + 3 ^ 40 * 2273073 * 2
def baseEnd_2273073 : Nat := 778119341171660216755889

theorem tailTrace_2273073 : CollatzResearch.WordTrace tailWord_2273073 prefixEnd_2273073 778119341171660216755889 := by
  unfold tailWord_2273073
  simp only [CollatzResearch.WordTrace]
  refine ⟨82905783294052205806535873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55270522196034803871023915 82905783294052205806535873)
  ·
    refine ⟨62179337470539154354901905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82905783294052205806535873 62179337470539154354901905)
    ·
      refine ⟨46634503102904365766176429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62179337470539154354901905 46634503102904365766176429)
      ·
        refine ⟨17487938663589137162316161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46634503102904365766176429 17487938663589137162316161)
        ·
          refine ⟨13115953997691852871737121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17487938663589137162316161 13115953997691852871737121)
          ·
            refine ⟨9836965498268889653802841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13115953997691852871737121 9836965498268889653802841)
            ·
              refine ⟨7377724123701667240352131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9836965498268889653802841 7377724123701667240352131)
              ·
                refine ⟨11066586185552500860528197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7377724123701667240352131 11066586185552500860528197)
                ·
                  refine ⟨2074984909791093911349037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11066586185552500860528197 2074984909791093911349037)
                  ·
                    refine ⟨778119341171660216755889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2074984909791093911349037 778119341171660216755889)
                    ·
                      rfl

theorem cell22_2273073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_2273073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273073 prefixEnd_2273073 := by exact prefixLift 2273073
  have htrace : WordTrace (prefixWord ++ tailWord_2273073) baseStart_2273073 baseEnd_2273073 := by
    simpa [prefixWord, tailWord_2273073, baseEnd_2273073] using wordTrace_append hprefix tailTrace_2273073
  have hstable : (prefixWord ++ tailWord_2273073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273073).length < 2 ^ (prefixWord ++ tailWord_2273073).sum := by decide
  have hdescent : baseEnd_2273073 < baseStart_2273073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273075 : List Nat := [1, 1, 1, 2, 8, 1, 1, 1, 6]
def baseStart_2273075 : Nat := 118140960795 + 2273075 * 2 ^ 59
def prefixEnd_2273075 : Nat := 4983230072969 + 3 ^ 40 * 2273075 * 2
def baseEnd_2273075 : Nat := 259373341937510959401961

theorem tailTrace_2273075 : CollatzResearch.WordTrace tailWord_2273075 prefixEnd_2273075 259373341937510959401961 := by
  unfold tailWord_2273075
  simp only [CollatzResearch.WordTrace]
  refine ⟨82905856240044960148108679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55270570826696640098739119 82905856240044960148108679)
  ·
    refine ⟨124358784360067440222163019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82905856240044960148108679 124358784360067440222163019)
    ·
      refine ⟨186538176540101160333244529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124358784360067440222163019 186538176540101160333244529)
      ·
        refine ⟨139903632405075870249933397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186538176540101160333244529 139903632405075870249933397)
        ·
          refine ⟨1639495692246982854491407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 139903632405075870249933397 1639495692246982854491407)
          ·
            refine ⟨2459243538370474281737111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1639495692246982854491407 2459243538370474281737111)
            ·
              refine ⟨3688865307555711422605667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2459243538370474281737111 3688865307555711422605667)
              ·
                refine ⟨5533297961333567133908501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3688865307555711422605667 5533297961333567133908501)
                ·
                  refine ⟨259373341937510959401961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5533297961333567133908501 259373341937510959401961)
                  ·
                    rfl

theorem cell22_2273075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 6].length) (baseStart_2273075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273075 prefixEnd_2273075 := by exact prefixLift 2273075
  have htrace : WordTrace (prefixWord ++ tailWord_2273075) baseStart_2273075 baseEnd_2273075 := by
    simpa [prefixWord, tailWord_2273075, baseEnd_2273075] using wordTrace_append hprefix tailTrace_2273075
  have hstable : (prefixWord ++ tailWord_2273075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273075).length < 2 ^ (prefixWord ++ tailWord_2273075).sum := by decide
  have hdescent : baseEnd_2273075 < baseStart_2273075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273094 : List Nat := [6, 1, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_2273094 : Nat := 118140960795 + 2273094 * 2 ^ 59
def prefixEnd_2273094 : Nat := 4983230072969 + 3 ^ 40 * 2273094 * 2
def baseEnd_2273094 : Nat := 778126529900823161980825

theorem tailTrace_2273094 : CollatzResearch.WordTrace tailWord_2273094 prefixEnd_2273094 778126529900823161980825 := by
  unfold tailWord_2273094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2590829663343003949782823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55271032817984084262033557 2590829663343003949782823)
  ·
    refine ⟨3886244495014505924674235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2590829663343003949782823 3886244495014505924674235)
    ·
      refine ⟨5829366742521758887011353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3886244495014505924674235 5829366742521758887011353)
      ·
        refine ⟨4372025056891319165258515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5829366742521758887011353 4372025056891319165258515)
        ·
          refine ⟨6558037585336978747887773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4372025056891319165258515 6558037585336978747887773)
          ·
            refine ⟨2459264094501367030457915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6558037585336978747887773 2459264094501367030457915)
            ·
              refine ⟨3688896141752050545686873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2459264094501367030457915 3688896141752050545686873)
              ·
                refine ⟨2766672106314037909265155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3688896141752050545686873 2766672106314037909265155)
                ·
                  refine ⟨4150008159471056863897733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766672106314037909265155 4150008159471056863897733)
                  ·
                    refine ⟨778126529900823161980825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4150008159471056863897733 778126529900823161980825)
                    ·
                      rfl

theorem cell22_2273094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_2273094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273094 prefixEnd_2273094 := by exact prefixLift 2273094
  have htrace : WordTrace (prefixWord ++ tailWord_2273094) baseStart_2273094 baseEnd_2273094 := by
    simpa [prefixWord, tailWord_2273094, baseEnd_2273094] using wordTrace_append hprefix tailTrace_2273094
  have hstable : (prefixWord ++ tailWord_2273094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273094).length < 2 ^ (prefixWord ++ tailWord_2273094).sum := by decide
  have hdescent : baseEnd_2273094 < baseStart_2273094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273146 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 1, 7]
def baseStart_2273146 : Nat := 118140960795 + 2273146 * 2 ^ 59
def prefixEnd_2273146 : Nat := 4983230072969 + 3 ^ 40 * 2273146 * 2
def baseEnd_2273146 : Nat := 778144330563512359680665

theorem tailTrace_2273146 : CollatzResearch.WordTrace tailWord_2273146 prefixEnd_2273146 778144330563512359680665 := by
  unfold tailWord_2273146
  simp only [CollatzResearch.WordTrace]
  refine ⟨20727111455696934818485823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55272297215191826182628861 20727111455696934818485823)
  ·
    refine ⟨31090667183545402227728735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20727111455696934818485823 31090667183545402227728735)
    ·
      refine ⟨46636000775318103341593103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31090667183545402227728735 46636000775318103341593103)
      ·
        refine ⟨69954001162977155012389655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46636000775318103341593103 69954001162977155012389655)
        ·
          refine ⟨104931001744465732518584483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69954001162977155012389655 104931001744465732518584483)
          ·
            refine ⟨157396502616698598777876725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104931001744465732518584483 157396502616698598777876725)
            ·
              refine ⟨14755922120315493635425943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 157396502616698598777876725 14755922120315493635425943)
              ·
                refine ⟨22133883180473240453138915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14755922120315493635425943 22133883180473240453138915)
                ·
                  refine ⟨33200824770709860679708373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22133883180473240453138915 33200824770709860679708373)
                  ·
                    refine ⟨778144330563512359680665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33200824770709860679708373 778144330563512359680665)
                    ·
                      rfl

theorem cell22_2273146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_2273146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273146 prefixEnd_2273146 := by exact prefixLift 2273146
  have htrace : WordTrace (prefixWord ++ tailWord_2273146) baseStart_2273146 baseEnd_2273146 := by
    simpa [prefixWord, tailWord_2273146, baseEnd_2273146] using wordTrace_append hprefix tailTrace_2273146
  have hstable : (prefixWord ++ tailWord_2273146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273146).length < 2 ^ (prefixWord ++ tailWord_2273146).sum := by decide
  have hdescent : baseEnd_2273146 < baseStart_2273146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273182 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 7]
def baseStart_2273182 : Nat := 118140960795 + 2273182 * 2 ^ 59
def prefixEnd_2273182 : Nat := 4983230072969 + 3 ^ 40 * 2273182 * 2
def baseEnd_2273182 : Nat := 259385551366406755260185

theorem tailTrace_2273182 : CollatzResearch.WordTrace tailWord_2273182 prefixEnd_2273182 259385551366406755260185 := by
  unfold tailWord_2273182
  simp only [CollatzResearch.WordTrace]
  refine ⟨10363719856332164677781725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55273172567104878281502533 10363719856332164677781725)
  ·
    refine ⟨3886394946124561754168147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10363719856332164677781725 3886394946124561754168147)
    ·
      refine ⟨5829592419186842631252221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3886394946124561754168147 5829592419186842631252221)
      ·
        refine ⟨2186097157195065986719583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5829592419186842631252221 2186097157195065986719583)
        ·
          refine ⟨3279145735792598980079375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2186097157195065986719583 3279145735792598980079375)
          ·
            refine ⟨4918718603688898470119063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3279145735792598980079375 4918718603688898470119063)
            ·
              refine ⟨7378077905533347705178595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4918718603688898470119063 7378077905533347705178595)
              ·
                refine ⟨11067116858300021557767893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7378077905533347705178595 11067116858300021557767893)
                ·
                  refine ⟨259385551366406755260185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11067116858300021557767893 259385551366406755260185)
                  ·
                    rfl

theorem cell22_2273182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_2273182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273182 prefixEnd_2273182 := by exact prefixLift 2273182
  have htrace : WordTrace (prefixWord ++ tailWord_2273182) baseStart_2273182 baseEnd_2273182 := by
    simpa [prefixWord, tailWord_2273182, baseEnd_2273182] using wordTrace_append hprefix tailTrace_2273182
  have hstable : (prefixWord ++ tailWord_2273182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273182).length < 2 ^ (prefixWord ++ tailWord_2273182).sum := by decide
  have hdescent : baseEnd_2273182 < baseStart_2273182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273223 : List Nat := [1, 1, 4, 1, 1, 2, 1, 5, 2, 4]
def baseStart_2273223 : Nat := 118140960795 + 2273223 * 2 ^ 59
def prefixEnd_2273223 : Nat := 4983230072969 + 3 ^ 40 * 2273223 * 2
def baseEnd_2273223 : Nat := 778170689237109825505429

theorem tailTrace_2273223 : CollatzResearch.WordTrace tailWord_2273223 prefixEnd_2273223 778170689237109825505429 := by
  unfold tailWord_2273223
  simp only [CollatzResearch.WordTrace]
  refine ⟨82911254243508781424496323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55274169495672520949664215 82911254243508781424496323)
  ·
    refine ⟨124366881365263172136744485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82911254243508781424496323 124366881365263172136744485)
    ·
      refine ⟨23318790255986844775639591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124366881365263172136744485 23318790255986844775639591)
      ·
        refine ⟨34978185383980267163459387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23318790255986844775639591 34978185383980267163459387)
        ·
          refine ⟨52467278075970400745189081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34978185383980267163459387 52467278075970400745189081)
          ·
            refine ⟨39350458556977800558891811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52467278075970400745189081 39350458556977800558891811)
            ·
              refine ⟨59025687835466700838337717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39350458556977800558891811 59025687835466700838337717)
              ·
                refine ⟨5533658234575003203594161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59025687835466700838337717 5533658234575003203594161)
                ·
                  refine ⟨4150243675931252402695621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5533658234575003203594161 4150243675931252402695621)
                  ·
                    refine ⟨778170689237109825505429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4150243675931252402695621 778170689237109825505429)
                    ·
                      rfl

theorem cell22_2273223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_2273223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273223 prefixEnd_2273223 := by exact prefixLift 2273223
  have htrace : WordTrace (prefixWord ++ tailWord_2273223) baseStart_2273223 baseEnd_2273223 := by
    simpa [prefixWord, tailWord_2273223, baseEnd_2273223] using wordTrace_append hprefix tailTrace_2273223
  have hstable : (prefixWord ++ tailWord_2273223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273223).length < 2 ^ (prefixWord ++ tailWord_2273223).sum := by decide
  have hdescent : baseEnd_2273223 < baseStart_2273223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273255 : List Nat := [1, 1, 5, 2, 3, 1, 2, 7]
def baseStart_2273255 : Nat := 118140960795 + 2273255 * 2 ^ 59
def prefixEnd_2273255 : Nat := 4983230072969 + 3 ^ 40 * 2273255 * 2
def baseEnd_2273255 : Nat := 86464627054563600967259

theorem tailTrace_2273255 : CollatzResearch.WordTrace tailWord_2273255 prefixEnd_2273255 86464627054563600967259 := by
  unfold tailWord_2273255
  simp only [CollatzResearch.WordTrace]
  refine ⟨82912421379392850889661219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55274947586261900593107479 82912421379392850889661219)
  ·
    refine ⟨124368632069089276334491829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82912421379392850889661219 124368632069089276334491829)
    ·
      refine ⟨11659559256477119656358609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124368632069089276334491829 11659559256477119656358609)
      ·
        refine ⟨8744669442357839742268957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11659559256477119656358609 8744669442357839742268957)
        ·
          refine ⟨3279251040884189903350859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8744669442357839742268957 3279251040884189903350859)
          ·
            refine ⟨4918876561326284855026289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3279251040884189903350859 4918876561326284855026289)
            ·
              refine ⟨3689157420994713641269717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4918876561326284855026289 3689157420994713641269717)
              ·
                refine ⟨86464627054563600967259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3689157420994713641269717 86464627054563600967259)
                ·
                  rfl

theorem cell22_2273255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 7].length) (baseStart_2273255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273255 prefixEnd_2273255 := by exact prefixLift 2273255
  have htrace : WordTrace (prefixWord ++ tailWord_2273255) baseStart_2273255 baseEnd_2273255 := by
    simpa [prefixWord, tailWord_2273255, baseEnd_2273255] using wordTrace_append hprefix tailTrace_2273255
  have hstable : (prefixWord ++ tailWord_2273255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273255).length < 2 ^ (prefixWord ++ tailWord_2273255).sum := by decide
  have hdescent : baseEnd_2273255 < baseStart_2273255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2273293 : List Nat := [1, 7, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_2273293 : Nat := 118140960795 + 2273293 * 2 ^ 59
def prefixEnd_2273293 : Nat := 4983230072969 + 3 ^ 40 * 2273293 * 2
def baseEnd_2273293 : Nat := 778194651667652976255215

theorem tailTrace_2273293 : CollatzResearch.WordTrace tailWord_2273293 prefixEnd_2273293 778194651667652976255215 := by
  unfold tailWord_2273293
  simp only [CollatzResearch.WordTrace]
  refine ⟨82913807353255183379544533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55275871568836788919696355 82913807353255183379544533)
  ·
    refine ⟨1943292359841918360458075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 82913807353255183379544533 1943292359841918360458075)
    ·
      refine ⟨2914938539762877540687113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1943292359841918360458075 2914938539762877540687113)
      ·
        refine ⟨2186203904822158155515335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2914938539762877540687113 2186203904822158155515335)
        ·
          refine ⟨3279305857233237233273003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2186203904822158155515335 3279305857233237233273003)
          ·
            refine ⟨4918958785849855849909505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3279305857233237233273003 4918958785849855849909505)
            ·
              refine ⟨3689219089387391887432129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4918958785849855849909505 3689219089387391887432129)
              ·
                refine ⟨2766914317040543915574097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3689219089387391887432129 2766914317040543915574097)
                ·
                  refine ⟨2075185737780407936680573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2766914317040543915574097 2075185737780407936680573)
                  ·
                    refine ⟨778194651667652976255215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2075185737780407936680573 778194651667652976255215)
                    ·
                      rfl

theorem cell22_2273293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_2273293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2273293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2273293 prefixEnd_2273293 := by exact prefixLift 2273293
  have htrace : WordTrace (prefixWord ++ tailWord_2273293) baseStart_2273293 baseEnd_2273293 := by
    simpa [prefixWord, tailWord_2273293, baseEnd_2273293] using wordTrace_append hprefix tailTrace_2273293
  have hstable : (prefixWord ++ tailWord_2273293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2273293).length < 2 ^ (prefixWord ++ tailWord_2273293).sum := by decide
  have hdescent : baseEnd_2273293 < baseStart_2273293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2273293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
