import V185TrunkScan21Chunk034

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_424093 : List Nat := [1, 4, 2, 1, 1, 4, 3, 5]
def baseStart_424093 : Nat := 118140960795 + 424093 * 2 ^ 59
def prefixEnd_424093 : Nat := 4983230072969 + 3 ^ 40 * 424093 * 2
def baseEnd_424093 : Nat := 32261266845528069316613

theorem tailTrace_424093 : CollatzResearch.WordTrace tailWord_424093 prefixEnd_424093 32261266845528069316613 := by
  unfold tailWord_424093
  simp only [CollatzResearch.WordTrace]
  refine ⟨15467942452590965163116933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10311961635060643442077955 15467942452590965163116933)
  ·
    refine ⟨2900239209860805968084425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15467942452590965163116933 2900239209860805968084425)
    ·
      refine ⟨2175179407395604476063319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2900239209860805968084425 2175179407395604476063319)
      ·
        refine ⟨3262769111093406714094979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2175179407395604476063319 3262769111093406714094979)
        ·
          refine ⟨4894153666640110071142469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3262769111093406714094979 4894153666640110071142469)
          ·
            refine ⟨917653812495020638339213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4894153666640110071142469 917653812495020638339213)
            ·
              refine ⟨344120179685632739377205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 917653812495020638339213 344120179685632739377205)
              ·
                refine ⟨32261266845528069316613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 344120179685632739377205 32261266845528069316613)
                ·
                  rfl

theorem cell21_424093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 5].length) (baseStart_424093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424093 prefixEnd_424093 := by exact prefixLift 424093
  have htrace : WordTrace (prefixWord ++ tailWord_424093) baseStart_424093 baseEnd_424093 := by
    simpa [prefixWord, tailWord_424093, baseEnd_424093] using wordTrace_append hprefix tailTrace_424093
  have hstable : (prefixWord ++ tailWord_424093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424093).length < 2 ^ (prefixWord ++ tailWord_424093).sum := by decide
  have hdescent : baseEnd_424093 < baseStart_424093 := by decide
  rcases family_descends (prefixWord ++ tailWord_424093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424110 : List Nat := [4, 1, 4, 2, 1, 1, 8]
def baseStart_424110 : Nat := 118140960795 + 424110 * 2 ^ 59
def prefixEnd_424110 : Nat := 4983230072969 + 3 ^ 40 * 424110 * 2
def baseEnd_424110 : Nat := 10754186685355106240719

theorem tailTrace_424110 : CollatzResearch.WordTrace tailWord_424110 prefixEnd_424110 10754186685355106240719 := by
  unfold tailWord_424110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1933570311691172133310723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10312374995686251377657189 1933570311691172133310723)
  ·
    refine ⟨2900355467536758199966085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1933570311691172133310723 2900355467536758199966085)
    ·
      refine ⟨543816650163142162493641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2900355467536758199966085 543816650163142162493641)
      ·
        refine ⟨407862487622356621870231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543816650163142162493641 407862487622356621870231)
        ·
          refine ⟨611793731433534932805347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407862487622356621870231 611793731433534932805347)
          ·
            refine ⟨917690597150302399208021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611793731433534932805347 917690597150302399208021)
            ·
              refine ⟨10754186685355106240719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 917690597150302399208021 10754186685355106240719)
              ·
                rfl

theorem cell21_424110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 8].length) (baseStart_424110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424110 prefixEnd_424110 := by exact prefixLift 424110
  have htrace : WordTrace (prefixWord ++ tailWord_424110) baseStart_424110 baseEnd_424110 := by
    simpa [prefixWord, tailWord_424110, baseEnd_424110] using wordTrace_append hprefix tailTrace_424110
  have hstable : (prefixWord ++ tailWord_424110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424110).length < 2 ^ (prefixWord ++ tailWord_424110).sum := by decide
  have hdescent : baseEnd_424110 < baseStart_424110 := by decide
  rcases family_descends (prefixWord ++ tailWord_424110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424121 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 6]
def baseStart_424121 : Nat := 118140960795 + 424121 * 2 ^ 59
def prefixEnd_424121 : Nat := 4983230072969 + 3 ^ 40 * 424121 * 2
def baseEnd_424121 : Nat := 96790190518062381483115

theorem tailTrace_424121 : CollatzResearch.WordTrace tailWord_424121 prefixEnd_424121 96790190518062381483115 := by
  unfold tailWord_424121
  simp only [CollatzResearch.WordTrace]
  refine ⟨15468963696489525945136217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10312642464326350630090811 15468963696489525945136217)
  ·
    refine ⟨11601722772367144458852163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15468963696489525945136217 11601722772367144458852163)
    ·
      refine ⟨17402584158550716688278245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11601722772367144458852163 17402584158550716688278245)
      ·
        refine ⟨3262984529728259379052171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17402584158550716688278245 3262984529728259379052171)
        ·
          refine ⟨4894476794592389068578257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3262984529728259379052171 4894476794592389068578257)
          ·
            refine ⟨3670857595944291801433693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4894476794592389068578257 3670857595944291801433693)
            ·
              refine ⟨1376571598479109425537635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3670857595944291801433693 1376571598479109425537635)
              ·
                refine ⟨2064857397718664138306453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1376571598479109425537635 2064857397718664138306453)
                ·
                  refine ⟨96790190518062381483115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2064857397718664138306453 96790190518062381483115)
                  ·
                    rfl

theorem cell21_424121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_424121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424121 prefixEnd_424121 := by exact prefixLift 424121
  have htrace : WordTrace (prefixWord ++ tailWord_424121) baseStart_424121 baseEnd_424121 := by
    simpa [prefixWord, tailWord_424121, baseEnd_424121] using wordTrace_append hprefix tailTrace_424121
  have hstable : (prefixWord ++ tailWord_424121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424121).length < 2 ^ (prefixWord ++ tailWord_424121).sum := by decide
  have hdescent : baseEnd_424121 < baseStart_424121 := by decide
  rcases family_descends (prefixWord ++ tailWord_424121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424124 : List Nat := [2, 2, 2, 3, 3, 1, 2, 1, 5]
def baseStart_424124 : Nat := 118140960795 + 424124 * 2 ^ 59
def prefixEnd_424124 : Nat := 4983230072969 + 3 ^ 40 * 424124 * 2
def baseEnd_424124 : Nat := 96790875158935042933109

theorem tailTrace_424124 : CollatzResearch.WordTrace tailWord_424124 prefixEnd_424124 96790875158935042933109 := by
  unfold tailWord_424124
  simp only [CollatzResearch.WordTrace]
  refine ⟨7734536557739328728747713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10312715410319104971663617 7734536557739328728747713)
  ·
    refine ⟨5800902418304496546560785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7734536557739328728747713 5800902418304496546560785)
    ·
      refine ⟨4350676813728372409920589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5800902418304496546560785 4350676813728372409920589)
      ·
        refine ⟨1631503805148139653720221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4350676813728372409920589 1631503805148139653720221)
        ·
          refine ⟨611813926930552370145083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1631503805148139653720221 611813926930552370145083)
          ·
            refine ⟨917720890395828555217625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611813926930552370145083 917720890395828555217625)
            ·
              refine ⟨688290667796871416413219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 917720890395828555217625 688290667796871416413219)
              ·
                refine ⟨1032436001695307124619829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688290667796871416413219 1032436001695307124619829)
                ·
                  refine ⟨96790875158935042933109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1032436001695307124619829 96790875158935042933109)
                  ·
                    rfl

theorem cell21_424124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_424124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424124 prefixEnd_424124 := by exact prefixLift 424124
  have htrace : WordTrace (prefixWord ++ tailWord_424124) baseStart_424124 baseEnd_424124 := by
    simpa [prefixWord, tailWord_424124, baseEnd_424124] using wordTrace_append hprefix tailTrace_424124
  have hstable : (prefixWord ++ tailWord_424124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424124).length < 2 ^ (prefixWord ++ tailWord_424124).sum := by decide
  have hdescent : baseEnd_424124 < baseStart_424124 := by decide
  rcases family_descends (prefixWord ++ tailWord_424124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424152 : List Nat := [2, 1, 2, 2, 4, 2, 1, 7]
def baseStart_424152 : Nat := 118140960795 + 424152 * 2 ^ 59
def prefixEnd_424152 : Nat := 4983230072969 + 3 ^ 40 * 424152 * 2
def baseEnd_424152 : Nat := 32265755046804405488795

theorem tailTrace_424152 : CollatzResearch.WordTrace tailWord_424152 prefixEnd_424152 32265755046804405488795 := by
  unfold tailWord_424152
  simp only [CollatzResearch.WordTrace]
  refine ⟨7735047179688609119757355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10313396239584812159676473 7735047179688609119757355)
  ·
    refine ⟨11602570769532913679636033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7735047179688609119757355 11602570769532913679636033)
    ·
      refine ⟨8701928077149685259727025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11602570769532913679636033 8701928077149685259727025)
      ·
        refine ⟨6526446057862263944795269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8701928077149685259727025 6526446057862263944795269)
        ·
          refine ⟨1223708635849174489649113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6526446057862263944795269 1223708635849174489649113)
          ·
            refine ⟨917781476886880867236835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1223708635849174489649113 917781476886880867236835)
            ·
              refine ⟨1376672215330321300855253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917781476886880867236835 1376672215330321300855253)
              ·
                refine ⟨32265755046804405488795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1376672215330321300855253 32265755046804405488795)
                ·
                  rfl

theorem cell21_424152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 7].length) (baseStart_424152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424152 prefixEnd_424152 := by exact prefixLift 424152
  have htrace : WordTrace (prefixWord ++ tailWord_424152) baseStart_424152 baseEnd_424152 := by
    simpa [prefixWord, tailWord_424152, baseEnd_424152] using wordTrace_append hprefix tailTrace_424152
  have hstable : (prefixWord ++ tailWord_424152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424152).length < 2 ^ (prefixWord ++ tailWord_424152).sum := by decide
  have hdescent : baseEnd_424152 < baseStart_424152 := by decide
  rcases family_descends (prefixWord ++ tailWord_424152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424276 : List Nat := [2, 4, 1, 1, 2, 2, 1, 5, 3]
def baseStart_424276 : Nat := 118140960795 + 424276 * 2 ^ 59
def prefixEnd_424276 : Nat := 4983230072969 + 3 ^ 40 * 424276 * 2
def baseEnd_424276 : Nat := 96825563629816556399465

theorem tailTrace_424276 : CollatzResearch.WordTrace tailWord_424276 prefixEnd_424276 96825563629816556399465 := by
  unfold tailWord_424276
  simp only [CollatzResearch.WordTrace]
  refine ⟨7737308505463993708514341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10316411340618658278019121 7737308505463993708514341)
  ·
    refine ⟨1450745344774498820346439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7737308505463993708514341 1450745344774498820346439)
    ·
      refine ⟨2176118017161748230519659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1450745344774498820346439 2176118017161748230519659)
      ·
        refine ⟨3264177025742622345779489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2176118017161748230519659 3264177025742622345779489)
        ·
          refine ⟨2448132769306966759334617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3264177025742622345779489 2448132769306966759334617)
          ·
            refine ⟨1836099576980225069500963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2448132769306966759334617 1836099576980225069500963)
            ·
              refine ⟨2754149365470337604251445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1836099576980225069500963 2754149365470337604251445)
              ·
                refine ⟨258201503012844150398573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2754149365470337604251445 258201503012844150398573)
                ·
                  refine ⟨96825563629816556399465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258201503012844150398573 96825563629816556399465)
                  ·
                    rfl

theorem cell21_424276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_424276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424276 prefixEnd_424276 := by exact prefixLift 424276
  have htrace : WordTrace (prefixWord ++ tailWord_424276) baseStart_424276 baseEnd_424276 := by
    simpa [prefixWord, tailWord_424276, baseEnd_424276] using wordTrace_append hprefix tailTrace_424276
  have hstable : (prefixWord ++ tailWord_424276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424276).length < 2 ^ (prefixWord ++ tailWord_424276).sum := by decide
  have hdescent : baseEnd_424276 < baseStart_424276 := by decide
  rcases family_descends (prefixWord ++ tailWord_424276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424290 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 6]
def baseStart_424290 : Nat := 118140960795 + 424290 * 2 ^ 59
def prefixEnd_424290 : Nat := 4983230072969 + 3 ^ 40 * 424290 * 2
def baseEnd_424290 : Nat := 96828758620555643166103

theorem tailTrace_424290 : CollatzResearch.WordTrace tailWord_424290 prefixEnd_424290 96828758620555643166103 := by
  unfold tailWord_424290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3868781908219316952009581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10316751755251511872025549 3868781908219316952009581)
  ·
    refine ⟨1450793215582243857003593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3868781908219316952009581 1450793215582243857003593)
    ·
      refine ⟨1088094911686682892752695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1450793215582243857003593 1088094911686682892752695)
      ·
        refine ⟨1632142367530024339129043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1088094911686682892752695 1632142367530024339129043)
        ·
          refine ⟨2448213551295036508693565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1632142367530024339129043 2448213551295036508693565)
          ·
            refine ⟨918080081735638690760087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2448213551295036508693565 918080081735638690760087)
            ·
              refine ⟨1377120122603458036140131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 918080081735638690760087 1377120122603458036140131)
              ·
                refine ⟨2065680183905187054210197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1377120122603458036140131 2065680183905187054210197)
                ·
                  refine ⟨96828758620555643166103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2065680183905187054210197 96828758620555643166103)
                  ·
                    rfl

theorem cell21_424290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_424290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424290 prefixEnd_424290 := by exact prefixLift 424290
  have htrace : WordTrace (prefixWord ++ tailWord_424290) baseStart_424290 baseEnd_424290 := by
    simpa [prefixWord, tailWord_424290, baseEnd_424290] using wordTrace_append hprefix tailTrace_424290
  have hstable : (prefixWord ++ tailWord_424290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424290).length < 2 ^ (prefixWord ++ tailWord_424290).sum := by decide
  have hdescent : baseEnd_424290 < baseStart_424290 := by decide
  rcases family_descends (prefixWord ++ tailWord_424290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424321 : List Nat := [1, 2, 4, 3, 1, 1, 4, 5]
def baseStart_424321 : Nat := 118140960795 + 424321 * 2 ^ 59
def prefixEnd_424321 : Nat := 4983230072969 + 3 ^ 40 * 424321 * 2
def baseEnd_424321 : Nat := 32278611080968826049791

theorem tailTrace_424321 : CollatzResearch.WordTrace tailWord_424321 prefixEnd_424321 32278611080968826049791 := by
  unfold tailWord_424321
  simp only [CollatzResearch.WordTrace]
  refine ⟨15476258295764960102416817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10317505530509973401611211 15476258295764960102416817)
  ·
    refine ⟨11607193721823720076812613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15476258295764960102416817 11607193721823720076812613)
    ·
      refine ⟨2176348822841947514402365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11607193721823720076812613 2176348822841947514402365)
      ·
        refine ⟨816130808565730317900887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2176348822841947514402365 816130808565730317900887)
        ·
          refine ⟨1224196212848595476851331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816130808565730317900887 1224196212848595476851331)
          ·
            refine ⟨1836294319272893215276997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224196212848595476851331 1836294319272893215276997)
            ·
              refine ⟨344305184863667477864437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1836294319272893215276997 344305184863667477864437)
              ·
                refine ⟨32278611080968826049791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 344305184863667477864437 32278611080968826049791)
                ·
                  rfl

theorem cell21_424321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 5].length) (baseStart_424321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424321 prefixEnd_424321 := by exact prefixLift 424321
  have htrace : WordTrace (prefixWord ++ tailWord_424321) baseStart_424321 baseEnd_424321 := by
    simpa [prefixWord, tailWord_424321, baseEnd_424321] using wordTrace_append hprefix tailTrace_424321
  have hstable : (prefixWord ++ tailWord_424321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424321).length < 2 ^ (prefixWord ++ tailWord_424321).sum := by decide
  have hdescent : baseEnd_424321 < baseStart_424321 := by decide
  rcases family_descends (prefixWord ++ tailWord_424321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424380 : List Nat := [2, 2, 2, 4, 1, 1, 2, 7]
def baseStart_424380 : Nat := 118140960795 + 424380 * 2 ^ 59
def prefixEnd_424380 : Nat := 4983230072969 + 3 ^ 40 * 424380 * 2
def baseEnd_424380 : Nat := 32283099282245162221973

theorem tailTrace_424380 : CollatzResearch.WordTrace tailWord_424380 prefixEnd_424380 32283099282245162221973 := by
  unfold tailWord_424380
  simp only [CollatzResearch.WordTrace]
  refine ⟨7739205101275606589407297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10318940135034142119209729 7739205101275606589407297)
  ·
    refine ⟨5804403825956704942055473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7739205101275606589407297 5804403825956704942055473)
    ·
      refine ⟨4353302869467528706541605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5804403825956704942055473 4353302869467528706541605)
      ·
        refine ⟨816244288025161632476551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4353302869467528706541605 816244288025161632476551)
        ·
          refine ⟨1224366432037742448714827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816244288025161632476551 1224366432037742448714827)
          ·
            refine ⟨1836549648056613673072241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224366432037742448714827 1836549648056613673072241)
            ·
              refine ⟨1377412236042460254804181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1836549648056613673072241 1377412236042460254804181)
              ·
                refine ⟨32283099282245162221973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1377412236042460254804181 32283099282245162221973)
                ·
                  rfl

theorem cell21_424380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 7].length) (baseStart_424380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424380 prefixEnd_424380 := by exact prefixLift 424380
  have htrace : WordTrace (prefixWord ++ tailWord_424380) baseStart_424380 baseEnd_424380 := by
    simpa [prefixWord, tailWord_424380, baseEnd_424380] using wordTrace_append hprefix tailTrace_424380
  have hstable : (prefixWord ++ tailWord_424380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424380).length < 2 ^ (prefixWord ++ tailWord_424380).sum := by decide
  have hdescent : baseEnd_424380 < baseStart_424380 := by decide
  rcases family_descends (prefixWord ++ tailWord_424380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424532 : List Nat := [2, 4, 1, 1, 1, 4, 2, 6]
def baseStart_424532 : Nat := 118140960795 + 424532 * 2 ^ 59
def prefixEnd_424532 : Nat := 4983230072969 + 3 ^ 40 * 424532 * 2
def baseEnd_424532 : Nat := 32294662105872333377425

theorem tailTrace_424532 : CollatzResearch.WordTrace tailWord_424532 prefixEnd_424532 32294662105872333377425 := by
  unfold tailWord_424532
  simp only [CollatzResearch.WordTrace]
  refine ⟨7741977049000271569173925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10322636065333695425565233 7741977049000271569173925)
  ·
    refine ⟨1451620696687550919220111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7741977049000271569173925 1451620696687550919220111)
    ·
      refine ⟨2177431045031326378830167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1451620696687550919220111 2177431045031326378830167)
      ·
        refine ⟨3266146567546989568245251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2177431045031326378830167 3266146567546989568245251)
        ·
          refine ⟨4899219851320484352367877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3266146567546989568245251 4899219851320484352367877)
          ·
            refine ⟨918603722122590816068977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4899219851320484352367877 918603722122590816068977)
            ·
              refine ⟨688952791591943112051733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 918603722122590816068977 688952791591943112051733)
              ·
                refine ⟨32294662105872333377425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 688952791591943112051733 32294662105872333377425)
                ·
                  rfl

theorem cell21_424532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 6].length) (baseStart_424532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424532 prefixEnd_424532 := by exact prefixLift 424532
  have htrace : WordTrace (prefixWord ++ tailWord_424532) baseStart_424532 baseEnd_424532 := by
    simpa [prefixWord, tailWord_424532, baseEnd_424532] using wordTrace_append hprefix tailTrace_424532
  have hstable : (prefixWord ++ tailWord_424532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424532).length < 2 ^ (prefixWord ++ tailWord_424532).sum := by decide
  have hdescent : baseEnd_424532 < baseStart_424532 := by decide
  rcases family_descends (prefixWord ++ tailWord_424532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424580 : List Nat := [2, 3, 2, 1, 3, 2, 1, 4, 3]
def baseStart_424580 : Nat := 118140960795 + 424580 * 2 ^ 59
def prefixEnd_424580 : Nat := 4983230072969 + 3 ^ 40 * 424580 * 2
def baseEnd_424580 : Nat := 96894940571579583332177

theorem tailTrace_424580 : CollatzResearch.WordTrace tailWord_424580 prefixEnd_424580 96894940571579583332177 := by
  unfold tailWord_424580
  simp only [CollatzResearch.WordTrace]
  refine ⟨7742852400913323668047597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10323803201217764890730129 7742852400913323668047597)
  ·
    refine ⟨2903569650342496375517849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7742852400913323668047597 2903569650342496375517849)
    ·
      refine ⟨2177677237756872281638387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2903569650342496375517849 2177677237756872281638387)
      ·
        refine ⟨3266515856635308422457581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2177677237756872281638387 3266515856635308422457581)
        ·
          refine ⟨1224943446238240658421593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3266515856635308422457581 1224943446238240658421593)
          ·
            refine ⟨918707584678680493816195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1224943446238240658421593 918707584678680493816195)
            ·
              refine ⟨1378061377018020740724293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 918707584678680493816195 1378061377018020740724293)
              ·
                refine ⟨258386508190878888885805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1378061377018020740724293 258386508190878888885805)
                ·
                  refine ⟨96894940571579583332177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258386508190878888885805 96894940571579583332177)
                  ·
                    rfl

theorem cell21_424580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_424580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424580 prefixEnd_424580 := by exact prefixLift 424580
  have htrace : WordTrace (prefixWord ++ tailWord_424580) baseStart_424580 baseEnd_424580 := by
    simpa [prefixWord, tailWord_424580, baseEnd_424580] using wordTrace_append hprefix tailTrace_424580
  have hstable : (prefixWord ++ tailWord_424580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424580).length < 2 ^ (prefixWord ++ tailWord_424580).sum := by decide
  have hdescent : baseEnd_424580 < baseStart_424580 := by decide
  rcases family_descends (prefixWord ++ tailWord_424580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424594 : List Nat := [3, 2, 3, 1, 2, 1, 2, 3, 4]
def baseStart_424594 : Nat := 118140960795 + 424594 * 2 ^ 59
def prefixEnd_424594 : Nat := 4983230072969 + 3 ^ 40 * 424594 * 2
def baseEnd_424594 : Nat := 96898135562318670098815

theorem tailTrace_424594 : CollatzResearch.WordTrace tailWord_424594 prefixEnd_424594 96898135562318670098815 := by
  unfold tailWord_424594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3871553855943981931776209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10324143615850618484736557 3871553855943981931776209)
  ·
    refine ⟨2903665391957986448832157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3871553855943981931776209 2903665391957986448832157)
    ·
      refine ⟨1088874521984244918312059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2903665391957986448832157 1088874521984244918312059)
      ·
        refine ⟨1633311782976367377468089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1088874521984244918312059 1633311782976367377468089)
        ·
          refine ⟨1224983837232275533101067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1633311782976367377468089 1224983837232275533101067)
          ·
            refine ⟨1837475755848413299651601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224983837232275533101067 1837475755848413299651601)
            ·
              refine ⟨1378106816886309974738701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1837475755848413299651601 1378106816886309974738701)
              ·
                refine ⟨516790056332366240527013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1378106816886309974738701 516790056332366240527013)
                ·
                  refine ⟨96898135562318670098815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 516790056332366240527013 96898135562318670098815)
                  ·
                    rfl

theorem cell21_424594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_424594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424594 prefixEnd_424594 := by exact prefixLift 424594
  have htrace : WordTrace (prefixWord ++ tailWord_424594) baseStart_424594 baseEnd_424594 := by
    simpa [prefixWord, tailWord_424594, baseEnd_424594] using wordTrace_append hprefix tailTrace_424594
  have hstable : (prefixWord ++ tailWord_424594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424594).length < 2 ^ (prefixWord ++ tailWord_424594).sum := by decide
  have hdescent : baseEnd_424594 < baseStart_424594 := by decide
  rcases family_descends (prefixWord ++ tailWord_424594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424639 : List Nat := [1, 1, 2, 2, 2, 4, 2, 4, 3]
def baseStart_424639 : Nat := 118140960795 + 424639 * 2 ^ 59
def prefixEnd_424639 : Nat := 4983230072969 + 3 ^ 40 * 424639 * 2
def baseEnd_424639 : Nat := 96908405175408591848723

theorem tailTrace_424639 : CollatzResearch.WordTrace tailWord_424639 prefixEnd_424639 96908405175408591848723 := by
  unfold tailWord_424639
  simp only [CollatzResearch.WordTrace]
  refine ⟨15487856708612900412492971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10325237805741933608328647 15487856708612900412492971)
  ·
    refine ⟨23231785062919350618739457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15487856708612900412492971 23231785062919350618739457)
    ·
      refine ⟨17423838797189512964054593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23231785062919350618739457 17423838797189512964054593)
      ·
        refine ⟨13067879097892134723040945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17423838797189512964054593 13067879097892134723040945)
        ·
          refine ⟨9800909323419101042280709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13067879097892134723040945 9800909323419101042280709)
          ·
            refine ⟨1837670498141081445427633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9800909323419101042280709 1837670498141081445427633)
            ·
              refine ⟨1378252873605811084070725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1837670498141081445427633 1378252873605811084070725)
              ·
                refine ⟨258422413801089578263261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1378252873605811084070725 258422413801089578263261)
                ·
                  refine ⟨96908405175408591848723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258422413801089578263261 96908405175408591848723)
                  ·
                    rfl

theorem cell21_424639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 3].length) (baseStart_424639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424639 prefixEnd_424639 := by exact prefixLift 424639
  have htrace : WordTrace (prefixWord ++ tailWord_424639) baseStart_424639 baseEnd_424639 := by
    simpa [prefixWord, tailWord_424639, baseEnd_424639] using wordTrace_append hprefix tailTrace_424639
  have hstable : (prefixWord ++ tailWord_424639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424639).length < 2 ^ (prefixWord ++ tailWord_424639).sum := by decide
  have hdescent : baseEnd_424639 < baseStart_424639 := by decide
  rcases family_descends (prefixWord ++ tailWord_424639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424681 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 7]
def baseStart_424681 : Nat := 118140960795 + 424681 * 2 ^ 59
def prefixEnd_424681 : Nat := 4983230072969 + 3 ^ 40 * 424681 * 2
def baseEnd_424681 : Nat := 96917990147625852148637

theorem tailTrace_424681 : CollatzResearch.WordTrace tailWord_424681 prefixEnd_424681 96917990147625852148637 := by
  unfold tailWord_424681
  simp only [CollatzResearch.WordTrace]
  refine ⟨15489388574460741585521897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10326259049640494390347931 15489388574460741585521897)
  ·
    refine ⟨11617041430845556189141423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15489388574460741585521897 11617041430845556189141423)
    ·
      refine ⟨17425562146268334283712135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11617041430845556189141423 17425562146268334283712135)
      ·
        refine ⟨26138343219402501425568203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17425562146268334283712135 26138343219402501425568203)
        ·
          refine ⟨39207514829103752138352305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26138343219402501425568203 39207514829103752138352305)
          ·
            refine ⟨29405636121827814103764229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39207514829103752138352305 29405636121827814103764229)
            ·
              refine ⟨5513556772842715144455793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29405636121827814103764229 5513556772842715144455793)
              ·
                refine ⟨4135167579632036358341845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5513556772842715144455793 4135167579632036358341845)
                ·
                  refine ⟨96917990147625852148637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4135167579632036358341845 96917990147625852148637)
                  ·
                    rfl

theorem cell21_424681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_424681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424681 prefixEnd_424681 := by exact prefixLift 424681
  have htrace : WordTrace (prefixWord ++ tailWord_424681) baseStart_424681 baseEnd_424681 := by
    simpa [prefixWord, tailWord_424681, baseEnd_424681] using wordTrace_append hprefix tailTrace_424681
  have hstable : (prefixWord ++ tailWord_424681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424681).length < 2 ^ (prefixWord ++ tailWord_424681).sum := by decide
  have hdescent : baseEnd_424681 < baseStart_424681 := by decide
  rcases family_descends (prefixWord ++ tailWord_424681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424698 : List Nat := [3, 1, 1, 1, 1, 3, 5, 1, 5]
def baseStart_424698 : Nat := 118140960795 + 424698 * 2 ^ 59
def prefixEnd_424698 : Nat := 4983230072969 + 3 ^ 40 * 424698 * 2
def baseEnd_424698 : Nat := 96921869779237600365269

theorem tailTrace_424698 : CollatzResearch.WordTrace tailWord_424698 prefixEnd_424698 96921869779237600365269 := by
  unfold tailWord_424698
  simp only [CollatzResearch.WordTrace]
  refine ⟨3872502153849788372222687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10326672410266102325927165 3872502153849788372222687)
  ·
    refine ⟨5808753230774682558334031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3872502153849788372222687 5808753230774682558334031)
    ·
      refine ⟨8713129846162023837501047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5808753230774682558334031 8713129846162023837501047)
      ·
        refine ⟨13069694769243035756251571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8713129846162023837501047 13069694769243035756251571)
        ·
          refine ⟨19604542153864553634377357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13069694769243035756251571 19604542153864553634377357)
          ·
            refine ⟨7351703307699207612891509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19604542153864553634377357 7351703307699207612891509)
            ·
              refine ⟨689222185096800713708579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7351703307699207612891509 689222185096800713708579)
              ·
                refine ⟨1033833277645201070562869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 689222185096800713708579 1033833277645201070562869)
                ·
                  refine ⟨96921869779237600365269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1033833277645201070562869 96921869779237600365269)
                  ·
                    rfl

theorem cell21_424698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_424698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424698 prefixEnd_424698 := by exact prefixLift 424698
  have htrace : WordTrace (prefixWord ++ tailWord_424698) baseStart_424698 baseEnd_424698 := by
    simpa [prefixWord, tailWord_424698, baseEnd_424698] using wordTrace_append hprefix tailTrace_424698
  have hstable : (prefixWord ++ tailWord_424698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424698).length < 2 ^ (prefixWord ++ tailWord_424698).sum := by decide
  have hdescent : baseEnd_424698 < baseStart_424698 := by decide
  rcases family_descends (prefixWord ++ tailWord_424698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424791 : List Nat := [1, 1, 3, 2, 4, 1, 1, 5, 3]
def baseStart_424791 : Nat := 118140960795 + 424791 * 2 ^ 59
def prefixEnd_424791 : Nat := 4983230072969 + 3 ^ 40 * 424791 * 2
def baseEnd_424791 : Nat := 96943093646290105315079

theorem tailTrace_424791 : CollatzResearch.WordTrace tailWord_424791 prefixEnd_424791 96943093646290105315079 := by
  unfold tailWord_424791
  simp only [CollatzResearch.WordTrace]
  refine ⟨15493400604062230372026227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10328933736041486914684151 15493400604062230372026227)
  ·
    refine ⟨23240100906093345558039341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15493400604062230372026227 23240100906093345558039341)
    ·
      refine ⟨8715037839785004584264753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23240100906093345558039341 8715037839785004584264753)
      ·
        refine ⟨6536278379838753438198565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8715037839785004584264753 6536278379838753438198565)
        ·
          refine ⟨1225552196219766269662231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6536278379838753438198565 1225552196219766269662231)
          ·
            refine ⟨1838328294329649404493347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225552196219766269662231 1838328294329649404493347)
            ·
              refine ⟨2757492441494474106740021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1838328294329649404493347 2757492441494474106740021)
              ·
                refine ⟨258514916390106947506877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2757492441494474106740021 258514916390106947506877)
                ·
                  refine ⟨96943093646290105315079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258514916390106947506877 96943093646290105315079)
                  ·
                    rfl

theorem cell21_424791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 3].length) (baseStart_424791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424791 prefixEnd_424791 := by exact prefixLift 424791
  have htrace : WordTrace (prefixWord ++ tailWord_424791) baseStart_424791 baseEnd_424791 := by
    simpa [prefixWord, tailWord_424791, baseEnd_424791] using wordTrace_append hprefix tailTrace_424791
  have hstable : (prefixWord ++ tailWord_424791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424791).length < 2 ^ (prefixWord ++ tailWord_424791).sum := by decide
  have hdescent : baseEnd_424791 < baseStart_424791 := by decide
  rcases family_descends (prefixWord ++ tailWord_424791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424805 : List Nat := [1, 3, 1, 3, 1, 1, 5, 2, 4]
def baseStart_424805 : Nat := 118140960795 + 424805 * 2 ^ 59
def prefixEnd_424805 : Nat := 4983230072969 + 3 ^ 40 * 424805 * 2
def baseEnd_424805 : Nat := 96946288637029192081717

theorem tailTrace_424805 : CollatzResearch.WordTrace tailWord_424805 prefixEnd_424805 96946288637029192081717 := by
  unfold tailWord_424805
  simp only [CollatzResearch.WordTrace]
  refine ⟨15493911226011510763035869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10329274150674340508690579 15493911226011510763035869)
  ·
    refine ⟨5810216709754316536138451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15493911226011510763035869 5810216709754316536138451)
    ·
      refine ⟨8715325064631474804207677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5810216709754316536138451 8715325064631474804207677)
      ·
        refine ⟨3268246899236803051577879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8715325064631474804207677 3268246899236803051577879)
        ·
          refine ⟨4902370348855204577366819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3268246899236803051577879 4902370348855204577366819)
          ·
            refine ⟨7353555523282806866050229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4902370348855204577366819 7353555523282806866050229)
            ·
              refine ⟨689395830307763143692209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7353555523282806866050229 689395830307763143692209)
              ·
                refine ⟨517046872730822357769157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689395830307763143692209 517046872730822357769157)
                ·
                  refine ⟨96946288637029192081717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 517046872730822357769157 96946288637029192081717)
                  ·
                    rfl

theorem cell21_424805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_424805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424805 prefixEnd_424805 := by exact prefixLift 424805
  have htrace : WordTrace (prefixWord ++ tailWord_424805) baseStart_424805 baseEnd_424805 := by
    simpa [prefixWord, tailWord_424805, baseEnd_424805] using wordTrace_append hprefix tailTrace_424805
  have hstable : (prefixWord ++ tailWord_424805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424805).length < 2 ^ (prefixWord ++ tailWord_424805).sum := by decide
  have hdescent : baseEnd_424805 < baseStart_424805 := by decide
  rcases family_descends (prefixWord ++ tailWord_424805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424864 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 6]
def baseStart_424864 : Nat := 118140960795 + 424864 * 2 ^ 59
def prefixEnd_424864 : Nat := 4983230072969 + 3 ^ 40 * 424864 * 2
def baseEnd_424864 : Nat := 96959753240858200598263

theorem tailTrace_424864 : CollatzResearch.WordTrace tailWord_424864 prefixEnd_424864 96959753240858200598263 := by
  unfold tailWord_424864
  simp only [CollatzResearch.WordTrace]
  refine ⟨7748031566398881919716823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10330708755198509226289097 7748031566398881919716823)
  ·
    refine ⟨11622047349598322879575235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7748031566398881919716823 11622047349598322879575235)
    ·
      refine ⟨17433071024397484319362853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11622047349598322879575235 17433071024397484319362853)
      ·
        refine ⟨3268700817074528309880535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17433071024397484319362853 3268700817074528309880535)
        ·
          refine ⟨4903051225611792464820803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3268700817074528309880535 4903051225611792464820803)
          ·
            refine ⟨7354576838417688697231205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4903051225611792464820803 7354576838417688697231205)
            ·
              refine ⟨1378983157203316630730851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7354576838417688697231205 1378983157203316630730851)
              ·
                refine ⟨2068474735804974946096277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378983157203316630730851 2068474735804974946096277)
                ·
                  refine ⟨96959753240858200598263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2068474735804974946096277 96959753240858200598263)
                  ·
                    rfl

theorem cell21_424864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_424864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424864 prefixEnd_424864 := by exact prefixLift 424864
  have htrace : WordTrace (prefixWord ++ tailWord_424864) baseStart_424864 baseEnd_424864 := by
    simpa [prefixWord, tailWord_424864, baseEnd_424864] using wordTrace_append hprefix tailTrace_424864
  have hstable : (prefixWord ++ tailWord_424864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424864).length < 2 ^ (prefixWord ++ tailWord_424864).sum := by decide
  have hdescent : baseEnd_424864 < baseStart_424864 := by decide
  rcases family_descends (prefixWord ++ tailWord_424864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424918 : List Nat := [5, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_424918 : Nat := 118140960795 + 424918 * 2 ^ 59
def prefixEnd_424918 : Nat := 4983230072969 + 3 ^ 40 * 424918 * 2
def baseEnd_424918 : Nat := 96972076776566106698153

theorem tailTrace_424918 : CollatzResearch.WordTrace tailWord_424918 prefixEnd_424918 96972076776566106698153 := by
  unfold tailWord_424918
  simp only [CollatzResearch.WordTrace]
  refine ⟨968627042162633191368713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10332021783068087374599605 968627042162633191368713)
  ·
    refine ⟨726470281621974893526535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 968627042162633191368713 726470281621974893526535)
    ·
      refine ⟨1089705422432962340289803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 726470281621974893526535 1089705422432962340289803)
      ·
        refine ⟨1634558133649443510434705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1089705422432962340289803 1634558133649443510434705)
        ·
          refine ⟨1225918600237082632826029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1634558133649443510434705 1225918600237082632826029)
          ·
            refine ⟨459719475088905987309761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1225918600237082632826029 459719475088905987309761)
            ·
              refine ⟨344789606316679490482321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459719475088905987309761 344789606316679490482321)
              ·
                refine ⟨258592204737509617861741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344789606316679490482321 258592204737509617861741)
                ·
                  refine ⟨96972076776566106698153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258592204737509617861741 96972076776566106698153)
                  ·
                    rfl

theorem cell21_424918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_424918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424918 prefixEnd_424918 := by exact prefixLift 424918
  have htrace : WordTrace (prefixWord ++ tailWord_424918) baseStart_424918 baseEnd_424918 := by
    simpa [prefixWord, tailWord_424918, baseEnd_424918] using wordTrace_append hprefix tailTrace_424918
  have hstable : (prefixWord ++ tailWord_424918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424918).length < 2 ^ (prefixWord ++ tailWord_424918).sum := by decide
  have hdescent : baseEnd_424918 < baseStart_424918 := by decide
  rcases family_descends (prefixWord ++ tailWord_424918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424954 : List Nat := [3, 1, 1, 1, 1, 2, 1, 11]
def baseStart_424954 : Nat := 118140960795 + 424954 * 2 ^ 59
def prefixEnd_424954 : Nat := 4983230072969 + 3 ^ 40 * 424954 * 2
def baseEnd_424954 : Nat := 32326764155679348032693

theorem tailTrace_424954 : CollatzResearch.WordTrace tailWord_424954 prefixEnd_424954 32326764155679348032693 := by
  unfold tailWord_424954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3874836425617927302552479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10332897134981139473473277 3874836425617927302552479)
  ·
    refine ⟨5812254638426890953828719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3874836425617927302552479 5812254638426890953828719)
    ·
      refine ⟨8718381957640336430743079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5812254638426890953828719 8718381957640336430743079)
      ·
        refine ⟨13077572936460504646114619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8718381957640336430743079 13077572936460504646114619)
        ·
          refine ⟨19616359404690756969171929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13077572936460504646114619 19616359404690756969171929)
          ·
            refine ⟨14712269553518067726878947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19616359404690756969171929 14712269553518067726878947)
            ·
              refine ⟨22068404330277101590318421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14712269553518067726878947 22068404330277101590318421)
              ·
                refine ⟨32326764155679348032693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 22068404330277101590318421 32326764155679348032693)
                ·
                  rfl

theorem cell21_424954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_424954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424954 prefixEnd_424954 := by exact prefixLift 424954
  have htrace : WordTrace (prefixWord ++ tailWord_424954) baseStart_424954 baseEnd_424954 := by
    simpa [prefixWord, tailWord_424954, baseEnd_424954] using wordTrace_append hprefix tailTrace_424954
  have hstable : (prefixWord ++ tailWord_424954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424954).length < 2 ^ (prefixWord ++ tailWord_424954).sum := by decide
  have hdescent : baseEnd_424954 < baseStart_424954 := by decide
  rcases family_descends (prefixWord ++ tailWord_424954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424974 : List Nat := [4, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_424974 : Nat := 118140960795 + 424974 * 2 ^ 59
def prefixEnd_424974 : Nat := 4983230072969 + 3 ^ 40 * 424974 * 2
def baseEnd_424974 : Nat := 96984856739522453764705

theorem tailTrace_424974 : CollatzResearch.WordTrace tailWord_424974 prefixEnd_424974 96984856739522453764705 := by
  unfold tailWord_424974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1937509395299906578242247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10333383441599501750625317 1937509395299906578242247)
  ·
    refine ⟨2906264092949859867363371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1937509395299906578242247 2906264092949859867363371)
    ·
      refine ⟨4359396139424789801045057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2906264092949859867363371 4359396139424789801045057)
      ·
        refine ⟨3269547104568592350783793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4359396139424789801045057 3269547104568592350783793)
        ·
          refine ⟨2452160328426444263087845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3269547104568592350783793 2452160328426444263087845)
          ·
            refine ⟨459780061579958299328971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2452160328426444263087845 459780061579958299328971)
            ·
              refine ⟨689670092369937448993457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459780061579958299328971 689670092369937448993457)
              ·
                refine ⟨517252569277453086745093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689670092369937448993457 517252569277453086745093)
                ·
                  refine ⟨96984856739522453764705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 517252569277453086745093 96984856739522453764705)
                  ·
                    rfl

theorem cell21_424974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_424974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424974 prefixEnd_424974 := by exact prefixLift 424974
  have htrace : WordTrace (prefixWord ++ tailWord_424974) baseStart_424974 baseEnd_424974 := by
    simpa [prefixWord, tailWord_424974, baseEnd_424974] using wordTrace_append hprefix tailTrace_424974
  have hstable : (prefixWord ++ tailWord_424974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424974).length < 2 ^ (prefixWord ++ tailWord_424974).sum := by decide
  have hdescent : baseEnd_424974 < baseStart_424974 := by decide
  rcases family_descends (prefixWord ++ tailWord_424974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424985 : List Nat := [1, 2, 1, 2, 1, 1, 5, 3, 5]
def baseStart_424985 : Nat := 118140960795 + 424985 * 2 ^ 59
def prefixEnd_424985 : Nat := 4983230072969 + 3 ^ 40 * 424985 * 2
def baseEnd_424985 : Nat := 96987367089388879081349

theorem tailTrace_424985 : CollatzResearch.WordTrace tailWord_424985 prefixEnd_424985 96987367089388879081349 := by
  unfold tailWord_424985
  simp only [CollatzResearch.WordTrace]
  refine ⟨15500476365359401504588409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10333650910239601003058939 15500476365359401504588409)
  ·
    refine ⟨11625357274019551128441307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15500476365359401504588409 11625357274019551128441307)
    ·
      refine ⟨17438035911029326692661961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11625357274019551128441307 17438035911029326692661961)
      ·
        refine ⟨13078526933271995019496471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17438035911029326692661961 13078526933271995019496471)
        ·
          refine ⟨19617790399907992529244707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13078526933271995019496471 19617790399907992529244707)
          ·
            refine ⟨29426685599861988793867061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19617790399907992529244707 29426685599861988793867061)
            ·
              refine ⟨2758751774987061449425037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29426685599861988793867061 2758751774987061449425037)
              ·
                refine ⟨1034531915620148043534389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2758751774987061449425037 1034531915620148043534389)
                ·
                  refine ⟨96987367089388879081349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1034531915620148043534389 96987367089388879081349)
                  ·
                    rfl

theorem cell21_424985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_424985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_424985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_424985 prefixEnd_424985 := by exact prefixLift 424985
  have htrace : WordTrace (prefixWord ++ tailWord_424985) baseStart_424985 baseEnd_424985 := by
    simpa [prefixWord, tailWord_424985, baseEnd_424985] using wordTrace_append hprefix tailTrace_424985
  have hstable : (prefixWord ++ tailWord_424985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424985).length < 2 ^ (prefixWord ++ tailWord_424985).sum := by decide
  have hdescent : baseEnd_424985 < baseStart_424985 := by decide
  rcases family_descends (prefixWord ++ tailWord_424985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425016 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 6]
def baseStart_425016 : Nat := 118140960795 + 425016 * 2 ^ 59
def prefixEnd_425016 : Nat := 4983230072969 + 3 ^ 40 * 425016 * 2
def baseEnd_425016 : Nat := 96994441711739714064619

theorem tailTrace_425016 : CollatzResearch.WordTrace tailWord_425016 prefixEnd_425016 96994441711739714064619 := by
  unfold tailWord_425016
  simp only [CollatzResearch.WordTrace]
  refine ⟨7750803514123546899483451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10334404685498062532644601 7750803514123546899483451)
  ·
    refine ⟨11626205271185320349225177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7750803514123546899483451 11626205271185320349225177)
    ·
      refine ⟨8719653953388990261918883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11626205271185320349225177 8719653953388990261918883)
      ·
        refine ⟨13079480930083485392878325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8719653953388990261918883 13079480930083485392878325)
        ·
          refine ⟨1226201337195326755582343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13079480930083485392878325 1226201337195326755582343)
          ·
            refine ⟨1839302005792990133373515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226201337195326755582343 1839302005792990133373515)
            ·
              refine ⟨2758953008689485200060273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1839302005792990133373515 2758953008689485200060273)
              ·
                refine ⟨2069214756517113900045205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2758953008689485200060273 2069214756517113900045205)
                ·
                  refine ⟨96994441711739714064619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2069214756517113900045205 96994441711739714064619)
                  ·
                    rfl

theorem cell21_425016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_425016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_425016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_425016 prefixEnd_425016 := by exact prefixLift 425016
  have htrace : WordTrace (prefixWord ++ tailWord_425016) baseStart_425016 baseEnd_425016 := by
    simpa [prefixWord, tailWord_425016, baseEnd_425016] using wordTrace_append hprefix tailTrace_425016
  have hstable : (prefixWord ++ tailWord_425016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425016).length < 2 ^ (prefixWord ++ tailWord_425016).sum := by decide
  have hdescent : baseEnd_425016 < baseStart_425016 := by decide
  rcases family_descends (prefixWord ++ tailWord_425016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425061 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 7]
def baseStart_425061 : Nat := 118140960795 + 425061 * 2 ^ 59
def prefixEnd_425061 : Nat := 4983230072969 + 3 ^ 40 * 425061 * 2
def baseEnd_425061 : Nat := 97004711324829635814527

theorem tailTrace_425061 : CollatzResearch.WordTrace tailWord_425061 prefixEnd_425061 97004711324829635814527 := by
  unfold tailWord_425061
  simp only [CollatzResearch.WordTrace]
  refine ⟨15503248313084066484355037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10335498875389377656236691 15503248313084066484355037)
  ·
    refine ⟨5813718117406524931633139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15503248313084066484355037 5813718117406524931633139)
    ·
      refine ⟨8720577176109787397449709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5813718117406524931633139 8720577176109787397449709)
      ·
        refine ⟨3270216441041170274043641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8720577176109787397449709 3270216441041170274043641)
        ·
          refine ⟨2452662330780877705532731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3270216441041170274043641 2452662330780877705532731)
          ·
            refine ⟨3678993496171316558299097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2452662330780877705532731 3678993496171316558299097)
            ·
              refine ⟨2759245122128487418724323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3678993496171316558299097 2759245122128487418724323)
              ·
                refine ⟨4138867683192731128086485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2759245122128487418724323 4138867683192731128086485)
                ·
                  refine ⟨97004711324829635814527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4138867683192731128086485 97004711324829635814527)
                  ·
                    rfl

theorem cell21_425061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_425061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_425061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_425061 prefixEnd_425061 := by exact prefixLift 425061
  have htrace : WordTrace (prefixWord ++ tailWord_425061) baseStart_425061 baseEnd_425061 := by
    simpa [prefixWord, tailWord_425061, baseEnd_425061] using wordTrace_append hprefix tailTrace_425061
  have hstable : (prefixWord ++ tailWord_425061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425061).length < 2 ^ (prefixWord ++ tailWord_425061).sum := by decide
  have hdescent : baseEnd_425061 < baseStart_425061 := by decide
  rcases family_descends (prefixWord ++ tailWord_425061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425174 : List Nat := [5, 2, 1, 2, 2, 2, 2, 5]
def baseStart_425174 : Nat := 118140960795 + 425174 * 2 ^ 59
def prefixEnd_425174 : Nat := 4983230072969 + 3 ^ 40 * 425174 * 2
def baseEnd_425174 : Nat := 32343499821455516810321

theorem tailTrace_425174 : CollatzResearch.WordTrace tailWord_425174 prefixEnd_425174 32343499821455516810321 := by
  unfold tailWord_425174
  simp only [CollatzResearch.WordTrace]
  refine ⟨969210610104667923951161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10338246507783124522145717 969210610104667923951161)
  ·
    refine ⟨726907957578500942963371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 969210610104667923951161 726907957578500942963371)
    ·
      refine ⟨1090361936367751414445057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 726907957578500942963371 1090361936367751414445057)
      ·
        refine ⟨817771452275813560833793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1090361936367751414445057 817771452275813560833793)
        ·
          refine ⟨613328589206860170625345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 817771452275813560833793 613328589206860170625345)
          ·
            refine ⟨459996441905145127969009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613328589206860170625345 459996441905145127969009)
            ·
              refine ⟨344997331428858845976757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459996441905145127969009 344997331428858845976757)
              ·
                refine ⟨32343499821455516810321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 344997331428858845976757 32343499821455516810321)
                ·
                  rfl

theorem cell21_425174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_425174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_425174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_425174 prefixEnd_425174 := by exact prefixLift 425174
  have htrace : WordTrace (prefixWord ++ tailWord_425174) baseStart_425174 baseEnd_425174 := by
    simpa [prefixWord, tailWord_425174, baseEnd_425174] using wordTrace_append hprefix tailTrace_425174
  have hstable : (prefixWord ++ tailWord_425174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425174).length < 2 ^ (prefixWord ++ tailWord_425174).sum := by decide
  have hdescent : baseEnd_425174 < baseStart_425174 := by decide
  rcases family_descends (prefixWord ++ tailWord_425174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425199 : List Nat := [1, 1, 2, 1, 7, 2, 7]
def baseStart_425199 : Nat := 118140960795 + 425199 * 2 ^ 59
def prefixEnd_425199 : Nat := 4983230072969 + 3 ^ 40 * 425199 * 2
def baseEnd_425199 : Nat := 10781800533885784723805

theorem tailTrace_425199 : CollatzResearch.WordTrace tailWord_425199 prefixEnd_425199 10781800533885784723805 := by
  unfold tailWord_425199
  simp only [CollatzResearch.WordTrace]
  refine ⟨15508281586584116052878651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10338854391056077368585767 15508281586584116052878651)
  ·
    refine ⟨23262422379876174079317977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15508281586584116052878651 23262422379876174079317977)
    ·
      refine ⟨17446816784907130559488483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23262422379876174079317977 17446816784907130559488483)
      ·
        refine ⟨26170225177360695839232725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17446816784907130559488483 26170225177360695839232725)
        ·
          refine ⟨613364652594391308732017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 26170225177360695839232725 613364652594391308732017)
          ·
            refine ⟨460023489445793481549013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613364652594391308732017 460023489445793481549013)
            ·
              refine ⟨10781800533885784723805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 460023489445793481549013 10781800533885784723805)
              ·
                rfl

theorem cell21_425199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 7].length) (baseStart_425199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_425199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_425199 prefixEnd_425199 := by exact prefixLift 425199
  have htrace : WordTrace (prefixWord ++ tailWord_425199) baseStart_425199 baseEnd_425199 := by
    simpa [prefixWord, tailWord_425199, baseEnd_425199] using wordTrace_append hprefix tailTrace_425199
  have hstable : (prefixWord ++ tailWord_425199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425199).length < 2 ^ (prefixWord ++ tailWord_425199).sum := by decide
  have hdescent : baseEnd_425199 < baseStart_425199 := by decide
  rcases family_descends (prefixWord ++ tailWord_425199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425306 : List Nat := [3, 1, 1, 2, 1, 2, 3, 5, 3]
def baseStart_425306 : Nat := 118140960795 + 425306 * 2 ^ 59
def prefixEnd_425306 : Nat := 4983230072969 + 3 ^ 40 * 425306 * 2
def baseEnd_425306 : Nat := 97060623662763654230693

theorem tailTrace_425306 : CollatzResearch.WordTrace tailWord_425306 prefixEnd_425306 97060623662763654230693 := by
  unfold tailWord_425306
  simp only [CollatzResearch.WordTrace]
  refine ⟨3878046049299118331755943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10341456131464315551349181 3878046049299118331755943)
  ·
    refine ⟨5817069073948677497633915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3878046049299118331755943 5817069073948677497633915)
    ·
      refine ⟨8725603610923016246450873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5817069073948677497633915 8725603610923016246450873)
      ·
        refine ⟨6544202708192262184838155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8725603610923016246450873 6544202708192262184838155)
        ·
          refine ⟨9816304062288393277257233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6544202708192262184838155 9816304062288393277257233)
          ·
            refine ⟨7362228046716294957942925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9816304062288393277257233 7362228046716294957942925)
            ·
              refine ⟨2760835517518610609228597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7362228046716294957942925 2760835517518610609228597)
              ·
                refine ⟨258828329767369744615181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2760835517518610609228597 258828329767369744615181)
                ·
                  refine ⟨97060623662763654230693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 258828329767369744615181 97060623662763654230693)
                  ·
                    rfl

theorem cell21_425306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_425306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_425306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_425306 prefixEnd_425306 := by exact prefixLift 425306
  have htrace : WordTrace (prefixWord ++ tailWord_425306) baseStart_425306 baseEnd_425306 := by
    simpa [prefixWord, tailWord_425306, baseEnd_425306] using wordTrace_append hprefix tailTrace_425306
  have hstable : (prefixWord ++ tailWord_425306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425306).length < 2 ^ (prefixWord ++ tailWord_425306).sum := by decide
  have hdescent : baseEnd_425306 < baseStart_425306 := by decide
  rcases family_descends (prefixWord ++ tailWord_425306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425309 : List Nat := [1, 4, 5, 1, 1, 1, 8]
def baseStart_425309 : Nat := 118140960795 + 425309 * 2 ^ 59
def prefixEnd_425309 : Nat := 4983230072969 + 3 ^ 40 * 425309 * 2
def baseEnd_425309 : Nat := 10784589811515146186743

theorem tailTrace_425309 : CollatzResearch.WordTrace tailWord_425309 prefixEnd_425309 10784589811515146186743 := by
  unfold tailWord_425309
  simp only [CollatzResearch.WordTrace]
  refine ⟨15512293616185604839382981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10341529077457069892921987 15512293616185604839382981)
  ·
    refine ⟨2908555053034800907384309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15512293616185604839382981 2908555053034800907384309)
    ·
      refine ⟨272677036222012585067279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2908555053034800907384309 272677036222012585067279)
      ·
        refine ⟨409015554333018877600919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272677036222012585067279 409015554333018877600919)
        ·
          refine ⟨613523331499528316401379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409015554333018877600919 613523331499528316401379)
          ·
            refine ⟨920284997249292474602069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613523331499528316401379 920284997249292474602069)
            ·
              refine ⟨10784589811515146186743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 920284997249292474602069 10784589811515146186743)
              ·
                rfl

theorem cell21_425309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 8].length) (baseStart_425309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_425309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_425309 prefixEnd_425309 := by exact prefixLift 425309
  have htrace : WordTrace (prefixWord ++ tailWord_425309) baseStart_425309 baseEnd_425309 := by
    simpa [prefixWord, tailWord_425309, baseEnd_425309] using wordTrace_append hprefix tailTrace_425309
  have hstable : (prefixWord ++ tailWord_425309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425309).length < 2 ^ (prefixWord ++ tailWord_425309).sum := by decide
  have hdescent : baseEnd_425309 < baseStart_425309 := by decide
  rcases family_descends (prefixWord ++ tailWord_425309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425351 : List Nat := [1, 1, 4, 2, 2, 2, 4, 5]
def baseStart_425351 : Nat := 118140960795 + 425351 * 2 ^ 59
def prefixEnd_425351 : Nat := 4983230072969 + 3 ^ 40 * 425351 * 2
def baseEnd_425351 : Nat := 32356964425284525326867

theorem tailTrace_425351 : CollatzResearch.WordTrace tailWord_425351 prefixEnd_425351 32356964425284525326867 := by
  unfold tailWord_425351
  simp only [CollatzResearch.WordTrace]
  refine ⟨15513825482033446012411907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10342550321355630674941271 15513825482033446012411907)
  ·
    refine ⟨23270738223050169018617861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15513825482033446012411907 23270738223050169018617861)
    ·
      refine ⟨4363263416821906690990849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23270738223050169018617861 4363263416821906690990849)
      ·
        refine ⟨3272447562616430018243137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4363263416821906690990849 3272447562616430018243137)
        ·
          refine ⟨2454335671962322513682353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3272447562616430018243137 2454335671962322513682353)
          ·
            refine ⟨1840751753971741885261765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2454335671962322513682353 1840751753971741885261765)
            ·
              refine ⟨345140953869701603486581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1840751753971741885261765 345140953869701603486581)
              ·
                refine ⟨32356964425284525326867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 345140953869701603486581 32356964425284525326867)
                ·
                  rfl

theorem cell21_425351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 5].length) (baseStart_425351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_425351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_425351 prefixEnd_425351 := by exact prefixLift 425351
  have htrace : WordTrace (prefixWord ++ tailWord_425351) baseStart_425351 baseEnd_425351 := by
    simpa [prefixWord, tailWord_425351, baseEnd_425351] using wordTrace_append hprefix tailTrace_425351
  have hstable : (prefixWord ++ tailWord_425351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425351).length < 2 ^ (prefixWord ++ tailWord_425351).sum := by decide
  have hdescent : baseEnd_425351 < baseStart_425351 := by decide
  rcases family_descends (prefixWord ++ tailWord_425351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425368 : List Nat := [2, 1, 2, 5, 3, 1, 7]
def baseStart_425368 : Nat := 118140960795 + 425368 * 2 ^ 59
def prefixEnd_425368 : Nat := 4983230072969 + 3 ^ 40 * 425368 * 2
def baseEnd_425368 : Nat := 10786085878607258244137

theorem tailTrace_425368 : CollatzResearch.WordTrace tailWord_425368 prefixEnd_425368 10786085878607258244137 := by
  unfold tailWord_425368
  simp only [CollatzResearch.WordTrace]
  refine ⟨7757222761485928957890379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10342963681981238610520505 7757222761485928957890379)
  ·
    refine ⟨11635834142228893436835569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7757222761485928957890379 11635834142228893436835569)
    ·
      refine ⟨8726875606671670077626677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11635834142228893436835569 8726875606671670077626677)
      ·
        refine ⟨818144588125469069777501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8726875606671670077626677 818144588125469069777501)
        ·
          refine ⟨306804220547050901166563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 818144588125469069777501 306804220547050901166563)
          ·
            refine ⟨460206330820576351749845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306804220547050901166563 460206330820576351749845)
            ·
              refine ⟨10786085878607258244137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 460206330820576351749845 10786085878607258244137)
              ·
                rfl

theorem cell21_425368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 7].length) (baseStart_425368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_425368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_425368 prefixEnd_425368 := by exact prefixLift 425368
  have htrace : WordTrace (prefixWord ++ tailWord_425368) baseStart_425368 baseEnd_425368 := by
    simpa [prefixWord, tailWord_425368, baseEnd_425368] using wordTrace_append hprefix tailTrace_425368
  have hstable : (prefixWord ++ tailWord_425368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425368).length < 2 ^ (prefixWord ++ tailWord_425368).sum := by decide
  have hdescent : baseEnd_425368 < baseStart_425368 := by decide
  rcases family_descends (prefixWord ++ tailWord_425368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425379 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 6]
def baseStart_425379 : Nat := 118140960795 + 425379 * 2 ^ 59
def prefixEnd_425379 : Nat := 4983230072969 + 3 ^ 40 * 425379 * 2
def baseEnd_425379 : Nat := 97077283257331749513877

theorem tailTrace_425379 : CollatzResearch.WordTrace tailWord_425379 prefixEnd_425379 97077283257331749513877 := by
  unfold tailWord_425379
  simp only [CollatzResearch.WordTrace]
  refine ⟨15514846725932006794431191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10343231150621337862954127 15514846725932006794431191)
  ·
    refine ⟨23272270088898010191646787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15514846725932006794431191 23272270088898010191646787)
    ·
      refine ⟨34908405133347015287470181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23272270088898010191646787 34908405133347015287470181)
      ·
        refine ⟨6545325962502565366400659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34908405133347015287470181 6545325962502565366400659)
        ·
          refine ⟨9817988943753848049600989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6545325962502565366400659 9817988943753848049600989)
          ·
            refine ⟨3681745853907693018600371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9817988943753848049600989 3681745853907693018600371)
            ·
              refine ⟨5522618780861539527900557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3681745853907693018600371 5522618780861539527900557)
              ·
                refine ⟨2070982042823077322962709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5522618780861539527900557 2070982042823077322962709)
                ·
                  refine ⟨97077283257331749513877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2070982042823077322962709 97077283257331749513877)
                  ·
                    rfl

theorem cell21_425379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 6].length) (baseStart_425379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_425379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_425379 prefixEnd_425379 := by exact prefixLift 425379
  have htrace : WordTrace (prefixWord ++ tailWord_425379) baseStart_425379 baseEnd_425379 := by
    simpa [prefixWord, tailWord_425379, baseEnd_425379] using wordTrace_append hprefix tailTrace_425379
  have hstable : (prefixWord ++ tailWord_425379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425379).length < 2 ^ (prefixWord ++ tailWord_425379).sum := by decide
  have hdescent : baseEnd_425379 < baseStart_425379 := by decide
  rcases family_descends (prefixWord ++ tailWord_425379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425424 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 7]
def baseStart_425424 : Nat := 118140960795 + 425424 * 2 ^ 59
def prefixEnd_425424 : Nat := 4983230072969 + 3 ^ 40 * 425424 * 2
def baseEnd_425424 : Nat := 97087552870421671263785

theorem tailTrace_425424 : CollatzResearch.WordTrace tailWord_425424 prefixEnd_425424 97087552870421671263785 := by
  unfold tailWord_425424
  simp only [CollatzResearch.WordTrace]
  refine ⟨7758244005384489739909663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10344325340512652986546217 7758244005384489739909663)
  ·
    refine ⟨11637366008076734609864495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7758244005384489739909663 11637366008076734609864495)
    ·
      refine ⟨17456049012115101914796743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11637366008076734609864495 17456049012115101914796743)
      ·
        refine ⟨26184073518172652872195115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17456049012115101914796743 26184073518172652872195115)
        ·
          refine ⟨39276110277258979308292673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26184073518172652872195115 39276110277258979308292673)
          ·
            refine ⟨29457082707944234481219505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39276110277258979308292673 29457082707944234481219505)
            ·
              refine ⟨22092812030958175860914629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29457082707944234481219505 22092812030958175860914629)
              ·
                refine ⟨4142402255804657973921493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22092812030958175860914629 4142402255804657973921493)
                ·
                  refine ⟨97087552870421671263785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4142402255804657973921493 97087552870421671263785)
                  ·
                    rfl

theorem cell21_425424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_425424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_425424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_425424 prefixEnd_425424 := by exact prefixLift 425424
  have htrace : WordTrace (prefixWord ++ tailWord_425424) baseStart_425424 baseEnd_425424 := by
    simpa [prefixWord, tailWord_425424, baseEnd_425424] using wordTrace_append hprefix tailTrace_425424
  have hstable : (prefixWord ++ tailWord_425424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425424).length < 2 ^ (prefixWord ++ tailWord_425424).sum := by decide
  have hdescent : baseEnd_425424 < baseStart_425424 := by decide
  rcases family_descends (prefixWord ++ tailWord_425424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425430 : List Nat := [5, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_425430 : Nat := 118140960795 + 425430 * 2 ^ 59
def prefixEnd_425430 : Nat := 4983230072969 + 3 ^ 40 * 425430 * 2
def baseEnd_425430 : Nat := 97088922152166994163773

theorem tailTrace_425430 : CollatzResearch.WordTrace tailWord_425430 prefixEnd_425430 97088922152166994163773 := by
  unfold tailWord_425430
  simp only [CollatzResearch.WordTrace]
  refine ⟨969794178046702656533609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10344471232498161669691829 969794178046702656533609)
  ·
    refine ⟨727345633535026992400207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 969794178046702656533609 727345633535026992400207)
    ·
      refine ⟨1091018450302540488600311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 727345633535026992400207 1091018450302540488600311)
      ·
        refine ⟨1636527675453810732900467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1091018450302540488600311 1636527675453810732900467)
        ·
          refine ⟨2454791513180716099350701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636527675453810732900467 2454791513180716099350701)
          ·
            refine ⟨920546817442768537256513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2454791513180716099350701 920546817442768537256513)
            ·
              refine ⟨690410113082076402942385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 920546817442768537256513 690410113082076402942385)
              ·
                refine ⟨517807584811557302206789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 690410113082076402942385 517807584811557302206789)
                ·
                  refine ⟨97088922152166994163773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 517807584811557302206789 97088922152166994163773)
                  ·
                    rfl

theorem cell21_425430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_425430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_425430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_425430 prefixEnd_425430 := by exact prefixLift 425430
  have htrace : WordTrace (prefixWord ++ tailWord_425430) baseStart_425430 baseEnd_425430 := by
    simpa [prefixWord, tailWord_425430, baseEnd_425430] using wordTrace_append hprefix tailTrace_425430
  have hstable : (prefixWord ++ tailWord_425430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425430).length < 2 ^ (prefixWord ++ tailWord_425430).sum := by decide
  have hdescent : baseEnd_425430 < baseStart_425430 := by decide
  rcases family_descends (prefixWord ++ tailWord_425430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425458 : List Nat := [3, 2, 1, 4, 1, 2, 1, 2, 5]
def baseStart_425458 : Nat := 118140960795 + 425458 * 2 ^ 59
def prefixEnd_425458 : Nat := 4983230072969 + 3 ^ 40 * 425458 * 2
def baseEnd_425458 : Nat := 97095312133645167697049

theorem tailTrace_425458 : CollatzResearch.WordTrace tailWord_425458 prefixEnd_425458 97095312133645167697049 := by
  unfold tailWord_425458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3879432023161450821639257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10345152061763868857704685 3879432023161450821639257)
  ·
    refine ⟨2909574017371088116229443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3879432023161450821639257 2909574017371088116229443)
    ·
      refine ⟨4364361026056632174344165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2909574017371088116229443 4364361026056632174344165)
      ·
        refine ⟨818317692385618532689531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4364361026056632174344165 818317692385618532689531)
        ·
          refine ⟨1227476538578427799034297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818317692385618532689531 1227476538578427799034297)
          ·
            refine ⟨920607403933820849275723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1227476538578427799034297 920607403933820849275723)
            ·
              refine ⟨1380911105900731273913585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920607403933820849275723 1380911105900731273913585)
              ·
                refine ⟨1035683329425548455435189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1380911105900731273913585 1035683329425548455435189)
                ·
                  refine ⟨97095312133645167697049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1035683329425548455435189 97095312133645167697049)
                  ·
                    rfl

theorem cell21_425458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_425458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_425458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_425458 prefixEnd_425458 := by exact prefixLift 425458
  have htrace : WordTrace (prefixWord ++ tailWord_425458) baseStart_425458 baseEnd_425458 := by
    simpa [prefixWord, tailWord_425458, baseEnd_425458] using wordTrace_append hprefix tailTrace_425458
  have hstable : (prefixWord ++ tailWord_425458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425458).length < 2 ^ (prefixWord ++ tailWord_425458).sum := by decide
  have hdescent : baseEnd_425458 < baseStart_425458 := by decide
  rcases family_descends (prefixWord ++ tailWord_425458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425624 : List Nat := [2, 1, 2, 4, 1, 2, 2, 3, 4]
def baseStart_425624 : Nat := 118140960795 + 425624 * 2 ^ 59
def prefixEnd_425624 : Nat := 4983230072969 + 3 ^ 40 * 425624 * 2
def baseEnd_425624 : Nat := 97133195595265767930043

theorem tailTrace_425624 : CollatzResearch.WordTrace tailWord_425624 prefixEnd_425624 97133195595265767930043 := by
  unfold tailWord_425624
  simp only [CollatzResearch.WordTrace]
  refine ⟨7761891305022206818549963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10349188406696275758066617 7761891305022206818549963)
  ·
    refine ⟨11642836957533310227824945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7761891305022206818549963 11642836957533310227824945)
    ·
      refine ⟨8732127718149982670868709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11642836957533310227824945 8732127718149982670868709)
      ·
        refine ⟨1637273947153121750787883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8732127718149982670868709 1637273947153121750787883)
        ·
          refine ⟨2455910920729682626181825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1637273947153121750787883 2455910920729682626181825)
          ·
            refine ⟨1841933190547261969636369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2455910920729682626181825 1841933190547261969636369)
            ·
              refine ⟨1381449892910446477227277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1841933190547261969636369 1381449892910446477227277)
              ·
                refine ⟨518043709841417428960229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1381449892910446477227277 518043709841417428960229)
                ·
                  refine ⟨97133195595265767930043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 518043709841417428960229 97133195595265767930043)
                  ·
                    rfl

theorem cell21_425624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_425624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_425624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_425624 prefixEnd_425624 := by exact prefixLift 425624
  have htrace : WordTrace (prefixWord ++ tailWord_425624) baseStart_425624 baseEnd_425624 := by
    simpa [prefixWord, tailWord_425624, baseEnd_425624] using wordTrace_append hprefix tailTrace_425624
  have hstable : (prefixWord ++ tailWord_425624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425624).length < 2 ^ (prefixWord ++ tailWord_425624).sum := by decide
  have hdescent : baseEnd_425624 < baseStart_425624 := by decide
  rcases family_descends (prefixWord ++ tailWord_425624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425762 : List Nat := [3, 3, 1, 1, 2, 1, 2, 5, 3]
def baseStart_425762 : Nat := 118140960795 + 425762 * 2 ^ 59
def prefixEnd_425762 : Nat := 4983230072969 + 3 ^ 40 * 425762 * 2
def baseEnd_425762 : Nat := 97164689075408194629761

theorem tailTrace_425762 : CollatzResearch.WordTrace tailWord_425762 prefixEnd_425762 97164689075408194629761 := by
  unfold tailWord_425762
  simp only [CollatzResearch.WordTrace]
  refine ⟨3882203970886115801405885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10352543922362975470415693 3882203970886115801405885)
  ·
    refine ⟨1455826489082293425527207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3882203970886115801405885 1455826489082293425527207)
    ·
      refine ⟨2183739733623440138290811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1455826489082293425527207 2183739733623440138290811)
      ·
        refine ⟨3275609600435160207436217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2183739733623440138290811 3275609600435160207436217)
        ·
          refine ⟨2456707200326370155577163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3275609600435160207436217 2456707200326370155577163)
          ·
            refine ⟨3685060800489555233365745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2456707200326370155577163 3685060800489555233365745)
            ·
              refine ⟨2763795600367166425024309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3685060800489555233365745 2763795600367166425024309)
              ·
                refine ⟨259105837534421852346029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2763795600367166425024309 259105837534421852346029)
                ·
                  refine ⟨97164689075408194629761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259105837534421852346029 97164689075408194629761)
                  ·
                    rfl

theorem cell21_425762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_425762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_425762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_425762 prefixEnd_425762 := by exact prefixLift 425762
  have htrace : WordTrace (prefixWord ++ tailWord_425762) baseStart_425762 baseEnd_425762 := by
    simpa [prefixWord, tailWord_425762, baseEnd_425762] using wordTrace_append hprefix tailTrace_425762
  have hstable : (prefixWord ++ tailWord_425762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425762).length < 2 ^ (prefixWord ++ tailWord_425762).sum := by decide
  have hdescent : baseEnd_425762 < baseStart_425762 := by decide
  rcases family_descends (prefixWord ++ tailWord_425762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425838 : List Nat := [4, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_425838 : Nat := 118140960795 + 425838 * 2 ^ 59
def prefixEnd_425838 : Nat := 4983230072969 + 3 ^ 40 * 425838 * 2
def baseEnd_425838 : Nat := 97182033310848951362939

theorem tailTrace_425838 : CollatzResearch.WordTrace tailWord_425838 prefixEnd_425838 97182033310848951362939 := by
  unfold tailWord_425838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1941448478908641023173771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10354391887512752123593445 1941448478908641023173771)
  ·
    refine ⟨2912172718362961534760657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1941448478908641023173771 2912172718362961534760657)
    ·
      refine ⟨2184129538772221151070493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2912172718362961534760657 2184129538772221151070493)
      ·
        refine ⟨819048577039582931651435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2184129538772221151070493 819048577039582931651435)
        ·
          refine ⟨1228572865559374397477153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819048577039582931651435 1228572865559374397477153)
          ·
            refine ⟨921429649169530798107865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1228572865559374397477153 921429649169530798107865)
            ·
              refine ⟨691072236877148098580899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 921429649169530798107865 691072236877148098580899)
              ·
                refine ⟨1036608355315722147871349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691072236877148098580899 1036608355315722147871349)
                ·
                  refine ⟨97182033310848951362939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1036608355315722147871349 97182033310848951362939)
                  ·
                    rfl

theorem cell21_425838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_425838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_425838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_425838 prefixEnd_425838 := by exact prefixLift 425838
  have htrace : WordTrace (prefixWord ++ tailWord_425838) baseStart_425838 baseEnd_425838 := by
    simpa [prefixWord, tailWord_425838, baseEnd_425838] using wordTrace_append hprefix tailTrace_425838
  have hstable : (prefixWord ++ tailWord_425838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425838).length < 2 ^ (prefixWord ++ tailWord_425838).sum := by decide
  have hdescent : baseEnd_425838 < baseStart_425838 := by decide
  rcases family_descends (prefixWord ++ tailWord_425838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425849 : List Nat := [1, 2, 1, 3, 2, 2, 2, 8]
def baseStart_425849 : Nat := 118140960795 + 425849 * 2 ^ 59
def prefixEnd_425849 : Nat := 4983230072969 + 3 ^ 40 * 425849 * 2
def baseEnd_425849 : Nat := 32394847886905125559861

theorem tailTrace_425849 : CollatzResearch.WordTrace tailWord_425849 prefixEnd_425849 32394847886905125559861 := by
  unfold tailWord_425849
  simp only [CollatzResearch.WordTrace]
  refine ⟨15531989034229277064040601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10354659356152851376027067 15531989034229277064040601)
  ·
    refine ⟨11648991775671957798030451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15531989034229277064040601 11648991775671957798030451)
    ·
      refine ⟨17473487663507936697045677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11648991775671957798030451 17473487663507936697045677)
      ·
        refine ⟨6552557873815476261392129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17473487663507936697045677 6552557873815476261392129)
        ·
          refine ⟨4914418405361607196044097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6552557873815476261392129 4914418405361607196044097)
          ·
            refine ⟨3685813804021205397033073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4914418405361607196044097 3685813804021205397033073)
            ·
              refine ⟨2764360353015904047774805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3685813804021205397033073 2764360353015904047774805)
              ·
                refine ⟨32394847886905125559861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2764360353015904047774805 32394847886905125559861)
                ·
                  rfl

theorem cell21_425849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 8].length) (baseStart_425849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_425849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_425849 prefixEnd_425849 := by exact prefixLift 425849
  have htrace : WordTrace (prefixWord ++ tailWord_425849) baseStart_425849 baseEnd_425849 := by
    simpa [prefixWord, tailWord_425849, baseEnd_425849] using wordTrace_append hprefix tailTrace_425849
  have hstable : (prefixWord ++ tailWord_425849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425849).length < 2 ^ (prefixWord ++ tailWord_425849).sum := by decide
  have hdescent : baseEnd_425849 < baseStart_425849 := by decide
  rcases family_descends (prefixWord ++ tailWord_425849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425942 : List Nat := [5, 2, 1, 1, 12]
def baseStart_425942 : Nat := 118140960795 + 425942 * 2 ^ 59
def prefixEnd_425942 : Nat := 4983230072969 + 3 ^ 40 * 425942 * 2
def baseEnd_425942 : Nat := 1200071204046517057153

theorem tailTrace_425942 : CollatzResearch.WordTrace tailWord_425942 prefixEnd_425942 1200071204046517057153 := by
  unfold tailWord_425942
  simp only [CollatzResearch.WordTrace]
  refine ⟨970961313930772121698505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10356920681928235964784053 970961313930772121698505)
  ·
    refine ⟨728220985448079091273879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 970961313930772121698505 728220985448079091273879)
    ·
      refine ⟨1092331478172118636910819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 728220985448079091273879 1092331478172118636910819)
      ·
        refine ⟨1638497217258177955366229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092331478172118636910819 1638497217258177955366229)
        ·
          refine ⟨1200071204046517057153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1638497217258177955366229 1200071204046517057153)
          ·
            rfl

theorem cell21_425942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 12].length) (baseStart_425942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_425942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_425942 prefixEnd_425942 := by exact prefixLift 425942
  have htrace : WordTrace (prefixWord ++ tailWord_425942) baseStart_425942 baseEnd_425942 := by
    simpa [prefixWord, tailWord_425942, baseEnd_425942] using wordTrace_append hprefix tailTrace_425942
  have hstable : (prefixWord ++ tailWord_425942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425942).length < 2 ^ (prefixWord ++ tailWord_425942).sum := by decide
  have hdescent : baseEnd_425942 < baseStart_425942 := by decide
  rcases family_descends (prefixWord ++ tailWord_425942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425956 : List Nat := [2, 3, 1, 1, 1, 1, 4, 3, 5]
def baseStart_425956 : Nat := 118140960795 + 425956 * 2 ^ 59
def prefixEnd_425956 : Nat := 4983230072969 + 3 ^ 40 * 425956 * 2
def baseEnd_425956 : Nat := 97208962518506968396031

theorem tailTrace_425956 : CollatzResearch.WordTrace tailWord_425956 prefixEnd_425956 97208962518506968396031 := by
  unfold tailWord_425956
  simp only [CollatzResearch.WordTrace]
  refine ⟨7767945822420817169092861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10357261096561089558790481 7767945822420817169092861)
  ·
    refine ⟨2912979683407806438409823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7767945822420817169092861 2912979683407806438409823)
    ·
      refine ⟨4369469525111709657614735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2912979683407806438409823 4369469525111709657614735)
      ·
        refine ⟨6554204287667564486422103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4369469525111709657614735 6554204287667564486422103)
        ·
          refine ⟨9831306431501346729633155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6554204287667564486422103 9831306431501346729633155)
          ·
            refine ⟨14746959647252020094449733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9831306431501346729633155 14746959647252020094449733)
            ·
              refine ⟨2765054933859753767709325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14746959647252020094449733 2765054933859753767709325)
              ·
                refine ⟨1036895600197407662890997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2765054933859753767709325 1036895600197407662890997)
                ·
                  refine ⟨97208962518506968396031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1036895600197407662890997 97208962518506968396031)
                  ·
                    rfl

theorem cell21_425956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_425956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_425956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_425956 prefixEnd_425956 := by exact prefixLift 425956
  have htrace : WordTrace (prefixWord ++ tailWord_425956) baseStart_425956 baseEnd_425956 := by
    simpa [prefixWord, tailWord_425956, baseEnd_425956] using wordTrace_append hprefix tailTrace_425956
  have hstable : (prefixWord ++ tailWord_425956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425956).length < 2 ^ (prefixWord ++ tailWord_425956).sum := by decide
  have hdescent : baseEnd_425956 < baseStart_425956 := by decide
  rcases family_descends (prefixWord ++ tailWord_425956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425959 : List Nat := [1, 1, 5, 2, 3, 2, 1, 6]
def baseStart_425959 : Nat := 118140960795 + 425959 * 2 ^ 59
def prefixEnd_425959 : Nat := 4983230072969 + 3 ^ 40 * 425959 * 2
def baseEnd_425959 : Nat := 32403215719793209948675

theorem tailTrace_425959 : CollatzResearch.WordTrace tailWord_425959 prefixEnd_425959 32403215719793209948675 := by
  unfold tailWord_425959
  simp only [CollatzResearch.WordTrace]
  refine ⟨15536001063830765850544931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10357334042553843900363287 15536001063830765850544931)
  ·
    refine ⟨23304001595746148775817397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15536001063830765850544931 23304001595746148775817397)
    ·
      refine ⟨2184750149601201447732881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23304001595746148775817397 2184750149601201447732881)
      ·
        refine ⟨1638562612200901085799661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2184750149601201447732881 1638562612200901085799661)
        ·
          refine ⟨614460979575337907174873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1638562612200901085799661 614460979575337907174873)
          ·
            refine ⟨460845734681503430381155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 614460979575337907174873 460845734681503430381155)
            ·
              refine ⟨691268602022255145571733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460845734681503430381155 691268602022255145571733)
              ·
                refine ⟨32403215719793209948675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 691268602022255145571733 32403215719793209948675)
                ·
                  rfl

theorem cell21_425959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 6].length) (baseStart_425959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_425959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_425959 prefixEnd_425959 := by exact prefixLift 425959
  have htrace : WordTrace (prefixWord ++ tailWord_425959) baseStart_425959 baseEnd_425959 := by
    simpa [prefixWord, tailWord_425959, baseEnd_425959] using wordTrace_append hprefix tailTrace_425959
  have hstable : (prefixWord ++ tailWord_425959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425959).length < 2 ^ (prefixWord ++ tailWord_425959).sum := by decide
  have hdescent : baseEnd_425959 < baseStart_425959 := by decide
  rcases family_descends (prefixWord ++ tailWord_425959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426032 : List Nat := [2, 1, 1, 1, 2, 5, 2, 2, 5]
def baseStart_426032 : Nat := 118140960795 + 426032 * 2 ^ 59
def prefixEnd_426032 : Nat := 4983230072969 + 3 ^ 40 * 426032 * 2
def baseEnd_426032 : Nat := 97226306753947725129209

theorem tailTrace_426032 : CollatzResearch.WordTrace tailWord_426032 prefixEnd_426032 97226306753947725129209 := by
  unfold tailWord_426032
  simp only [CollatzResearch.WordTrace]
  refine ⟨7769331796283149658976175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10359109061710866211968233 7769331796283149658976175)
  ·
    refine ⟨11653997694424724488464263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7769331796283149658976175 11653997694424724488464263)
    ·
      refine ⟨17480996541637086732696395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11653997694424724488464263 17480996541637086732696395)
      ·
        refine ⟨26221494812455630099044593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17480996541637086732696395 26221494812455630099044593)
        ·
          refine ⟨19666121109341722574283445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26221494812455630099044593 19666121109341722574283445)
          ·
            refine ⟨1843698854000786491339073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19666121109341722574283445 1843698854000786491339073)
            ·
              refine ⟨1382774140500589868504305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1843698854000786491339073 1382774140500589868504305)
              ·
                refine ⟨1037080605375442401378229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1382774140500589868504305 1037080605375442401378229)
                ·
                  refine ⟨97226306753947725129209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1037080605375442401378229 97226306753947725129209)
                  ·
                    rfl

theorem cell21_426032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_426032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_426032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_426032 prefixEnd_426032 := by exact prefixLift 426032
  have htrace : WordTrace (prefixWord ++ tailWord_426032) baseStart_426032 baseEnd_426032 := by
    simpa [prefixWord, tailWord_426032, baseEnd_426032] using wordTrace_append hprefix tailTrace_426032
  have hstable : (prefixWord ++ tailWord_426032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426032).length < 2 ^ (prefixWord ++ tailWord_426032).sum := by decide
  have hdescent : baseEnd_426032 < baseStart_426032 := by decide
  rcases family_descends (prefixWord ++ tailWord_426032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426066 : List Nat := [3, 2, 2, 1, 4, 2, 1, 1, 5]
def baseStart_426066 : Nat := 118140960795 + 426066 * 2 ^ 59
def prefixEnd_426066 : Nat := 4983230072969 + 3 ^ 40 * 426066 * 2
def baseEnd_426066 : Nat := 97234066017171221562473

theorem tailTrace_426066 : CollatzResearch.WordTrace tailWord_426066 prefixEnd_426066 97234066017171221562473 := by
  unfold tailWord_426066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3884975918610780781172513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10359935782962082083126701 3884975918610780781172513)
  ·
    refine ⟨2913731938958085585879385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3884975918610780781172513 2913731938958085585879385)
    ·
      refine ⟨2185298954218564189409539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2913731938958085585879385 2185298954218564189409539)
      ·
        refine ⟨3277948431327846284114309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2185298954218564189409539 3277948431327846284114309)
        ·
          refine ⟨614615330873971178271433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3277948431327846284114309 614615330873971178271433)
          ·
            refine ⟨460961498155478383703575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 614615330873971178271433 460961498155478383703575)
            ·
              refine ⟨691442247233217575555363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460961498155478383703575 691442247233217575555363)
              ·
                refine ⟨1037163370849826363333045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691442247233217575555363 1037163370849826363333045)
                ·
                  refine ⟨97234066017171221562473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1037163370849826363333045 97234066017171221562473)
                  ·
                    rfl

theorem cell21_426066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_426066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_426066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_426066 prefixEnd_426066 := by exact prefixLift 426066
  have htrace : WordTrace (prefixWord ++ tailWord_426066) baseStart_426066 baseEnd_426066 := by
    simpa [prefixWord, tailWord_426066, baseEnd_426066] using wordTrace_append hprefix tailTrace_426066
  have hstable : (prefixWord ++ tailWord_426066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426066).length < 2 ^ (prefixWord ++ tailWord_426066).sum := by decide
  have hdescent : baseEnd_426066 < baseStart_426066 := by decide
  rcases family_descends (prefixWord ++ tailWord_426066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426080 : List Nat := [2, 1, 1, 3, 2, 3, 4, 1, 4]
def baseStart_426080 : Nat := 118140960795 + 426080 * 2 ^ 59
def prefixEnd_426080 : Nat := 4983230072969 + 3 ^ 40 * 426080 * 2
def baseEnd_426080 : Nat := 97237261007910308329111

theorem tailTrace_426080 : CollatzResearch.WordTrace tailWord_426080 prefixEnd_426080 97237261007910308329111 := by
  unfold tailWord_426080
  simp only [CollatzResearch.WordTrace]
  refine ⟨7770207148196201757849847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10360276197594935677133129 7770207148196201757849847)
  ·
    refine ⟨11655310722294302636774771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7770207148196201757849847 11655310722294302636774771)
    ·
      refine ⟨17482966083441453955162157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11655310722294302636774771 17482966083441453955162157)
      ·
        refine ⟨6556112281290545233185809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17482966083441453955162157 6556112281290545233185809)
        ·
          refine ⟨4917084210967908924889357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6556112281290545233185809 4917084210967908924889357)
          ·
            refine ⟨1843906579112965846833509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4917084210967908924889357 1843906579112965846833509)
            ·
              refine ⟨345732483583681096281283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1843906579112965846833509 345732483583681096281283)
              ·
                refine ⟨518598725375521644421925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345732483583681096281283 518598725375521644421925)
                ·
                  refine ⟨97237261007910308329111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 518598725375521644421925 97237261007910308329111)
                  ·
                    rfl

theorem cell21_426080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 4].length) (baseStart_426080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_426080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_426080 prefixEnd_426080 := by exact prefixLift 426080
  have htrace : WordTrace (prefixWord ++ tailWord_426080) baseStart_426080 baseEnd_426080 := by
    simpa [prefixWord, tailWord_426080, baseEnd_426080] using wordTrace_append hprefix tailTrace_426080
  have hstable : (prefixWord ++ tailWord_426080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426080).length < 2 ^ (prefixWord ++ tailWord_426080).sum := by decide
  have hdescent : baseEnd_426080 < baseStart_426080 := by decide
  rcases family_descends (prefixWord ++ tailWord_426080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426142 : List Nat := [4, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_426142 : Nat := 118140960795 + 426142 * 2 ^ 59
def prefixEnd_426142 : Nat := 4983230072969 + 3 ^ 40 * 426142 * 2
def baseEnd_426142 : Nat := 97251410252611978295651

theorem tailTrace_426142 : CollatzResearch.WordTrace tailWord_426142 prefixEnd_426142 97251410252611978295651 := by
  unfold tailWord_426142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1942834452770973513057085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10361783748111858736304453 1942834452770973513057085)
  ·
    refine ⟨728562919789115067396407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1942834452770973513057085 728562919789115067396407)
    ·
      refine ⟨1092844379683672601094611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 728562919789115067396407 1092844379683672601094611)
      ·
        refine ⟨1639266569525508901641917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092844379683672601094611 1639266569525508901641917)
        ·
          refine ⟨614724963572065838115719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1639266569525508901641917 614724963572065838115719)
          ·
            refine ⟨922087445358098757173579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614724963572065838115719 922087445358098757173579)
            ·
              refine ⟨1383131168037148135760369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922087445358098757173579 1383131168037148135760369)
              ·
                refine ⟨1037348376027861101820277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1383131168037148135760369 1037348376027861101820277)
                ·
                  refine ⟨97251410252611978295651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1037348376027861101820277 97251410252611978295651)
                  ·
                    rfl

theorem cell21_426142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_426142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_426142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_426142 prefixEnd_426142 := by exact prefixLift 426142
  have htrace : WordTrace (prefixWord ++ tailWord_426142) baseStart_426142 baseEnd_426142 := by
    simpa [prefixWord, tailWord_426142, baseEnd_426142] using wordTrace_append hprefix tailTrace_426142
  have hstable : (prefixWord ++ tailWord_426142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426142).length < 2 ^ (prefixWord ++ tailWord_426142).sum := by decide
  have hdescent : baseEnd_426142 < baseStart_426142 := by decide
  rcases family_descends (prefixWord ++ tailWord_426142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426210 : List Nat := [3, 3, 4, 1, 2, 1, 1, 3, 3]
def baseStart_426210 : Nat := 118140960795 + 426210 * 2 ^ 59
def prefixEnd_426210 : Nat := 4983230072969 + 3 ^ 40 * 426210 * 2
def baseEnd_426210 : Nat := 97266928779058971162179

theorem tailTrace_426210 : CollatzResearch.WordTrace tailWord_426210 prefixEnd_426210 97266928779058971162179 := by
  unfold tailWord_426210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3886288946480358929483021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10363437190614290478621389 3886288946480358929483021)
  ·
    refine ⟨1457358354930134598556133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3886288946480358929483021 1457358354930134598556133)
    ·
      refine ⟨273254691549400237229275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1457358354930134598556133 273254691549400237229275)
      ·
        refine ⟨409882037324100355843913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273254691549400237229275 409882037324100355843913)
        ·
          refine ⟨307411527993075266882935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409882037324100355843913 307411527993075266882935)
          ·
            refine ⟨461117291989612900324403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307411527993075266882935 461117291989612900324403)
            ·
              refine ⟨691675937984419350486605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461117291989612900324403 691675937984419350486605)
              ·
                refine ⟨259378476744157256432477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 691675937984419350486605 259378476744157256432477)
                ·
                  refine ⟨97266928779058971162179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259378476744157256432477 97266928779058971162179)
                  ·
                    rfl

theorem cell21_426210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_426210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_426210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_426210 prefixEnd_426210 := by exact prefixLift 426210
  have htrace : WordTrace (prefixWord ++ tailWord_426210) baseStart_426210 baseEnd_426210 := by
    simpa [prefixWord, tailWord_426210, baseEnd_426210] using wordTrace_append hprefix tailTrace_426210
  have hstable : (prefixWord ++ tailWord_426210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426210).length < 2 ^ (prefixWord ++ tailWord_426210).sum := by decide
  have hdescent : baseEnd_426210 < baseStart_426210 := by decide
  rcases family_descends (prefixWord ++ tailWord_426210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426215 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 6]
def baseStart_426215 : Nat := 118140960795 + 426215 * 2 ^ 59
def prefixEnd_426215 : Nat := 4983230072969 + 3 ^ 40 * 426215 * 2
def baseEnd_426215 : Nat := 97268069847180073578835

theorem tailTrace_426215 : CollatzResearch.WordTrace tailWord_426215 prefixEnd_426215 97268069847180073578835 := by
  unfold tailWord_426215
  simp only [CollatzResearch.WordTrace]
  refine ⟨15545338150903321571864099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10363558767268881047909399 15545338150903321571864099)
  ·
    refine ⟨23318007226354982357796149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15545338150903321571864099 23318007226354982357796149)
    ·
      refine ⟨2186063177470779596043389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23318007226354982357796149 2186063177470779596043389)
      ·
        refine ⟨819773691551542348516271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2186063177470779596043389 819773691551542348516271)
        ·
          refine ⟨1229660537327313522774407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819773691551542348516271 1229660537327313522774407)
          ·
            refine ⟨1844490805990970284161611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229660537327313522774407 1844490805990970284161611)
            ·
              refine ⟨2766736208986455426242417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1844490805990970284161611 2766736208986455426242417)
              ·
                refine ⟨2075052156739841569681813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2766736208986455426242417 2075052156739841569681813)
                ·
                  refine ⟨97268069847180073578835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2075052156739841569681813 97268069847180073578835)
                  ·
                    rfl

theorem cell21_426215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 6].length) (baseStart_426215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_426215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_426215 prefixEnd_426215 := by exact prefixLift 426215
  have htrace : WordTrace (prefixWord ++ tailWord_426215) baseStart_426215 baseEnd_426215 := by
    simpa [prefixWord, tailWord_426215, baseEnd_426215] using wordTrace_append hprefix tailTrace_426215
  have hstable : (prefixWord ++ tailWord_426215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426215).length < 2 ^ (prefixWord ++ tailWord_426215).sum := by decide
  have hdescent : baseEnd_426215 < baseStart_426215 := by decide
  rcases family_descends (prefixWord ++ tailWord_426215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426291 : List Nat := [1, 1, 1, 2, 5, 1, 4, 2, 4]
def baseStart_426291 : Nat := 118140960795 + 426291 * 2 ^ 59
def prefixEnd_426291 : Nat := 4983230072969 + 3 ^ 40 * 426291 * 2
def baseEnd_426291 : Nat := 97285414082620830312013

theorem tailTrace_426291 : CollatzResearch.WordTrace tailWord_426291 prefixEnd_426291 97285414082620830312013 := by
  unfold tailWord_426291
  simp only [CollatzResearch.WordTrace]
  refine ⟨15548110098627986551630727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10365406732418657701087151 15548110098627986551630727)
  ·
    refine ⟨23322165147941979827446091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15548110098627986551630727 23322165147941979827446091)
    ·
      refine ⟨34983247721912969741169137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23322165147941979827446091 34983247721912969741169137)
      ·
        refine ⟨26237435791434727305876853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34983247721912969741169137 26237435791434727305876853)
        ·
          refine ⟨2459759605447005684925955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26237435791434727305876853 2459759605447005684925955)
          ·
            refine ⟨3689639408170508527388933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2459759605447005684925955 3689639408170508527388933)
            ·
              refine ⟨691807389031970348885425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3689639408170508527388933 691807389031970348885425)
              ·
                refine ⟨518855541773977761664069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 691807389031970348885425 518855541773977761664069)
                ·
                  refine ⟨97285414082620830312013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 518855541773977761664069 97285414082620830312013)
                  ·
                    rfl

theorem cell21_426291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 4].length) (baseStart_426291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_426291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_426291 prefixEnd_426291 := by exact prefixLift 426291
  have htrace : WordTrace (prefixWord ++ tailWord_426291) baseStart_426291 baseEnd_426291 := by
    simpa [prefixWord, tailWord_426291, baseEnd_426291] using wordTrace_append hprefix tailTrace_426291
  have hstable : (prefixWord ++ tailWord_426291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426291).length < 2 ^ (prefixWord ++ tailWord_426291).sum := by decide
  have hdescent : baseEnd_426291 < baseStart_426291 := by decide
  rcases family_descends (prefixWord ++ tailWord_426291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426398 : List Nat := [4, 3, 1, 2, 1, 1, 9]
def baseStart_426398 : Nat := 118140960795 + 426398 * 2 ^ 59
def prefixEnd_426398 : Nat := 4983230072969 + 3 ^ 40 * 426398 * 2
def baseEnd_426398 : Nat := 10812203660045824669829

theorem tailTrace_426398 : CollatzResearch.WordTrace tailWord_426398 prefixEnd_426398 10812203660045824669829 := by
  unfold tailWord_426398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1944001588655042978221981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10368008472826895883850565 1944001588655042978221981)
  ·
    refine ⟨729000595745641116833243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1944001588655042978221981 729000595745641116833243)
    ·
      refine ⟨1093500893618461675249865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 729000595745641116833243 1093500893618461675249865)
      ·
        refine ⟨820125670213846256437399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1093500893618461675249865 820125670213846256437399)
        ·
          refine ⟨1230188505320769384656099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820125670213846256437399 1230188505320769384656099)
          ·
            refine ⟨1845282757981154076984149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230188505320769384656099 1845282757981154076984149)
            ·
              refine ⟨10812203660045824669829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1845282757981154076984149 10812203660045824669829)
              ·
                rfl

theorem cell21_426398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 9].length) (baseStart_426398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_426398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_426398 prefixEnd_426398 := by exact prefixLift 426398
  have htrace : WordTrace (prefixWord ++ tailWord_426398) baseStart_426398 baseEnd_426398 := by
    simpa [prefixWord, tailWord_426398, baseEnd_426398] using wordTrace_append hprefix tailTrace_426398
  have hstable : (prefixWord ++ tailWord_426398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426398).length < 2 ^ (prefixWord ++ tailWord_426398).sum := by decide
  have hdescent : baseEnd_426398 < baseStart_426398 := by decide
  rcases family_descends (prefixWord ++ tailWord_426398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426474 : List Nat := [3, 1, 3, 1, 3, 3, 1, 6]
def baseStart_426474 : Nat := 118140960795 + 426474 * 2 ^ 59
def prefixEnd_426474 : Nat := 4983230072969 + 3 ^ 40 * 426474 * 2
def baseEnd_426474 : Nat := 32442392391951059587213

theorem tailTrace_426474 : CollatzResearch.WordTrace tailWord_426474 prefixEnd_426474 32442392391951059587213 := by
  unfold tailWord_426474
  simp only [CollatzResearch.WordTrace]
  refine ⟨3888696164241252201385619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10369856437976672537028317 3888696164241252201385619)
  ·
    refine ⟨5833044246361878302078429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3888696164241252201385619 5833044246361878302078429)
    ·
      refine ⟨2187391592385704363279411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5833044246361878302078429 2187391592385704363279411)
      ·
        refine ⟨3281087388578556544919117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2187391592385704363279411 3281087388578556544919117)
        ·
          refine ⟨1230407770716958704344669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3281087388578556544919117 1230407770716958704344669)
          ·
            refine ⟨461402914018859514129251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1230407770716958704344669 461402914018859514129251)
            ·
              refine ⟨692104371028289271193877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461402914018859514129251 692104371028289271193877)
              ·
                refine ⟨32442392391951059587213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 692104371028289271193877 32442392391951059587213)
                ·
                  rfl

theorem cell21_426474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_426474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_426474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_426474 prefixEnd_426474 := by exact prefixLift 426474
  have htrace : WordTrace (prefixWord ++ tailWord_426474) baseStart_426474 baseEnd_426474 := by
    simpa [prefixWord, tailWord_426474, baseEnd_426474] using wordTrace_append hprefix tailTrace_426474
  have hstable : (prefixWord ++ tailWord_426474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426474).length < 2 ^ (prefixWord ++ tailWord_426474).sum := by decide
  have hdescent : baseEnd_426474 < baseStart_426474 := by decide
  rcases family_descends (prefixWord ++ tailWord_426474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426547 : List Nat := [1, 1, 1, 2, 4, 2, 1, 4, 5]
def baseStart_426547 : Nat := 118140960795 + 426547 * 2 ^ 59
def prefixEnd_426547 : Nat := 4983230072969 + 3 ^ 40 * 426547 * 2
def baseEnd_426547 : Nat := 97343836770421274044823

theorem tailTrace_426547 : CollatzResearch.WordTrace tailWord_426547 prefixEnd_426547 97343836770421274044823 := by
  unfold tailWord_426547
  simp only [CollatzResearch.WordTrace]
  refine ⟨15557447185700542272949895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10371631457133694848633263 15557447185700542272949895)
  ·
    refine ⟨23336170778550813409424843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15557447185700542272949895 23336170778550813409424843)
    ·
      refine ⟨35004256167826220114137265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23336170778550813409424843 35004256167826220114137265)
      ·
        refine ⟨26253192125869665085602949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35004256167826220114137265 26253192125869665085602949)
        ·
          refine ⟨4922473523600562203550553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26253192125869665085602949 4922473523600562203550553)
          ·
            refine ⟨3691855142700421652662915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4922473523600562203550553 3691855142700421652662915)
            ·
              refine ⟨5537782714050632478994373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3691855142700421652662915 5537782714050632478994373)
              ·
                refine ⟨1038334258884493589811445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5537782714050632478994373 1038334258884493589811445)
                ·
                  refine ⟨97343836770421274044823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1038334258884493589811445 97343836770421274044823)
                  ·
                    rfl

theorem cell21_426547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 5].length) (baseStart_426547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_426547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_426547 prefixEnd_426547 := by exact prefixLift 426547
  have htrace : WordTrace (prefixWord ++ tailWord_426547) baseStart_426547 baseEnd_426547 := by
    simpa [prefixWord, tailWord_426547, baseEnd_426547] using wordTrace_append hprefix tailTrace_426547
  have hstable : (prefixWord ++ tailWord_426547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426547).length < 2 ^ (prefixWord ++ tailWord_426547).sum := by decide
  have hdescent : baseEnd_426547 < baseStart_426547 := by decide
  rcases family_descends (prefixWord ++ tailWord_426547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426550 : List Nat := [5, 1, 2, 1, 2, 2, 1, 7]
def baseStart_426550 : Nat := 118140960795 + 426550 * 2 ^ 59
def prefixEnd_426550 : Nat := 4983230072969 + 3 ^ 40 * 426550 * 2
def baseEnd_426550 : Nat := 32448173803764645164939

theorem tailTrace_426550 : CollatzResearch.WordTrace tailWord_426550 prefixEnd_426550 32448173803764645164939 := by
  unfold tailWord_426550
  simp only [CollatzResearch.WordTrace]
  refine ⟨972347287793104611581819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10371704403126449190206069 972347287793104611581819)
  ·
    refine ⟨1458520931689656917372729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 972347287793104611581819 1458520931689656917372729)
    ·
      refine ⟨1093890698767242688029547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1458520931689656917372729 1093890698767242688029547)
      ·
        refine ⟨1640836048150864032044321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1093890698767242688029547 1640836048150864032044321)
        ·
          refine ⟨1230627036113148024033241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1640836048150864032044321 1230627036113148024033241)
          ·
            refine ⟨922970277084861018024931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1230627036113148024033241 922970277084861018024931)
            ·
              refine ⟨1384455415627291527037397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922970277084861018024931 1384455415627291527037397)
              ·
                refine ⟨32448173803764645164939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1384455415627291527037397 32448173803764645164939)
                ·
                  rfl

theorem cell21_426550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_426550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_426550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_426550 prefixEnd_426550 := by exact prefixLift 426550
  have htrace : WordTrace (prefixWord ++ tailWord_426550) baseStart_426550 baseEnd_426550 := by
    simpa [prefixWord, tailWord_426550, baseEnd_426550] using wordTrace_append hprefix tailTrace_426550
  have hstable : (prefixWord ++ tailWord_426550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426550).length < 2 ^ (prefixWord ++ tailWord_426550).sum := by decide
  have hdescent : baseEnd_426550 < baseStart_426550 := by decide
  rcases family_descends (prefixWord ++ tailWord_426550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426578 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 6]
def baseStart_426578 : Nat := 118140960795 + 426578 * 2 ^ 59
def prefixEnd_426578 : Nat := 4983230072969 + 3 ^ 40 * 426578 * 2
def baseEnd_426578 : Nat := 97350911392772109028093

theorem tailTrace_426578 : CollatzResearch.WordTrace tailWord_426578 prefixEnd_426578 97350911392772109028093 := by
  unfold tailWord_426578
  simp only [CollatzResearch.WordTrace]
  refine ⟨3889644462147058641832097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10372385232392156378218925 3889644462147058641832097)
  ·
    refine ⟨2917233346610293981374073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3889644462147058641832097 2917233346610293981374073)
    ·
      refine ⟨2187925009957720486030555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2917233346610293981374073 2187925009957720486030555)
      ·
        refine ⟨3281887514936580729045833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2187925009957720486030555 3281887514936580729045833)
        ·
          refine ⟨2461415636202435546784375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3281887514936580729045833 2461415636202435546784375)
          ·
            refine ⟨3692123454303653320176563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461415636202435546784375 3692123454303653320176563)
            ·
              refine ⟨5538185181455479980264845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3692123454303653320176563 5538185181455479980264845)
              ·
                refine ⟨2076819443045804992599317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5538185181455479980264845 2076819443045804992599317)
                ·
                  refine ⟨97350911392772109028093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2076819443045804992599317 97350911392772109028093)
                  ·
                    rfl

theorem cell21_426578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_426578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_426578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_426578 prefixEnd_426578 := by exact prefixLift 426578
  have htrace : WordTrace (prefixWord ++ tailWord_426578) baseStart_426578 baseEnd_426578 := by
    simpa [prefixWord, tailWord_426578, baseEnd_426578] using wordTrace_append hprefix tailTrace_426578
  have hstable : (prefixWord ++ tailWord_426578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426578).length < 2 ^ (prefixWord ++ tailWord_426578).sum := by decide
  have hdescent : baseEnd_426578 < baseStart_426578 := by decide
  rcases family_descends (prefixWord ++ tailWord_426578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426592 : List Nat := [2, 1, 1, 3, 2, 1, 3, 8]
def baseStart_426592 : Nat := 118140960795 + 426592 * 2 ^ 59
def prefixEnd_426592 : Nat := 4983230072969 + 3 ^ 40 * 426592 * 2
def baseEnd_426592 : Nat := 32451368794503731931577

theorem tailTrace_426592 : CollatzResearch.WordTrace tailWord_426592 prefixEnd_426592 32451368794503731931577 := by
  unfold tailWord_426592
  simp only [CollatzResearch.WordTrace]
  refine ⟨7779544235268757479169015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10372725647025009972225353 7779544235268757479169015)
  ·
    refine ⟨11669316352903136218753523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7779544235268757479169015 11669316352903136218753523)
    ·
      refine ⟨17503974529354704328130285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11669316352903136218753523 17503974529354704328130285)
      ·
        refine ⟨6563990448508014123048857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17503974529354704328130285 6563990448508014123048857)
        ·
          refine ⟨4922992836381010592286643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6563990448508014123048857 4922992836381010592286643)
          ·
            refine ⟨7384489254571515888429965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4922992836381010592286643 7384489254571515888429965)
            ·
              refine ⟨2769183470464318458161237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7384489254571515888429965 2769183470464318458161237)
              ·
                refine ⟨32451368794503731931577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2769183470464318458161237 32451368794503731931577)
                ·
                  rfl

theorem cell21_426592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 8].length) (baseStart_426592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_426592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_426592 prefixEnd_426592 := by exact prefixLift 426592
  have htrace : WordTrace (prefixWord ++ tailWord_426592) baseStart_426592 baseEnd_426592 := by
    simpa [prefixWord, tailWord_426592, baseEnd_426592] using wordTrace_append hprefix tailTrace_426592
  have hstable : (prefixWord ++ tailWord_426592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426592).length < 2 ^ (prefixWord ++ tailWord_426592).sum := by decide
  have hdescent : baseEnd_426592 < baseStart_426592 := by decide
  rcases family_descends (prefixWord ++ tailWord_426592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426837 : List Nat := [1, 3, 2, 2, 2, 1, 5, 5]
def baseStart_426837 : Nat := 118140960795 + 426837 * 2 ^ 59
def prefixEnd_426837 : Nat := 4983230072969 + 3 ^ 40 * 426837 * 2
def baseEnd_426837 : Nat := 32470006240481738070299

theorem tailTrace_426837 : CollatzResearch.WordTrace tailWord_426837 prefixEnd_426837 32470006240481738070299 := by
  unfold tailWord_426837
  simp only [CollatzResearch.WordTrace]
  refine ⟨15568024354649921801006765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10378682903099947867337843 15568024354649921801006765)
  ·
    refine ⟨5838009132993720675377537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15568024354649921801006765 5838009132993720675377537)
    ·
      refine ⟨4378506849745290506533153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5838009132993720675377537 4378506849745290506533153)
      ·
        refine ⟨3283880137308967879899865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4378506849745290506533153 3283880137308967879899865)
        ·
          refine ⟨2462910102981725909924899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3283880137308967879899865 2462910102981725909924899)
          ·
            refine ⟨3694365154472588864887349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2462910102981725909924899 3694365154472588864887349)
            ·
              refine ⟨346346733231805206083189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3694365154472588864887349 346346733231805206083189)
              ·
                refine ⟨32470006240481738070299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 346346733231805206083189 32470006240481738070299)
                ·
                  rfl

theorem cell21_426837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 5].length) (baseStart_426837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_426837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_426837 prefixEnd_426837 := by exact prefixLift 426837
  have htrace : WordTrace (prefixWord ++ tailWord_426837) baseStart_426837 baseEnd_426837 := by
    simpa [prefixWord, tailWord_426837, baseEnd_426837] using wordTrace_append hprefix tailTrace_426837
  have hstable : (prefixWord ++ tailWord_426837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426837).length < 2 ^ (prefixWord ++ tailWord_426837).sum := by decide
  have hdescent : baseEnd_426837 < baseStart_426837 := by decide
  rcases family_descends (prefixWord ++ tailWord_426837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426913 : List Nat := [1, 2, 3, 4, 1, 3, 7]
def baseStart_426913 : Nat := 118140960795 + 426913 * 2 ^ 59
def prefixEnd_426913 : Nat := 4983230072969 + 3 ^ 40 * 426913 * 2
def baseEnd_426913 : Nat := 10825262550765107882675

theorem tailTrace_426913 : CollatzResearch.WordTrace tailWord_426913 prefixEnd_426913 10825262550765107882675 := by
  unfold tailWord_426913
  simp only [CollatzResearch.WordTrace]
  refine ⟨15570796302374586780773393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10380530868249724520515595 15570796302374586780773393)
  ·
    refine ⟨11678097226780940085580045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15570796302374586780773393 11678097226780940085580045)
    ·
      refine ⟨4379286460042852532092517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11678097226780940085580045 4379286460042852532092517)
      ·
        refine ⟨821116211258034849767347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4379286460042852532092517 821116211258034849767347)
        ·
          refine ⟨1231674316887052274651021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821116211258034849767347 1231674316887052274651021)
          ·
            refine ⟨461877868832644602994133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1231674316887052274651021 461877868832644602994133)
            ·
              refine ⟨10825262550765107882675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 461877868832644602994133 10825262550765107882675)
              ·
                rfl

theorem cell21_426913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 7].length) (baseStart_426913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_426913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_426913 prefixEnd_426913 := by exact prefixLift 426913
  have htrace : WordTrace (prefixWord ++ tailWord_426913) baseStart_426913 baseEnd_426913 := by
    simpa [prefixWord, tailWord_426913, baseEnd_426913] using wordTrace_append hprefix tailTrace_426913
  have hstable : (prefixWord ++ tailWord_426913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426913).length < 2 ^ (prefixWord ++ tailWord_426913).sum := by decide
  have hdescent : baseEnd_426913 < baseStart_426913 := by decide
  rcases family_descends (prefixWord ++ tailWord_426913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426975 : List Nat := [1, 1, 2, 3, 5, 1, 2, 2, 4]
def baseStart_426975 : Nat := 118140960795 + 426975 * 2 ^ 59
def prefixEnd_426975 : Nat := 4983230072969 + 3 ^ 40 * 426975 * 2
def baseEnd_426975 : Nat := 97441512201587640910615

theorem tailTrace_426975 : CollatzResearch.WordTrace tailWord_426975 prefixEnd_426975 97441512201587640910615 := by
  unfold tailWord_426975
  simp only [CollatzResearch.WordTrace]
  refine ⟨15573057628149971369530379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10382038418766647579686919 15573057628149971369530379)
  ·
    refine ⟨23359586442224957054295569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15573057628149971369530379 23359586442224957054295569)
    ·
      refine ⟨17519689831668717790721677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23359586442224957054295569 17519689831668717790721677)
      ·
        refine ⟨6569883686875769171520629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17519689831668717790721677 6569883686875769171520629)
        ·
          refine ⟨615926595644603359830059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6569883686875769171520629 615926595644603359830059)
          ·
            refine ⟨923889893466905039745089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615926595644603359830059 923889893466905039745089)
            ·
              refine ⟨692917420100178779808817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 923889893466905039745089 692917420100178779808817)
              ·
                refine ⟨519688065075134084856613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 692917420100178779808817 519688065075134084856613)
                ·
                  refine ⟨97441512201587640910615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 519688065075134084856613 97441512201587640910615)
                  ·
                    rfl

theorem cell21_426975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 4].length) (baseStart_426975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_426975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_426975 prefixEnd_426975 := by exact prefixLift 426975
  have htrace : WordTrace (prefixWord ++ tailWord_426975) baseStart_426975 baseEnd_426975 := by
    simpa [prefixWord, tailWord_426975, baseEnd_426975] using wordTrace_append hprefix tailTrace_426975
  have hstable : (prefixWord ++ tailWord_426975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426975).length < 2 ^ (prefixWord ++ tailWord_426975).sum := by decide
  have hdescent : baseEnd_426975 < baseStart_426975 := by decide
  rcases family_descends (prefixWord ++ tailWord_426975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426978 : List Nat := [3, 3, 3, 1, 1, 2, 1, 4, 3]
def baseStart_426978 : Nat := 118140960795 + 426978 * 2 ^ 59
def prefixEnd_426978 : Nat := 4983230072969 + 3 ^ 40 * 426978 * 2
def baseEnd_426978 : Nat := 97442196842460302360609

theorem tailTrace_426978 : CollatzResearch.WordTrace tailWord_426978 prefixEnd_426978 97442196842460302360609 := by
  unfold tailWord_426978
  simp only [CollatzResearch.WordTrace]
  refine ⟨3893291761784775720472397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10382111364759401921259725 3893291761784775720472397)
  ·
    refine ⟨1459984410669290895177149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3893291761784775720472397 1459984410669290895177149)
    ·
      refine ⟨547494154000984085691431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1459984410669290895177149 547494154000984085691431)
      ·
        refine ⟨821241231001476128537147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547494154000984085691431 821241231001476128537147)
        ·
          refine ⟨1231861846502214192805721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821241231001476128537147 1231861846502214192805721)
          ·
            refine ⟨923896384876660644604291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1231861846502214192805721 923896384876660644604291)
            ·
              refine ⟨1385844577314990966906437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923896384876660644604291 1385844577314990966906437)
              ·
                refine ⟨259845858246560806294957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1385844577314990966906437 259845858246560806294957)
                ·
                  refine ⟨97442196842460302360609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259845858246560806294957 97442196842460302360609)
                  ·
                    rfl

theorem cell21_426978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_426978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_426978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_426978 prefixEnd_426978 := by exact prefixLift 426978
  have htrace : WordTrace (prefixWord ++ tailWord_426978) baseStart_426978 baseEnd_426978 := by
    simpa [prefixWord, tailWord_426978, baseEnd_426978] using wordTrace_append hprefix tailTrace_426978
  have hstable : (prefixWord ++ tailWord_426978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426978).length < 2 ^ (prefixWord ++ tailWord_426978).sum := by decide
  have hdescent : baseEnd_426978 < baseStart_426978 := by decide
  rcases family_descends (prefixWord ++ tailWord_426978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427020 : List Nat := [2, 2, 1, 2, 3, 2, 1, 5, 3]
def baseStart_427020 : Nat := 118140960795 + 427020 * 2 ^ 59
def prefixEnd_427020 : Nat := 4983230072969 + 3 ^ 40 * 427020 * 2
def baseEnd_427020 : Nat := 97451781814677562660523

theorem tailTrace_427020 : CollatzResearch.WordTrace tailWord_427020 prefixEnd_427020 97451781814677562660523 := by
  unfold tailWord_427020
  simp only [CollatzResearch.WordTrace]
  refine ⟨7787349456493472027459257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10383132608657962703279009 7787349456493472027459257)
  ·
    refine ⟨5840512092370104020594443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7787349456493472027459257 5840512092370104020594443)
    ·
      refine ⟨8760768138555156030891665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5840512092370104020594443 8760768138555156030891665)
      ·
        refine ⟨6570576103916367023168749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8760768138555156030891665 6570576103916367023168749)
        ·
          refine ⟨2463966038968637633688281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6570576103916367023168749 2463966038968637633688281)
          ·
            refine ⟨1847974529226478225266211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2463966038968637633688281 1847974529226478225266211)
            ·
              refine ⟨2771961793839717337899317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847974529226478225266211 2771961793839717337899317)
              ·
                refine ⟨259871418172473500428061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2771961793839717337899317 259871418172473500428061)
                ·
                  refine ⟨97451781814677562660523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259871418172473500428061 97451781814677562660523)
                  ·
                    rfl

theorem cell21_427020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_427020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427020 prefixEnd_427020 := by exact prefixLift 427020
  have htrace : WordTrace (prefixWord ++ tailWord_427020) baseStart_427020 baseEnd_427020 := by
    simpa [prefixWord, tailWord_427020, baseEnd_427020] using wordTrace_append hprefix tailTrace_427020
  have hstable : (prefixWord ++ tailWord_427020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427020).length < 2 ^ (prefixWord ++ tailWord_427020).sum := by decide
  have hdescent : baseEnd_427020 < baseStart_427020 := by decide
  rcases family_descends (prefixWord ++ tailWord_427020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427026 : List Nat := [3, 2, 5, 1, 1, 2, 1, 2, 4]
def baseStart_427026 : Nat := 118140960795 + 427026 * 2 ^ 59
def prefixEnd_427026 : Nat := 4983230072969 + 3 ^ 40 * 427026 * 2
def baseEnd_427026 : Nat := 97453151096422885560511

theorem tailTrace_427026 : CollatzResearch.WordTrace tailWord_427026 prefixEnd_427026 97453151096422885560511 := by
  unfold tailWord_427026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3893729437741301769909233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10383278500643471386424621 3893729437741301769909233)
  ·
    refine ⟨2920297078305976327431925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3893729437741301769909233 2920297078305976327431925)
    ·
      refine ⟨273777851091185280696743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2920297078305976327431925 273777851091185280696743)
      ·
        refine ⟨410666776636777921045115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273777851091185280696743 410666776636777921045115)
        ·
          refine ⟨616000164955166881567673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410666776636777921045115 616000164955166881567673)
          ·
            refine ⟨462000123716375161175755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 616000164955166881567673 462000123716375161175755)
            ·
              refine ⟨693000185574562741763633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462000123716375161175755 693000185574562741763633)
              ·
                refine ⟨519750139180922056322725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 693000185574562741763633 519750139180922056322725)
                ·
                  refine ⟨97453151096422885560511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 519750139180922056322725 97453151096422885560511)
                  ·
                    rfl

theorem cell21_427026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_427026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427026 prefixEnd_427026 := by exact prefixLift 427026
  have htrace : WordTrace (prefixWord ++ tailWord_427026) baseStart_427026 baseEnd_427026 := by
    simpa [prefixWord, tailWord_427026, baseEnd_427026] using wordTrace_append hprefix tailTrace_427026
  have hstable : (prefixWord ++ tailWord_427026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427026).length < 2 ^ (prefixWord ++ tailWord_427026).sum := by decide
  have hdescent : baseEnd_427026 < baseStart_427026 := by decide
  rcases family_descends (prefixWord ++ tailWord_427026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427065 : List Nat := [1, 2, 1, 5, 2, 1, 4, 5]
def baseStart_427065 : Nat := 118140960795 + 427065 * 2 ^ 59
def prefixEnd_427065 : Nat := 4983230072969 + 3 ^ 40 * 427065 * 2
def baseEnd_427065 : Nat := 32487350475922494803477

theorem tailTrace_427065 : CollatzResearch.WordTrace tailWord_427065 prefixEnd_427065 32487350475922494803477 := by
  unfold tailWord_427065
  simp only [CollatzResearch.WordTrace]
  refine ⟨15576340197823916740306649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10384226798549277826871099 15576340197823916740306649)
  ·
    refine ⟨11682255148367937555229987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15576340197823916740306649 11682255148367937555229987)
    ·
      refine ⟨17523382722551906332844981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11682255148367937555229987 17523382722551906332844981)
      ·
        refine ⟨1642817130239241218704217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17523382722551906332844981 1642817130239241218704217)
        ·
          refine ⟨1232112847679430914028163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1642817130239241218704217 1232112847679430914028163)
          ·
            refine ⟨1848169271519146371042245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232112847679430914028163 1848169271519146371042245)
            ·
              refine ⟨346531738409839944570421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1848169271519146371042245 346531738409839944570421)
              ·
                refine ⟨32487350475922494803477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 346531738409839944570421 32487350475922494803477)
                ·
                  rfl

theorem cell21_427065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 5].length) (baseStart_427065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427065 prefixEnd_427065 := by exact prefixLift 427065
  have htrace : WordTrace (prefixWord ++ tailWord_427065) baseStart_427065 baseEnd_427065 := by
    simpa [prefixWord, tailWord_427065, baseEnd_427065] using wordTrace_append hprefix tailTrace_427065
  have hstable : (prefixWord ++ tailWord_427065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427065).length < 2 ^ (prefixWord ++ tailWord_427065).sum := by decide
  have hdescent : baseEnd_427065 < baseStart_427065 := by decide
  rcases family_descends (prefixWord ++ tailWord_427065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427093 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 6]
def baseStart_427093 : Nat := 118140960795 + 427093 * 2 ^ 59
def prefixEnd_427093 : Nat := 4983230072969 + 3 ^ 40 * 427093 * 2
def baseEnd_427093 : Nat := 97468441409245657943707

theorem tailTrace_427093 : CollatzResearch.WordTrace tailWord_427093 prefixEnd_427093 97468441409245657943707 := by
  unfold tailWord_427093
  simp only [CollatzResearch.WordTrace]
  refine ⟨15577361441722477522325933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10384907627814985014883955 15577361441722477522325933)
  ·
    refine ⟨5841510540645929070872225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15577361441722477522325933 5841510540645929070872225)
    ·
      refine ⟨4381132905484446803154169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5841510540645929070872225 4381132905484446803154169)
      ·
        refine ⟨3285849679113335102365627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4381132905484446803154169 3285849679113335102365627)
        ·
          refine ⟨4928774518670002653548441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3285849679113335102365627 4928774518670002653548441)
          ·
            refine ⟨3696580889002501990161331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4928774518670002653548441 3696580889002501990161331)
            ·
              refine ⟨5544871333503752985241997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3696580889002501990161331 5544871333503752985241997)
              ·
                refine ⟨2079326750063907369465749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5544871333503752985241997 2079326750063907369465749)
                ·
                  refine ⟨97468441409245657943707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2079326750063907369465749 97468441409245657943707)
                  ·
                    rfl

theorem cell21_427093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_427093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427093 prefixEnd_427093 := by exact prefixLift 427093
  have htrace : WordTrace (prefixWord ++ tailWord_427093) baseStart_427093 baseEnd_427093 := by
    simpa [prefixWord, tailWord_427093, baseEnd_427093] using wordTrace_append hprefix tailTrace_427093
  have hstable : (prefixWord ++ tailWord_427093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427093).length < 2 ^ (prefixWord ++ tailWord_427093).sum := by decide
  have hdescent : baseEnd_427093 < baseStart_427093 := by decide
  rcases family_descends (prefixWord ++ tailWord_427093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427102 : List Nat := [4, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_427102 : Nat := 118140960795 + 427102 * 2 ^ 59
def prefixEnd_427102 : Nat := 4983230072969 + 3 ^ 40 * 427102 * 2
def baseEnd_427102 : Nat := 97470495331863642293689

theorem tailTrace_427102 : CollatzResearch.WordTrace tailWord_427102 prefixEnd_427102 97470495331863642293689 := by
  unfold tailWord_427102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1947211212336234007425445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10385126465793248039602373 1947211212336234007425445)
  ·
    refine ⟨365102102313043876392271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1947211212336234007425445 365102102313043876392271)
    ·
      refine ⟨547653153469565814588407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365102102313043876392271 547653153469565814588407)
      ·
        refine ⟨821479730204348721882611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547653153469565814588407 821479730204348721882611)
        ·
          refine ⟨1232219595306523082823917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821479730204348721882611 1232219595306523082823917)
          ·
            refine ⟨462082348239946156058969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1232219595306523082823917 462082348239946156058969)
            ·
              refine ⟨346561761179959617044227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462082348239946156058969 346561761179959617044227)
              ·
                refine ⟨519842641769939425566341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346561761179959617044227 519842641769939425566341)
                ·
                  refine ⟨97470495331863642293689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 519842641769939425566341 97470495331863642293689)
                  ·
                    rfl

theorem cell21_427102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_427102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427102 prefixEnd_427102 := by exact prefixLift 427102
  have htrace : WordTrace (prefixWord ++ tailWord_427102) baseStart_427102 baseEnd_427102 := by
    simpa [prefixWord, tailWord_427102, baseEnd_427102] using wordTrace_append hprefix tailTrace_427102
  have hstable : (prefixWord ++ tailWord_427102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427102).length < 2 ^ (prefixWord ++ tailWord_427102).sum := by decide
  have hdescent : baseEnd_427102 < baseStart_427102 := by decide
  rcases family_descends (prefixWord ++ tailWord_427102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427183 : List Nat := [1, 1, 2, 1, 2, 3, 2, 9]
def baseStart_427183 : Nat := 118140960795 + 427183 * 2 ^ 59
def prefixEnd_427183 : Nat := 4983230072969 + 3 ^ 40 * 427183 * 2
def baseEnd_427183 : Nat := 32496326878475167147841

theorem tailTrace_427183 : CollatzResearch.WordTrace tailWord_427183 prefixEnd_427183 32496326878475167147841 := by
  unfold tailWord_427183
  simp only [CollatzResearch.WordTrace]
  refine ⟨15580644011396422893102203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10387096007597615262068135 15580644011396422893102203)
  ·
    refine ⟨23370966017094634339653305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15580644011396422893102203 23370966017094634339653305)
    ·
      refine ⟨17528224512820975754739979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23370966017094634339653305 17528224512820975754739979)
      ·
        refine ⟨26292336769231463632109969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17528224512820975754739979 26292336769231463632109969)
        ·
          refine ⟨19719252576923597724082477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26292336769231463632109969 19719252576923597724082477)
          ·
            refine ⟨7394719716346349146530929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19719252576923597724082477 7394719716346349146530929)
            ·
              refine ⟨5546039787259761859898197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7394719716346349146530929 5546039787259761859898197)
              ·
                refine ⟨32496326878475167147841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5546039787259761859898197 32496326878475167147841)
                ·
                  rfl

theorem cell21_427183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 9].length) (baseStart_427183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427183 prefixEnd_427183 := by exact prefixLift 427183
  have htrace : WordTrace (prefixWord ++ tailWord_427183) baseStart_427183 baseEnd_427183 := by
    simpa [prefixWord, tailWord_427183, baseEnd_427183] using wordTrace_append hprefix tailTrace_427183
  have hstable : (prefixWord ++ tailWord_427183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427183).length < 2 ^ (prefixWord ++ tailWord_427183).sum := by decide
  have hdescent : baseEnd_427183 < baseStart_427183 := by decide
  rcases family_descends (prefixWord ++ tailWord_427183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427200 : List Nat := [2, 1, 1, 2, 6, 1, 8]
def baseStart_427200 : Nat := 118140960795 + 427200 * 2 ^ 59
def prefixEnd_427200 : Nat := 4983230072969 + 3 ^ 40 * 427200 * 2
def baseEnd_427200 : Nat := 10832540029670805517795

theorem tailTrace_427200 : CollatzResearch.WordTrace tailWord_427200 prefixEnd_427200 10832540029670805517795 := by
  unfold tailWord_427200
  simp only [CollatzResearch.WordTrace]
  refine ⟨7790632026167417398235527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10387509368223223197647369 7790632026167417398235527)
  ·
    refine ⟨11685948039251126097353291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7790632026167417398235527 11685948039251126097353291)
    ·
      refine ⟨17528922058876689146029937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11685948039251126097353291 17528922058876689146029937)
      ·
        refine ⟨13146691544157516859522453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17528922058876689146029937 13146691544157516859522453)
        ·
          refine ⟨616251166132383602790115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13146691544157516859522453 616251166132383602790115)
          ·
            refine ⟨924376749198575404185173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616251166132383602790115 924376749198575404185173)
            ·
              refine ⟨10832540029670805517795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 924376749198575404185173 10832540029670805517795)
              ·
                rfl

theorem cell21_427200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 8].length) (baseStart_427200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427200 prefixEnd_427200 := by exact prefixLift 427200
  have htrace : WordTrace (prefixWord ++ tailWord_427200) baseStart_427200 baseEnd_427200 := by
    simpa [prefixWord, tailWord_427200, baseEnd_427200] using wordTrace_append hprefix tailTrace_427200
  have hstable : (prefixWord ++ tailWord_427200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427200).length < 2 ^ (prefixWord ++ tailWord_427200).sum := by decide
  have hdescent : baseEnd_427200 < baseStart_427200 := by decide
  rcases family_descends (prefixWord ++ tailWord_427200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427262 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_427262 : Nat := 118140960795 + 427262 * 2 ^ 59
def prefixEnd_427262 : Nat := 4983230072969 + 3 ^ 40 * 427262 * 2
def baseEnd_427262 : Nat := 97507009511738919626695

theorem tailTrace_427262 : CollatzResearch.WordTrace tailWord_427262 prefixEnd_427262 97507009511738919626695 := by
  unfold tailWord_427262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1947940672263777423153505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10389016918740146256818693 1947940672263777423153505)
  ·
    refine ⟨1460955504197833067365129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1947940672263777423153505 1460955504197833067365129)
    ·
      refine ⟨1095716628148374800523847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1460955504197833067365129 1095716628148374800523847)
      ·
        refine ⟨1643574942222562200785771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1095716628148374800523847 1643574942222562200785771)
        ·
          refine ⟨2465362413333843301178657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1643574942222562200785771 2465362413333843301178657)
          ·
            refine ⟨1849021810000382475883993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2465362413333843301178657 1849021810000382475883993)
            ·
              refine ⟨1386766357500286856912995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1849021810000382475883993 1386766357500286856912995)
              ·
                refine ⟨2080149536250430285369493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386766357500286856912995 2080149536250430285369493)
                ·
                  refine ⟨97507009511738919626695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2080149536250430285369493 97507009511738919626695)
                  ·
                    rfl

theorem cell21_427262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_427262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427262 prefixEnd_427262 := by exact prefixLift 427262
  have htrace : WordTrace (prefixWord ++ tailWord_427262) baseStart_427262 baseEnd_427262 := by
    simpa [prefixWord, tailWord_427262, baseEnd_427262] using wordTrace_append hprefix tailTrace_427262
  have hstable : (prefixWord ++ tailWord_427262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427262).length < 2 ^ (prefixWord ++ tailWord_427262).sum := by decide
  have hdescent : baseEnd_427262 < baseStart_427262 := by decide
  rcases family_descends (prefixWord ++ tailWord_427262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427265 : List Nat := [1, 2, 4, 1, 1, 4, 3, 2, 3]
def baseStart_427265 : Nat := 118140960795 + 427265 * 2 ^ 59
def prefixEnd_427265 : Nat := 4983230072969 + 3 ^ 40 * 427265 * 2
def baseEnd_427265 : Nat := 97507694152611581076689

theorem tailTrace_427265 : CollatzResearch.WordTrace tailWord_427265 prefixEnd_427265 97507694152611581076689 := by
  unfold tailWord_427265
  simp only [CollatzResearch.WordTrace]
  refine ⟨15583634797099350897587249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10389089864732900598391499 15583634797099350897587249)
  ·
    refine ⟨11687726097824513173190437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15583634797099350897587249 11687726097824513173190437)
    ·
      refine ⟨2191448643342096219973207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11687726097824513173190437 2191448643342096219973207)
      ·
        refine ⟨3287172965013144329959811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2191448643342096219973207 3287172965013144329959811)
        ·
          refine ⟨4930759447519716494939717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3287172965013144329959811 4930759447519716494939717)
          ·
            refine ⟨924517396409946842801197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4930759447519716494939717 924517396409946842801197)
            ·
              refine ⟨346694023653730066050449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 924517396409946842801197 346694023653730066050449)
              ·
                refine ⟨260020517740297549537837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346694023653730066050449 260020517740297549537837)
                ·
                  refine ⟨97507694152611581076689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260020517740297549537837 97507694152611581076689)
                  ·
                    rfl

theorem cell21_427265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 3].length) (baseStart_427265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427265 prefixEnd_427265 := by exact prefixLift 427265
  have htrace : WordTrace (prefixWord ++ tailWord_427265) baseStart_427265 baseEnd_427265 := by
    simpa [prefixWord, tailWord_427265, baseEnd_427265] using wordTrace_append hprefix tailTrace_427265
  have hstable : (prefixWord ++ tailWord_427265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427265).length < 2 ^ (prefixWord ++ tailWord_427265).sum := by decide
  have hdescent : baseEnd_427265 < baseStart_427265 := by decide
  rcases family_descends (prefixWord ++ tailWord_427265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427276 : List Nat := [2, 2, 1, 2, 2, 4, 2, 6]
def baseStart_427276 : Nat := 118140960795 + 427276 * 2 ^ 59
def prefixEnd_427276 : Nat := 4983230072969 + 3 ^ 40 * 427276 * 2
def baseEnd_427276 : Nat := 32503401500826002131111

theorem tailTrace_427276 : CollatzResearch.WordTrace tailWord_427276 prefixEnd_427276 32503401500826002131111 := by
  unfold tailWord_427276
  simp only [CollatzResearch.WordTrace]
  refine ⟨7792018000029749888118841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10389357333372999850825121 7792018000029749888118841)
  ·
    refine ⟨5844013500022312416089131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7792018000029749888118841 5844013500022312416089131)
    ·
      refine ⟨8766020250033468624133697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5844013500022312416089131 8766020250033468624133697)
      ·
        refine ⟨6574515187525101468100273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8766020250033468624133697 6574515187525101468100273)
        ·
          refine ⟨4930886390643826101075205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6574515187525101468100273 4930886390643826101075205)
          ·
            refine ⟨924541198245717393951601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4930886390643826101075205 924541198245717393951601)
            ·
              refine ⟨693405898684288045463701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 924541198245717393951601 693405898684288045463701)
              ·
                refine ⟨32503401500826002131111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 693405898684288045463701 32503401500826002131111)
                ·
                  rfl

theorem cell21_427276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 6].length) (baseStart_427276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427276 prefixEnd_427276 := by exact prefixLift 427276
  have htrace : WordTrace (prefixWord ++ tailWord_427276) baseStart_427276 baseEnd_427276 := by
    simpa [prefixWord, tailWord_427276, baseEnd_427276] using wordTrace_append hprefix tailTrace_427276
  have hstable : (prefixWord ++ tailWord_427276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427276).length < 2 ^ (prefixWord ++ tailWord_427276).sum := by decide
  have hdescent : baseEnd_427276 < baseStart_427276 := by decide
  rcases family_descends (prefixWord ++ tailWord_427276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427324 : List Nat := [2, 2, 2, 2, 1, 4, 1, 4, 3]
def baseStart_427324 : Nat := 118140960795 + 427324 * 2 ^ 59
def prefixEnd_427324 : Nat := 4983230072969 + 3 ^ 40 * 427324 * 2
def baseEnd_427324 : Nat := 97521158756440589593235

theorem tailTrace_427324 : CollatzResearch.WordTrace tailWord_427324 prefixEnd_427324 97521158756440589593235 := by
  unfold tailWord_427324
  simp only [CollatzResearch.WordTrace]
  refine ⟨7792893351942801986992513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10390524469257069315990017 7792893351942801986992513)
  ·
    refine ⟨5844670013957101490244385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7792893351942801986992513 5844670013957101490244385)
    ·
      refine ⟨4383502510467826117683289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5844670013957101490244385 4383502510467826117683289)
      ·
        refine ⟨3287626882850869588262467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4383502510467826117683289 3287626882850869588262467)
        ·
          refine ⟨4931440324276304382393701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3287626882850869588262467 4931440324276304382393701)
          ·
            refine ⟨924645060801807071698819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4931440324276304382393701 924645060801807071698819)
            ·
              refine ⟨1386967591202710607548229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924645060801807071698819 1386967591202710607548229)
              ·
                refine ⟨260056423350508238915293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1386967591202710607548229 260056423350508238915293)
                ·
                  refine ⟨97521158756440589593235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260056423350508238915293 97521158756440589593235)
                  ·
                    rfl

theorem cell21_427324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_427324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427324 prefixEnd_427324 := by exact prefixLift 427324
  have htrace : WordTrace (prefixWord ++ tailWord_427324) baseStart_427324 baseEnd_427324 := by
    simpa [prefixWord, tailWord_427324, baseEnd_427324] using wordTrace_append hprefix tailTrace_427324
  have hstable : (prefixWord ++ tailWord_427324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427324).length < 2 ^ (prefixWord ++ tailWord_427324).sum := by decide
  have hdescent : baseEnd_427324 < baseStart_427324 := by decide
  rcases family_descends (prefixWord ++ tailWord_427324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427341 : List Nat := [1, 6, 1, 3, 1, 1, 1, 2, 5]
def baseStart_427341 : Nat := 118140960795 + 427341 * 2 ^ 59
def prefixEnd_427341 : Nat := 4983230072969 + 3 ^ 40 * 427341 * 2
def baseEnd_427341 : Nat := 97525038388052337809867

theorem tailTrace_427341 : CollatzResearch.WordTrace tailWord_427341 prefixEnd_427341 97525038388052337809867 := by
  unfold tailWord_427341
  simp only [CollatzResearch.WordTrace]
  refine ⟨15586406744824015877353877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10390937829882677251569251 15586406744824015877353877)
  ·
    refine ⟨730612816163625744250963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15586406744824015877353877 730612816163625744250963)
    ·
      refine ⟨1095919224245438616376445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 730612816163625744250963 1095919224245438616376445)
      ·
        refine ⟨410969709092039481141167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1095919224245438616376445 410969709092039481141167)
        ·
          refine ⟨616454563638059221711751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410969709092039481141167 616454563638059221711751)
          ·
            refine ⟨924681845457088832567627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616454563638059221711751 924681845457088832567627)
            ·
              refine ⟨1387022768185633248851441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924681845457088832567627 1387022768185633248851441)
              ·
                refine ⟨1040267076139224936638581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1387022768185633248851441 1040267076139224936638581)
                ·
                  refine ⟨97525038388052337809867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1040267076139224936638581 97525038388052337809867)
                  ·
                    rfl

theorem cell21_427341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_427341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427341 prefixEnd_427341 := by exact prefixLift 427341
  have htrace : WordTrace (prefixWord ++ tailWord_427341) baseStart_427341 baseEnd_427341 := by
    simpa [prefixWord, tailWord_427341, baseEnd_427341] using wordTrace_append hprefix tailTrace_427341
  have hstable : (prefixWord ++ tailWord_427341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427341).length < 2 ^ (prefixWord ++ tailWord_427341).sum := by decide
  have hdescent : baseEnd_427341 < baseStart_427341 := by decide
  rcases family_descends (prefixWord ++ tailWord_427341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427352 : List Nat := [2, 1, 2, 2, 1, 1, 7, 5]
def baseStart_427352 : Nat := 118140960795 + 427352 * 2 ^ 59
def prefixEnd_427352 : Nat := 4983230072969 + 3 ^ 40 * 427352 * 2
def baseEnd_427352 : Nat := 32509182912639587708837

theorem tailTrace_427352 : CollatzResearch.WordTrace tailWord_427352 prefixEnd_427352 32509182912639587708837 := by
  unfold tailWord_427352
  simp only [CollatzResearch.WordTrace]
  refine ⟨7793403973892082378002155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10391205298522776504002873 7793403973892082378002155)
  ·
    refine ⟨11690105960838123567003233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7793403973892082378002155 11690105960838123567003233)
    ·
      refine ⟨8767579470628592675252425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11690105960838123567003233 8767579470628592675252425)
      ·
        refine ⟨6575684602971444506439319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8767579470628592675252425 6575684602971444506439319)
        ·
          refine ⟨9863526904457166759658979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6575684602971444506439319 9863526904457166759658979)
          ·
            refine ⟨14795290356685750139488469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9863526904457166759658979 14795290356685750139488469)
            ·
              refine ⟨346764617734822268894261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14795290356685750139488469 346764617734822268894261)
              ·
                refine ⟨32509182912639587708837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 346764617734822268894261 32509182912639587708837)
                ·
                  rfl

theorem cell21_427352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 5].length) (baseStart_427352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427352 prefixEnd_427352 := by exact prefixLift 427352
  have htrace : WordTrace (prefixWord ++ tailWord_427352) baseStart_427352 baseEnd_427352 := by
    simpa [prefixWord, tailWord_427352, baseEnd_427352] using wordTrace_append hprefix tailTrace_427352
  have hstable : (prefixWord ++ tailWord_427352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427352).length < 2 ^ (prefixWord ++ tailWord_427352).sum := by decide
  have hdescent : baseEnd_427352 < baseStart_427352 := by decide
  rcases family_descends (prefixWord ++ tailWord_427352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427383 : List Nat := [1, 1, 3, 1, 1, 2, 3, 6, 3]
def baseStart_427383 : Nat := 118140960795 + 427383 * 2 ^ 59
def prefixEnd_427383 : Nat := 4983230072969 + 3 ^ 40 * 427383 * 2
def baseEnd_427383 : Nat := 97534623360269598109781

theorem tailTrace_427383 : CollatzResearch.WordTrace tailWord_427383 prefixEnd_427383 97534623360269598109781 := by
  unfold tailWord_427383
  simp only [CollatzResearch.WordTrace]
  refine ⟨15587938610671857050382803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10391959073781238033588535 15587938610671857050382803)
  ·
    refine ⟨23381907916007785575574205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15587938610671857050382803 23381907916007785575574205)
    ·
      refine ⟨8768215468502919590840327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23381907916007785575574205 8768215468502919590840327)
      ·
        refine ⟨13152323202754379386260491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8768215468502919590840327 13152323202754379386260491)
        ·
          refine ⟨19728484804131569079390737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13152323202754379386260491 19728484804131569079390737)
          ·
            refine ⟨14796363603098676809543053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19728484804131569079390737 14796363603098676809543053)
            ·
              refine ⟨5548636351162003803578645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14796363603098676809543053 5548636351162003803578645)
              ·
                refine ⟨260092328960718928292749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5548636351162003803578645 260092328960718928292749)
                ·
                  refine ⟨97534623360269598109781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260092328960718928292749 97534623360269598109781)
                  ·
                    rfl

theorem cell21_427383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 3].length) (baseStart_427383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427383 prefixEnd_427383 := by exact prefixLift 427383
  have htrace : WordTrace (prefixWord ++ tailWord_427383) baseStart_427383 baseEnd_427383 := by
    simpa [prefixWord, tailWord_427383, baseEnd_427383] using wordTrace_append hprefix tailTrace_427383
  have hstable : (prefixWord ++ tailWord_427383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427383).length < 2 ^ (prefixWord ++ tailWord_427383).sum := by decide
  have hdescent : baseEnd_427383 < baseStart_427383 := by decide
  rcases family_descends (prefixWord ++ tailWord_427383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427397 : List Nat := [1, 3, 1, 1, 3, 1, 2, 5, 4]
def baseStart_427397 : Nat := 118140960795 + 427397 * 2 ^ 59
def prefixEnd_427397 : Nat := 4983230072969 + 3 ^ 40 * 427397 * 2
def baseEnd_427397 : Nat := 97537818351008684876419

theorem tailTrace_427397 : CollatzResearch.WordTrace tailWord_427397 prefixEnd_427397 97537818351008684876419 := by
  unfold tailWord_427397
  simp only [CollatzResearch.WordTrace]
  refine ⟨15588449232621137441392445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10392299488414091627594963 15588449232621137441392445)
  ·
    refine ⟨5845668462232926540522167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15588449232621137441392445 5845668462232926540522167)
    ·
      refine ⟨8768502693349389810783251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5845668462232926540522167 8768502693349389810783251)
      ·
        refine ⟨13152754040024084716174877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8768502693349389810783251 13152754040024084716174877)
        ·
          refine ⟨4932282765009031768565579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13152754040024084716174877 4932282765009031768565579)
          ·
            refine ⟨7398424147513547652848369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4932282765009031768565579 7398424147513547652848369)
            ·
              refine ⟨5548818110635160739636277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7398424147513547652848369 5548818110635160739636277)
              ·
                refine ⟨520201697872046319340901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5548818110635160739636277 520201697872046319340901)
                ·
                  refine ⟨97537818351008684876419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 520201697872046319340901 97537818351008684876419)
                  ·
                    rfl

theorem cell21_427397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_427397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427397 prefixEnd_427397 := by exact prefixLift 427397
  have htrace : WordTrace (prefixWord ++ tailWord_427397) baseStart_427397 baseEnd_427397 := by
    simpa [prefixWord, tailWord_427397, baseEnd_427397] using wordTrace_append hprefix tailTrace_427397
  have hstable : (prefixWord ++ tailWord_427397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427397).length < 2 ^ (prefixWord ++ tailWord_427397).sum := by decide
  have hdescent : baseEnd_427397 < baseStart_427397 := by decide
  rcases family_descends (prefixWord ++ tailWord_427397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427442 : List Nat := [3, 2, 1, 1, 1, 1, 2, 5, 5]
def baseStart_427442 : Nat := 118140960795 + 427442 * 2 ^ 59
def prefixEnd_427442 : Nat := 4983230072969 + 3 ^ 40 * 427442 * 2
def baseEnd_427442 : Nat := 97548087964098606626327

theorem tailTrace_427442 : CollatzResearch.WordTrace tailWord_427442 prefixEnd_427442 97548087964098606626327 := by
  unfold tailWord_427442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3897522629364527531695145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10393393678305406751187053 3897522629364527531695145)
  ·
    refine ⟨2923141972023395648771359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3897522629364527531695145 2923141972023395648771359)
    ·
      refine ⟨4384712958035093473157039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2923141972023395648771359 4384712958035093473157039)
      ·
        refine ⟨6577069437052640209735559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4384712958035093473157039 6577069437052640209735559)
        ·
          refine ⟨9865604155578960314603339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6577069437052640209735559 9865604155578960314603339)
          ·
            refine ⟨14798406233368440471905009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9865604155578960314603339 14798406233368440471905009)
            ·
              refine ⟨11098804675026330353928757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14798406233368440471905009 11098804675026330353928757)
              ·
                refine ⟨1040512938283718470680821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11098804675026330353928757 1040512938283718470680821)
                ·
                  refine ⟨97548087964098606626327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1040512938283718470680821 97548087964098606626327)
                  ·
                    rfl

theorem cell21_427442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_427442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427442 prefixEnd_427442 := by exact prefixLift 427442
  have htrace : WordTrace (prefixWord ++ tailWord_427442) baseStart_427442 baseEnd_427442 := by
    simpa [prefixWord, tailWord_427442, baseEnd_427442] using wordTrace_append hprefix tailTrace_427442
  have hstable : (prefixWord ++ tailWord_427442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427442).length < 2 ^ (prefixWord ++ tailWord_427442).sum := by decide
  have hdescent : baseEnd_427442 < baseStart_427442 := by decide
  rcases family_descends (prefixWord ++ tailWord_427442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427493 : List Nat := [1, 3, 1, 5, 1, 1, 4, 2, 3]
def baseStart_427493 : Nat := 118140960795 + 427493 * 2 ^ 59
def prefixEnd_427493 : Nat := 4983230072969 + 3 ^ 40 * 427493 * 2
def baseEnd_427493 : Nat := 97559726858933851276223

theorem tailTrace_427493 : CollatzResearch.WordTrace tailWord_427493 prefixEnd_427493 97559726858933851276223 := by
  unfold tailWord_427493
  simp only [CollatzResearch.WordTrace]
  refine ⟨15591950640273345836887133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10394633760182230557924755 15591950640273345836887133)
  ·
    refine ⟨5846981490102504688832675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15591950640273345836887133 5846981490102504688832675)
    ·
      refine ⟨8770472235153757033249013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5846981490102504688832675 8770472235153757033249013)
      ·
        refine ⟨822231772045664721867095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8770472235153757033249013 822231772045664721867095)
        ·
          refine ⟨1233347658068497082800643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822231772045664721867095 1233347658068497082800643)
          ·
            refine ⟨1850021487102745624200965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233347658068497082800643 1850021487102745624200965)
            ·
              refine ⟨346879028831764804537681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1850021487102745624200965 346879028831764804537681)
              ·
                refine ⟨260159271623823603403261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346879028831764804537681 260159271623823603403261)
                ·
                  refine ⟨97559726858933851276223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260159271623823603403261 97559726858933851276223)
                  ·
                    rfl

theorem cell21_427493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_427493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427493 prefixEnd_427493 := by exact prefixLift 427493
  have htrace : WordTrace (prefixWord ++ tailWord_427493) baseStart_427493 baseEnd_427493 := by
    simpa [prefixWord, tailWord_427493, baseEnd_427493] using wordTrace_append hprefix tailTrace_427493
  have hstable : (prefixWord ++ tailWord_427493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427493).length < 2 ^ (prefixWord ++ tailWord_427493).sum := by decide
  have hdescent : baseEnd_427493 < baseStart_427493 := by decide
  rcases family_descends (prefixWord ++ tailWord_427493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427504 : List Nat := [2, 1, 1, 1, 3, 6, 1, 6]
def baseStart_427504 : Nat := 118140960795 + 427504 * 2 ^ 59
def prefixEnd_427504 : Nat := 4983230072969 + 3 ^ 40 * 427504 * 2
def baseEnd_427504 : Nat := 32520745736266758864289

theorem tailTrace_427504 : CollatzResearch.WordTrace tailWord_427504 prefixEnd_427504 32520745736266758864289 := by
  unfold tailWord_427504
  simp only [CollatzResearch.WordTrace]
  refine ⟨7796175921616747357768783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10394901228822329810358377 7796175921616747357768783)
  ·
    refine ⟨11694263882425121036653175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7796175921616747357768783 11694263882425121036653175)
    ·
      refine ⟨17541395823637681554979763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11694263882425121036653175 17541395823637681554979763)
      ·
        refine ⟨26312093735456522332469645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17541395823637681554979763 26312093735456522332469645)
        ·
          refine ⟨9867035150796195874676117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26312093735456522332469645 9867035150796195874676117)
          ·
            refine ⟨462517272693571681625443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9867035150796195874676117 462517272693571681625443)
            ·
              refine ⟨693775909040357522438165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462517272693571681625443 693775909040357522438165)
              ·
                refine ⟨32520745736266758864289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 693775909040357522438165 32520745736266758864289)
                ·
                  rfl

theorem cell21_427504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 6].length) (baseStart_427504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427504 prefixEnd_427504 := by exact prefixLift 427504
  have htrace : WordTrace (prefixWord ++ tailWord_427504) baseStart_427504 baseEnd_427504 := by
    simpa [prefixWord, tailWord_427504, baseEnd_427504] using wordTrace_append hprefix tailTrace_427504
  have hstable : (prefixWord ++ tailWord_427504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427504).length < 2 ^ (prefixWord ++ tailWord_427504).sum := by decide
  have hdescent : baseEnd_427504 < baseStart_427504 := by decide
  rcases family_descends (prefixWord ++ tailWord_427504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427521 : List Nat := [1, 2, 4, 1, 4, 1, 3, 5]
def baseStart_427521 : Nat := 118140960795 + 427521 * 2 ^ 59
def prefixEnd_427521 : Nat := 4983230072969 + 3 ^ 40 * 427521 * 2
def baseEnd_427521 : Nat := 32522038946804008269833

theorem tailTrace_427521 : CollatzResearch.WordTrace tailWord_427521 prefixEnd_427521 32522038946804008269833 := by
  unfold tailWord_427521
  simp only [CollatzResearch.WordTrace]
  refine ⟨15592971884171906618906417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10395314589447937745937611 15592971884171906618906417)
  ·
    refine ⟨11694728913128929964179813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15592971884171906618906417 11694728913128929964179813)
    ·
      refine ⟨2192761671211674368283715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11694728913128929964179813 2192761671211674368283715)
      ·
        refine ⟨3289142506817511552425573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2192761671211674368283715 3289142506817511552425573)
        ·
          refine ⟨616714220028283416079795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3289142506817511552425573 616714220028283416079795)
          ·
            refine ⟨925071330042425124119693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616714220028283416079795 925071330042425124119693)
            ·
              refine ⟨346901748765909421544885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 925071330042425124119693 346901748765909421544885)
              ·
                refine ⟨32522038946804008269833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 346901748765909421544885 32522038946804008269833)
                ·
                  rfl

theorem cell21_427521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 5].length) (baseStart_427521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427521 prefixEnd_427521 := by exact prefixLift 427521
  have htrace : WordTrace (prefixWord ++ tailWord_427521) baseStart_427521 baseEnd_427521 := by
    simpa [prefixWord, tailWord_427521, baseEnd_427521] using wordTrace_append hprefix tailTrace_427521
  have hstable : (prefixWord ++ tailWord_427521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427521).length < 2 ^ (prefixWord ++ tailWord_427521).sum := by decide
  have hdescent : baseEnd_427521 < baseStart_427521 := by decide
  rcases family_descends (prefixWord ++ tailWord_427521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427549 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 6]
def baseStart_427549 : Nat := 118140960795 + 427549 * 2 ^ 59
def prefixEnd_427549 : Nat := 4983230072969 + 3 ^ 40 * 427549 * 2
def baseEnd_427549 : Nat := 97572506821890198342775

theorem tailTrace_427549 : CollatzResearch.WordTrace tailWord_427549 prefixEnd_427549 97572506821890198342775 := by
  unfold tailWord_427549
  simp only [CollatzResearch.WordTrace]
  refine ⟨15593993128070467400925701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10395995418713644933950467 15593993128070467400925701)
  ·
    refine ⟨2923873711513212637673569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15593993128070467400925701 2923873711513212637673569)
    ·
      refine ⟨2192905283634909478255177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2923873711513212637673569 2192905283634909478255177)
      ·
        refine ⟨1644678962726182108691383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2192905283634909478255177 1644678962726182108691383)
        ·
          refine ⟨2467018444089273163037075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1644678962726182108691383 2467018444089273163037075)
          ·
            refine ⟨3700527666133909744555613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467018444089273163037075 3700527666133909744555613)
            ·
              refine ⟨1387697874800216154208355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3700527666133909744555613 1387697874800216154208355)
              ·
                refine ⟨2081546812200324231312533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1387697874800216154208355 2081546812200324231312533)
                ·
                  refine ⟨97572506821890198342775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2081546812200324231312533 97572506821890198342775)
                  ·
                    rfl

theorem cell21_427549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_427549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427549 prefixEnd_427549 := by exact prefixLift 427549
  have htrace : WordTrace (prefixWord ++ tailWord_427549) baseStart_427549 baseEnd_427549 := by
    simpa [prefixWord, tailWord_427549, baseEnd_427549] using wordTrace_append hprefix tailTrace_427549
  have hstable : (prefixWord ++ tailWord_427549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427549).length < 2 ^ (prefixWord ++ tailWord_427549).sum := by decide
  have hdescent : baseEnd_427549 < baseStart_427549 := by decide
  rcases family_descends (prefixWord ++ tailWord_427549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427552 : List Nat := [2, 1, 1, 6, 1, 1, 2, 4, 3]
def baseStart_427552 : Nat := 118140960795 + 427552 * 2 ^ 59
def prefixEnd_427552 : Nat := 4983230072969 + 3 ^ 40 * 427552 * 2
def baseEnd_427552 : Nat := 97573191462762859792769

theorem tailTrace_427552 : CollatzResearch.WordTrace tailWord_427552 prefixEnd_427552 97573191462762859792769 := by
  unfold tailWord_427552
  simp only [CollatzResearch.WordTrace]
  refine ⟨7797051273529799456642455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10396068364706399275523273 7797051273529799456642455)
  ·
    refine ⟨11695576910294699184963683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7797051273529799456642455 11695576910294699184963683)
    ·
      refine ⟨17543365365442048777445525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11695576910294699184963683 17543365365442048777445525)
      ·
        refine ⟨822345251505096036442759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17543365365442048777445525 822345251505096036442759)
        ·
          refine ⟨1233517877257644054664139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822345251505096036442759 1233517877257644054664139)
          ·
            refine ⟨1850276815886466081996209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233517877257644054664139 1850276815886466081996209)
            ·
              refine ⟨1387707611914849561497157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1850276815886466081996209 1387707611914849561497157)
              ·
                refine ⟨260195177234034292780717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1387707611914849561497157 260195177234034292780717)
                ·
                  refine ⟨97573191462762859792769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260195177234034292780717 97573191462762859792769)
                  ·
                    rfl

theorem cell21_427552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 3].length) (baseStart_427552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427552 prefixEnd_427552 := by exact prefixLift 427552
  have htrace : WordTrace (prefixWord ++ tailWord_427552) baseStart_427552 baseEnd_427552 := by
    simpa [prefixWord, tailWord_427552, baseEnd_427552] using wordTrace_append hprefix tailTrace_427552
  have hstable : (prefixWord ++ tailWord_427552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427552).length < 2 ^ (prefixWord ++ tailWord_427552).sum := by decide
  have hdescent : baseEnd_427552 < baseStart_427552 := by decide
  rcases family_descends (prefixWord ++ tailWord_427552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427580 : List Nat := [2, 2, 2, 2, 4, 1, 1, 7]
def baseStart_427580 : Nat := 118140960795 + 427580 * 2 ^ 59
def prefixEnd_427580 : Nat := 4983230072969 + 3 ^ 40 * 427580 * 2
def baseEnd_427580 : Nat := 32526527148080344442015

theorem tailTrace_427580 : CollatzResearch.WordTrace tailWord_427580 prefixEnd_427580 32526527148080344442015 := by
  unfold tailWord_427580
  simp only [CollatzResearch.WordTrace]
  refine ⟨7797561895479079847652097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10396749193972106463536129 7797561895479079847652097)
  ·
    refine ⟨5848171421609309885739073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7797561895479079847652097 5848171421609309885739073)
    ·
      refine ⟨4386128566206982414304305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5848171421609309885739073 4386128566206982414304305)
      ·
        refine ⟨3289596424655236810728229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4386128566206982414304305 3289596424655236810728229)
        ·
          refine ⟨616799329622856902011543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3289596424655236810728229 616799329622856902011543)
          ·
            refine ⟨925198994434285353017315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616799329622856902011543 925198994434285353017315)
            ·
              refine ⟨1387798491651428029525973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925198994434285353017315 1387798491651428029525973)
              ·
                refine ⟨32526527148080344442015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1387798491651428029525973 32526527148080344442015)
                ·
                  rfl

theorem cell21_427580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 7].length) (baseStart_427580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427580 prefixEnd_427580 := by exact prefixLift 427580
  have htrace : WordTrace (prefixWord ++ tailWord_427580) baseStart_427580 baseEnd_427580 := by
    simpa [prefixWord, tailWord_427580, baseEnd_427580] using wordTrace_append hprefix tailTrace_427580
  have hstable : (prefixWord ++ tailWord_427580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427580).length < 2 ^ (prefixWord ++ tailWord_427580).sum := by decide
  have hdescent : baseEnd_427580 < baseStart_427580 := by decide
  rcases family_descends (prefixWord ++ tailWord_427580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427597 : List Nat := [1, 6, 1, 1, 3, 2, 7]
def baseStart_427597 : Nat := 118140960795 + 427597 * 2 ^ 59
def prefixEnd_427597 : Nat := 4983230072969 + 3 ^ 40 * 427597 * 2
def baseEnd_427597 : Nat := 10842606786205864615853

theorem tailTrace_427597 : CollatzResearch.WordTrace tailWord_427597 prefixEnd_427597 10842606786205864615853 := by
  unfold tailWord_427597
  simp only [CollatzResearch.WordTrace]
  refine ⟨15595743831896571598673045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10397162554597714399115363 15595743831896571598673045)
  ·
    refine ⟨731050492120151793687799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15595743831896571598673045 731050492120151793687799)
    ·
      refine ⟨1096575738180227690531699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 731050492120151793687799 1096575738180227690531699)
      ·
        refine ⟨1644863607270341535797549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1096575738180227690531699 1644863607270341535797549)
        ·
          refine ⟨616823852726378075924081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1644863607270341535797549 616823852726378075924081)
          ·
            refine ⟨462617889544783556943061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 616823852726378075924081 462617889544783556943061)
            ·
              refine ⟨10842606786205864615853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 462617889544783556943061 10842606786205864615853)
              ·
                rfl

theorem cell21_427597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 7].length) (baseStart_427597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427597 prefixEnd_427597 := by exact prefixLift 427597
  have htrace : WordTrace (prefixWord ++ tailWord_427597) baseStart_427597 baseEnd_427597 := by
    simpa [prefixWord, tailWord_427597, baseEnd_427597] using wordTrace_append hprefix tailTrace_427597
  have hstable : (prefixWord ++ tailWord_427597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427597).length < 2 ^ (prefixWord ++ tailWord_427597).sum := by decide
  have hdescent : baseEnd_427597 < baseStart_427597 := by decide
  rcases family_descends (prefixWord ++ tailWord_427597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427656 : List Nat := [2, 1, 3, 5, 1, 9]
def baseStart_427656 : Nat := 118140960795 + 427656 * 2 ^ 59
def prefixEnd_427656 : Nat := 4983230072969 + 3 ^ 40 * 427656 * 2
def baseEnd_427656 : Nat := 3614700951099325557749

theorem tailTrace_427656 : CollatzResearch.WordTrace tailWord_427656 prefixEnd_427656 3614700951099325557749 := by
  unfold tailWord_427656
  simp only [CollatzResearch.WordTrace]
  refine ⟨7798947869341412337535411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10398597159121883116713881 7798947869341412337535411)
  ·
    refine ⟨11698421804012118506303117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7798947869341412337535411 11698421804012118506303117)
    ·
      refine ⟨4386908176504544439863669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11698421804012118506303117 4386908176504544439863669)
      ·
        refine ⟨411272641547301041237219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4386908176504544439863669 411272641547301041237219)
        ·
          refine ⟨616908962320951561855829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411272641547301041237219 616908962320951561855829)
          ·
            refine ⟨3614700951099325557749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 616908962320951561855829 3614700951099325557749)
            ·
              rfl

theorem cell21_427656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 9].length) (baseStart_427656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427656 prefixEnd_427656 := by exact prefixLift 427656
  have htrace : WordTrace (prefixWord ++ tailWord_427656) baseStart_427656 baseEnd_427656 := by
    simpa [prefixWord, tailWord_427656, baseEnd_427656] using wordTrace_append hprefix tailTrace_427656
  have hstable : (prefixWord ++ tailWord_427656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427656).length < 2 ^ (prefixWord ++ tailWord_427656).sum := by decide
  have hdescent : baseEnd_427656 < baseStart_427656 := by decide
  rcases family_descends (prefixWord ++ tailWord_427656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427763 : List Nat := [1, 1, 1, 2, 2, 3, 5, 3, 3]
def baseStart_427763 : Nat := 118140960795 + 427763 * 2 ^ 59
def prefixEnd_427763 : Nat := 4983230072969 + 3 ^ 40 * 427763 * 2
def baseEnd_427763 : Nat := 97621344537473381775671

theorem tailTrace_427763 : CollatzResearch.WordTrace tailWord_427763 prefixEnd_427763 97621344537473381775671 := by
  unfold tailWord_427763
  simp only [CollatzResearch.WordTrace]
  refine ⟨15601798349295181949215943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10401198899530121299477295 15601798349295181949215943)
  ·
    refine ⟨23402697523942772923823915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15601798349295181949215943 23402697523942772923823915)
    ·
      refine ⟨35104046285914159385735873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23402697523942772923823915 35104046285914159385735873)
      ·
        refine ⟨26328034714435619539301905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35104046285914159385735873 26328034714435619539301905)
        ·
          refine ⟨19746026035826714654476429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26328034714435619539301905 19746026035826714654476429)
          ·
            refine ⟨7404759763435017995428661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19746026035826714654476429 7404759763435017995428661)
            ·
              refine ⟨694196227822032937071437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7404759763435017995428661 694196227822032937071437)
              ·
                refine ⟨260323585433262351401789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 694196227822032937071437 260323585433262351401789)
                ·
                  refine ⟨97621344537473381775671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260323585433262351401789 97621344537473381775671)
                  ·
                    rfl

theorem cell21_427763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 3].length) (baseStart_427763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427763 prefixEnd_427763 := by exact prefixLift 427763
  have htrace : WordTrace (prefixWord ++ tailWord_427763) baseStart_427763 baseEnd_427763 := by
    simpa [prefixWord, tailWord_427763, baseEnd_427763] using wordTrace_append hprefix tailTrace_427763
  have hstable : (prefixWord ++ tailWord_427763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427763).length < 2 ^ (prefixWord ++ tailWord_427763).sum := by decide
  have hdescent : baseEnd_427763 < baseStart_427763 := by decide
  rcases family_descends (prefixWord ++ tailWord_427763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427836 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 6]
def baseStart_427836 : Nat := 118140960795 + 427836 * 2 ^ 59
def prefixEnd_427836 : Nat := 4983230072969 + 3 ^ 40 * 427836 * 2
def baseEnd_427836 : Nat := 97638004132041477058855

theorem tailTrace_427836 : CollatzResearch.WordTrace tailWord_427836 prefixEnd_427836 97638004132041477058855 := by
  unfold tailWord_427836
  simp only [CollatzResearch.WordTrace]
  refine ⟨7802230439015357708311681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10402973918687143611082241 7802230439015357708311681)
  ·
    refine ⟨5851672829261518281233761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7802230439015357708311681 5851672829261518281233761)
    ·
      refine ⟨4388754621946138710925321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5851672829261518281233761 4388754621946138710925321)
      ·
        refine ⟨3291565966459604033193991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4388754621946138710925321 3291565966459604033193991)
        ·
          refine ⟨4937348949689406049790987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3291565966459604033193991 4937348949689406049790987)
          ·
            refine ⟨7406023424534109074686481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4937348949689406049790987 7406023424534109074686481)
            ·
              refine ⟨5554517568400581806014861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7406023424534109074686481 5554517568400581806014861)
              ·
                refine ⟨2082944088150218177255573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5554517568400581806014861 2082944088150218177255573)
                ·
                  refine ⟨97638004132041477058855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2082944088150218177255573 97638004132041477058855)
                  ·
                    rfl

theorem cell21_427836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_427836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427836 prefixEnd_427836 := by exact prefixLift 427836
  have htrace : WordTrace (prefixWord ++ tailWord_427836) baseStart_427836 baseEnd_427836 := by
    simpa [prefixWord, tailWord_427836, baseEnd_427836] using wordTrace_append hprefix tailTrace_427836
  have hstable : (prefixWord ++ tailWord_427836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427836).length < 2 ^ (prefixWord ++ tailWord_427836).sum := by decide
  have hdescent : baseEnd_427836 < baseStart_427836 := by decide
  rcases family_descends (prefixWord ++ tailWord_427836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427918 : List Nat := [4, 1, 1, 5, 1, 2, 2, 5]
def baseStart_427918 : Nat := 118140960795 + 427918 * 2 ^ 59
def prefixEnd_427918 : Nat := 4983230072969 + 3 ^ 40 * 427918 * 2
def baseEnd_427918 : Nat := 32552239216409185564007

theorem tailTrace_427918 : CollatzResearch.WordTrace tailWord_427918 prefixEnd_427918 32552239216409185564007 := by
  unfold tailWord_427918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1950931457966705427638551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10404967775822428947405605 1950931457966705427638551)
  ·
    refine ⟨2926397186950058141457827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1950931457966705427638551 2926397186950058141457827)
    ·
      refine ⟨4389595780425087212186741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2926397186950058141457827 4389595780425087212186741)
      ·
        refine ⟨411524604414851926142507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4389595780425087212186741 411524604414851926142507)
        ·
          refine ⟨617286906622277889213761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411524604414851926142507 617286906622277889213761)
          ·
            refine ⟨462965179966708416910321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 617286906622277889213761 462965179966708416910321)
            ·
              refine ⟨347223884975031312682741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462965179966708416910321 347223884975031312682741)
              ·
                refine ⟨32552239216409185564007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 347223884975031312682741 32552239216409185564007)
                ·
                  rfl

theorem cell21_427918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_427918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427918 prefixEnd_427918 := by exact prefixLift 427918
  have htrace : WordTrace (prefixWord ++ tailWord_427918) baseStart_427918 baseEnd_427918 := by
    simpa [prefixWord, tailWord_427918, baseEnd_427918] using wordTrace_append hprefix tailTrace_427918
  have hstable : (prefixWord ++ tailWord_427918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427918).length < 2 ^ (prefixWord ++ tailWord_427918).sum := by decide
  have hdescent : baseEnd_427918 < baseStart_427918 := by decide
  rcases family_descends (prefixWord ++ tailWord_427918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427932 : List Nat := [2, 2, 3, 3, 1, 1, 3, 3, 3]
def baseStart_427932 : Nat := 118140960795 + 427932 * 2 ^ 59
def prefixEnd_427932 : Nat := 4983230072969 + 3 ^ 40 * 427932 * 2
def baseEnd_427932 : Nat := 97659912639966643458659

theorem tailTrace_427932 : CollatzResearch.WordTrace tailWord_427932 prefixEnd_427932 97659912639966643458659 := by
  unfold tailWord_427932
  simp only [CollatzResearch.WordTrace]
  refine ⟨7803981142841461906059025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10405308190455282541412033 7803981142841461906059025)
  ·
    refine ⟨5852985857131096429544269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7803981142841461906059025 5852985857131096429544269)
    ·
      refine ⟨2194869696424161161079101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5852985857131096429544269 2194869696424161161079101)
      ·
        refine ⟨823076136159060435404663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2194869696424161161079101 823076136159060435404663)
        ·
          refine ⟨1234614204238590653106995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 823076136159060435404663 1234614204238590653106995)
          ·
            refine ⟨1851921306357885979660493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1234614204238590653106995 1851921306357885979660493)
            ·
              refine ⟨694470489884207242372685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1851921306357885979660493 694470489884207242372685)
              ·
                refine ⟨260426433706577715889757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 694470489884207242372685 260426433706577715889757)
                ·
                  refine ⟨97659912639966643458659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260426433706577715889757 97659912639966643458659)
                  ·
                    rfl

theorem cell21_427932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_427932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427932 prefixEnd_427932 := by exact prefixLift 427932
  have htrace : WordTrace (prefixWord ++ tailWord_427932) baseStart_427932 baseEnd_427932 := by
    simpa [prefixWord, tailWord_427932, baseEnd_427932] using wordTrace_append hprefix tailTrace_427932
  have hstable : (prefixWord ++ tailWord_427932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427932).length < 2 ^ (prefixWord ++ tailWord_427932).sum := by decide
  have hdescent : baseEnd_427932 < baseStart_427932 := by decide
  rcases family_descends (prefixWord ++ tailWord_427932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427943 : List Nat := [1, 1, 6, 1, 2, 1, 9]
def baseStart_427943 : Nat := 118140960795 + 427943 * 2 ^ 59
def prefixEnd_427943 : Nat := 4983230072969 + 3 ^ 40 * 427943 * 2
def baseEnd_427943 : Nat := 10851380332203674308367

theorem tailTrace_427943 : CollatzResearch.WordTrace tailWord_427943 prefixEnd_427943 10851380332203674308367 := by
  unfold tailWord_427943
  simp only [CollatzResearch.WordTrace]
  refine ⟨15608363488643072690768483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10405575659095381793845655 15608363488643072690768483)
  ·
    refine ⟨23412545232964609036152725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15608363488643072690768483 23412545232964609036152725)
    ·
      refine ⟨1097463057795216048569659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23412545232964609036152725 1097463057795216048569659)
      ·
        refine ⟨1646194586692824072854489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1097463057795216048569659 1646194586692824072854489)
        ·
          refine ⟨1234645940019618054640867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1646194586692824072854489 1234645940019618054640867)
          ·
            refine ⟨1851968910029427081961301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1234645940019618054640867 1851968910029427081961301)
            ·
              refine ⟨10851380332203674308367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1851968910029427081961301 10851380332203674308367)
              ·
                rfl

theorem cell21_427943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 9].length) (baseStart_427943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_427943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_427943 prefixEnd_427943 := by exact prefixLift 427943
  have htrace : WordTrace (prefixWord ++ tailWord_427943) baseStart_427943 baseEnd_427943 := by
    simpa [prefixWord, tailWord_427943, baseEnd_427943] using wordTrace_append hprefix tailTrace_427943
  have hstable : (prefixWord ++ tailWord_427943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427943).length < 2 ^ (prefixWord ++ tailWord_427943).sum := by decide
  have hdescent : baseEnd_427943 < baseStart_427943 := by decide
  rcases family_descends (prefixWord ++ tailWord_427943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428095 : List Nat := [1, 1, 2, 2, 3, 1, 6, 5]
def baseStart_428095 : Nat := 118140960795 + 428095 * 2 ^ 59
def prefixEnd_428095 : Nat := 4983230072969 + 3 ^ 40 * 428095 * 2
def baseEnd_428095 : Nat := 32565703820238194080553

theorem tailTrace_428095 : CollatzResearch.WordTrace tailWord_428095 prefixEnd_428095 32565703820238194080553 := by
  unfold tailWord_428095
  simp only [CollatzResearch.WordTrace]
  refine ⟨15613907384092402650301739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10409271589394935100201159 15613907384092402650301739)
  ·
    refine ⟨23420861076138603975452609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15613907384092402650301739 23420861076138603975452609)
    ·
      refine ⟨17565645807103952981589457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23420861076138603975452609 17565645807103952981589457)
      ·
        refine ⟨13174234355327964736192093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17565645807103952981589457 13174234355327964736192093)
        ·
          refine ⟨4940337883247986776072035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13174234355327964736192093 4940337883247986776072035)
          ·
            refine ⟨7410506824871980164108053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4940337883247986776072035 7410506824871980164108053)
            ·
              refine ⟨347367507415874070192565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7410506824871980164108053 347367507415874070192565)
              ·
                refine ⟨32565703820238194080553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 347367507415874070192565 32565703820238194080553)
                ·
                  rfl

theorem cell21_428095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 5].length) (baseStart_428095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_428095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_428095 prefixEnd_428095 := by exact prefixLift 428095
  have htrace : WordTrace (prefixWord ++ tailWord_428095) baseStart_428095 baseEnd_428095 := by
    simpa [prefixWord, tailWord_428095, baseEnd_428095] using wordTrace_append hprefix tailTrace_428095
  have hstable : (prefixWord ++ tailWord_428095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428095).length < 2 ^ (prefixWord ++ tailWord_428095).sum := by decide
  have hdescent : baseEnd_428095 < baseStart_428095 := by decide
  rcases family_descends (prefixWord ++ tailWord_428095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428118 : List Nat := [5, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_428118 : Nat := 118140960795 + 428118 * 2 ^ 59
def prefixEnd_428118 : Nat := 4983230072969 + 3 ^ 40 * 428118 * 2
def baseEnd_428118 : Nat := 97702360374071653358279

theorem tailTrace_428118 : CollatzResearch.WordTrace tailWord_428118 prefixEnd_428118 97702360374071653358279 := by
  unfold tailWord_428118
  simp only [CollatzResearch.WordTrace]
  refine ⟨975921641438067348649313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10409830842006051718926005 975921641438067348649313)
  ·
    refine ⟨731941231078550511486985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 975921641438067348649313 731941231078550511486985)
    ·
      refine ⟨548955923308912883615239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 731941231078550511486985 548955923308912883615239)
      ·
        refine ⟨823433884963369325422859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548955923308912883615239 823433884963369325422859)
        ·
          refine ⟨1235150827445053988134289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 823433884963369325422859 1235150827445053988134289)
          ·
            refine ⟨926363120583790491100717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1235150827445053988134289 926363120583790491100717)
            ·
              refine ⟨347386170218921434162769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 926363120583790491100717 347386170218921434162769)
              ·
                refine ⟨260539627664191075622077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347386170218921434162769 260539627664191075622077)
                ·
                  refine ⟨97702360374071653358279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260539627664191075622077 97702360374071653358279)
                  ·
                    rfl

theorem cell21_428118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_428118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_428118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_428118 prefixEnd_428118 := by exact prefixLift 428118
  have htrace : WordTrace (prefixWord ++ tailWord_428118) baseStart_428118 baseEnd_428118 := by
    simpa [prefixWord, tailWord_428118, baseEnd_428118] using wordTrace_append hprefix tailTrace_428118
  have hstable : (prefixWord ++ tailWord_428118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428118).length < 2 ^ (prefixWord ++ tailWord_428118).sum := by decide
  have hdescent : baseEnd_428118 < baseStart_428118 := by decide
  rcases family_descends (prefixWord ++ tailWord_428118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428174 : List Nat := [4, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_428174 : Nat := 118140960795 + 428174 * 2 ^ 59
def prefixEnd_428174 : Nat := 4983230072969 + 3 ^ 40 * 428174 * 2
def baseEnd_428174 : Nat := 97715140337028000424831

theorem tailTrace_428174 : CollatzResearch.WordTrace tailWord_428174 prefixEnd_428174 97715140337028000424831 := by
  unfold tailWord_428174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1952098593850774892803447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10411192500537466094951717 1952098593850774892803447)
  ·
    refine ⟨2928147890776162339205171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1952098593850774892803447 2928147890776162339205171)
    ·
      refine ⟨4392221836164243508807757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2928147890776162339205171 4392221836164243508807757)
      ·
        refine ⟨1647083188561591315802909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4392221836164243508807757 1647083188561591315802909)
        ·
          refine ⟨617656195710596743426091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1647083188561591315802909 617656195710596743426091)
          ·
            refine ⟨926484293565895115139137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617656195710596743426091 926484293565895115139137)
            ·
              refine ⟨694863220174421336354353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 926484293565895115139137 694863220174421336354353)
              ·
                refine ⟨521147415130816002265765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694863220174421336354353 521147415130816002265765)
                ·
                  refine ⟨97715140337028000424831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 521147415130816002265765 97715140337028000424831)
                  ·
                    rfl

theorem cell21_428174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_428174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_428174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_428174 prefixEnd_428174 := by exact prefixLift 428174
  have htrace : WordTrace (prefixWord ++ tailWord_428174) baseStart_428174 baseEnd_428174 := by
    simpa [prefixWord, tailWord_428174, baseEnd_428174] using wordTrace_append hprefix tailTrace_428174
  have hstable : (prefixWord ++ tailWord_428174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428174).length < 2 ^ (prefixWord ++ tailWord_428174).sum := by decide
  have hdescent : baseEnd_428174 < baseStart_428174 := by decide
  rcases family_descends (prefixWord ++ tailWord_428174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428264 : List Nat := [2, 1, 4, 1, 2, 4, 2, 5]
def baseStart_428264 : Nat := 118140960795 + 428264 * 2 ^ 59
def prefixEnd_428264 : Nat := 4983230072969 + 3 ^ 40 * 428264 * 2
def baseEnd_428264 : Nat := 32578559854402614641549

theorem tailTrace_428264 : CollatzResearch.WordTrace tailWord_428264 prefixEnd_428264 32578559854402614641549 := by
  unfold tailWord_428264
  simp only [CollatzResearch.WordTrace]
  refine ⟨7810035660240072256601923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10413380880320096342135897 7810035660240072256601923)
  ·
    refine ⟨11715053490360108384902885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7810035660240072256601923 11715053490360108384902885)
    ·
      refine ⟨2196572529442520322169291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11715053490360108384902885 2196572529442520322169291)
      ·
        refine ⟨3294858794163780483253937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2196572529442520322169291 3294858794163780483253937)
        ·
          refine ⟨2471144095622835362440453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3294858794163780483253937 2471144095622835362440453)
          ·
            refine ⟨463339517929281630457585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2471144095622835362440453 463339517929281630457585)
            ·
              refine ⟨347504638446961222843189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463339517929281630457585 347504638446961222843189)
              ·
                refine ⟨32578559854402614641549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 347504638446961222843189 32578559854402614641549)
                ·
                  rfl

theorem cell21_428264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 5].length) (baseStart_428264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_428264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_428264 prefixEnd_428264 := by exact prefixLift 428264
  have htrace : WordTrace (prefixWord ++ tailWord_428264) baseStart_428264 baseEnd_428264 := by
    simpa [prefixWord, tailWord_428264, baseEnd_428264] using wordTrace_append hprefix tailTrace_428264
  have hstable : (prefixWord ++ tailWord_428264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428264).length < 2 ^ (prefixWord ++ tailWord_428264).sum := by decide
  have hdescent : baseEnd_428264 < baseStart_428264 := by decide
  rcases family_descends (prefixWord ++ tailWord_428264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428275 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 8]
def baseStart_428275 : Nat := 118140960795 + 428275 * 2 ^ 59
def prefixEnd_428275 : Nat := 4983230072969 + 3 ^ 40 * 428275 * 2
def baseEnd_428275 : Nat := 97738189913074269241291

theorem tailTrace_428275 : CollatzResearch.WordTrace tailWord_428275 prefixEnd_428275 97738189913074269241291 := by
  unfold tailWord_428275
  simp only [CollatzResearch.WordTrace]
  refine ⟨15620472523440293391854279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10413648348960195594569519 15620472523440293391854279)
  ·
    refine ⟨23430708785160440087781419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15620472523440293391854279 23430708785160440087781419)
    ·
      refine ⟨35146063177740660131672129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23430708785160440087781419 35146063177740660131672129)
      ·
        refine ⟨26359547383305495098754097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35146063177740660131672129 26359547383305495098754097)
        ·
          refine ⟨19769660537479121324065573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26359547383305495098754097 19769660537479121324065573)
          ·
            refine ⟨3706811350777335248262295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19769660537479121324065573 3706811350777335248262295)
            ·
              refine ⟨5560217026166002872393443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3706811350777335248262295 5560217026166002872393443)
              ·
                refine ⟨8340325539249004308590165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5560217026166002872393443 8340325539249004308590165)
                ·
                  refine ⟨97738189913074269241291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8340325539249004308590165 97738189913074269241291)
                  ·
                    rfl

theorem cell21_428275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 8].length) (baseStart_428275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_428275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_428275 prefixEnd_428275 := by exact prefixLift 428275
  have htrace : WordTrace (prefixWord ++ tailWord_428275) baseStart_428275 baseEnd_428275 := by
    simpa [prefixWord, tailWord_428275, baseEnd_428275] using wordTrace_append hprefix tailTrace_428275
  have hstable : (prefixWord ++ tailWord_428275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428275).length < 2 ^ (prefixWord ++ tailWord_428275).sum := by decide
  have hdescent : baseEnd_428275 < baseStart_428275 := by decide
  rcases family_descends (prefixWord ++ tailWord_428275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428309 : List Nat := [1, 3, 2, 1, 2, 1, 6, 1, 4]
def baseStart_428309 : Nat := 118140960795 + 428309 * 2 ^ 59
def prefixEnd_428309 : Nat := 4983230072969 + 3 ^ 40 * 428309 * 2
def baseEnd_428309 : Nat := 97745949176297765674555

theorem tailTrace_428309 : CollatzResearch.WordTrace tailWord_428309 prefixEnd_428309 97745949176297765674555 := by
  unfold tailWord_428309
  simp only [CollatzResearch.WordTrace]
  refine ⟨15621712605317117198591981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10414475070211411465727987 15621712605317117198591981)
  ·
    refine ⟨5858142226993918949471993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15621712605317117198591981 5858142226993918949471993)
    ·
      refine ⟨4393606670245439212103995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5858142226993918949471993 4393606670245439212103995)
      ·
        refine ⟨6590410005368158818155993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4393606670245439212103995 6590410005368158818155993)
        ·
          refine ⟨4942807504026119113616995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6590410005368158818155993 4942807504026119113616995)
          ·
            refine ⟨7414211256039178670425493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4942807504026119113616995 7414211256039178670425493)
            ·
              refine ⟨347541152626836500176195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7414211256039178670425493 347541152626836500176195)
              ·
                refine ⟨521311728940254750264293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347541152626836500176195 521311728940254750264293)
                ·
                  refine ⟨97745949176297765674555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 521311728940254750264293 97745949176297765674555)
                  ·
                    rfl

theorem cell21_428309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_428309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_428309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_428309 prefixEnd_428309 := by exact prefixLift 428309
  have htrace : WordTrace (prefixWord ++ tailWord_428309) baseStart_428309 baseEnd_428309 := by
    simpa [prefixWord, tailWord_428309, baseEnd_428309] using wordTrace_append hprefix tailTrace_428309
  have hstable : (prefixWord ++ tailWord_428309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428309).length < 2 ^ (prefixWord ++ tailWord_428309).sum := by decide
  have hdescent : baseEnd_428309 < baseStart_428309 := by decide
  rcases family_descends (prefixWord ++ tailWord_428309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428368 : List Nat := [2, 1, 1, 1, 1, 6, 2, 3, 4]
def baseStart_428368 : Nat := 118140960795 + 428368 * 2 ^ 59
def prefixEnd_428368 : Nat := 4983230072969 + 3 ^ 40 * 428368 * 2
def baseEnd_428368 : Nat := 97759413780126774191101

theorem tailTrace_428368 : CollatzResearch.WordTrace tailWord_428368 prefixEnd_428368 97759413780126774191101 := by
  unfold tailWord_428368
  simp only [CollatzResearch.WordTrace]
  refine ⟨7811932256051685137494879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10415909674735580183326505 7811932256051685137494879)
  ·
    refine ⟨11717898384077527706242319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7811932256051685137494879 11717898384077527706242319)
    ·
      refine ⟨17576847576116291559363479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11717898384077527706242319 17576847576116291559363479)
      ·
        refine ⟨26365271364174437339045219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17576847576116291559363479 26365271364174437339045219)
        ·
          refine ⟨39547907046261656008567829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26365271364174437339045219 39547907046261656008567829)
          ·
            refine ⟨1853808142793515125401617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39547907046261656008567829 1853808142793515125401617)
            ·
              refine ⟨1390356107095136344051213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1853808142793515125401617 1390356107095136344051213)
              ·
                refine ⟨521383540160676129019205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1390356107095136344051213 521383540160676129019205)
                ·
                  refine ⟨97759413780126774191101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 521383540160676129019205 97759413780126774191101)
                  ·
                    rfl

theorem cell21_428368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_428368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_428368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_428368 prefixEnd_428368 := by exact prefixLift 428368
  have htrace : WordTrace (prefixWord ++ tailWord_428368) baseStart_428368 baseEnd_428368 := by
    simpa [prefixWord, tailWord_428368, baseEnd_428368] using wordTrace_append hprefix tailTrace_428368
  have hstable : (prefixWord ++ tailWord_428368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428368).length < 2 ^ (prefixWord ++ tailWord_428368).sum := by decide
  have hdescent : baseEnd_428368 < baseStart_428368 := by decide
  rcases family_descends (prefixWord ++ tailWord_428368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428413 : List Nat := [1, 4, 1, 1, 2, 3, 1, 3, 5]
def baseStart_428413 : Nat := 118140960795 + 428413 * 2 ^ 59
def prefixEnd_428413 : Nat := 4983230072969 + 3 ^ 40 * 428413 * 2
def baseEnd_428413 : Nat := 97769683393216695941009

theorem tailTrace_428413 : CollatzResearch.WordTrace tailWord_428413 prefixEnd_428413 97769683393216695941009 := by
  unfold tailWord_428413
  simp only [CollatzResearch.WordTrace]
  refine ⟨15625505796940342960377893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10417003864626895306918595 15625505796940342960377893)
  ·
    refine ⟨2929782336926314305070855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15625505796940342960377893 2929782336926314305070855)
    ·
      refine ⟨4394673505389471457606283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2929782336926314305070855 4394673505389471457606283)
      ·
        refine ⟨6592010258084207186409425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4394673505389471457606283 6592010258084207186409425)
        ·
          refine ⟨4944007693563155389807069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6592010258084207186409425 4944007693563155389807069)
          ·
            refine ⟨1854002885086183271177651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4944007693563155389807069 1854002885086183271177651)
            ·
              refine ⟨2781004327629274906766477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1854002885086183271177651 2781004327629274906766477)
              ·
                refine ⟨1042876622860978090037429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2781004327629274906766477 1042876622860978090037429)
                ·
                  refine ⟨97769683393216695941009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1042876622860978090037429 97769683393216695941009)
                  ·
                    rfl

theorem cell21_428413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_428413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_428413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_428413 prefixEnd_428413 := by exact prefixLift 428413
  have htrace : WordTrace (prefixWord ++ tailWord_428413) baseStart_428413 baseEnd_428413 := by
    simpa [prefixWord, tailWord_428413, baseEnd_428413] using wordTrace_append hprefix tailTrace_428413
  have hstable : (prefixWord ++ tailWord_428413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428413).length < 2 ^ (prefixWord ++ tailWord_428413).sum := by decide
  have hdescent : baseEnd_428413 < baseStart_428413 := by decide
  rcases family_descends (prefixWord ++ tailWord_428413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428430 : List Nat := [4, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_428430 : Nat := 118140960795 + 428430 * 2 ^ 59
def prefixEnd_428430 : Nat := 4983230072969 + 3 ^ 40 * 428430 * 2
def baseEnd_428430 : Nat := 97773563024828444157641

theorem tailTrace_428430 : CollatzResearch.WordTrace tailWord_428430 prefixEnd_428430 97773563024828444157641 := by
  unfold tailWord_428430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1953265729734844357968343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10417417225252503242497829 1953265729734844357968343)
  ·
    refine ⟨2929898594602266536952515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1953265729734844357968343 2929898594602266536952515)
    ·
      refine ⟨4394847891903399805428773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2929898594602266536952515 4394847891903399805428773)
      ·
        refine ⟨824033979731887463517895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4394847891903399805428773 824033979731887463517895)
        ·
          refine ⟨1236050969597831195276843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824033979731887463517895 1236050969597831195276843)
          ·
            refine ⟨1854076454396746792915265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1236050969597831195276843 1854076454396746792915265)
            ·
              refine ⟨1390557340797560094686449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1854076454396746792915265 1390557340797560094686449)
              ·
                refine ⟨1042918005598170071014837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1390557340797560094686449 1042918005598170071014837)
                ·
                  refine ⟨97773563024828444157641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1042918005598170071014837 97773563024828444157641)
                  ·
                    rfl

theorem cell21_428430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_428430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_428430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_428430 prefixEnd_428430 := by exact prefixLift 428430
  have htrace : WordTrace (prefixWord ++ tailWord_428430) baseStart_428430 baseEnd_428430 := by
    simpa [prefixWord, tailWord_428430, baseEnd_428430] using wordTrace_append hprefix tailTrace_428430
  have hstable : (prefixWord ++ tailWord_428430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428430).length < 2 ^ (prefixWord ++ tailWord_428430).sum := by decide
  have hdescent : baseEnd_428430 < baseStart_428430 := by decide
  rcases family_descends (prefixWord ++ tailWord_428430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428506 : List Nat := [3, 1, 1, 2, 3, 1, 2, 5, 3]
def baseStart_428506 : Nat := 118140960795 + 428506 * 2 ^ 59
def prefixEnd_428506 : Nat := 4983230072969 + 3 ^ 40 * 428506 * 2
def baseEnd_428506 : Nat := 97790907260269200890819

theorem tailTrace_428506 : CollatzResearch.WordTrace tailWord_428506 prefixEnd_428506 97790907260269200890819 := by
  unfold tailWord_428506
  simp only [CollatzResearch.WordTrace]
  refine ⟨3907224446400854960878343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10419265190402279895675581 3907224446400854960878343)
  ·
    refine ⟨5860836669601282441317515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3907224446400854960878343 5860836669601282441317515)
    ·
      refine ⟨8791255004401923661976273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5860836669601282441317515 8791255004401923661976273)
      ·
        refine ⟨6593441253301442746482205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8791255004401923661976273 6593441253301442746482205)
        ·
          refine ⟨2472540469988041029930827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6593441253301442746482205 2472540469988041029930827)
          ·
            refine ⟨3708810704982061544896241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472540469988041029930827 3708810704982061544896241)
            ·
              refine ⟨2781608028736546158672181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3708810704982061544896241 2781608028736546158672181)
              ·
                refine ⟨260775752694051202375517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2781608028736546158672181 260775752694051202375517)
                ·
                  refine ⟨97790907260269200890819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260775752694051202375517 97790907260269200890819)
                  ·
                    rfl

theorem cell21_428506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_428506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_428506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_428506 prefixEnd_428506 := by exact prefixLift 428506
  have htrace : WordTrace (prefixWord ++ tailWord_428506) baseStart_428506 baseEnd_428506 := by
    simpa [prefixWord, tailWord_428506, baseEnd_428506] using wordTrace_append hprefix tailTrace_428506
  have hstable : (prefixWord ++ tailWord_428506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428506).length < 2 ^ (prefixWord ++ tailWord_428506).sum := by decide
  have hdescent : baseEnd_428506 < baseStart_428506 := by decide
  rcases family_descends (prefixWord ++ tailWord_428506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428520 : List Nat := [2, 1, 4, 1, 1, 3, 1, 4, 4]
def baseStart_428520 : Nat := 118140960795 + 428520 * 2 ^ 59
def prefixEnd_428520 : Nat := 4983230072969 + 3 ^ 40 * 428520 * 2
def baseEnd_428520 : Nat := 97794102251008287657457

theorem tailTrace_428520 : CollatzResearch.WordTrace tailWord_428520 prefixEnd_428520 97794102251008287657457 := by
  unfold tailWord_428520
  simp only [CollatzResearch.WordTrace]
  refine ⟨7814704203776350117261507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10419605605035133489682009 7814704203776350117261507)
  ·
    refine ⟨11722056305664525175892261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7814704203776350117261507 11722056305664525175892261)
    ·
      refine ⟨2197885557312098470479799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11722056305664525175892261 2197885557312098470479799)
      ·
        refine ⟨3296828335968147705719699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2197885557312098470479799 3296828335968147705719699)
        ·
          refine ⟨4945242503952221558579549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3296828335968147705719699 4945242503952221558579549)
          ·
            refine ⟨1854465938982083084467331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4945242503952221558579549 1854465938982083084467331)
            ·
              refine ⟨2781698908473124626700997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1854465938982083084467331 2781698908473124626700997)
              ·
                refine ⟨521568545338710867506437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2781698908473124626700997 521568545338710867506437)
                ·
                  refine ⟨97794102251008287657457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 521568545338710867506437 97794102251008287657457)
                  ·
                    rfl

theorem cell21_428520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_428520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_428520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_428520 prefixEnd_428520 := by exact prefixLift 428520
  have htrace : WordTrace (prefixWord ++ tailWord_428520) baseStart_428520 baseEnd_428520 := by
    simpa [prefixWord, tailWord_428520, baseEnd_428520] using wordTrace_append hprefix tailTrace_428520
  have hstable : (prefixWord ++ tailWord_428520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428520).length < 2 ^ (prefixWord ++ tailWord_428520).sum := by decide
  have hdescent : baseEnd_428520 < baseStart_428520 := by decide
  rcases family_descends (prefixWord ++ tailWord_428520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428557 : List Nat := [1, 7, 1, 1, 1, 2, 2, 3, 3]
def baseStart_428557 : Nat := 118140960795 + 428557 * 2 ^ 59
def prefixEnd_428557 : Nat := 4983230072969 + 3 ^ 40 * 428557 * 2
def baseEnd_428557 : Nat := 97802546155104445540715

theorem tailTrace_428557 : CollatzResearch.WordTrace tailWord_428557 prefixEnd_428557 97802546155104445540715 := by
  unfold tailWord_428557
  simp only [CollatzResearch.WordTrace]
  refine ⟨15630757908418655553619925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10420505272279103702413283 15630757908418655553619925)
  ·
    refine ⟨366345888478562239537967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 15630757908418655553619925 366345888478562239537967)
    ·
      refine ⟨549518832717843359306951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366345888478562239537967 549518832717843359306951)
      ·
        refine ⟨824278249076765038960427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549518832717843359306951 824278249076765038960427)
        ·
          refine ⟨1236417373615147558440641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824278249076765038960427 1236417373615147558440641)
          ·
            refine ⟨927313030211360668830481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1236417373615147558440641 927313030211360668830481)
            ·
              refine ⟨695484772658520501622861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 927313030211360668830481 695484772658520501622861)
              ·
                refine ⟨260806789746945188108573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 695484772658520501622861 260806789746945188108573)
                ·
                  refine ⟨97802546155104445540715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260806789746945188108573 97802546155104445540715)
                  ·
                    rfl

theorem cell21_428557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_428557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_428557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_428557 prefixEnd_428557 := by exact prefixLift 428557
  have htrace : WordTrace (prefixWord ++ tailWord_428557) baseStart_428557 baseEnd_428557 := by
    simpa [prefixWord, tailWord_428557, baseEnd_428557] using wordTrace_append hprefix tailTrace_428557
  have hstable : (prefixWord ++ tailWord_428557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428557).length < 2 ^ (prefixWord ++ tailWord_428557).sum := by decide
  have hdescent : baseEnd_428557 < baseStart_428557 := by decide
  rcases family_descends (prefixWord ++ tailWord_428557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428641 : List Nat := [1, 2, 3, 1, 1, 4, 3, 1, 5]
def baseStart_428641 : Nat := 118140960795 + 428641 * 2 ^ 59
def prefixEnd_428641 : Nat := 4983230072969 + 3 ^ 40 * 428641 * 2
def baseEnd_428641 : Nat := 97821716099538966140543

theorem tailTrace_428641 : CollatzResearch.WordTrace tailWord_428641 prefixEnd_428641 97821716099538966140543 := by
  unfold tailWord_428641
  simp only [CollatzResearch.WordTrace]
  refine ⟨15633821640114337899677777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10422547760076225266451851 15633821640114337899677777)
  ·
    refine ⟨11725366230085753424758333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15633821640114337899677777 11725366230085753424758333)
    ·
      refine ⟨4397012336282157534284375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11725366230085753424758333 4397012336282157534284375)
      ·
        refine ⟨6595518504423236301426563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4397012336282157534284375 6595518504423236301426563)
        ·
          refine ⟨9893277756634854452139845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6595518504423236301426563 9893277756634854452139845)
          ·
            refine ⟨1854989579369035209776221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9893277756634854452139845 1854989579369035209776221)
            ·
              refine ⟨695621092263388203666083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1854989579369035209776221 695621092263388203666083)
              ·
                refine ⟨1043431638395082305499125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 695621092263388203666083 1043431638395082305499125)
                ·
                  refine ⟨97821716099538966140543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1043431638395082305499125 97821716099538966140543)
                  ·
                    rfl

theorem cell21_428641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_428641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_428641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_428641 prefixEnd_428641 := by exact prefixLift 428641
  have htrace : WordTrace (prefixWord ++ tailWord_428641) baseStart_428641 baseEnd_428641 := by
    simpa [prefixWord, tailWord_428641, baseEnd_428641] using wordTrace_append hprefix tailTrace_428641
  have hstable : (prefixWord ++ tailWord_428641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428641).length < 2 ^ (prefixWord ++ tailWord_428641).sum := by decide
  have hdescent : baseEnd_428641 < baseStart_428641 := by decide
  rcases family_descends (prefixWord ++ tailWord_428641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428692 : List Nat := [2, 4, 2, 2, 1, 1, 4, 2, 3]
def baseStart_428692 : Nat := 118140960795 + 428692 * 2 ^ 59
def prefixEnd_428692 : Nat := 4983230072969 + 3 ^ 40 * 428692 * 2
def baseEnd_428692 : Nat := 97833354994374210790439

theorem tailTrace_428692 : CollatzResearch.WordTrace tailWord_428692 prefixEnd_428692 97833354994374210790439 := by
  unfold tailWord_428692
  simp only [CollatzResearch.WordTrace]
  refine ⟨7817840881464786804892165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10423787841953049073189553 7817840881464786804892165)
  ·
    refine ⟨1465845165274647525917281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7817840881464786804892165 1465845165274647525917281)
    ·
      refine ⟨1099383873955985644437961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1465845165274647525917281 1099383873955985644437961)
      ·
        refine ⟨824537905466989233328471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1099383873955985644437961 824537905466989233328471)
        ·
          refine ⟨1236806858200483849992707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824537905466989233328471 1236806858200483849992707)
          ·
            refine ⟨1855210287300725774989061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1236806858200483849992707 1855210287300725774989061)
            ·
              refine ⟨347851928868886082810449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1855210287300725774989061 347851928868886082810449)
              ·
                refine ⟨260888946651664562107837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347851928868886082810449 260888946651664562107837)
                ·
                  refine ⟨97833354994374210790439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260888946651664562107837 97833354994374210790439)
                  ·
                    rfl

theorem cell21_428692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_428692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_428692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_428692 prefixEnd_428692 := by exact prefixLift 428692
  have htrace : WordTrace (prefixWord ++ tailWord_428692) baseStart_428692 baseEnd_428692 := by
    simpa [prefixWord, tailWord_428692, baseEnd_428692] using wordTrace_append hprefix tailTrace_428692
  have hstable : (prefixWord ++ tailWord_428692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428692).length < 2 ^ (prefixWord ++ tailWord_428692).sum := by decide
  have hdescent : baseEnd_428692 < baseStart_428692 := by decide
  rcases family_descends (prefixWord ++ tailWord_428692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428717 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 7]
def baseStart_428717 : Nat := 118140960795 + 428717 * 2 ^ 59
def prefixEnd_428717 : Nat := 4983230072969 + 3 ^ 40 * 428717 * 2
def baseEnd_428717 : Nat := 97839060334979722873721

theorem tailTrace_428717 : CollatzResearch.WordTrace tailWord_428717 prefixEnd_428717 97839060334979722873721 := by
  unfold tailWord_428717
  simp only [CollatzResearch.WordTrace]
  refine ⟨15636593587839002879444405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10424395725226001919629603 15636593587839002879444405)
  ·
    refine ⟨1465930648859906519947913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15636593587839002879444405 1465930648859906519947913)
    ·
      refine ⟨1099447986644929889960935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1465930648859906519947913 1099447986644929889960935)
      ·
        refine ⟨1649171979967394834941403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1099447986644929889960935 1649171979967394834941403)
        ·
          refine ⟨2473757969951092252412105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1649171979967394834941403 2473757969951092252412105)
          ·
            refine ⟨1855318477463319189309079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2473757969951092252412105 1855318477463319189309079)
            ·
              refine ⟨2782977716194978783963619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1855318477463319189309079 2782977716194978783963619)
              ·
                refine ⟨4174466574292468175945429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2782977716194978783963619 4174466574292468175945429)
                ·
                  refine ⟨97839060334979722873721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4174466574292468175945429 97839060334979722873721)
                  ·
                    rfl

theorem cell21_428717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_428717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_428717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_428717 prefixEnd_428717 := by exact prefixLift 428717
  have htrace : WordTrace (prefixWord ++ tailWord_428717) baseStart_428717 baseEnd_428717 := by
    simpa [prefixWord, tailWord_428717, baseEnd_428717] using wordTrace_append hprefix tailTrace_428717
  have hstable : (prefixWord ++ tailWord_428717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428717).length < 2 ^ (prefixWord ++ tailWord_428717).sum := by decide
  have hdescent : baseEnd_428717 < baseStart_428717 := by decide
  rcases family_descends (prefixWord ++ tailWord_428717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428748 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 6]
def baseStart_428748 : Nat := 118140960795 + 428748 * 2 ^ 59
def prefixEnd_428748 : Nat := 4983230072969 + 3 ^ 40 * 428748 * 2
def baseEnd_428748 : Nat := 97846134957330557856991

theorem tailTrace_428748 : CollatzResearch.WordTrace tailWord_428748 prefixEnd_428748 97846134957330557856991 := by
  unfold tailWord_428748
  simp only [CollatzResearch.WordTrace]
  refine ⟨7818862125363347586911449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10425149500484463449215265 7818862125363347586911449)
  ·
    refine ⟨5864146594022510690183587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7818862125363347586911449 5864146594022510690183587)
    ·
      refine ⟨8796219891033766035275381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5864146594022510690183587 8796219891033766035275381)
      ·
        refine ⟨824645614784415565807067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8796219891033766035275381 824645614784415565807067)
        ·
          refine ⟨1236968422176623348710601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824645614784415565807067 1236968422176623348710601)
          ·
            refine ⟨927726316632467511532951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1236968422176623348710601 927726316632467511532951)
            ·
              refine ⟨1391589474948701267299427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927726316632467511532951 1391589474948701267299427)
              ·
                refine ⟨2087384212423051900949141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391589474948701267299427 2087384212423051900949141)
                ·
                  refine ⟨97846134957330557856991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2087384212423051900949141 97846134957330557856991)
                  ·
                    rfl

theorem cell21_428748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_428748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_428748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_428748 prefixEnd_428748 := by exact prefixLift 428748
  have htrace : WordTrace (prefixWord ++ tailWord_428748) baseStart_428748 baseEnd_428748 := by
    simpa [prefixWord, tailWord_428748, baseEnd_428748] using wordTrace_append hprefix tailTrace_428748
  have hstable : (prefixWord ++ tailWord_428748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428748).length < 2 ^ (prefixWord ++ tailWord_428748).sum := by decide
  have hdescent : baseEnd_428748 < baseStart_428748 := by decide
  rcases family_descends (prefixWord ++ tailWord_428748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428861 : List Nat := [1, 4, 1, 4, 3, 1, 2, 2, 3]
def baseStart_428861 : Nat := 118140960795 + 428861 * 2 ^ 59
def prefixEnd_428861 : Nat := 4983230072969 + 3 ^ 40 * 428861 * 2
def baseEnd_428861 : Nat := 97871923096867472473427

theorem tailTrace_428861 : CollatzResearch.WordTrace tailWord_428861 prefixEnd_428861 97871923096867472473427 := by
  unfold tailWord_428861
  simp only [CollatzResearch.WordTrace]
  refine ⟨15641845699317315472686437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10427897132878210315124291 15641845699317315472686437)
  ·
    refine ⟨2932846068621996651128707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15641845699317315472686437 2932846068621996651128707)
    ·
      refine ⟨4399269102932994976693061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2932846068621996651128707 4399269102932994976693061)
      ·
        refine ⟨824862956799936558129949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4399269102932994976693061 824862956799936558129949)
        ·
          refine ⟨309323608799976209298731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 824862956799936558129949 309323608799976209298731)
          ·
            refine ⟨463985413199964313948097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309323608799976209298731 463985413199964313948097)
            ·
              refine ⟨347989059899973235461073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463985413199964313948097 347989059899973235461073)
              ·
                refine ⟨260991794924979926595805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347989059899973235461073 260991794924979926595805)
                ·
                  refine ⟨97871923096867472473427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260991794924979926595805 97871923096867472473427)
                  ·
                    rfl

theorem cell21_428861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_428861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_428861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_428861 prefixEnd_428861 := by exact prefixLift 428861
  have htrace : WordTrace (prefixWord ++ tailWord_428861) baseStart_428861 baseEnd_428861 := by
    simpa [prefixWord, tailWord_428861, baseEnd_428861] using wordTrace_append hprefix tailTrace_428861
  have hstable : (prefixWord ++ tailWord_428861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428861).length < 2 ^ (prefixWord ++ tailWord_428861).sum := by decide
  have hdescent : baseEnd_428861 < baseStart_428861 := by decide
  rcases family_descends (prefixWord ++ tailWord_428861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428917 : List Nat := [1, 3, 4, 1, 1, 4, 1, 2, 4]
def baseStart_428917 : Nat := 118140960795 + 428917 * 2 ^ 59
def prefixEnd_428917 : Nat := 4983230072969 + 3 ^ 40 * 428917 * 2
def baseEnd_428917 : Nat := 97884703059823819539979

theorem tailTrace_428917 : CollatzResearch.WordTrace tailWord_428917 prefixEnd_428917 97884703059823819539979 := by
  unfold tailWord_428917
  simp only [CollatzResearch.WordTrace]
  refine ⟨15643888187114437036725005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10429258791409624691150003 15643888187114437036725005)
  ·
    refine ⟨5866458070167913888771877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15643888187114437036725005 5866458070167913888771877)
    ·
      refine ⟨1099960888156483854144727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5866458070167913888771877 1099960888156483854144727)
      ·
        refine ⟨1649941332234725781217091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1099960888156483854144727 1649941332234725781217091)
        ·
          refine ⟨2474911998352088671825637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1649941332234725781217091 2474911998352088671825637)
          ·
            refine ⟨464045999691016625967307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2474911998352088671825637 464045999691016625967307)
            ·
              refine ⟨696068999536524938950961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464045999691016625967307 696068999536524938950961)
              ·
                refine ⟨522051749652393704213221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 696068999536524938950961 522051749652393704213221)
                ·
                  refine ⟨97884703059823819539979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 522051749652393704213221 97884703059823819539979)
                  ·
                    rfl

theorem cell21_428917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_428917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_428917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_428917 prefixEnd_428917 := by exact prefixLift 428917
  have htrace : WordTrace (prefixWord ++ tailWord_428917) baseStart_428917 baseEnd_428917 := by
    simpa [prefixWord, tailWord_428917, baseEnd_428917] using wordTrace_append hprefix tailTrace_428917
  have hstable : (prefixWord ++ tailWord_428917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428917).length < 2 ^ (prefixWord ++ tailWord_428917).sum := by decide
  have hdescent : baseEnd_428917 < baseStart_428917 := by decide
  rcases family_descends (prefixWord ++ tailWord_428917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428959 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 6]
def baseStart_428959 : Nat := 118140960795 + 428959 * 2 ^ 59
def prefixEnd_428959 : Nat := 4983230072969 + 3 ^ 40 * 428959 * 2
def baseEnd_428959 : Nat := 97894288032041079839893

theorem tailTrace_428959 : CollatzResearch.WordTrace tailWord_428959 prefixEnd_428959 97894288032041079839893 := by
  unfold tailWord_428959
  simp only [CollatzResearch.WordTrace]
  refine ⟨15645420052962278209753931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10430280035308185473169287 15645420052962278209753931)
  ·
    refine ⟨23468130079443417314630897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15645420052962278209753931 23468130079443417314630897)
    ·
      refine ⟨17601097559582562985973173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23468130079443417314630897 17601097559582562985973173)
      ·
        refine ⟨1650102896210865279934985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17601097559582562985973173 1650102896210865279934985)
        ·
          refine ⟨1237577172158148959951239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1650102896210865279934985 1237577172158148959951239)
          ·
            refine ⟨1856365758237223439926859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237577172158148959951239 1856365758237223439926859)
            ·
              refine ⟨2784548637355835159890289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1856365758237223439926859 2784548637355835159890289)
              ·
                refine ⟨2088411478016876369917717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2784548637355835159890289 2088411478016876369917717)
                ·
                  refine ⟨97894288032041079839893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2088411478016876369917717 97894288032041079839893)
                  ·
                    rfl

theorem cell21_428959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 6].length) (baseStart_428959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_428959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_428959 prefixEnd_428959 := by exact prefixLift 428959
  have htrace : WordTrace (prefixWord ++ tailWord_428959) baseStart_428959 baseEnd_428959 := by
    simpa [prefixWord, tailWord_428959, baseEnd_428959] using wordTrace_append hprefix tailTrace_428959
  have hstable : (prefixWord ++ tailWord_428959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428959).length < 2 ^ (prefixWord ++ tailWord_428959).sum := by decide
  have hdescent : baseEnd_428959 < baseStart_428959 := by decide
  rcases family_descends (prefixWord ++ tailWord_428959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428990 : List Nat := [4, 2, 1, 1, 1, 2, 4, 6]
def baseStart_428990 : Nat := 118140960795 + 428990 * 2 ^ 59
def prefixEnd_428990 : Nat := 4983230072969 + 3 ^ 40 * 428990 * 2
def baseEnd_428990 : Nat := 32633787551463971607721

theorem tailTrace_428990 : CollatzResearch.WordTrace tailWord_428990 prefixEnd_428990 32633787551463971607721 := by
  unfold tailWord_428990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1955818839481246313016553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10431033810566647002754949 1955818839481246313016553)
  ·
    refine ⟨1466864129610934734762415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1955818839481246313016553 1466864129610934734762415)
    ·
      refine ⟨2200296194416402102143623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1466864129610934734762415 2200296194416402102143623)
      ·
        refine ⟨3300444291624603153215435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2200296194416402102143623 3300444291624603153215435)
        ·
          refine ⟨4950666437436904729823153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3300444291624603153215435 4950666437436904729823153)
          ·
            refine ⟨3712999828077678547367365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4950666437436904729823153 3712999828077678547367365)
            ·
              refine ⟨696187467764564727631381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3712999828077678547367365 696187467764564727631381)
              ·
                refine ⟨32633787551463971607721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 696187467764564727631381 32633787551463971607721)
                ·
                  rfl

theorem cell21_428990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_428990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_428990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_428990 prefixEnd_428990 := by exact prefixLift 428990
  have htrace : WordTrace (prefixWord ++ tailWord_428990) baseStart_428990 baseEnd_428990 := by
    simpa [prefixWord, tailWord_428990, baseEnd_428990] using wordTrace_append hprefix tailTrace_428990
  have hstable : (prefixWord ++ tailWord_428990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428990).length < 2 ^ (prefixWord ++ tailWord_428990).sum := by decide
  have hdescent : baseEnd_428990 < baseStart_428990 := by decide
  rcases family_descends (prefixWord ++ tailWord_428990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429004 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 7]
def baseStart_429004 : Nat := 118140960795 + 429004 * 2 ^ 59
def prefixEnd_429004 : Nat := 4983230072969 + 3 ^ 40 * 429004 * 2
def baseEnd_429004 : Nat := 97904557645131001589801

theorem tailTrace_429004 : CollatzResearch.WordTrace tailWord_429004 prefixEnd_429004 97904557645131001589801 := by
  unfold tailWord_429004
  simp only [CollatzResearch.WordTrace]
  refine ⟨7823530668899625447571033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10431374225199500596761377 7823530668899625447571033)
  ·
    refine ⟨5867648001674719085678275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7823530668899625447571033 5867648001674719085678275)
    ·
      refine ⟨8801472002512078628517413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5867648001674719085678275 8801472002512078628517413)
      ·
        refine ⟨1650276000471014742847015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8801472002512078628517413 1650276000471014742847015)
        ·
          refine ⟨2475414000706522114270523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1650276000471014742847015 2475414000706522114270523)
          ·
            refine ⟨3713121001059783171405785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475414000706522114270523 3713121001059783171405785)
            ·
              refine ⟨2784840750794837378554339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3713121001059783171405785 2784840750794837378554339)
              ·
                refine ⟨4177261126192256067831509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2784840750794837378554339 4177261126192256067831509)
                ·
                  refine ⟨97904557645131001589801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4177261126192256067831509 97904557645131001589801)
                  ·
                    rfl

theorem cell21_429004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_429004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_429004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_429004 prefixEnd_429004 := by exact prefixLift 429004
  have htrace : WordTrace (prefixWord ++ tailWord_429004) baseStart_429004 baseEnd_429004 := by
    simpa [prefixWord, tailWord_429004, baseEnd_429004] using wordTrace_append hprefix tailTrace_429004
  have hstable : (prefixWord ++ tailWord_429004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429004).length < 2 ^ (prefixWord ++ tailWord_429004).sum := by decide
  have hdescent : baseEnd_429004 < baseStart_429004 := by decide
  rcases family_descends (prefixWord ++ tailWord_429004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429139 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 9]
def baseStart_429139 : Nat := 118140960795 + 429139 * 2 ^ 59
def prefixEnd_429139 : Nat := 4983230072969 + 3 ^ 40 * 429139 * 2
def baseEnd_429139 : Nat := 97935366484400766839525

theorem tailTrace_429139 : CollatzResearch.WordTrace tailWord_429139 prefixEnd_429139 97935366484400766839525 := by
  unfold tailWord_429139
  simp only [CollatzResearch.WordTrace]
  refine ⟨15651985192310168951306471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10434656794873445967537647 15651985192310168951306471)
  ·
    refine ⟨23477977788465253426959707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15651985192310168951306471 23477977788465253426959707)
    ·
      refine ⟨35216966682697880140439561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23477977788465253426959707 35216966682697880140439561)
      ·
        refine ⟨26412725012023410105329671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35216966682697880140439561 26412725012023410105329671)
        ·
          refine ⟨39619087518035115157994507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26412725012023410105329671 39619087518035115157994507)
          ·
            refine ⟨59428631277052672736991761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39619087518035115157994507 59428631277052672736991761)
            ·
              refine ⟨44571473457789504552743821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59428631277052672736991761 44571473457789504552743821)
              ·
                refine ⟨16714302546671064207278933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44571473457789504552743821 16714302546671064207278933)
                ·
                  refine ⟨97935366484400766839525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16714302546671064207278933 97935366484400766839525)
                  ·
                    rfl

theorem cell21_429139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 9].length) (baseStart_429139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_429139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_429139 prefixEnd_429139 := by exact prefixLift 429139
  have htrace : WordTrace (prefixWord ++ tailWord_429139) baseStart_429139 baseEnd_429139 := by
    simpa [prefixWord, tailWord_429139, baseEnd_429139] using wordTrace_append hprefix tailTrace_429139
  have hstable : (prefixWord ++ tailWord_429139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429139).length < 2 ^ (prefixWord ++ tailWord_429139).sum := by decide
  have hdescent : baseEnd_429139 < baseStart_429139 := by decide
  rcases family_descends (prefixWord ++ tailWord_429139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429207 : List Nat := [1, 1, 3, 3, 3, 3, 2, 2, 3]
def baseStart_429207 : Nat := 118140960795 + 429207 * 2 ^ 59
def prefixEnd_429207 : Nat := 4983230072969 + 3 ^ 40 * 429207 * 2
def baseEnd_429207 : Nat := 97950885010847759706053

theorem tailTrace_429207 : CollatzResearch.WordTrace tailWord_429207 prefixEnd_429207 97950885010847759706053 := by
  unfold tailWord_429207
  simp only [CollatzResearch.WordTrace]
  refine ⟨15654465356063816564781875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10436310237375877709854583 15654465356063816564781875)
  ·
    refine ⟨23481698034095724847172813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15654465356063816564781875 23481698034095724847172813)
    ·
      refine ⟨8805636762785896817689805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23481698034095724847172813 8805636762785896817689805)
      ·
        refine ⟨3302113786044711306633677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8805636762785896817689805 3302113786044711306633677)
        ·
          refine ⟨1238292669766766739987629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3302113786044711306633677 1238292669766766739987629)
          ·
            refine ⟨464359751162537527495361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1238292669766766739987629 464359751162537527495361)
            ·
              refine ⟨348269813371903145621521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 464359751162537527495361 348269813371903145621521)
              ·
                refine ⟨261202360028927359216141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348269813371903145621521 261202360028927359216141)
                ·
                  refine ⟨97950885010847759706053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261202360028927359216141 97950885010847759706053)
                  ·
                    rfl

theorem cell21_429207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 3].length) (baseStart_429207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_429207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_429207 prefixEnd_429207 := by exact prefixLift 429207
  have htrace : WordTrace (prefixWord ++ tailWord_429207) baseStart_429207 baseEnd_429207 := by
    simpa [prefixWord, tailWord_429207, baseEnd_429207] using wordTrace_append hprefix tailTrace_429207
  have hstable : (prefixWord ++ tailWord_429207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429207).length < 2 ^ (prefixWord ++ tailWord_429207).sum := by decide
  have hdescent : baseEnd_429207 < baseStart_429207 := by decide
  rcases family_descends (prefixWord ++ tailWord_429207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429280 : List Nat := [2, 1, 1, 3, 1, 5, 3, 1, 4]
def baseStart_429280 : Nat := 118140960795 + 429280 * 2 ^ 59
def prefixEnd_429280 : Nat := 4983230072969 + 3 ^ 40 * 429280 * 2
def baseEnd_429280 : Nat := 97967544605415854989237

theorem tailTrace_429280 : CollatzResearch.WordTrace tailWord_429280 prefixEnd_429280 97967544605415854989237 := by
  unfold tailWord_429280
  simp only [CollatzResearch.WordTrace]
  refine ⟨7828563942399675016094647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10438085256532900021459529 7828563942399675016094647)
  ·
    refine ⟨11742845913599512524141971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7828563942399675016094647 11742845913599512524141971)
    ·
      refine ⟨17614268870399268786212957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11742845913599512524141971 17614268870399268786212957)
      ·
        refine ⟨6605350826399725794829859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17614268870399268786212957 6605350826399725794829859)
        ·
          refine ⟨9908026239599588692244789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6605350826399725794829859 9908026239599588692244789)
          ·
            refine ⟨928877459962461439897949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9908026239599588692244789 928877459962461439897949)
            ·
              refine ⟨348329047485923039961731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 928877459962461439897949 348329047485923039961731)
              ·
                refine ⟨522493571228884559942597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348329047485923039961731 522493571228884559942597)
                ·
                  refine ⟨97967544605415854989237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 522493571228884559942597 97967544605415854989237)
                  ·
                    rfl

theorem cell21_429280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 4].length) (baseStart_429280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_429280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_429280 prefixEnd_429280 := by exact prefixLift 429280
  have htrace : WordTrace (prefixWord ++ tailWord_429280) baseStart_429280 baseEnd_429280 := by
    simpa [prefixWord, tailWord_429280, baseEnd_429280] using wordTrace_append hprefix tailTrace_429280
  have hstable : (prefixWord ++ tailWord_429280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429280).length < 2 ^ (prefixWord ++ tailWord_429280).sum := by decide
  have hdescent : baseEnd_429280 < baseStart_429280 := by decide
  rcases family_descends (prefixWord ++ tailWord_429280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429294 : List Nat := [4, 1, 2, 1, 1, 1, 6, 5]
def baseStart_429294 : Nat := 118140960795 + 429294 * 2 ^ 59
def prefixEnd_429294 : Nat := 4983230072969 + 3 ^ 40 * 429294 * 2
def baseEnd_429294 : Nat := 32656913198718313918625

theorem tailTrace_429294 : CollatzResearch.WordTrace tailWord_429294 prefixEnd_429294 32656913198718313918625 := by
  unfold tailWord_429294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1957204813343578802899867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10438425671165753615465957 1957204813343578802899867)
  ·
    refine ⟨2935807220015368204349801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1957204813343578802899867 2935807220015368204349801)
    ·
      refine ⟨2201855415011526153262351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2935807220015368204349801 2201855415011526153262351)
      ·
        refine ⟨3302783122517289229893527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2201855415011526153262351 3302783122517289229893527)
        ·
          refine ⟨4954174683775933844840291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3302783122517289229893527 4954174683775933844840291)
          ·
            refine ⟨7431262025663900767260437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4954174683775933844840291 7431262025663900767260437)
            ·
              refine ⟨348340407452995348465333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7431262025663900767260437 348340407452995348465333)
              ·
                refine ⟨32656913198718313918625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 348340407452995348465333 32656913198718313918625)
                ·
                  rfl

theorem cell21_429294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_429294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_429294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_429294 prefixEnd_429294 := by exact prefixLift 429294
  have htrace : WordTrace (prefixWord ++ tailWord_429294) baseStart_429294 baseEnd_429294 := by
    simpa [prefixWord, tailWord_429294, baseEnd_429294] using wordTrace_append hprefix tailTrace_429294
  have hstable : (prefixWord ++ tailWord_429294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429294).length < 2 ^ (prefixWord ++ tailWord_429294).sum := by decide
  have hdescent : baseEnd_429294 < baseStart_429294 := by decide
  rcases family_descends (prefixWord ++ tailWord_429294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429373 : List Nat := [1, 4, 1, 5, 1, 1, 2, 2, 4]
def baseStart_429373 : Nat := 118140960795 + 429373 * 2 ^ 59
def prefixEnd_429373 : Nat := 4983230072969 + 3 ^ 40 * 429373 * 2
def baseEnd_429373 : Nat := 97988768472468359939047

theorem tailTrace_429373 : CollatzResearch.WordTrace tailWord_429373 prefixEnd_429373 97988768472468359939047 := by
  unfold tailWord_429373
  simp only [CollatzResearch.WordTrace]
  refine ⟨15660519873462426915324773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10440346582308284610216515 15660519873462426915324773)
  ·
    refine ⟨2936347476274205046623395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15660519873462426915324773 2936347476274205046623395)
    ·
      refine ⟨4404521214411307569935093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2936347476274205046623395 4404521214411307569935093)
      ·
        refine ⟨412923863851060084681415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4404521214411307569935093 412923863851060084681415)
        ·
          refine ⟨619385795776590127022123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412923863851060084681415 619385795776590127022123)
          ·
            refine ⟨929078693664885190533185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619385795776590127022123 929078693664885190533185)
            ·
              refine ⟨696809020248663892899889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 929078693664885190533185 696809020248663892899889)
              ·
                refine ⟨522606765186497919674917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 696809020248663892899889 522606765186497919674917)
                ·
                  refine ⟨97988768472468359939047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 522606765186497919674917 97988768472468359939047)
                  ·
                    rfl

theorem cell21_429373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_429373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_429373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_429373 prefixEnd_429373 := by exact prefixLift 429373
  have htrace : WordTrace (prefixWord ++ tailWord_429373) baseStart_429373 baseEnd_429373 := by
    simpa [prefixWord, tailWord_429373, baseEnd_429373] using wordTrace_append hprefix tailTrace_429373
  have hstable : (prefixWord ++ tailWord_429373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429373).length < 2 ^ (prefixWord ++ tailWord_429373).sum := by decide
  have hdescent : baseEnd_429373 < baseStart_429373 := by decide
  rcases family_descends (prefixWord ++ tailWord_429373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429508 : List Nat := [2, 3, 3, 2, 1, 2, 1, 3, 4]
def baseStart_429508 : Nat := 118140960795 + 429508 * 2 ^ 59
def prefixEnd_429508 : Nat := 4983230072969 + 3 ^ 40 * 429508 * 2
def baseEnd_429508 : Nat := 98019577311738125188771

theorem tailTrace_429508 : CollatzResearch.WordTrace tailWord_429508 prefixEnd_429508 98019577311738125188771 := by
  unfold tailWord_429508
  simp only [CollatzResearch.WordTrace]
  refine ⟨7832721863986672485744589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10443629151982229980992785 7832721863986672485744589)
  ·
    refine ⟨2937270698995002182154221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7832721863986672485744589 2937270698995002182154221)
    ·
      refine ⟨1101476512123125818307833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2937270698995002182154221 1101476512123125818307833)
      ·
        refine ⟨826107384092344363730875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1101476512123125818307833 826107384092344363730875)
        ·
          refine ⟨1239161076138516545596313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826107384092344363730875 1239161076138516545596313)
          ·
            refine ⟨929370807103887409197235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1239161076138516545596313 929370807103887409197235)
            ·
              refine ⟨1394056210655831113795853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929370807103887409197235 1394056210655831113795853)
              ·
                refine ⟨522771078995936667673445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1394056210655831113795853 522771078995936667673445)
                ·
                  refine ⟨98019577311738125188771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 522771078995936667673445 98019577311738125188771)
                  ·
                    rfl

theorem cell21_429508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_429508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_429508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_429508 prefixEnd_429508 := by exact prefixLift 429508
  have htrace : WordTrace (prefixWord ++ tailWord_429508) baseStart_429508 baseEnd_429508 := by
    simpa [prefixWord, tailWord_429508, baseEnd_429508] using wordTrace_append hprefix tailTrace_429508
  have hstable : (prefixWord ++ tailWord_429508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429508).length < 2 ^ (prefixWord ++ tailWord_429508).sum := by decide
  have hdescent : baseEnd_429508 < baseStart_429508 := by decide
  rcases family_descends (prefixWord ++ tailWord_429508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429519 : List Nat := [1, 1, 2, 1, 1, 4, 2, 4, 5]
def baseStart_429519 : Nat := 118140960795 + 429519 * 2 ^ 59
def prefixEnd_429519 : Nat := 4983230072969 + 3 ^ 40 * 429519 * 2
def baseEnd_429519 : Nat := 98022087661604550505415

theorem tailTrace_429519 : CollatzResearch.WordTrace tailWord_429519 prefixEnd_429519 98022087661604550505415 := by
  unfold tailWord_429519
  simp only [CollatzResearch.WordTrace]
  refine ⟨15665844930933493850139611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10443896620622329233426407 15665844930933493850139611)
  ·
    refine ⟨23498767396400240775209417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15665844930933493850139611 23498767396400240775209417)
    ·
      refine ⟨17624075547300180581407063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23498767396400240775209417 17624075547300180581407063)
      ·
        refine ⟨26436113320950270872110595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17624075547300180581407063 26436113320950270872110595)
        ·
          refine ⟨39654169981425406308165893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26436113320950270872110595 39654169981425406308165893)
          ·
            refine ⟨7435156871517263682781105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39654169981425406308165893 7435156871517263682781105)
            ·
              refine ⟨5576367653637947762085829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7435156871517263682781105 5576367653637947762085829)
              ·
                refine ⟨1045568935057115205391093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5576367653637947762085829 1045568935057115205391093)
                ·
                  refine ⟨98022087661604550505415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1045568935057115205391093 98022087661604550505415)
                  ·
                    rfl

theorem cell21_429519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 5].length) (baseStart_429519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_429519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_429519 prefixEnd_429519 := by exact prefixLift 429519
  have htrace : WordTrace (prefixWord ++ tailWord_429519) baseStart_429519 baseEnd_429519 := by
    simpa [prefixWord, tailWord_429519, baseEnd_429519] using wordTrace_append hprefix tailTrace_429519
  have hstable : (prefixWord ++ tailWord_429519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429519).length < 2 ^ (prefixWord ++ tailWord_429519).sum := by decide
  have hdescent : baseEnd_429519 < baseStart_429519 := by decide
  rcases family_descends (prefixWord ++ tailWord_429519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429553 : List Nat := [1, 2, 2, 2, 3, 3, 1, 4, 3]
def baseStart_429553 : Nat := 118140960795 + 429553 * 2 ^ 59
def prefixEnd_429553 : Nat := 4983230072969 + 3 ^ 40 * 429553 * 2
def baseEnd_429553 : Nat := 98029846924828046938679

theorem tailTrace_429553 : CollatzResearch.WordTrace tailWord_429553 prefixEnd_429553 98029846924828046938679 := by
  unfold tailWord_429553
  simp only [CollatzResearch.WordTrace]
  refine ⟨15667085012810317656877313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10444723341873545104584875 15667085012810317656877313)
  ·
    refine ⟨11750313759607738242657985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15667085012810317656877313 11750313759607738242657985)
    ·
      refine ⟨8812735319705803681993489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11750313759607738242657985 8812735319705803681993489)
      ·
        refine ⟨6609551489779352761495117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8812735319705803681993489 6609551489779352761495117)
        ·
          refine ⟨2478581808667257285560669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6609551489779352761495117 2478581808667257285560669)
          ·
            refine ⟨929468178250221482085251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2478581808667257285560669 929468178250221482085251)
            ·
              refine ⟨1394202267375332223127877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929468178250221482085251 1394202267375332223127877)
              ·
                refine ⟨261412925132874791836477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1394202267375332223127877 261412925132874791836477)
                ·
                  refine ⟨98029846924828046938679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261412925132874791836477 98029846924828046938679)
                  ·
                    rfl

theorem cell21_429553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 3].length) (baseStart_429553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_429553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_429553 prefixEnd_429553 := by exact prefixLift 429553
  have htrace : WordTrace (prefixWord ++ tailWord_429553) baseStart_429553 baseEnd_429553 := by
    simpa [prefixWord, tailWord_429553, baseEnd_429553] using wordTrace_append hprefix tailTrace_429553
  have hstable : (prefixWord ++ tailWord_429553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429553).length < 2 ^ (prefixWord ++ tailWord_429553).sum := by decide
  have hdescent : baseEnd_429553 < baseStart_429553 := by decide
  rcases family_descends (prefixWord ++ tailWord_429553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429677 : List Nat := [1, 5, 1, 1, 4, 2, 2, 1, 4]
def baseStart_429677 : Nat := 118140960795 + 429677 * 2 ^ 59
def prefixEnd_429677 : Nat := 4983230072969 + 3 ^ 40 * 429677 * 2
def baseEnd_429677 : Nat := 98058145414231386871759

theorem tailTrace_429677 : CollatzResearch.WordTrace tailWord_429677 prefixEnd_429677 98058145414231386871759 := by
  unfold tailWord_429677
  simp only [CollatzResearch.WordTrace]
  refine ⟨15671607664361086834391285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10447738442907391222927523 15671607664361086834391285)
  ·
    refine ⟨1469213218533851890724183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15671607664361086834391285 1469213218533851890724183)
    ·
      refine ⟨2203819827800777836086275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1469213218533851890724183 2203819827800777836086275)
      ·
        refine ⟨3305729741701166754129413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2203819827800777836086275 3305729741701166754129413)
        ·
          refine ⟨619824326568968766399265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3305729741701166754129413 619824326568968766399265)
          ·
            refine ⟨464868244926726574799449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 619824326568968766399265 464868244926726574799449)
            ·
              refine ⟨348651183695044931099587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 464868244926726574799449 348651183695044931099587)
              ·
                refine ⟨522976775542567396649381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348651183695044931099587 522976775542567396649381)
                ·
                  refine ⟨98058145414231386871759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 522976775542567396649381 98058145414231386871759)
                  ·
                    rfl

theorem cell21_429677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_429677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_429677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_429677 prefixEnd_429677 := by exact prefixLift 429677
  have htrace : WordTrace (prefixWord ++ tailWord_429677) baseStart_429677 baseEnd_429677 := by
    simpa [prefixWord, tailWord_429677, baseEnd_429677] using wordTrace_append hprefix tailTrace_429677
  have hstable : (prefixWord ++ tailWord_429677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429677).length < 2 ^ (prefixWord ++ tailWord_429677).sum := by decide
  have hdescent : baseEnd_429677 < baseStart_429677 := by decide
  rcases family_descends (prefixWord ++ tailWord_429677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429719 : List Nat := [1, 1, 3, 3, 2, 3, 2, 2, 4]
def baseStart_429719 : Nat := 118140960795 + 429719 * 2 ^ 59
def prefixEnd_429719 : Nat := 4983230072969 + 3 ^ 40 * 429719 * 2
def baseEnd_429719 : Nat := 98067730386448647171673

theorem tailTrace_429719 : CollatzResearch.WordTrace tailWord_429719 prefixEnd_429719 98067730386448647171673 := by
  unfold tailWord_429719
  simp only [CollatzResearch.WordTrace]
  refine ⟨15673139530208928007420211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10448759686805952004946807 15673139530208928007420211)
  ·
    refine ⟨23509709295313392011130317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15673139530208928007420211 23509709295313392011130317)
    ·
      refine ⟨8816140985742522004173869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23509709295313392011130317 8816140985742522004173869)
      ·
        refine ⟨3306052869653445751565201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8816140985742522004173869 3306052869653445751565201)
        ·
          refine ⟨2479539652240084313673901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3306052869653445751565201 2479539652240084313673901)
          ·
            refine ⟨929827369590031617627713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2479539652240084313673901 929827369590031617627713)
            ·
              refine ⟨697370527192523713220785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 929827369590031617627713 697370527192523713220785)
              ·
                refine ⟨523027895394392784915589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697370527192523713220785 523027895394392784915589)
                ·
                  refine ⟨98067730386448647171673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 523027895394392784915589 98067730386448647171673)
                  ·
                    rfl

theorem cell21_429719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 4].length) (baseStart_429719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_429719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_429719 prefixEnd_429719 := by exact prefixLift 429719
  have htrace : WordTrace (prefixWord ++ tailWord_429719) baseStart_429719 baseEnd_429719 := by
    simpa [prefixWord, tailWord_429719, baseEnd_429719] using wordTrace_append hprefix tailTrace_429719
  have hstable : (prefixWord ++ tailWord_429719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429719).length < 2 ^ (prefixWord ++ tailWord_429719).sum := by decide
  have hdescent : baseEnd_429719 < baseStart_429719 := by decide
  rcases family_descends (prefixWord ++ tailWord_429719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429747 : List Nat := [1, 1, 1, 2, 3, 3, 3, 2, 5]
def baseStart_429747 : Nat := 118140960795 + 429747 * 2 ^ 59
def prefixEnd_429747 : Nat := 4983230072969 + 3 ^ 40 * 429747 * 2
def baseEnd_429747 : Nat := 98074120367926820704949

theorem tailTrace_429747 : CollatzResearch.WordTrace tailWord_429747 prefixEnd_429747 98074120367926820704949 := by
  unfold tailWord_429747
  simp only [CollatzResearch.WordTrace]
  refine ⟨15674160774107488789439495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10449440516071659192959663 15674160774107488789439495)
  ·
    refine ⟨23511241161161233184159243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15674160774107488789439495 23511241161161233184159243)
    ·
      refine ⟨35266861741741849776238865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23511241161161233184159243 35266861741741849776238865)
      ·
        refine ⟨26450146306306387332179149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35266861741741849776238865 26450146306306387332179149)
        ·
          refine ⟨9918804864864895249567181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26450146306306387332179149 9918804864864895249567181)
          ·
            refine ⟨3719551824324335718587693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9918804864864895249567181 3719551824324335718587693)
            ·
              refine ⟨1394831934121625894470385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3719551824324335718587693 1394831934121625894470385)
              ·
                refine ⟨1046123950591219420852789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1394831934121625894470385 1046123950591219420852789)
                ·
                  refine ⟨98074120367926820704949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1046123950591219420852789 98074120367926820704949)
                  ·
                    rfl

theorem cell21_429747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 5].length) (baseStart_429747 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_429747 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_429747 prefixEnd_429747 := by exact prefixLift 429747
  have htrace : WordTrace (prefixWord ++ tailWord_429747) baseStart_429747 baseEnd_429747 := by
    simpa [prefixWord, tailWord_429747, baseEnd_429747] using wordTrace_append hprefix tailTrace_429747
  have hstable : (prefixWord ++ tailWord_429747).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429747).length < 2 ^ (prefixWord ++ tailWord_429747).sum := by decide
  have hdescent : baseEnd_429747 < baseStart_429747 := by decide
  rcases family_descends (prefixWord ++ tailWord_429747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429809 : List Nat := [1, 2, 2, 2, 2, 3, 4, 5]
def baseStart_429809 : Nat := 118140960795 + 429809 * 2 ^ 59
def prefixEnd_429809 : Nat := 4983230072969 + 3 ^ 40 * 429809 * 2
def baseEnd_429809 : Nat := 32696089870876163557163

theorem tailTrace_429809 : CollatzResearch.WordTrace tailWord_429809 prefixEnd_429809 32696089870876163557163 := by
  unfold tailWord_429809
  simp only [CollatzResearch.WordTrace]
  refine ⟨15676422099882873378196481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10450948066588582252130987 15676422099882873378196481)
  ·
    refine ⟨11757316574912155033647361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15676422099882873378196481 11757316574912155033647361)
    ·
      refine ⟨8817987431184116275235521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11757316574912155033647361 8817987431184116275235521)
      ·
        refine ⟨6613490573388087206426641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8817987431184116275235521 6613490573388087206426641)
        ·
          refine ⟨4960117930041065404819981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6613490573388087206426641 4960117930041065404819981)
          ·
            refine ⟨1860044223765399526807493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4960117930041065404819981 1860044223765399526807493)
            ·
              refine ⟨348758291956012411276405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1860044223765399526807493 348758291956012411276405)
              ·
                refine ⟨32696089870876163557163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 348758291956012411276405 32696089870876163557163)
                ·
                  rfl

theorem cell21_429809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 5].length) (baseStart_429809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_429809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_429809 prefixEnd_429809 := by exact prefixLift 429809
  have htrace : WordTrace (prefixWord ++ tailWord_429809) baseStart_429809 baseEnd_429809 := by
    simpa [prefixWord, tailWord_429809, baseEnd_429809] using wordTrace_append hprefix tailTrace_429809
  have hstable : (prefixWord ++ tailWord_429809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429809).length < 2 ^ (prefixWord ++ tailWord_429809).sum := by decide
  have hdescent : baseEnd_429809 < baseStart_429809 := by decide
  rcases family_descends (prefixWord ++ tailWord_429809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429812 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 6]
def baseStart_429812 : Nat := 118140960795 + 429812 * 2 ^ 59
def prefixEnd_429812 : Nat := 4983230072969 + 3 ^ 40 * 429812 * 2
def baseEnd_429812 : Nat := 98088954253501152121483

theorem tailTrace_429812 : CollatzResearch.WordTrace tailWord_429812 prefixEnd_429812 98088954253501152121483 := by
  unfold tailWord_429812
  simp only [CollatzResearch.WordTrace]
  refine ⟨7838265759436002445277845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10451021012581336593703793 7838265759436002445277845)
  ·
    refine ⟨367418707473562614622399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7838265759436002445277845 367418707473562614622399)
    ·
      refine ⟨551128061210343921933599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367418707473562614622399 551128061210343921933599)
      ·
        refine ⟨826692091815515882900399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551128061210343921933599 826692091815515882900399)
        ·
          refine ⟨1240038137723273824350599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826692091815515882900399 1240038137723273824350599)
          ·
            refine ⟨1860057206584910736525899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240038137723273824350599 1860057206584910736525899)
            ·
              refine ⟨2790085809877366104788849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1860057206584910736525899 2790085809877366104788849)
              ·
                refine ⟨2092564357408024578591637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2790085809877366104788849 2092564357408024578591637)
                ·
                  refine ⟨98088954253501152121483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2092564357408024578591637 98088954253501152121483)
                  ·
                    rfl

theorem cell21_429812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_429812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_429812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_429812 prefixEnd_429812 := by exact prefixLift 429812
  have htrace : WordTrace (prefixWord ++ tailWord_429812) baseStart_429812 baseEnd_429812 := by
    simpa [prefixWord, tailWord_429812, baseEnd_429812] using wordTrace_append hprefix tailTrace_429812
  have hstable : (prefixWord ++ tailWord_429812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429812).length < 2 ^ (prefixWord ++ tailWord_429812).sum := by decide
  have hdescent : baseEnd_429812 < baseStart_429812 := by decide
  rcases family_descends (prefixWord ++ tailWord_429812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429868 : List Nat := [2, 2, 1, 1, 1, 5, 2, 7]
def baseStart_429868 : Nat := 118140960795 + 429868 * 2 ^ 59
def prefixEnd_429868 : Nat := 4983230072969 + 3 ^ 40 * 429868 * 2
def baseEnd_429868 : Nat := 32700578072152499729345

theorem tailTrace_429868 : CollatzResearch.WordTrace tailWord_429868 prefixEnd_429868 32700578072152499729345 := by
  unfold tailWord_429868
  simp only [CollatzResearch.WordTrace]
  refine ⟨7839287003334563227297129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10452382671112750969729505 7839287003334563227297129)
  ·
    refine ⟨5879465252500922420472847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7839287003334563227297129 5879465252500922420472847)
    ·
      refine ⟨8819197878751383630709271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5879465252500922420472847 8819197878751383630709271)
      ·
        refine ⟨13228796818127075446063907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8819197878751383630709271 13228796818127075446063907)
        ·
          refine ⟨19843195227190613169095861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13228796818127075446063907 19843195227190613169095861)
          ·
            refine ⟨1860299552549119984602737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19843195227190613169095861 1860299552549119984602737)
            ·
              refine ⟨1395224664411839988452053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1860299552549119984602737 1395224664411839988452053)
              ·
                refine ⟨32700578072152499729345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1395224664411839988452053 32700578072152499729345)
                ·
                  rfl

theorem cell21_429868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 7].length) (baseStart_429868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_429868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_429868 prefixEnd_429868 := by exact prefixLift 429868
  have htrace : WordTrace (prefixWord ++ tailWord_429868) baseStart_429868 baseEnd_429868 := by
    simpa [prefixWord, tailWord_429868, baseEnd_429868] using wordTrace_append hprefix tailTrace_429868
  have hstable : (prefixWord ++ tailWord_429868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429868).length < 2 ^ (prefixWord ++ tailWord_429868).sum := by decide
  have hdescent : baseEnd_429868 < baseStart_429868 := by decide
  rcases family_descends (prefixWord ++ tailWord_429868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429950 : List Nat := [4, 2, 3, 1, 1, 1, 2, 4, 3]
def baseStart_429950 : Nat := 118140960795 + 429950 * 2 ^ 59
def prefixEnd_429950 : Nat := 4983230072969 + 3 ^ 40 * 429950 * 2
def baseEnd_429950 : Nat := 98120447733643578821201

theorem tailTrace_429950 : CollatzResearch.WordTrace tailWord_429950 prefixEnd_429950 98120447733643578821201 := by
  unfold tailWord_429950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1960195599046506807384913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10454376528248036306052869 1960195599046506807384913)
  ·
    refine ⟨1470146699284880105538685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1960195599046506807384913 1470146699284880105538685)
    ·
      refine ⟨551305012231830039577007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1470146699284880105538685 551305012231830039577007)
      ·
        refine ⟨826957518347745059365511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551305012231830039577007 826957518347745059365511)
        ·
          refine ⟨1240436277521617589048267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826957518347745059365511 1240436277521617589048267)
          ·
            refine ⟨1860654416282426383572401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240436277521617589048267 1860654416282426383572401)
            ·
              refine ⟨1395490812211819787679301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1860654416282426383572401 1395490812211819787679301)
              ·
                refine ⟨261654527289716210189869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1395490812211819787679301 261654527289716210189869)
                ·
                  refine ⟨98120447733643578821201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261654527289716210189869 98120447733643578821201)
                  ·
                    rfl

theorem cell21_429950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_429950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_429950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_429950 prefixEnd_429950 := by exact prefixLift 429950
  have htrace : WordTrace (prefixWord ++ tailWord_429950) baseStart_429950 baseEnd_429950 := by
    simpa [prefixWord, tailWord_429950, baseEnd_429950] using wordTrace_append hprefix tailTrace_429950
  have hstable : (prefixWord ++ tailWord_429950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429950).length < 2 ^ (prefixWord ++ tailWord_429950).sum := by decide
  have hdescent : baseEnd_429950 < baseStart_429950 := by decide
  rcases family_descends (prefixWord ++ tailWord_429950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429975 : List Nat := [1, 1, 3, 3, 1, 3, 2, 2, 5]
def baseStart_429975 : Nat := 118140960795 + 429975 * 2 ^ 59
def prefixEnd_429975 : Nat := 4983230072969 + 3 ^ 40 * 429975 * 2
def baseEnd_429975 : Nat := 98126153074249090904483

theorem tailTrace_429975 : CollatzResearch.WordTrace tailWord_429975 prefixEnd_429975 98126153074249090904483 := by
  unfold tailWord_429975
  simp only [CollatzResearch.WordTrace]
  refine ⟨15682476617281483728739379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10454984411520989152492919 15682476617281483728739379)
  ·
    refine ⟨23523714925922225593109069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15682476617281483728739379 23523714925922225593109069)
    ·
      refine ⟨8821393097220834597415901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23523714925922225593109069 8821393097220834597415901)
      ·
        refine ⟨3308022411457812974030963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8821393097220834597415901 3308022411457812974030963)
        ·
          refine ⟨4962033617186719461046445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3308022411457812974030963 4962033617186719461046445)
          ·
            refine ⟨1860762606445019797892417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4962033617186719461046445 1860762606445019797892417)
            ·
              refine ⟨1395571954833764848419313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1860762606445019797892417 1395571954833764848419313)
              ·
                refine ⟨1046678966125323636314485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1395571954833764848419313 1046678966125323636314485)
                ·
                  refine ⟨98126153074249090904483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1046678966125323636314485 98126153074249090904483)
                  ·
                    rfl

theorem cell21_429975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 5].length) (baseStart_429975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_429975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_429975 prefixEnd_429975 := by exact prefixLift 429975
  have htrace : WordTrace (prefixWord ++ tailWord_429975) baseStart_429975 baseEnd_429975 := by
    simpa [prefixWord, tailWord_429975, baseEnd_429975] using wordTrace_append hprefix tailTrace_429975
  have hstable : (prefixWord ++ tailWord_429975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429975).length < 2 ^ (prefixWord ++ tailWord_429975).sum := by decide
  have hdescent : baseEnd_429975 < baseStart_429975 := by decide
  rcases family_descends (prefixWord ++ tailWord_429975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429978 : List Nat := [3, 1, 1, 4, 2, 3, 2, 5]
def baseStart_429978 : Nat := 118140960795 + 429978 * 2 ^ 59
def prefixEnd_429978 : Nat := 4983230072969 + 3 ^ 40 * 429978 * 2
def baseEnd_429978 : Nat := 32708945905040584118159

theorem tailTrace_429978 : CollatzResearch.WordTrace tailWord_429978 prefixEnd_429978 32708945905040584118159 := by
  unfold tailWord_429978
  simp only [CollatzResearch.WordTrace]
  refine ⟨3920646509067653810274647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10455057357513743494065725 3920646509067653810274647)
  ·
    refine ⟨5880969763601480715411971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3920646509067653810274647 5880969763601480715411971)
    ·
      refine ⟨8821454645402221073117957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5880969763601480715411971 8821454645402221073117957)
      ·
        refine ⟨1654022746012916451209617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8821454645402221073117957 1654022746012916451209617)
        ·
          refine ⟨1240517059509687338407213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1654022746012916451209617 1240517059509687338407213)
          ·
            refine ⟨465193897316132751902705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1240517059509687338407213 465193897316132751902705)
            ·
              refine ⟨348895422987099563927029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465193897316132751902705 348895422987099563927029)
              ·
                refine ⟨32708945905040584118159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 348895422987099563927029 32708945905040584118159)
                ·
                  rfl

theorem cell21_429978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_429978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_429978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_429978 prefixEnd_429978 := by exact prefixLift 429978
  have htrace : WordTrace (prefixWord ++ tailWord_429978) baseStart_429978 baseEnd_429978 := by
    simpa [prefixWord, tailWord_429978, baseEnd_429978] using wordTrace_append hprefix tailTrace_429978
  have hstable : (prefixWord ++ tailWord_429978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429978).length < 2 ^ (prefixWord ++ tailWord_429978).sum := by decide
  have hdescent : baseEnd_429978 < baseStart_429978 := by decide
  rcases family_descends (prefixWord ++ tailWord_429978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430009 : List Nat := [1, 2, 1, 4, 2, 1, 5, 2, 3]
def baseStart_430009 : Nat := 118140960795 + 430009 * 2 ^ 59
def prefixEnd_430009 : Nat := 4983230072969 + 3 ^ 40 * 430009 * 2
def baseEnd_430009 : Nat := 98133912337472587337747

theorem tailTrace_430009 : CollatzResearch.WordTrace tailWord_430009 prefixEnd_430009 98133912337472587337747 := by
  unfold tailWord_430009
  simp only [CollatzResearch.WordTrace]
  refine ⟨15683716699158307535477081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10455811132772205023651387 15683716699158307535477081)
  ·
    refine ⟨11762787524368730651607811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15683716699158307535477081 11762787524368730651607811)
    ·
      refine ⟨17644181286553095977411717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11762787524368730651607811 17644181286553095977411717)
      ·
        refine ⟨3308283991228705495764697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17644181286553095977411717 3308283991228705495764697)
        ·
          refine ⟨2481212993421529121823523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3308283991228705495764697 2481212993421529121823523)
          ·
            refine ⟨3721819490132293682735285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2481212993421529121823523 3721819490132293682735285)
            ·
              refine ⟨348920577199902532756433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3721819490132293682735285 348920577199902532756433)
              ·
                refine ⟨261690432899926899567325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348920577199902532756433 261690432899926899567325)
                ·
                  refine ⟨98133912337472587337747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261690432899926899567325 98133912337472587337747)
                  ·
                    rfl

theorem cell21_430009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 3].length) (baseStart_430009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430009 prefixEnd_430009 := by exact prefixLift 430009
  have htrace : WordTrace (prefixWord ++ tailWord_430009) baseStart_430009 baseEnd_430009 := by
    simpa [prefixWord, tailWord_430009, baseEnd_430009] using wordTrace_append hprefix tailTrace_430009
  have hstable : (prefixWord ++ tailWord_430009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430009).length < 2 ^ (prefixWord ++ tailWord_430009).sum := by decide
  have hdescent : baseEnd_430009 < baseStart_430009 := by decide
  rcases family_descends (prefixWord ++ tailWord_430009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430116 : List Nat := [2, 3, 1, 4, 2, 2, 1, 2, 4]
def baseStart_430116 : Nat := 118140960795 + 430116 * 2 ^ 59
def prefixEnd_430116 : Nat := 4983230072969 + 3 ^ 40 * 430116 * 2
def baseEnd_430116 : Nat := 98158331195264179054195

theorem tailTrace_430116 : CollatzResearch.WordTrace tailWord_430116 prefixEnd_430116 98158331195264179054195 := by
  unfold tailWord_430116
  simp only [CollatzResearch.WordTrace]
  refine ⟨7843809654885332404811101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10458412873180443206414801 7843809654885332404811101)
  ·
    refine ⟨2941428620581999651804163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7843809654885332404811101 2941428620581999651804163)
    ·
      refine ⟨4412142930872999477706245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2941428620581999651804163 4412142930872999477706245)
      ·
        refine ⟨827276799538687402069921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4412142930872999477706245 827276799538687402069921)
        ·
          refine ⟨620457599654015551552441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 827276799538687402069921 620457599654015551552441)
          ·
            refine ⟨465343199740511663664331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620457599654015551552441 465343199740511663664331)
            ·
              refine ⟨698014799610767495496497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465343199740511663664331 698014799610767495496497)
              ·
                refine ⟨523511099708075621622373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698014799610767495496497 523511099708075621622373)
                ·
                  refine ⟨98158331195264179054195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 523511099708075621622373 98158331195264179054195)
                  ·
                    rfl

theorem cell21_430116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_430116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430116 prefixEnd_430116 := by exact prefixLift 430116
  have htrace : WordTrace (prefixWord ++ tailWord_430116) baseStart_430116 baseEnd_430116 := by
    simpa [prefixWord, tailWord_430116, baseEnd_430116] using wordTrace_append hprefix tailTrace_430116
  have hstable : (prefixWord ++ tailWord_430116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430116).length < 2 ^ (prefixWord ++ tailWord_430116).sum := by decide
  have hdescent : baseEnd_430116 < baseStart_430116 := by decide
  rcases family_descends (prefixWord ++ tailWord_430116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430155 : List Nat := [1, 1, 1, 1, 3, 1, 2, 11]
def baseStart_430155 : Nat := 118140960795 + 430155 * 2 ^ 59
def prefixEnd_430155 : Nat := 4983230072969 + 3 ^ 40 * 430155 * 2
def baseEnd_430155 : Nat := 32722410508869592634705

theorem tailTrace_430155 : CollatzResearch.WordTrace tailWord_430155 prefixEnd_430155 32722410508869592634705 := by
  unfold tailWord_430155
  simp only [CollatzResearch.WordTrace]
  refine ⟨15689041756629374470291919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10459361171086249646861279 15689041756629374470291919)
  ·
    refine ⟨23533562634944061705437879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15689041756629374470291919 23533562634944061705437879)
    ·
      refine ⟨35300343952416092558156819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23533562634944061705437879 35300343952416092558156819)
      ·
        refine ⟨52950515928624138837235229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35300343952416092558156819 52950515928624138837235229)
        ·
          refine ⟨19856443473234052063963211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52950515928624138837235229 19856443473234052063963211)
          ·
            refine ⟨29784665209851078095944817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19856443473234052063963211 29784665209851078095944817)
            ·
              refine ⟨22338498907388308571958613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29784665209851078095944817 22338498907388308571958613)
              ·
                refine ⟨32722410508869592634705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 22338498907388308571958613 32722410508869592634705)
                ·
                  rfl

theorem cell21_430155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 11].length) (baseStart_430155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430155 prefixEnd_430155 := by exact prefixLift 430155
  have htrace : WordTrace (prefixWord ++ tailWord_430155) baseStart_430155 baseEnd_430155 := by
    simpa [prefixWord, tailWord_430155, baseEnd_430155] using wordTrace_append hprefix tailTrace_430155
  have hstable : (prefixWord ++ tailWord_430155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430155).length < 2 ^ (prefixWord ++ tailWord_430155).sum := by decide
  have hdescent : baseEnd_430155 < baseStart_430155 := by decide
  rcases family_descends (prefixWord ++ tailWord_430155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430172 : List Nat := [2, 2, 4, 1, 1, 2, 9]
def baseStart_430172 : Nat := 118140960795 + 430172 * 2 ^ 59
def prefixEnd_430172 : Nat := 4983230072969 + 3 ^ 40 * 430172 * 2
def baseEnd_430172 : Nat := 10907901239802280680083

theorem tailTrace_430172 : CollatzResearch.WordTrace tailWord_430172 prefixEnd_430172 10907901239802280680083 := by
  unfold tailWord_430172
  simp only [CollatzResearch.WordTrace]
  refine ⟨7844830898783893186830385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10459774531711857582440513 7844830898783893186830385)
  ·
    refine ⟨5883623174087919890122789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7844830898783893186830385 5883623174087919890122789)
    ·
      refine ⟨1103179345141484979398023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5883623174087919890122789 1103179345141484979398023)
      ·
        refine ⟨1654769017712227469097035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1103179345141484979398023 1654769017712227469097035)
        ·
          refine ⟨2482153526568341203645553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1654769017712227469097035 2482153526568341203645553)
          ·
            refine ⟨1861615144926255902734165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2482153526568341203645553 1861615144926255902734165)
            ·
              refine ⟨10907901239802280680083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1861615144926255902734165 10907901239802280680083)
              ·
                rfl

theorem cell21_430172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 9].length) (baseStart_430172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430172 prefixEnd_430172 := by exact prefixLift 430172
  have htrace : WordTrace (prefixWord ++ tailWord_430172) baseStart_430172 baseEnd_430172 := by
    simpa [prefixWord, tailWord_430172, baseEnd_430172] using wordTrace_append hprefix tailTrace_430172
  have hstable : (prefixWord ++ tailWord_430172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430172).length < 2 ^ (prefixWord ++ tailWord_430172).sum := by decide
  have hdescent : baseEnd_430172 < baseStart_430172 := by decide
  rcases family_descends (prefixWord ++ tailWord_430172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430178 : List Nat := [3, 3, 2, 2, 3, 1, 1, 1, 5]
def baseStart_430178 : Nat := 118140960795 + 430178 * 2 ^ 59
def prefixEnd_430178 : Nat := 4983230072969 + 3 ^ 40 * 430178 * 2
def baseEnd_430178 : Nat := 98172480439965849020735

theorem tailTrace_430178 : CollatzResearch.WordTrace tailWord_430178 prefixEnd_430178 98172480439965849020735 := by
  unfold tailWord_430178
  simp only [CollatzResearch.WordTrace]
  refine ⟨3922470158886512349594797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10459920423697366265586125 3922470158886512349594797)
  ·
    refine ⟨1470926309582442131098049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3922470158886512349594797 1470926309582442131098049)
    ·
      refine ⟨1103194732186831598323537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1470926309582442131098049 1103194732186831598323537)
      ·
        refine ⟨827396049140123698742653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1103194732186831598323537 827396049140123698742653)
        ·
          refine ⟨310273518427546387028495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 827396049140123698742653 310273518427546387028495)
          ·
            refine ⟨465410277641319580542743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310273518427546387028495 465410277641319580542743)
            ·
              refine ⟨698115416461979370814115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465410277641319580542743 698115416461979370814115)
              ·
                refine ⟨1047173124692969056221173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698115416461979370814115 1047173124692969056221173)
                ·
                  refine ⟨98172480439965849020735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1047173124692969056221173 98172480439965849020735)
                  ·
                    rfl

theorem cell21_430178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_430178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430178 prefixEnd_430178 := by exact prefixLift 430178
  have htrace : WordTrace (prefixWord ++ tailWord_430178) baseStart_430178 baseEnd_430178 := by
    simpa [prefixWord, tailWord_430178, baseEnd_430178] using wordTrace_append hprefix tailTrace_430178
  have hstable : (prefixWord ++ tailWord_430178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430178).length < 2 ^ (prefixWord ++ tailWord_430178).sum := by decide
  have hdescent : baseEnd_430178 < baseStart_430178 := by decide
  rcases family_descends (prefixWord ++ tailWord_430178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430231 : List Nat := [1, 1, 3, 3, 13]
def baseStart_430231 : Nat := 118140960795 + 430231 * 2 ^ 59
def prefixEnd_430231 : Nat := 4983230072969 + 3 ^ 40 * 430231 * 2
def baseEnd_430231 : Nat := 1212155256321599193053

theorem tailTrace_430231 : CollatzResearch.WordTrace tailWord_430231 prefixEnd_430231 1212155256321599193053 := by
  unfold tailWord_430231
  simp only [CollatzResearch.WordTrace]
  refine ⟨15691813704354039450058547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10461209136236026300039031 15691813704354039450058547)
  ·
    refine ⟨23537720556531059175087821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15691813704354039450058547 23537720556531059175087821)
    ·
      refine ⟨8826645208699147190657933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23537720556531059175087821 8826645208699147190657933)
      ·
        refine ⟨3309991953262180196496725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8826645208699147190657933 3309991953262180196496725)
        ·
          refine ⟨1212155256321599193053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 3309991953262180196496725 1212155256321599193053)
          ·
            rfl

theorem cell21_430231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 13].length) (baseStart_430231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430231 prefixEnd_430231 := by exact prefixLift 430231
  have htrace : WordTrace (prefixWord ++ tailWord_430231) baseStart_430231 baseEnd_430231 := by
    simpa [prefixWord, tailWord_430231, baseEnd_430231] using wordTrace_append hprefix tailTrace_430231
  have hstable : (prefixWord ++ tailWord_430231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430231).length < 2 ^ (prefixWord ++ tailWord_430231).sum := by decide
  have hdescent : baseEnd_430231 < baseStart_430231 := by decide
  rcases family_descends (prefixWord ++ tailWord_430231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430237 : List Nat := [1, 4, 2, 1, 1, 3, 4, 2, 3]
def baseStart_430237 : Nat := 118140960795 + 430237 * 2 ^ 59
def prefixEnd_430237 : Nat := 4983230072969 + 3 ^ 40 * 430237 * 2
def baseEnd_430237 : Nat := 98185945043794857537281

theorem tailTrace_430237 : CollatzResearch.WordTrace tailWord_430237 prefixEnd_430237 98185945043794857537281 := by
  unfold tailWord_430237
  simp only [CollatzResearch.WordTrace]
  refine ⟨15692032542332302474776965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10461355028221534983184643 15692032542332302474776965)
  ·
    refine ⟨2942256101687306714020681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15692032542332302474776965 2942256101687306714020681)
    ·
      refine ⟨2206692076265480035515511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2942256101687306714020681 2206692076265480035515511)
      ·
        refine ⟨3310038114398220053273267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2206692076265480035515511 3310038114398220053273267)
        ·
          refine ⟨4965057171597330079909901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3310038114398220053273267 4965057171597330079909901)
          ·
            refine ⟨1861896439348998779966213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4965057171597330079909901 1861896439348998779966213)
            ·
              refine ⟨349105582377937271243665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1861896439348998779966213 349105582377937271243665)
              ·
                refine ⟨261829186783452953432749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349105582377937271243665 261829186783452953432749)
                ·
                  refine ⟨98185945043794857537281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261829186783452953432749 98185945043794857537281)
                  ·
                    rfl

theorem cell21_430237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_430237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430237 prefixEnd_430237 := by exact prefixLift 430237
  have htrace : WordTrace (prefixWord ++ tailWord_430237) baseStart_430237 baseEnd_430237 := by
    simpa [prefixWord, tailWord_430237, baseEnd_430237] using wordTrace_append hprefix tailTrace_430237
  have hstable : (prefixWord ++ tailWord_430237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430237).length < 2 ^ (prefixWord ++ tailWord_430237).sum := by decide
  have hdescent : baseEnd_430237 < baseStart_430237 := by decide
  rcases family_descends (prefixWord ++ tailWord_430237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430296 : List Nat := [2, 1, 2, 2, 4, 1, 2, 4, 3]
def baseStart_430296 : Nat := 118140960795 + 430296 * 2 ^ 59
def prefixEnd_430296 : Nat := 4983230072969 + 3 ^ 40 * 430296 * 2
def baseEnd_430296 : Nat := 98199409647623866053827

theorem tailTrace_430296 : CollatzResearch.WordTrace tailWord_430296 prefixEnd_430296 98199409647623866053827 := by
  unfold tailWord_430296
  simp only [CollatzResearch.WordTrace]
  refine ⟨7847092224559277775587371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10462789632745703700783161 7847092224559277775587371)
  ·
    refine ⟨11770638336838916663381057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7847092224559277775587371 11770638336838916663381057)
    ·
      refine ⟨8827978752629187497535793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11770638336838916663381057 8827978752629187497535793)
      ·
        refine ⟨6620984064471890623151845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8827978752629187497535793 6620984064471890623151845)
        ·
          refine ⟨1241434512088479491840971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6620984064471890623151845 1241434512088479491840971)
          ·
            refine ⟨1862151768132719237761457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241434512088479491840971 1862151768132719237761457)
            ·
              refine ⟨1396613826099539428321093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1862151768132719237761457 1396613826099539428321093)
              ·
                refine ⟨261865092393663642810205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1396613826099539428321093 261865092393663642810205)
                ·
                  refine ⟨98199409647623866053827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261865092393663642810205 98199409647623866053827)
                  ·
                    rfl

theorem cell21_430296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 3].length) (baseStart_430296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430296 prefixEnd_430296 := by exact prefixLift 430296
  have htrace : WordTrace (prefixWord ++ tailWord_430296) baseStart_430296 baseEnd_430296 := by
    simpa [prefixWord, tailWord_430296, baseEnd_430296] using wordTrace_append hprefix tailTrace_430296
  have hstable : (prefixWord ++ tailWord_430296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430296).length < 2 ^ (prefixWord ++ tailWord_430296).sum := by decide
  have hdescent : baseEnd_430296 < baseStart_430296 := by decide
  rcases family_descends (prefixWord ++ tailWord_430296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430355 : List Nat := [1, 1, 1, 2, 1, 3, 1, 8, 3]
def baseStart_430355 : Nat := 118140960795 + 430355 * 2 ^ 59
def prefixEnd_430355 : Nat := 4983230072969 + 3 ^ 40 * 430355 * 2
def baseEnd_430355 : Nat := 98212874251452874570373

theorem tailTrace_430355 : CollatzResearch.WordTrace tailWord_430355 prefixEnd_430355 98212874251452874570373 := by
  unfold tailWord_430355
  simp only [CollatzResearch.WordTrace]
  refine ⟨15696336355904808627572519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10464224237269872418381679 15696336355904808627572519)
  ·
    refine ⟨23544504533857212941358779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15696336355904808627572519 23544504533857212941358779)
    ·
      refine ⟨35316756800785819412038169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23544504533857212941358779 35316756800785819412038169)
      ·
        refine ⟨26487567600589364559028627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35316756800785819412038169 26487567600589364559028627)
        ·
          refine ⟨39731351400884046838542941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26487567600589364559028627 39731351400884046838542941)
          ·
            refine ⟨14899256775331517564453603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39731351400884046838542941 14899256775331517564453603)
            ·
              refine ⟨22348885162997276346680405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14899256775331517564453603 22348885162997276346680405)
              ·
                refine ⟨261900998003874332187661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 22348885162997276346680405 261900998003874332187661)
                ·
                  refine ⟨98212874251452874570373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261900998003874332187661 98212874251452874570373)
                  ·
                    rfl

theorem cell21_430355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 3].length) (baseStart_430355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430355 prefixEnd_430355 := by exact prefixLift 430355
  have htrace : WordTrace (prefixWord ++ tailWord_430355) baseStart_430355 baseEnd_430355 := by
    simpa [prefixWord, tailWord_430355, baseEnd_430355] using wordTrace_append hprefix tailTrace_430355
  have hstable : (prefixWord ++ tailWord_430355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430355).length < 2 ^ (prefixWord ++ tailWord_430355).sum := by decide
  have hdescent : baseEnd_430355 < baseStart_430355 := by decide
  rcases family_descends (prefixWord ++ tailWord_430355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430383 : List Nat := [1, 1, 2, 1, 2, 1, 6, 7]
def baseStart_430383 : Nat := 118140960795 + 430383 * 2 ^ 59
def prefixEnd_430383 : Nat := 4983230072969 + 3 ^ 40 * 430383 * 2
def baseEnd_430383 : Nat := 32739754744310349367883

theorem tailTrace_430383 : CollatzResearch.WordTrace tailWord_430383 prefixEnd_430383 32739754744310349367883 := by
  unfold tailWord_430383
  simp only [CollatzResearch.WordTrace]
  refine ⟨15697357599803369409591803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10464905066535579606394535 15697357599803369409591803)
  ·
    refine ⟨23546036399705054114387705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15697357599803369409591803 23546036399705054114387705)
    ·
      refine ⟨17659527299778790585790779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23546036399705054114387705 17659527299778790585790779)
      ·
        refine ⟨26489290949668185878686169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17659527299778790585790779 26489290949668185878686169)
        ·
          refine ⟨19866968212251139409014627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26489290949668185878686169 19866968212251139409014627)
          ·
            refine ⟨29800452318376709113521941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19866968212251139409014627 29800452318376709113521941)
            ·
              refine ⟨1396896202423908239696341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29800452318376709113521941 1396896202423908239696341)
              ·
                refine ⟨32739754744310349367883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1396896202423908239696341 32739754744310349367883)
                ·
                  rfl

theorem cell21_430383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 7].length) (baseStart_430383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430383 prefixEnd_430383 := by exact prefixLift 430383
  have htrace : WordTrace (prefixWord ++ tailWord_430383) baseStart_430383 baseEnd_430383 := by
    simpa [prefixWord, tailWord_430383, baseEnd_430383] using wordTrace_append hprefix tailTrace_430383
  have hstable : (prefixWord ++ tailWord_430383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430383).length < 2 ^ (prefixWord ++ tailWord_430383).sum := by decide
  have hdescent : baseEnd_430383 < baseStart_430383 := by decide
  rcases family_descends (prefixWord ++ tailWord_430383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430445 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 6]
def baseStart_430445 : Nat := 118140960795 + 430445 * 2 ^ 59
def prefixEnd_430445 : Nat := 4983230072969 + 3 ^ 40 * 430445 * 2
def baseEnd_430445 : Nat := 98233413477632718070189

theorem tailTrace_430445 : CollatzResearch.WordTrace tailWord_430445 prefixEnd_430445 98233413477632718070189 := by
  unfold tailWord_430445
  simp only [CollatzResearch.WordTrace]
  refine ⟨15699618925578753998348789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10466412617052502665565859 15699618925578753998348789)
  ·
    refine ⟨1471839274273008187345199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15699618925578753998348789 1471839274273008187345199)
    ·
      refine ⟨2207758911409512281017799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1471839274273008187345199 2207758911409512281017799)
      ·
        refine ⟨3311638367114268421526699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2207758911409512281017799 3311638367114268421526699)
        ·
          refine ⟨4967457550671402632290049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3311638367114268421526699 4967457550671402632290049)
          ·
            refine ⟨3725593163003551974217537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4967457550671402632290049 3725593163003551974217537)
            ·
              refine ⟨2794194872252663980663153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3725593163003551974217537 2794194872252663980663153)
              ·
                refine ⟨2095646154189497985497365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2794194872252663980663153 2095646154189497985497365)
                ·
                  refine ⟨98233413477632718070189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2095646154189497985497365 98233413477632718070189)
                  ·
                    rfl

theorem cell21_430445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_430445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430445 prefixEnd_430445 := by exact prefixLift 430445
  have htrace : WordTrace (prefixWord ++ tailWord_430445) baseStart_430445 baseEnd_430445 := by
    simpa [prefixWord, tailWord_430445, baseEnd_430445] using wordTrace_append hprefix tailTrace_430445
  have hstable : (prefixWord ++ tailWord_430445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430445).length < 2 ^ (prefixWord ++ tailWord_430445).sum := by decide
  have hdescent : baseEnd_430445 < baseStart_430445 := by decide
  rcases family_descends (prefixWord ++ tailWord_430445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430448 : List Nat := [2, 1, 1, 1, 4, 4, 2, 3, 3]
def baseStart_430448 : Nat := 118140960795 + 430448 * 2 ^ 59
def prefixEnd_430448 : Nat := 4983230072969 + 3 ^ 40 * 430448 * 2
def baseEnd_430448 : Nat := 98234098118505379520183

theorem tailTrace_430448 : CollatzResearch.WordTrace tailWord_430448 prefixEnd_430448 98234098118505379520183 := by
  unfold tailWord_430448
  simp only [CollatzResearch.WordTrace]
  refine ⟨7849864172283942755353999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10466485563045257007138665 7849864172283942755353999)
  ·
    refine ⟨11774796258425914133030999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7849864172283942755353999 11774796258425914133030999)
    ·
      refine ⟨17662194387638871199546499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11774796258425914133030999 17662194387638871199546499)
      ·
        refine ⟨26493291581458306799319749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17662194387638871199546499 26493291581458306799319749)
        ·
          refine ⟨4967492171523432524872453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26493291581458306799319749 4967492171523432524872453)
          ·
            refine ⟨931404782160643598413585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4967492171523432524872453 931404782160643598413585)
            ·
              refine ⟨698553586620482698810189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 931404782160643598413585 698553586620482698810189)
              ·
                refine ⟨261957594982681012053821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 698553586620482698810189 261957594982681012053821)
                ·
                  refine ⟨98234098118505379520183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261957594982681012053821 98234098118505379520183)
                  ·
                    rfl

theorem cell21_430448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 3].length) (baseStart_430448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430448 prefixEnd_430448 := by exact prefixLift 430448
  have htrace : WordTrace (prefixWord ++ tailWord_430448) baseStart_430448 baseEnd_430448 := by
    simpa [prefixWord, tailWord_430448, baseEnd_430448] using wordTrace_append hprefix tailTrace_430448
  have hstable : (prefixWord ++ tailWord_430448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430448).length < 2 ^ (prefixWord ++ tailWord_430448).sum := by decide
  have hdescent : baseEnd_430448 < baseStart_430448 := by decide
  rcases family_descends (prefixWord ++ tailWord_430448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430459 : List Nat := [1, 1, 1, 1, 1, 8, 8]
def baseStart_430459 : Nat := 118140960795 + 430459 * 2 ^ 59
def prefixEnd_430459 : Nat := 4983230072969 + 3 ^ 40 * 430459 * 2
def baseEnd_430459 : Nat := 10915178718707978315203

theorem tailTrace_430459 : CollatzResearch.WordTrace tailWord_430459 prefixEnd_430459 10915178718707978315203 := by
  unfold tailWord_430459
  simp only [CollatzResearch.WordTrace]
  refine ⟨15700129547528034389358431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10466753031685356259572287 15700129547528034389358431)
  ·
    refine ⟨23550194321292051584037647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15700129547528034389358431 23550194321292051584037647)
    ·
      refine ⟨35325291481938077376056471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23550194321292051584037647 35325291481938077376056471)
      ·
        refine ⟨52987937222907116064084707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35325291481938077376056471 52987937222907116064084707)
        ·
          refine ⟨79481905834360674096127061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52987937222907116064084707 79481905834360674096127061)
          ·
            refine ⟨931428583996414149563989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 79481905834360674096127061 931428583996414149563989)
            ·
              refine ⟨10915178718707978315203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 931428583996414149563989 10915178718707978315203)
              ·
                rfl

theorem cell21_430459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 8].length) (baseStart_430459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430459 prefixEnd_430459 := by exact prefixLift 430459
  have htrace : WordTrace (prefixWord ++ tailWord_430459) baseStart_430459 baseEnd_430459 := by
    simpa [prefixWord, tailWord_430459, baseEnd_430459] using wordTrace_append hprefix tailTrace_430459
  have hstable : (prefixWord ++ tailWord_430459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430459).length < 2 ^ (prefixWord ++ tailWord_430459).sum := by decide
  have hdescent : baseEnd_430459 < baseStart_430459 := by decide
  rcases family_descends (prefixWord ++ tailWord_430459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430521 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 6]
def baseStart_430521 : Nat := 118140960795 + 430521 * 2 ^ 59
def prefixEnd_430521 : Nat := 4983230072969 + 3 ^ 40 * 430521 * 2
def baseEnd_430521 : Nat := 98250757713073474803367

theorem tailTrace_430521 : CollatzResearch.WordTrace tailWord_430521 prefixEnd_430521 98250757713073474803367 := by
  unfold tailWord_430521
  simp only [CollatzResearch.WordTrace]
  refine ⟨15702390873303418978115417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10468260582202279318743611 15702390873303418978115417)
  ·
    refine ⟨11776793154977564233586563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15702390873303418978115417 11776793154977564233586563)
    ·
      refine ⟨17665189732466346350379845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11776793154977564233586563 17665189732466346350379845)
      ·
        refine ⟨3312223074837439940696221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17665189732466346350379845 3312223074837439940696221)
        ·
          refine ⟨1242083653064039977761083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3312223074837439940696221 1242083653064039977761083)
          ·
            refine ⟨1863125479596059966641625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1242083653064039977761083 1863125479596059966641625)
            ·
              refine ⟨1397344109697044974981219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1863125479596059966641625 1397344109697044974981219)
              ·
                refine ⟨2096016164545567462471829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1397344109697044974981219 2096016164545567462471829)
                ·
                  refine ⟨98250757713073474803367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2096016164545567462471829 98250757713073474803367)
                  ·
                    rfl

theorem cell21_430521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_430521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430521 prefixEnd_430521 := by exact prefixLift 430521
  have htrace : WordTrace (prefixWord ++ tailWord_430521) baseStart_430521 baseEnd_430521 := by
    simpa [prefixWord, tailWord_430521, baseEnd_430521] using wordTrace_append hprefix tailTrace_430521
  have hstable : (prefixWord ++ tailWord_430521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430521).length < 2 ^ (prefixWord ++ tailWord_430521).sum := by decide
  have hdescent : baseEnd_430521 < baseStart_430521 := by decide
  rcases family_descends (prefixWord ++ tailWord_430521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430524 : List Nat := [2, 2, 2, 4, 1, 3, 1, 1, 5]
def baseStart_430524 : Nat := 118140960795 + 430524 * 2 ^ 59
def prefixEnd_430524 : Nat := 4983230072969 + 3 ^ 40 * 430524 * 2
def baseEnd_430524 : Nat := 98251442353946136253361

theorem tailTrace_430524 : CollatzResearch.WordTrace tailWord_430524 prefixEnd_430524 98251442353946136253361 := by
  unfold tailWord_430524
  simp only [CollatzResearch.WordTrace]
  refine ⟨7851250146146275245237313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10468333528195033660316417 7851250146146275245237313)
  ·
    refine ⟨5888437609609706433927985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7851250146146275245237313 5888437609609706433927985)
    ·
      refine ⟨4416328207207279825445989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5888437609609706433927985 4416328207207279825445989)
      ·
        refine ⟨828061538851364967271123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4416328207207279825445989 828061538851364967271123)
        ·
          refine ⟨1242092308277047450906685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828061538851364967271123 1242092308277047450906685)
          ·
            refine ⟨465784615603892794090007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1242092308277047450906685 465784615603892794090007)
            ·
              refine ⟨698676923405839191135011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465784615603892794090007 698676923405839191135011)
              ·
                refine ⟨1048015385108758786702517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698676923405839191135011 1048015385108758786702517)
                ·
                  refine ⟨98251442353946136253361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1048015385108758786702517 98251442353946136253361)
                  ·
                    rfl

theorem cell21_430524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_430524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430524 prefixEnd_430524 := by exact prefixLift 430524
  have htrace : WordTrace (prefixWord ++ tailWord_430524) baseStart_430524 baseEnd_430524 := by
    simpa [prefixWord, tailWord_430524, baseEnd_430524] using wordTrace_append hprefix tailTrace_430524
  have hstable : (prefixWord ++ tailWord_430524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430524).length < 2 ^ (prefixWord ++ tailWord_430524).sum := by decide
  have hdescent : baseEnd_430524 < baseStart_430524 := by decide
  rcases family_descends (prefixWord ++ tailWord_430524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430535 : List Nat := [1, 1, 4, 1, 1, 4, 1, 8]
def baseStart_430535 : Nat := 118140960795 + 430535 * 2 ^ 59
def prefixEnd_430535 : Nat := 4983230072969 + 3 ^ 40 * 430535 * 2
def baseEnd_430535 : Nat := 32751317567937520523335

theorem tailTrace_430535 : CollatzResearch.WordTrace tailWord_430535 prefixEnd_430535 32751317567937520523335 := by
  unfold tailWord_430535
  simp only [CollatzResearch.WordTrace]
  refine ⟨15702901495252699369125059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10468600996835132912750039 15702901495252699369125059)
  ·
    refine ⟨23554352242879049053687589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15702901495252699369125059 23554352242879049053687589)
    ·
      refine ⟨4416441045539821697566423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23554352242879049053687589 4416441045539821697566423)
      ·
        refine ⟨6624661568309732546349635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4416441045539821697566423 6624661568309732546349635)
        ·
          refine ⟨9936992352464598819524453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6624661568309732546349635 9936992352464598819524453)
          ·
            refine ⟨1863186066087112278660835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9936992352464598819524453 1863186066087112278660835)
            ·
              refine ⟨2794779099130668417991253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1863186066087112278660835 2794779099130668417991253)
              ·
                refine ⟨32751317567937520523335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2794779099130668417991253 32751317567937520523335)
                ·
                  rfl

theorem cell21_430535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 8].length) (baseStart_430535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430535 prefixEnd_430535 := by exact prefixLift 430535
  have htrace : WordTrace (prefixWord ++ tailWord_430535) baseStart_430535 baseEnd_430535 := by
    simpa [prefixWord, tailWord_430535, baseEnd_430535] using wordTrace_append hprefix tailTrace_430535
  have hstable : (prefixWord ++ tailWord_430535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430535).length < 2 ^ (prefixWord ++ tailWord_430535).sum := by decide
  have hdescent : baseEnd_430535 < baseStart_430535 := by decide
  rcases family_descends (prefixWord ++ tailWord_430535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430597 : List Nat := [1, 3, 1, 1, 2, 2, 4, 3, 4]
def baseStart_430597 : Nat := 118140960795 + 430597 * 2 ^ 59
def prefixEnd_430597 : Nat := 4983230072969 + 3 ^ 40 * 430597 * 2
def baseEnd_430597 : Nat := 98268101948514231536545

theorem tailTrace_430597 : CollatzResearch.WordTrace tailWord_430597 prefixEnd_430597 98268101948514231536545 := by
  unfold tailWord_430597
  simp only [CollatzResearch.WordTrace]
  refine ⟨15705162821028083957882045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10470108547352055971921363 15705162821028083957882045)
  ·
    refine ⟨5889436057885531484205767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15705162821028083957882045 5889436057885531484205767)
    ·
      refine ⟨8834154086828297226308651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5889436057885531484205767 8834154086828297226308651)
      ·
        refine ⟨13251231130242445839462977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8834154086828297226308651 13251231130242445839462977)
        ·
          refine ⟨9938423347681834379597233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13251231130242445839462977 9938423347681834379597233)
          ·
            refine ⟨7453817510761375784697925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9938423347681834379597233 7453817510761375784697925)
            ·
              refine ⟨1397590783267757959630861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7453817510761375784697925 1397590783267757959630861)
              ·
                refine ⟨524096543725409234861573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1397590783267757959630861 524096543725409234861573)
                ·
                  refine ⟨98268101948514231536545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 524096543725409234861573 98268101948514231536545)
                  ·
                    rfl

theorem cell21_430597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_430597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430597 prefixEnd_430597 := by exact prefixLift 430597
  have htrace : WordTrace (prefixWord ++ tailWord_430597) baseStart_430597 baseEnd_430597 := by
    simpa [prefixWord, tailWord_430597, baseEnd_430597] using wordTrace_append hprefix tailTrace_430597
  have hstable : (prefixWord ++ tailWord_430597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430597).length < 2 ^ (prefixWord ++ tailWord_430597).sum := by decide
  have hdescent : baseEnd_430597 < baseStart_430597 := by decide
  rcases family_descends (prefixWord ++ tailWord_430597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430631 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 6]
def baseStart_430631 : Nat := 118140960795 + 430631 * 2 ^ 59
def prefixEnd_430631 : Nat := 4983230072969 + 3 ^ 40 * 430631 * 2
def baseEnd_430631 : Nat := 98275861211737727969809

theorem tailTrace_430631 : CollatzResearch.WordTrace tailWord_430631 prefixEnd_430631 98275861211737727969809 := by
  unfold tailWord_430631
  simp only [CollatzResearch.WordTrace]
  refine ⟨15706402902904907764619747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10470935268603271843079831 15706402902904907764619747)
  ·
    refine ⟨23559604354357361646929621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15706402902904907764619747 23559604354357361646929621)
    ·
      refine ⟨552178227055250663599913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 23559604354357361646929621 552178227055250663599913)
      ·
        refine ⟨414133670291437997699935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552178227055250663599913 414133670291437997699935)
        ·
          refine ⟨621200505437156996549903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414133670291437997699935 621200505437156996549903)
          ·
            refine ⟨931800758155735494824855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621200505437156996549903 931800758155735494824855)
            ·
              refine ⟨1397701137233603242237283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 931800758155735494824855 1397701137233603242237283)
              ·
                refine ⟨2096551705850404863355925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1397701137233603242237283 2096551705850404863355925)
                ·
                  refine ⟨98275861211737727969809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2096551705850404863355925 98275861211737727969809)
                  ·
                    rfl

theorem cell21_430631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 6].length) (baseStart_430631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430631 prefixEnd_430631 := by exact prefixLift 430631
  have htrace : WordTrace (prefixWord ++ tailWord_430631) baseStart_430631 baseEnd_430631 := by
    simpa [prefixWord, tailWord_430631, baseEnd_430631] using wordTrace_append hprefix tailTrace_430631
  have hstable : (prefixWord ++ tailWord_430631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430631).length < 2 ^ (prefixWord ++ tailWord_430631).sum := by decide
  have hdescent : baseEnd_430631 < baseStart_430631 := by decide
  rcases family_descends (prefixWord ++ tailWord_430631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430642 : List Nat := [3, 2, 1, 1, 2, 1, 3, 3, 5]
def baseStart_430642 : Nat := 118140960795 + 430642 * 2 ^ 59
def prefixEnd_430642 : Nat := 4983230072969 + 3 ^ 40 * 430642 * 2
def baseEnd_430642 : Nat := 98278371561604153286453

theorem tailTrace_430642 : CollatzResearch.WordTrace tailWord_430642 prefixEnd_430642 98278371561604153286453 := by
  unfold tailWord_430642
  simp only [CollatzResearch.WordTrace]
  refine ⟨3926701026466264160817545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10471202737243371095513453 3926701026466264160817545)
  ·
    refine ⟨2945025769849698120613159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3926701026466264160817545 2945025769849698120613159)
    ·
      refine ⟨4417538654774547180919739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2945025769849698120613159 4417538654774547180919739)
      ·
        refine ⟨6626307982161820771379609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4417538654774547180919739 6626307982161820771379609)
        ·
          refine ⟨4969730986621365578534707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6626307982161820771379609 4969730986621365578534707)
          ·
            refine ⟨7454596479932048367802061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4969730986621365578534707 7454596479932048367802061)
            ·
              refine ⟨2795473679974518137925773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7454596479932048367802061 2795473679974518137925773)
              ·
                refine ⟨1048302629990444301722165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2795473679974518137925773 1048302629990444301722165)
                ·
                  refine ⟨98278371561604153286453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1048302629990444301722165 98278371561604153286453)
                  ·
                    rfl

theorem cell21_430642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_430642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430642 prefixEnd_430642 := by exact prefixLift 430642
  have htrace : WordTrace (prefixWord ++ tailWord_430642) baseStart_430642 baseEnd_430642 := by
    simpa [prefixWord, tailWord_430642, baseEnd_430642] using wordTrace_append hprefix tailTrace_430642
  have hstable : (prefixWord ++ tailWord_430642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430642).length < 2 ^ (prefixWord ++ tailWord_430642).sum := by decide
  have hdescent : baseEnd_430642 < baseStart_430642 := by decide
  rcases family_descends (prefixWord ++ tailWord_430642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430662 : List Nat := [6, 1, 1, 1, 2, 1, 4, 5]
def baseStart_430662 : Nat := 118140960795 + 430662 * 2 ^ 59
def prefixEnd_430662 : Nat := 4983230072969 + 3 ^ 40 * 430662 * 2
def baseEnd_430662 : Nat := 32760978611362854317693

theorem tailTrace_430662 : CollatzResearch.WordTrace tailWord_430662 prefixEnd_430662 32760978611362854317693 := by
  unfold tailWord_430662
  simp only [CollatzResearch.WordTrace]
  refine ⟨490860423931018751843695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10471689043861733372665493 490860423931018751843695)
  ·
    refine ⟨736290635896528127765543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 490860423931018751843695 736290635896528127765543)
    ·
      refine ⟨1104435953844792191648315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 736290635896528127765543 1104435953844792191648315)
      ·
        refine ⟨1656653930767188287472473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1104435953844792191648315 1656653930767188287472473)
        ·
          refine ⟨1242490448075391215604355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1656653930767188287472473 1242490448075391215604355)
          ·
            refine ⟨1863735672113086823406533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1242490448075391215604355 1863735672113086823406533)
            ·
              refine ⟨349450438521203779388725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1863735672113086823406533 349450438521203779388725)
              ·
                refine ⟨32760978611362854317693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 349450438521203779388725 32760978611362854317693)
                ·
                  rfl

theorem cell21_430662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_430662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430662 prefixEnd_430662 := by exact prefixLift 430662
  have htrace : WordTrace (prefixWord ++ tailWord_430662) baseStart_430662 baseEnd_430662 := by
    simpa [prefixWord, tailWord_430662, baseEnd_430662] using wordTrace_append hprefix tailTrace_430662
  have hstable : (prefixWord ++ tailWord_430662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430662).length < 2 ^ (prefixWord ++ tailWord_430662).sum := by decide
  have hdescent : baseEnd_430662 < baseStart_430662 := by decide
  rcases family_descends (prefixWord ++ tailWord_430662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430676 : List Nat := [2, 4, 1, 1, 1, 3, 3, 3, 3]
def baseStart_430676 : Nat := 118140960795 + 430676 * 2 ^ 59
def prefixEnd_430676 : Nat := 4983230072969 + 3 ^ 40 * 430676 * 2
def baseEnd_430676 : Nat := 98286130824827649719717

theorem tailTrace_430676 : CollatzResearch.WordTrace tailWord_430676 prefixEnd_430676 98286130824827649719717 := by
  unfold tailWord_430676
  simp only [CollatzResearch.WordTrace]
  refine ⟨7854022093870940225003941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10472029458494586966671921 7854022093870940225003941)
  ·
    refine ⟨1472629142600801292188239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7854022093870940225003941 1472629142600801292188239)
    ·
      refine ⟨2208943713901201938282359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1472629142600801292188239 2208943713901201938282359)
      ·
        refine ⟨3313415570851802907423539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2208943713901201938282359 3313415570851802907423539)
        ·
          refine ⟨4970123356277704361135309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3313415570851802907423539 4970123356277704361135309)
          ·
            refine ⟨1863796258604139135425741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4970123356277704361135309 1863796258604139135425741)
            ·
              refine ⟨698923596976552175784653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1863796258604139135425741 698923596976552175784653)
              ·
                refine ⟨262096348866207065919245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 698923596976552175784653 262096348866207065919245)
                ·
                  refine ⟨98286130824827649719717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262096348866207065919245 98286130824827649719717)
                  ·
                    rfl

theorem cell21_430676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_430676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430676 prefixEnd_430676 := by exact prefixLift 430676
  have htrace : WordTrace (prefixWord ++ tailWord_430676) baseStart_430676 baseEnd_430676 := by
    simpa [prefixWord, tailWord_430676, baseEnd_430676] using wordTrace_append hprefix tailTrace_430676
  have hstable : (prefixWord ++ tailWord_430676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430676).length < 2 ^ (prefixWord ++ tailWord_430676).sum := by decide
  have hdescent : baseEnd_430676 < baseStart_430676 := by decide
  rcases family_descends (prefixWord ++ tailWord_430676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430693 : List Nat := [1, 3, 1, 3, 4, 1, 3, 2, 3]
def baseStart_430693 : Nat := 118140960795 + 430693 * 2 ^ 59
def prefixEnd_430693 : Nat := 4983230072969 + 3 ^ 40 * 430693 * 2
def baseEnd_430693 : Nat := 98290010456439397936349

theorem tailTrace_430693 : CollatzResearch.WordTrace tailWord_430693 prefixEnd_430693 98290010456439397936349 := by
  unfold tailWord_430693
  simp only [CollatzResearch.WordTrace]
  refine ⟨15708664228680292353376733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10472442819120194902251155 15708664228680292353376733)
  ·
    refine ⟨5890749085755109632516275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15708664228680292353376733 5890749085755109632516275)
    ·
      refine ⟨8836123628632664448774413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5890749085755109632516275 8836123628632664448774413)
      ·
        refine ⟨3313546360737249168290405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8836123628632664448774413 3313546360737249168290405)
        ·
          refine ⟨621289942638234219054451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3313546360737249168290405 621289942638234219054451)
          ·
            refine ⟨931934913957351328581677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621289942638234219054451 931934913957351328581677)
            ·
              refine ⟨349475592734006748218129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 931934913957351328581677 349475592734006748218129)
              ·
                refine ⟨262106694550505061163597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349475592734006748218129 262106694550505061163597)
                ·
                  refine ⟨98290010456439397936349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262106694550505061163597 98290010456439397936349)
                  ·
                    rfl

theorem cell21_430693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_430693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430693 prefixEnd_430693 := by exact prefixLift 430693
  have htrace : WordTrace (prefixWord ++ tailWord_430693) baseStart_430693 baseEnd_430693 := by
    simpa [prefixWord, tailWord_430693, baseEnd_430693] using wordTrace_append hprefix tailTrace_430693
  have hstable : (prefixWord ++ tailWord_430693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430693).length < 2 ^ (prefixWord ++ tailWord_430693).sum := by decide
  have hdescent : baseEnd_430693 < baseStart_430693 := by decide
  rcases family_descends (prefixWord ++ tailWord_430693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430704 : List Nat := [2, 1, 1, 1, 7, 1, 2, 6]
def baseStart_430704 : Nat := 118140960795 + 430704 * 2 ^ 59
def prefixEnd_430704 : Nat := 4983230072969 + 3 ^ 40 * 430704 * 2
def baseEnd_430704 : Nat := 32764173602101941084331

theorem tailTrace_430704 : CollatzResearch.WordTrace tailWord_430704 prefixEnd_430704 32764173602101941084331 := by
  unfold tailWord_430704
  simp only [CollatzResearch.WordTrace]
  refine ⟨7854532715820220616013583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10472710287760294154684777 7854532715820220616013583)
  ·
    refine ⟨11781799073730330924020375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7854532715820220616013583 11781799073730330924020375)
    ·
      refine ⟨17672698610595496386030563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11781799073730330924020375 17672698610595496386030563)
      ·
        refine ⟨26509047915893244579045845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17672698610595496386030563 26509047915893244579045845)
        ·
          refine ⟨621305810528747919821387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 26509047915893244579045845 621305810528747919821387)
          ·
            refine ⟨931958715793121879732081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621305810528747919821387 931958715793121879732081)
            ·
              refine ⟨698969036844841409799061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 931958715793121879732081 698969036844841409799061)
              ·
                refine ⟨32764173602101941084331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 698969036844841409799061 32764173602101941084331)
                ·
                  rfl

theorem cell21_430704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 6].length) (baseStart_430704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430704 prefixEnd_430704 := by exact prefixLift 430704
  have htrace : WordTrace (prefixWord ++ tailWord_430704) baseStart_430704 baseEnd_430704 := by
    simpa [prefixWord, tailWord_430704, baseEnd_430704] using wordTrace_append hprefix tailTrace_430704
  have hstable : (prefixWord ++ tailWord_430704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430704).length < 2 ^ (prefixWord ++ tailWord_430704).sum := by decide
  have hdescent : baseEnd_430704 < baseStart_430704 := by decide
  rcases family_descends (prefixWord ++ tailWord_430704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430732 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 6]
def baseStart_430732 : Nat := 118140960795 + 430732 * 2 ^ 59
def prefixEnd_430732 : Nat := 4983230072969 + 3 ^ 40 * 430732 * 2
def baseEnd_430732 : Nat := 98298910787783996786269

theorem tailTrace_430732 : CollatzResearch.WordTrace tailWord_430732 prefixEnd_430732 98298910787783996786269 := by
  unfold tailWord_430732
  simp only [CollatzResearch.WordTrace]
  refine ⟨7855043337769501007023225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10473391117026001342697633 7855043337769501007023225)
  ·
    refine ⟨5891282503327125755267419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7855043337769501007023225 5891282503327125755267419)
    ·
      refine ⟨8836923754990688632901129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5891282503327125755267419 8836923754990688632901129)
      ·
        refine ⟨6627692816243016474675847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8836923754990688632901129 6627692816243016474675847)
        ·
          refine ⟨9941539224364524712013771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6627692816243016474675847 9941539224364524712013771)
          ·
            refine ⟨14912308836546787068020657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9941539224364524712013771 14912308836546787068020657)
            ·
              refine ⟨11184231627410090301015493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14912308836546787068020657 11184231627410090301015493)
              ·
                refine ⟨2097043430139391931440405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11184231627410090301015493 2097043430139391931440405)
                ·
                  refine ⟨98298910787783996786269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2097043430139391931440405 98298910787783996786269)
                  ·
                    rfl

theorem cell21_430732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_430732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430732 prefixEnd_430732 := by exact prefixLift 430732
  have htrace : WordTrace (prefixWord ++ tailWord_430732) baseStart_430732 baseEnd_430732 := by
    simpa [prefixWord, tailWord_430732, baseEnd_430732] using wordTrace_append hprefix tailTrace_430732
  have hstable : (prefixWord ++ tailWord_430732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430732).length < 2 ^ (prefixWord ++ tailWord_430732).sum := by decide
  have hdescent : baseEnd_430732 < baseStart_430732 := by decide
  rcases family_descends (prefixWord ++ tailWord_430732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430749 : List Nat := [1, 4, 2, 1, 1, 1, 3, 4, 4]
def baseStart_430749 : Nat := 118140960795 + 430749 * 2 ^ 59
def prefixEnd_430749 : Nat := 4983230072969 + 3 ^ 40 * 430749 * 2
def baseEnd_430749 : Nat := 98302790419395745002901

theorem tailTrace_430749 : CollatzResearch.WordTrace tailWord_430749 prefixEnd_430749 98302790419395745002901 := by
  unfold tailWord_430749
  simp only [CollatzResearch.WordTrace]
  refine ⟨15710706716477413917415301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10473804477651609278276867 15710706716477413917415301)
  ·
    refine ⟨2945757509339515109515369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15710706716477413917415301 2945757509339515109515369)
    ·
      refine ⟨2209318132004636332136527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2945757509339515109515369 2209318132004636332136527)
      ·
        refine ⟨3313977198006954498204791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2209318132004636332136527 3313977198006954498204791)
        ·
          refine ⟨4970965797010431747307187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3313977198006954498204791 4970965797010431747307187)
          ·
            refine ⟨7456448695515647620960781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4970965797010431747307187 7456448695515647620960781)
            ·
              refine ⟨2796168260818367857860293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7456448695515647620960781 2796168260818367857860293)
              ·
                refine ⟨524281548903443973348805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2796168260818367857860293 524281548903443973348805)
                ·
                  refine ⟨98302790419395745002901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 524281548903443973348805 98302790419395745002901)
                  ·
                    rfl

theorem cell21_430749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_430749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430749 prefixEnd_430749 := by exact prefixLift 430749
  have htrace : WordTrace (prefixWord ++ tailWord_430749) baseStart_430749 baseEnd_430749 := by
    simpa [prefixWord, tailWord_430749, baseEnd_430749] using wordTrace_append hprefix tailTrace_430749
  have hstable : (prefixWord ++ tailWord_430749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430749).length < 2 ^ (prefixWord ++ tailWord_430749).sum := by decide
  have hdescent : baseEnd_430749 < baseStart_430749 := by decide
  rcases family_descends (prefixWord ++ tailWord_430749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430752 : List Nat := [2, 1, 1, 4, 4, 1, 1, 4, 3]
def baseStart_430752 : Nat := 118140960795 + 430752 * 2 ^ 59
def prefixEnd_430752 : Nat := 4983230072969 + 3 ^ 40 * 430752 * 2
def baseEnd_430752 : Nat := 98303475060268406452895

theorem tailTrace_430752 : CollatzResearch.WordTrace tailWord_430752 prefixEnd_430752 98303475060268406452895 := by
  unfold tailWord_430752
  simp only [CollatzResearch.WordTrace]
  refine ⟨7855408067733272714887255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10473877423644363619849673 7855408067733272714887255)
  ·
    refine ⟨11783112101599909072330883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7855408067733272714887255 11783112101599909072330883)
    ·
      refine ⟨17674668152399863608496325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11783112101599909072330883 17674668152399863608496325)
      ·
        refine ⟨3314000278574974426593061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17674668152399863608496325 3314000278574974426593061)
        ·
          refine ⟨621375052232807704986199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3314000278574974426593061 621375052232807704986199)
          ·
            refine ⟨932062578349211557479299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621375052232807704986199 932062578349211557479299)
            ·
              refine ⟨1398093867523817336218949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932062578349211557479299 1398093867523817336218949)
              ·
                refine ⟨262142600160715750541053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1398093867523817336218949 262142600160715750541053)
                ·
                  refine ⟨98303475060268406452895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262142600160715750541053 98303475060268406452895)
                  ·
                    rfl

theorem cell21_430752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 3].length) (baseStart_430752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430752 prefixEnd_430752 := by exact prefixLift 430752
  have htrace : WordTrace (prefixWord ++ tailWord_430752) baseStart_430752 baseEnd_430752 := by
    simpa [prefixWord, tailWord_430752, baseEnd_430752] using wordTrace_append hprefix tailTrace_430752
  have hstable : (prefixWord ++ tailWord_430752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430752).length < 2 ^ (prefixWord ++ tailWord_430752).sum := by decide
  have hdescent : baseEnd_430752 < baseStart_430752 := by decide
  rcases family_descends (prefixWord ++ tailWord_430752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430780 : List Nat := [2, 2, 2, 3, 1, 1, 5, 5]
def baseStart_430780 : Nat := 118140960795 + 430780 * 2 ^ 59
def prefixEnd_430780 : Nat := 4983230072969 + 3 ^ 40 * 430780 * 2
def baseEnd_430780 : Nat := 32769955013915526662057

theorem tailTrace_430780 : CollatzResearch.WordTrace tailWord_430780 prefixEnd_430780 32769955013915526662057 := by
  unfold tailWord_430780
  simp only [CollatzResearch.WordTrace]
  refine ⟨7855918689682553105896897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10474558252910070807862529 7855918689682553105896897)
  ·
    refine ⟨5891939017261914829422673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7855918689682553105896897 5891939017261914829422673)
    ·
      refine ⟨4418954262946436122067005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5891939017261914829422673 4418954262946436122067005)
      ·
        refine ⟨1657107848604913545775127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4418954262946436122067005 1657107848604913545775127)
        ·
          refine ⟨2485661772907370318662691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1657107848604913545775127 2485661772907370318662691)
          ·
            refine ⟨3728492659361055477994037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485661772907370318662691 3728492659361055477994037)
            ·
              refine ⟨349546186815098951061941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3728492659361055477994037 349546186815098951061941)
              ·
                refine ⟨32769955013915526662057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 349546186815098951061941 32769955013915526662057)
                ·
                  rfl

theorem cell21_430780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 5].length) (baseStart_430780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430780 prefixEnd_430780 := by exact prefixLift 430780
  have htrace : WordTrace (prefixWord ++ tailWord_430780) baseStart_430780 baseEnd_430780 := by
    simpa [prefixWord, tailWord_430780, baseEnd_430780] using wordTrace_append hprefix tailTrace_430780
  have hstable : (prefixWord ++ tailWord_430780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430780).length < 2 ^ (prefixWord ++ tailWord_430780).sum := by decide
  have hdescent : baseEnd_430780 < baseStart_430780 := by decide
  rcases family_descends (prefixWord ++ tailWord_430780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430797 : List Nat := [1, 6, 2, 1, 2, 1, 8]
def baseStart_430797 : Nat := 118140960795 + 430797 * 2 ^ 59
def prefixEnd_430797 : Nat := 4983230072969 + 3 ^ 40 * 430797 * 2
def baseEnd_430797 : Nat := 10923749408150925355867

theorem tailTrace_430797 : CollatzResearch.WordTrace tailWord_430797 prefixEnd_430797 10923749408150925355867 := by
  unfold tailWord_430797
  simp only [CollatzResearch.WordTrace]
  refine ⟨15712457420303518115162645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10474971613535678743441763 15712457420303518115162645)
  ·
    refine ⟨736521441576727411648249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15712457420303518115162645 736521441576727411648249)
    ·
      refine ⟨552391081182545558736187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 736521441576727411648249 552391081182545558736187)
      ·
        refine ⟨828586621773818338104281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552391081182545558736187 828586621773818338104281)
        ·
          refine ⟨621439966330363753578211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 828586621773818338104281 621439966330363753578211)
          ·
            refine ⟨932159949495545630367317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621439966330363753578211 932159949495545630367317)
            ·
              refine ⟨10923749408150925355867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 932159949495545630367317 10923749408150925355867)
              ·
                rfl

theorem cell21_430797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 8].length) (baseStart_430797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430797 prefixEnd_430797 := by exact prefixLift 430797
  have htrace : WordTrace (prefixWord ++ tailWord_430797) baseStart_430797 baseEnd_430797 := by
    simpa [prefixWord, tailWord_430797, baseEnd_430797] using wordTrace_append hprefix tailTrace_430797
  have hstable : (prefixWord ++ tailWord_430797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430797).length < 2 ^ (prefixWord ++ tailWord_430797).sum := by decide
  have hdescent : baseEnd_430797 < baseStart_430797 := by decide
  rcases family_descends (prefixWord ++ tailWord_430797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430853 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 7]
def baseStart_430853 : Nat := 118140960795 + 430853 * 2 ^ 59
def prefixEnd_430853 : Nat := 4983230072969 + 3 ^ 40 * 430853 * 2
def baseEnd_430853 : Nat := 98326524636314675269355

theorem tailTrace_430853 : CollatzResearch.WordTrace tailWord_430853 prefixEnd_430853 98326524636314675269355 := by
  unfold tailWord_430853
  simp only [CollatzResearch.WordTrace]
  refine ⟨15714499908100639679201213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10476333272067093119467475 15714499908100639679201213)
  ·
    refine ⟨5892937465537739879700455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15714499908100639679201213 5892937465537739879700455)
    ·
      refine ⟨8839406198306609819550683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5892937465537739879700455 8839406198306609819550683)
      ·
        refine ⟨13259109297459914729326025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8839406198306609819550683 13259109297459914729326025)
        ·
          refine ⟨9944331973094936046994519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13259109297459914729326025 9944331973094936046994519)
          ·
            refine ⟨14916497959642404070491779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9944331973094936046994519 14916497959642404070491779)
            ·
              refine ⟨22374746939463606105737669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14916497959642404070491779 22374746939463606105737669)
              ·
                refine ⟨4195265051149426144825813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22374746939463606105737669 4195265051149426144825813)
                ·
                  refine ⟨98326524636314675269355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4195265051149426144825813 98326524636314675269355)
                  ·
                    rfl

theorem cell21_430853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_430853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_430853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_430853 prefixEnd_430853 := by exact prefixLift 430853
  have htrace : WordTrace (prefixWord ++ tailWord_430853) baseStart_430853 baseEnd_430853 := by
    simpa [prefixWord, tailWord_430853, baseEnd_430853] using wordTrace_append hprefix tailTrace_430853
  have hstable : (prefixWord ++ tailWord_430853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430853).length < 2 ^ (prefixWord ++ tailWord_430853).sum := by decide
  have hdescent : baseEnd_430853 < baseStart_430853 := by decide
  rcases family_descends (prefixWord ++ tailWord_430853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431090 : List Nat := [3, 2, 1, 5, 1, 2, 2, 2, 3]
def baseStart_431090 : Nat := 118140960795 + 431090 * 2 ^ 59
def prefixEnd_431090 : Nat := 4983230072969 + 3 ^ 40 * 431090 * 2
def baseEnd_431090 : Nat := 98380611265254929818871

theorem tailTrace_431090 : CollatzResearch.WordTrace tailWord_431090 prefixEnd_431090 98380611265254929818871 := by
  unfold tailWord_431090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3930786002060507288894681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10482096005494686103719149 3930786002060507288894681)
  ·
    refine ⟨2948089501545380466671011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3930786002060507288894681 2948089501545380466671011)
    ·
      refine ⟨4422134252318070700006517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2948089501545380466671011 4422134252318070700006517)
      ·
        refine ⟨414575086154819128125611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4422134252318070700006517 414575086154819128125611)
        ·
          refine ⟨621862629232228692188417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414575086154819128125611 621862629232228692188417)
          ·
            refine ⟨466396971924171519141313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 621862629232228692188417 466396971924171519141313)
            ·
              refine ⟨349797728943128639355985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466396971924171519141313 349797728943128639355985)
              ·
                refine ⟨262348296707346479516989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349797728943128639355985 262348296707346479516989)
                ·
                  refine ⟨98380611265254929818871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262348296707346479516989 98380611265254929818871)
                  ·
                    rfl

theorem cell21_431090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_431090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_431090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_431090 prefixEnd_431090 := by exact prefixLift 431090
  have htrace : WordTrace (prefixWord ++ tailWord_431090) baseStart_431090 baseEnd_431090 := by
    simpa [prefixWord, tailWord_431090, baseEnd_431090] using wordTrace_append hprefix tailTrace_431090
  have hstable : (prefixWord ++ tailWord_431090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431090).length < 2 ^ (prefixWord ++ tailWord_431090).sum := by decide
  have hdescent : baseEnd_431090 < baseStart_431090 := by decide
  rcases family_descends (prefixWord ++ tailWord_431090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431132 : List Nat := [2, 2, 3, 1, 4, 1, 2, 3, 3]
def baseStart_431132 : Nat := 118140960795 + 431132 * 2 ^ 59
def prefixEnd_431132 : Nat := 4983230072969 + 3 ^ 40 * 431132 * 2
def baseEnd_431132 : Nat := 98390196237472190118785

theorem tailTrace_431132 : CollatzResearch.WordTrace tailWord_431132 prefixEnd_431132 98390196237472190118785 := by
  unfold tailWord_431132
  simp only [CollatzResearch.WordTrace]
  refine ⟨7862337937044935164303825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10483117249393246885738433 7862337937044935164303825)
  ·
    refine ⟨5896753452783701373227869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7862337937044935164303825 5896753452783701373227869)
    ·
      refine ⟨2211282544793888014960451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5896753452783701373227869 2211282544793888014960451)
      ·
        refine ⟨3316923817190832022440677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2211282544793888014960451 3316923817190832022440677)
        ·
          refine ⟨621923215723281004207627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3316923817190832022440677 621923215723281004207627)
          ·
            refine ⟨932884823584921506311441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621923215723281004207627 932884823584921506311441)
            ·
              refine ⟨699663617688691129733581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 932884823584921506311441 699663617688691129733581)
              ·
                refine ⟨262373856633259173650093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 699663617688691129733581 262373856633259173650093)
                ·
                  refine ⟨98390196237472190118785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262373856633259173650093 98390196237472190118785)
                  ·
                    rfl

theorem cell21_431132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_431132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_431132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_431132 prefixEnd_431132 := by exact prefixLift 431132
  have htrace : WordTrace (prefixWord ++ tailWord_431132) baseStart_431132 baseEnd_431132 := by
    simpa [prefixWord, tailWord_431132, baseEnd_431132] using wordTrace_append hprefix tailTrace_431132
  have hstable : (prefixWord ++ tailWord_431132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431132).length < 2 ^ (prefixWord ++ tailWord_431132).sum := by decide
  have hdescent : baseEnd_431132 < baseStart_431132 := by decide
  rcases family_descends (prefixWord ++ tailWord_431132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431188 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 6]
def baseStart_431188 : Nat := 118140960795 + 431188 * 2 ^ 59
def prefixEnd_431188 : Nat := 4983230072969 + 3 ^ 40 * 431188 * 2
def baseEnd_431188 : Nat := 98402976200428537185337

theorem tailTrace_431188 : CollatzResearch.WordTrace tailWord_431188 prefixEnd_431188 98402976200428537185337 := by
  unfold tailWord_431188
  simp only [CollatzResearch.WordTrace]
  refine ⟨7863359180943495946323109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10484478907924661261764145 7863359180943495946323109)
  ·
    refine ⟨1474379846426905489935583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7863359180943495946323109 1474379846426905489935583)
    ·
      refine ⟨2211569769640358234903375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1474379846426905489935583 2211569769640358234903375)
      ·
        refine ⟨3317354654460537352355063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2211569769640358234903375 3317354654460537352355063)
        ·
          refine ⟨4976031981690806028532595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3317354654460537352355063 4976031981690806028532595)
          ·
            refine ⟨7464047972536209042798893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4976031981690806028532595 7464047972536209042798893)
            ·
              refine ⟨2799017989701078391049585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7464047972536209042798893 2799017989701078391049585)
              ·
                refine ⟨2099263492275808793287189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2799017989701078391049585 2099263492275808793287189)
                ·
                  refine ⟨98402976200428537185337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2099263492275808793287189 98402976200428537185337)
                  ·
                    rfl

theorem cell21_431188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_431188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_431188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_431188 prefixEnd_431188 := by exact prefixLift 431188
  have htrace : WordTrace (prefixWord ++ tailWord_431188) baseStart_431188 baseEnd_431188 := by
    simpa [prefixWord, tailWord_431188, baseEnd_431188] using wordTrace_append hprefix tailTrace_431188
  have hstable : (prefixWord ++ tailWord_431188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431188).length < 2 ^ (prefixWord ++ tailWord_431188).sum := by decide
  have hdescent : baseEnd_431188 < baseStart_431188 := by decide
  rcases family_descends (prefixWord ++ tailWord_431188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431208 : List Nat := [2, 1, 4, 4, 1, 2, 1, 1, 5]
def baseStart_431208 : Nat := 118140960795 + 431208 * 2 ^ 59
def prefixEnd_431208 : Nat := 4983230072969 + 3 ^ 40 * 431208 * 2
def baseEnd_431208 : Nat := 98407540472912946851963

theorem tailTrace_431208 : CollatzResearch.WordTrace tailWord_431208 prefixEnd_431208 98407540472912946851963 := by
  unfold tailWord_431208
  simp only [CollatzResearch.WordTrace]
  refine ⟨7863723910907267654187139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10484965214543023538916185 7863723910907267654187139)
  ·
    refine ⟨11795585866360901481280709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7863723910907267654187139 11795585866360901481280709)
    ·
      refine ⟨2211672349942669027740133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11795585866360901481280709 2211672349942669027740133)
      ·
        refine ⟨414688565614250442701275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2211672349942669027740133 414688565614250442701275)
        ·
          refine ⟨622032848421375664051913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414688565614250442701275 622032848421375664051913)
          ·
            refine ⟨466524636316031748038935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622032848421375664051913 466524636316031748038935)
            ·
              refine ⟨699786954474047622058403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466524636316031748038935 699786954474047622058403)
              ·
                refine ⟨1049680431711071433087605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699786954474047622058403 1049680431711071433087605)
                ·
                  refine ⟨98407540472912946851963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1049680431711071433087605 98407540472912946851963)
                  ·
                    rfl

theorem cell21_431208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 5].length) (baseStart_431208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_431208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_431208 prefixEnd_431208 := by exact prefixLift 431208
  have htrace : WordTrace (prefixWord ++ tailWord_431208) baseStart_431208 baseEnd_431208 := by
    simpa [prefixWord, tailWord_431208, baseEnd_431208] using wordTrace_append hprefix tailTrace_431208
  have hstable : (prefixWord ++ tailWord_431208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431208).length < 2 ^ (prefixWord ++ tailWord_431208).sum := by decide
  have hdescent : baseEnd_431208 < baseStart_431208 := by decide
  rcases family_descends (prefixWord ++ tailWord_431208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431281 : List Nat := [1, 2, 2, 5, 1, 1, 2, 3, 4]
def baseStart_431281 : Nat := 118140960795 + 431281 * 2 ^ 59
def prefixEnd_431281 : Nat := 4983230072969 + 3 ^ 40 * 431281 * 2
def baseEnd_431281 : Nat := 98424200067481042135147

theorem tailTrace_431281 : CollatzResearch.WordTrace tailWord_431281 prefixEnd_431281 98424200067481042135147 := by
  unfold tailWord_431281
  simp only [CollatzResearch.WordTrace]
  refine ⟨15730110350550068775781697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10486740233700045850521131 15730110350550068775781697)
  ·
    refine ⟨11797582762912551581836273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15730110350550068775781697 11797582762912551581836273)
    ·
      refine ⟨8848187072184413686377205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11797582762912551581836273 8848187072184413686377205)
      ·
        refine ⟨829517538017288783097863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8848187072184413686377205 829517538017288783097863)
        ·
          refine ⟨1244276307025933174646795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829517538017288783097863 1244276307025933174646795)
          ·
            refine ⟨1866414460538899761970193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244276307025933174646795 1866414460538899761970193)
            ·
              refine ⟨1399810845404174821477645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1866414460538899761970193 1399810845404174821477645)
              ·
                refine ⟨524929067026565558054117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1399810845404174821477645 524929067026565558054117)
                ·
                  refine ⟨98424200067481042135147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 524929067026565558054117 98424200067481042135147)
                  ·
                    rfl

theorem cell21_431281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_431281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_431281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_431281 prefixEnd_431281 := by exact prefixLift 431281
  have htrace : WordTrace (prefixWord ++ tailWord_431281) baseStart_431281 baseEnd_431281 := by
    simpa [prefixWord, tailWord_431281, baseEnd_431281] using wordTrace_append hprefix tailTrace_431281
  have hstable : (prefixWord ++ tailWord_431281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431281).length < 2 ^ (prefixWord ++ tailWord_431281).sum := by decide
  have hdescent : baseEnd_431281 < baseStart_431281 := by decide
  rcases family_descends (prefixWord ++ tailWord_431281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431354 : List Nat := [3, 1, 1, 1, 1, 4, 3, 7]
def baseStart_431354 : Nat := 118140960795 + 431354 * 2 ^ 59
def prefixEnd_431354 : Nat := 4983230072969 + 3 ^ 40 * 431354 * 2
def baseEnd_431354 : Nat := 32813619887349712472777

theorem tailTrace_431354 : CollatzResearch.WordTrace tailWord_431354 prefixEnd_431354 32813619887349712472777 := by
  unfold tailWord_431354
  simp only [CollatzResearch.WordTrace]
  refine ⟨3933193219821400560797279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10488515252857068162126077 3933193219821400560797279)
  ·
    refine ⟨5899789829732100841195919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3933193219821400560797279 5899789829732100841195919)
    ·
      refine ⟨8849684744598151261793879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5899789829732100841195919 8849684744598151261793879)
      ·
        refine ⟨13274527116897226892690819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8849684744598151261793879 13274527116897226892690819)
        ·
          refine ⟨19911790675345840339036229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13274527116897226892690819 19911790675345840339036229)
          ·
            refine ⟨3733460751627345063569293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19911790675345840339036229 3733460751627345063569293)
            ·
              refine ⟨1400047781860254398838485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3733460751627345063569293 1400047781860254398838485)
              ·
                refine ⟨32813619887349712472777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1400047781860254398838485 32813619887349712472777)
                ·
                  rfl

theorem cell21_431354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_431354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_431354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_431354 prefixEnd_431354 := by exact prefixLift 431354
  have htrace : WordTrace (prefixWord ++ tailWord_431354) baseStart_431354 baseEnd_431354 := by
    simpa [prefixWord, tailWord_431354, baseEnd_431354] using wordTrace_append hprefix tailTrace_431354
  have hstable : (prefixWord ++ tailWord_431354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431354).length < 2 ^ (prefixWord ++ tailWord_431354).sum := by decide
  have hdescent : baseEnd_431354 < baseStart_431354 := by decide
  rcases family_descends (prefixWord ++ tailWord_431354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431391 : List Nat := [1, 1, 2, 4, 5, 1, 2, 1, 4]
def baseStart_431391 : Nat := 118140960795 + 431391 * 2 ^ 59
def prefixEnd_431391 : Nat := 4983230072969 + 3 ^ 40 * 431391 * 2
def baseEnd_431391 : Nat := 98449303566145295301589

theorem tailTrace_431391 : CollatzResearch.WordTrace tailWord_431391 prefixEnd_431391 98449303566145295301589 := by
  unfold tailWord_431391
  simp only [CollatzResearch.WordTrace]
  refine ⟨15734122380151557562286027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10489414920101038374857351 15734122380151557562286027)
  ·
    refine ⟨23601183570227336343429041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15734122380151557562286027 23601183570227336343429041)
    ·
      refine ⟨17700887677670502257571781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23601183570227336343429041 17700887677670502257571781)
      ·
        refine ⟨3318916439563219173294709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17700887677670502257571781 3318916439563219173294709)
        ·
          refine ⟨311148416209051797496379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3318916439563219173294709 311148416209051797496379)
          ·
            refine ⟨466722624313577696244569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311148416209051797496379 466722624313577696244569)
            ·
              refine ⟨350041968235183272183427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466722624313577696244569 350041968235183272183427)
              ·
                refine ⟨525062952352774908275141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350041968235183272183427 525062952352774908275141)
                ·
                  refine ⟨98449303566145295301589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 525062952352774908275141 98449303566145295301589)
                  ·
                    rfl

theorem cell21_431391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 4].length) (baseStart_431391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_431391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_431391 prefixEnd_431391 := by exact prefixLift 431391
  have htrace : WordTrace (prefixWord ++ tailWord_431391) baseStart_431391 baseEnd_431391 := by
    simpa [prefixWord, tailWord_431391, baseEnd_431391] using wordTrace_append hprefix tailTrace_431391
  have hstable : (prefixWord ++ tailWord_431391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431391).length < 2 ^ (prefixWord ++ tailWord_431391).sum := by decide
  have hdescent : baseEnd_431391 < baseStart_431391 := by decide
  rcases family_descends (prefixWord ++ tailWord_431391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431436 : List Nat := [2, 2, 1, 3, 2, 4, 2, 2, 3]
def baseStart_431436 : Nat := 118140960795 + 431436 * 2 ^ 59
def prefixEnd_431436 : Nat := 4983230072969 + 3 ^ 40 * 431436 * 2
def baseEnd_431436 : Nat := 98459573179235217051497

theorem tailTrace_431436 : CollatzResearch.WordTrace tailWord_431436 prefixEnd_431436 98459573179235217051497 := by
  unfold tailWord_431436
  simp only [CollatzResearch.WordTrace]
  refine ⟨7867881832494265123837081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10490509109992353498449441 7867881832494265123837081)
  ·
    refine ⟨5900911374370698842877811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7867881832494265123837081 5900911374370698842877811)
    ·
      refine ⟨8851367061556048264316717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5900911374370698842877811 8851367061556048264316717)
      ·
        refine ⟨3319262648083518099118769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8851367061556048264316717 3319262648083518099118769)
        ·
          refine ⟨2489446986062638574339077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3319262648083518099118769 2489446986062638574339077)
          ·
            refine ⟨466771309886744732688577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2489446986062638574339077 466771309886744732688577)
            ·
              refine ⟨350078482415058549516433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466771309886744732688577 350078482415058549516433)
              ·
                refine ⟨262558861811293912137325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350078482415058549516433 262558861811293912137325)
                ·
                  refine ⟨98459573179235217051497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262558861811293912137325 98459573179235217051497)
                  ·
                    rfl

theorem cell21_431436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_431436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_431436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_431436 prefixEnd_431436 := by exact prefixLift 431436
  have htrace : WordTrace (prefixWord ++ tailWord_431436) baseStart_431436 baseEnd_431436 := by
    simpa [prefixWord, tailWord_431436, baseEnd_431436] using wordTrace_append hprefix tailTrace_431436
  have hstable : (prefixWord ++ tailWord_431436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431436).length < 2 ^ (prefixWord ++ tailWord_431436).sum := by decide
  have hdescent : baseEnd_431436 < baseStart_431436 := by decide
  rcases family_descends (prefixWord ++ tailWord_431436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431447 : List Nat := [1, 1, 3, 2, 3, 4, 1, 6]
def baseStart_431447 : Nat := 118140960795 + 431447 * 2 ^ 59
def prefixEnd_431447 : Nat := 4983230072969 + 3 ^ 40 * 431447 * 2
def baseEnd_431447 : Nat := 32820694509700547456047

theorem tailTrace_431447 : CollatzResearch.WordTrace tailWord_431447 prefixEnd_431447 32820694509700547456047 := by
  unfold tailWord_431447
  simp only [CollatzResearch.WordTrace]
  refine ⟨15736164867948679126324595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10490776578632452750883063 15736164867948679126324595)
  ·
    refine ⟨23604247301923018689486893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15736164867948679126324595 23604247301923018689486893)
    ·
      refine ⟨8851592738221132008557585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23604247301923018689486893 8851592738221132008557585)
      ·
        refine ⟨6638694553665849006418189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8851592738221132008557585 6638694553665849006418189)
        ·
          refine ⟨2489510457624693377406821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6638694553665849006418189 2489510457624693377406821)
          ·
            refine ⟨466783210804630008263779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2489510457624693377406821 466783210804630008263779)
            ·
              refine ⟨700174816206945012395669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466783210804630008263779 700174816206945012395669)
              ·
                refine ⟨32820694509700547456047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 700174816206945012395669 32820694509700547456047)
                ·
                  rfl

theorem cell21_431447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 6].length) (baseStart_431447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_431447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_431447 prefixEnd_431447 := by exact prefixLift 431447
  have htrace : WordTrace (prefixWord ++ tailWord_431447) baseStart_431447 baseEnd_431447 := by
    simpa [prefixWord, tailWord_431447, baseEnd_431447] using wordTrace_append hprefix tailTrace_431447
  have hstable : (prefixWord ++ tailWord_431447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431447).length < 2 ^ (prefixWord ++ tailWord_431447).sum := by decide
  have hdescent : baseEnd_431447 < baseStart_431447 := by decide
  rcases family_descends (prefixWord ++ tailWord_431447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431461 : List Nat := [1, 3, 1, 3, 1, 2, 3, 2, 5]
def baseStart_431461 : Nat := 118140960795 + 431461 * 2 ^ 59
def prefixEnd_431461 : Nat := 4983230072969 + 3 ^ 40 * 431461 * 2
def baseEnd_431461 : Nat := 98465278519840729134779

theorem tailTrace_431461 : CollatzResearch.WordTrace tailWord_431461 prefixEnd_431461 98465278519840729134779 := by
  unfold tailWord_431461
  simp only [CollatzResearch.WordTrace]
  refine ⟨15736675489897959517334237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10491116993265306344889491 15736675489897959517334237)
  ·
    refine ⟨5901253308711734819000339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15736675489897959517334237 5901253308711734819000339)
    ·
      refine ⟨8851879963067602228500509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5901253308711734819000339 8851879963067602228500509)
      ·
        refine ⟨3319454986150350835687691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8851879963067602228500509 3319454986150350835687691)
        ·
          refine ⟨4979182479225526253531537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3319454986150350835687691 4979182479225526253531537)
          ·
            refine ⟨3734386859419144690148653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4979182479225526253531537 3734386859419144690148653)
            ·
              refine ⟨1400395072282179258805745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3734386859419144690148653 1400395072282179258805745)
              ·
                refine ⟨1050296304211634444104309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1400395072282179258805745 1050296304211634444104309)
                ·
                  refine ⟨98465278519840729134779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1050296304211634444104309 98465278519840729134779)
                  ·
                    rfl

theorem cell21_431461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_431461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_431461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_431461 prefixEnd_431461 := by exact prefixLift 431461
  have htrace : WordTrace (prefixWord ++ tailWord_431461) baseStart_431461 baseEnd_431461 := by
    simpa [prefixWord, tailWord_431461, baseEnd_431461] using wordTrace_append hprefix tailTrace_431461
  have hstable : (prefixWord ++ tailWord_431461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431461).length < 2 ^ (prefixWord ++ tailWord_431461).sum := by decide
  have hdescent : baseEnd_431461 < baseStart_431461 := by decide
  rcases family_descends (prefixWord ++ tailWord_431461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431464 : List Nat := [2, 1, 4, 2, 3, 1, 3, 5]
def baseStart_431464 : Nat := 118140960795 + 431464 * 2 ^ 59
def prefixEnd_431464 : Nat := 4983230072969 + 3 ^ 40 * 431464 * 2
def baseEnd_431464 : Nat := 32821987720237796861591

theorem tailTrace_431464 : CollatzResearch.WordTrace tailWord_431464 prefixEnd_431464 32821987720237796861591 := by
  unfold tailWord_431464
  simp only [CollatzResearch.WordTrace]
  refine ⟨7868392454443545514846723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10491189939258060686462297 7868392454443545514846723)
  ·
    refine ⟨11802588681665318272270085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7868392454443545514846723 11802588681665318272270085)
    ·
      refine ⟨2212985377812247176050641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11802588681665318272270085 2212985377812247176050641)
      ·
        refine ⟨1659739033359185382037981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2212985377812247176050641 1659739033359185382037981)
        ·
          refine ⟨622402137509694518264243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1659739033359185382037981 622402137509694518264243)
          ·
            refine ⟨933603206264541777396365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622402137509694518264243 933603206264541777396365)
            ·
              refine ⟨350101202349203166523637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 933603206264541777396365 350101202349203166523637)
              ·
                refine ⟨32821987720237796861591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 350101202349203166523637 32821987720237796861591)
                ·
                  rfl

theorem cell21_431464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 5].length) (baseStart_431464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_431464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_431464 prefixEnd_431464 := by exact prefixLift 431464
  have htrace : WordTrace (prefixWord ++ tailWord_431464) baseStart_431464 baseEnd_431464 := by
    simpa [prefixWord, tailWord_431464, baseEnd_431464] using wordTrace_append hprefix tailTrace_431464
  have hstable : (prefixWord ++ tailWord_431464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431464).length < 2 ^ (prefixWord ++ tailWord_431464).sum := by decide
  have hdescent : baseEnd_431464 < baseStart_431464 := by decide
  rcases family_descends (prefixWord ++ tailWord_431464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431492 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 6]
def baseStart_431492 : Nat := 118140960795 + 431492 * 2 ^ 59
def prefixEnd_431492 : Nat := 4983230072969 + 3 ^ 40 * 431492 * 2
def baseEnd_431492 : Nat := 98472353142191564118049

theorem tailTrace_431492 : CollatzResearch.WordTrace tailWord_431492 prefixEnd_431492 98472353142191564118049 := by
  unfold tailWord_431492
  simp only [CollatzResearch.WordTrace]
  refine ⟨7868903076392825905856365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10491870768523767874475153 7868903076392825905856365)
  ·
    refine ⟨2950838653647309714696137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7868903076392825905856365 2950838653647309714696137)
    ·
      refine ⟨2213128990235482286022103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2950838653647309714696137 2213128990235482286022103)
      ·
        refine ⟨3319693485353223429033155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2213128990235482286022103 3319693485353223429033155)
        ·
          refine ⟨4979540228029835143549733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3319693485353223429033155 4979540228029835143549733)
          ·
            refine ⟨933663792755594089415575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4979540228029835143549733 933663792755594089415575)
            ·
              refine ⟨1400495689133391134123363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 933663792755594089415575 1400495689133391134123363)
              ·
                refine ⟨2100743533700086701185045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1400495689133391134123363 2100743533700086701185045)
                ·
                  refine ⟨98472353142191564118049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2100743533700086701185045 98472353142191564118049)
                  ·
                    rfl

theorem cell21_431492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_431492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_431492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_431492 prefixEnd_431492 := by exact prefixLift 431492
  have htrace : WordTrace (prefixWord ++ tailWord_431492) baseStart_431492 baseEnd_431492 := by
    simpa [prefixWord, tailWord_431492, baseEnd_431492] using wordTrace_append hprefix tailTrace_431492
  have hstable : (prefixWord ++ tailWord_431492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431492).length < 2 ^ (prefixWord ++ tailWord_431492).sum := by decide
  have hdescent : baseEnd_431492 < baseStart_431492 := by decide
  rcases family_descends (prefixWord ++ tailWord_431492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431596 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 9]
def baseStart_431596 : Nat := 118140960795 + 431596 * 2 ^ 59
def prefixEnd_431596 : Nat := 4983230072969 + 3 ^ 40 * 431596 * 2
def baseEnd_431596 : Nat := 98496087359110494384503

theorem tailTrace_431596 : CollatzResearch.WordTrace tailWord_431596 prefixEnd_431596 98496087359110494384503 := by
  unfold tailWord_431596
  simp only [CollatzResearch.WordTrace]
  refine ⟨7870799672204438786749321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10494399562939251715665761 7870799672204438786749321)
  ·
    refine ⟨5903099754153329090061991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7870799672204438786749321 5903099754153329090061991)
    ·
      refine ⟨8854649631229993635092987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5903099754153329090061991 8854649631229993635092987)
      ·
        refine ⟨13281974446844990452639481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8854649631229993635092987 13281974446844990452639481)
        ·
          refine ⟨9961480835133742839479611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13281974446844990452639481 9961480835133742839479611)
          ·
            refine ⟨14942221252700614259219417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9961480835133742839479611 14942221252700614259219417)
            ·
              refine ⟨11206665939525460694414563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14942221252700614259219417 11206665939525460694414563)
              ·
                refine ⟨16809998909288191041621845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11206665939525460694414563 16809998909288191041621845)
                ·
                  refine ⟨98496087359110494384503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16809998909288191041621845 98496087359110494384503)
                  ·
                    rfl

theorem cell21_431596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_431596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_431596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_431596 prefixEnd_431596 := by exact prefixLift 431596
  have htrace : WordTrace (prefixWord ++ tailWord_431596) baseStart_431596 baseEnd_431596 := by
    simpa [prefixWord, tailWord_431596, baseEnd_431596] using wordTrace_append hprefix tailTrace_431596
  have hstable : (prefixWord ++ tailWord_431596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431596).length < 2 ^ (prefixWord ++ tailWord_431596).sum := by decide
  have hdescent : baseEnd_431596 < baseStart_431596 := by decide
  rcases family_descends (prefixWord ++ tailWord_431596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431605 : List Nat := [1, 3, 5, 1, 1, 3, 2, 2, 3]
def baseStart_431605 : Nat := 118140960795 + 431605 * 2 ^ 59
def prefixEnd_431605 : Nat := 4983230072969 + 3 ^ 40 * 431605 * 2
def baseEnd_431605 : Nat := 98498141281728478734485

theorem tailTrace_431605 : CollatzResearch.WordTrace tailWord_431605 prefixEnd_431605 98498141281728478734485 := by
  unfold tailWord_431605
  simp only [CollatzResearch.WordTrace]
  refine ⟨15741927601376272110576269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10494618400917514740384179 15741927601376272110576269)
  ·
    refine ⟨5903222850516102041466101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15741927601376272110576269 5903222850516102041466101)
    ·
      refine ⟨553427142235884566387447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5903222850516102041466101 553427142235884566387447)
      ·
        refine ⟨830140713353826849581171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553427142235884566387447 830140713353826849581171)
        ·
          refine ⟨1245211070030740274371757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830140713353826849581171 1245211070030740274371757)
          ·
            refine ⟨466954151261527602889409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1245211070030740274371757 466954151261527602889409)
            ·
              refine ⟨350215613446145702167057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466954151261527602889409 350215613446145702167057)
              ·
                refine ⟨262661710084609276625293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350215613446145702167057 262661710084609276625293)
                ·
                  refine ⟨98498141281728478734485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262661710084609276625293 98498141281728478734485)
                  ·
                    rfl

theorem cell21_431605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_431605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_431605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_431605 prefixEnd_431605 := by exact prefixLift 431605
  have htrace : WordTrace (prefixWord ++ tailWord_431605) baseStart_431605 baseEnd_431605 := by
    simpa [prefixWord, tailWord_431605, baseEnd_431605] using wordTrace_append hprefix tailTrace_431605
  have hstable : (prefixWord ++ tailWord_431605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431605).length < 2 ^ (prefixWord ++ tailWord_431605).sum := by decide
  have hdescent : baseEnd_431605 < baseStart_431605 := by decide
  rcases family_descends (prefixWord ++ tailWord_431605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431630 : List Nat := [4, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_431630 : Nat := 118140960795 + 431630 * 2 ^ 59
def prefixEnd_431630 : Nat := 4983230072969 + 3 ^ 40 * 431630 * 2
def baseEnd_431630 : Nat := 98503846622333990817767

theorem tailTrace_431630 : CollatzResearch.WordTrace tailWord_431630 prefixEnd_431630 98503846622333990817767 := by
  unfold tailWord_431630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1967854928285712672529543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10495226284190467586824229 1967854928285712672529543)
  ·
    refine ⟨2951782392428569008794315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1967854928285712672529543 2951782392428569008794315)
    ·
      refine ⟨4427673588642853513191473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2951782392428569008794315 4427673588642853513191473)
      ·
        refine ⟨3320755191482140134893605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4427673588642853513191473 3320755191482140134893605)
        ·
          refine ⟨622641598402901275292551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3320755191482140134893605 622641598402901275292551)
          ·
            refine ⟨933962397604351912938827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622641598402901275292551 933962397604351912938827)
            ·
              refine ⟨1400943596406527869408241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 933962397604351912938827 1400943596406527869408241)
              ·
                refine ⟨1050707697304895902056181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1400943596406527869408241 1050707697304895902056181)
                ·
                  refine ⟨98503846622333990817767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1050707697304895902056181 98503846622333990817767)
                  ·
                    rfl

theorem cell21_431630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_431630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_431630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_431630 prefixEnd_431630 := by exact prefixLift 431630
  have htrace : WordTrace (prefixWord ++ tailWord_431630) baseStart_431630 baseEnd_431630 := by
    simpa [prefixWord, tailWord_431630, baseEnd_431630] using wordTrace_append hprefix tailTrace_431630
  have hstable : (prefixWord ++ tailWord_431630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431630).length < 2 ^ (prefixWord ++ tailWord_431630).sum := by decide
  have hdescent : baseEnd_431630 < baseStart_431630 := by decide
  rcases family_descends (prefixWord ++ tailWord_431630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431658 : List Nat := [3, 1, 4, 1, 1, 1, 10]
def baseStart_431658 : Nat := 118140960795 + 431658 * 2 ^ 59
def prefixEnd_431658 : Nat := 4983230072969 + 3 ^ 40 * 431658 * 2
def baseEnd_431658 : Nat := 10945581844868018261227

theorem tailTrace_431658 : CollatzResearch.WordTrace tailWord_431658 prefixEnd_431658 10945581844868018261227 := by
  unfold tailWord_431658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3935965167546065540563907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10495907113456174774837085 3935965167546065540563907)
  ·
    refine ⟨5903947751319098310845861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3935965167546065540563907 5903947751319098310845861)
    ·
      refine ⟨1106990203372330933283599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5903947751319098310845861 1106990203372330933283599)
      ·
        refine ⟨1660485305058496399925399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1106990203372330933283599 1660485305058496399925399)
        ·
          refine ⟨2490727957587744599888099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1660485305058496399925399 2490727957587744599888099)
          ·
            refine ⟨3736091936381616899832149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490727957587744599888099 3736091936381616899832149)
            ·
              refine ⟨10945581844868018261227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3736091936381616899832149 10945581844868018261227)
              ·
                rfl

theorem cell21_431658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 10].length) (baseStart_431658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_431658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_431658 prefixEnd_431658 := by exact prefixLift 431658
  have htrace : WordTrace (prefixWord ++ tailWord_431658) baseStart_431658 baseEnd_431658 := by
    simpa [prefixWord, tailWord_431658, baseEnd_431658] using wordTrace_append hprefix tailTrace_431658
  have hstable : (prefixWord ++ tailWord_431658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431658).length < 2 ^ (prefixWord ++ tailWord_431658).sum := by decide
  have hdescent : baseEnd_431658 < baseStart_431658 := by decide
  rcases family_descends (prefixWord ++ tailWord_431658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431703 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 6]
def baseStart_431703 : Nat := 118140960795 + 431703 * 2 ^ 59
def prefixEnd_431703 : Nat := 4983230072969 + 3 ^ 40 * 431703 * 2
def baseEnd_431703 : Nat := 98520506216902086100951

theorem tailTrace_431703 : CollatzResearch.WordTrace tailWord_431703 prefixEnd_431703 98520506216902086100951 := by
  unfold tailWord_431703
  simp only [CollatzResearch.WordTrace]
  refine ⟨15745501955021234847643763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10497001303347489898429175 15745501955021234847643763)
  ·
    refine ⟨23618252932531852271465645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15745501955021234847643763 23618252932531852271465645)
    ·
      refine ⟨8856844849699444601799617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23618252932531852271465645 8856844849699444601799617)
      ·
        refine ⟨6642633637274583451349713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8856844849699444601799617 6642633637274583451349713)
        ·
          refine ⟨4981975227955937588512285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6642633637274583451349713 4981975227955937588512285)
          ·
            refine ⟨1868240710483476595692107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4981975227955937588512285 1868240710483476595692107)
            ·
              refine ⟨2802361065725214893538161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868240710483476595692107 2802361065725214893538161)
              ·
                refine ⟨2101770799293911170153621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2802361065725214893538161 2101770799293911170153621)
                ·
                  refine ⟨98520506216902086100951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2101770799293911170153621 98520506216902086100951)
                  ·
                    rfl

theorem cell21_431703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 6].length) (baseStart_431703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_431703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_431703 prefixEnd_431703 := by exact prefixLift 431703
  have htrace : WordTrace (prefixWord ++ tailWord_431703) baseStart_431703 baseEnd_431703 := by
    simpa [prefixWord, tailWord_431703, baseEnd_431703] using wordTrace_append hprefix tailTrace_431703
  have hstable : (prefixWord ++ tailWord_431703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431703).length < 2 ^ (prefixWord ++ tailWord_431703).sum := by decide
  have hdescent : baseEnd_431703 < baseStart_431703 := by decide
  rcases family_descends (prefixWord ++ tailWord_431703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431709 : List Nat := [1, 4, 4, 2, 2, 1, 7]
def baseStart_431709 : Nat := 118140960795 + 431709 * 2 ^ 59
def prefixEnd_431709 : Nat := 4983230072969 + 3 ^ 40 * 431709 * 2
def baseEnd_431709 : Nat := 10946875055405267666771

theorem tailTrace_431709 : CollatzResearch.WordTrace tailWord_431709 prefixEnd_431709 10946875055405267666771 := by
  unfold tailWord_431709
  simp only [CollatzResearch.WordTrace]
  refine ⟨15745720792999497872362181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10497147195332998581574787 15745720792999497872362181)
  ·
    refine ⟨2952322648687405851067909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15745720792999497872362181 2952322648687405851067909)
    ·
      refine ⟨553560496628888597075233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2952322648687405851067909 553560496628888597075233)
      ·
        refine ⟨415170372471666447806425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 553560496628888597075233 415170372471666447806425)
        ·
          refine ⟨311377779353749835854819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415170372471666447806425 311377779353749835854819)
          ·
            refine ⟨467066669030624753782229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311377779353749835854819 467066669030624753782229)
            ·
              refine ⟨10946875055405267666771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 467066669030624753782229 10946875055405267666771)
              ·
                rfl

theorem cell21_431709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 7].length) (baseStart_431709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_431709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_431709 prefixEnd_431709 := by exact prefixLift 431709
  have htrace : WordTrace (prefixWord ++ tailWord_431709) baseStart_431709 baseEnd_431709 := by
    simpa [prefixWord, tailWord_431709, baseEnd_431709] using wordTrace_append hprefix tailTrace_431709
  have hstable : (prefixWord ++ tailWord_431709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431709).length < 2 ^ (prefixWord ++ tailWord_431709).sum := by decide
  have hdescent : baseEnd_431709 < baseStart_431709 := by decide
  rcases family_descends (prefixWord ++ tailWord_431709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431720 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 6]
def baseStart_431720 : Nat := 118140960795 + 431720 * 2 ^ 59
def prefixEnd_431720 : Nat := 4983230072969 + 3 ^ 40 * 431720 * 2
def baseEnd_431720 : Nat := 98524385848513834317583

theorem tailTrace_431720 : CollatzResearch.WordTrace tailWord_431720 prefixEnd_431720 98524385848513834317583 := by
  unfold tailWord_431720
  simp only [CollatzResearch.WordTrace]
  refine ⟨7873060997979823375506307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10497414663973097834008409 7873060997979823375506307)
  ·
    refine ⟨11809591496969735063259461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7873060997979823375506307 11809591496969735063259461)
    ·
      refine ⟨2214298405681825324361149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11809591496969735063259461 2214298405681825324361149)
      ·
        refine ⟨830361902130684496635431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2214298405681825324361149 830361902130684496635431)
        ·
          refine ⟨1245542853196026744953147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830361902130684496635431 1245542853196026744953147)
          ·
            refine ⟨1868314279794040117429721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245542853196026744953147 1868314279794040117429721)
            ·
              refine ⟨1401235709845530088072291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1868314279794040117429721 1401235709845530088072291)
              ·
                refine ⟨2101853564768295132108437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401235709845530088072291 2101853564768295132108437)
                ·
                  refine ⟨98524385848513834317583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2101853564768295132108437 98524385848513834317583)
                  ·
                    rfl

theorem cell21_431720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_431720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_431720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_431720 prefixEnd_431720 := by exact prefixLift 431720
  have htrace : WordTrace (prefixWord ++ tailWord_431720) baseStart_431720 baseEnd_431720 := by
    simpa [prefixWord, tailWord_431720, baseEnd_431720] using wordTrace_append hprefix tailTrace_431720
  have hstable : (prefixWord ++ tailWord_431720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431720).length < 2 ^ (prefixWord ++ tailWord_431720).sum := by decide
  have hdescent : baseEnd_431720 < baseStart_431720 := by decide
  rcases family_descends (prefixWord ++ tailWord_431720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431830 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_431830 : Nat := 118140960795 + 431830 * 2 ^ 59
def prefixEnd_431830 : Nat := 4983230072969 + 3 ^ 40 * 431830 * 2
def baseEnd_431830 : Nat := 98549489347178087484025

theorem tailTrace_431830 : CollatzResearch.WordTrace tailWord_431830 prefixEnd_431830 98549489347178087484025 := by
  unfold tailWord_431830
  simp only [CollatzResearch.WordTrace]
  refine ⟨984383376597570971094809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10500089350374090358344629 984383376597570971094809)
  ·
    refine ⟨738287532448178228321107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 984383376597570971094809 738287532448178228321107)
    ·
      refine ⟨1107431298672267342481661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 738287532448178228321107 1107431298672267342481661)
      ·
        refine ⟨415286737002100253430623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1107431298672267342481661 415286737002100253430623)
        ·
          refine ⟨622930105503150380145935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415286737002100253430623 622930105503150380145935)
          ·
            refine ⟨934395158254725570218903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622930105503150380145935 934395158254725570218903)
            ·
              refine ⟨1401592737382088355328355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934395158254725570218903 1401592737382088355328355)
              ·
                refine ⟨2102389106073132532992533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401592737382088355328355 2102389106073132532992533)
                ·
                  refine ⟨98549489347178087484025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2102389106073132532992533 98549489347178087484025)
                  ·
                    rfl

theorem cell21_431830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_431830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_431830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_431830 prefixEnd_431830 := by exact prefixLift 431830
  have htrace : WordTrace (prefixWord ++ tailWord_431830) baseStart_431830 baseEnd_431830 := by
    simpa [prefixWord, tailWord_431830, baseEnd_431830] using wordTrace_append hprefix tailTrace_431830
  have hstable : (prefixWord ++ tailWord_431830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431830).length < 2 ^ (prefixWord ++ tailWord_431830).sum := by decide
  have hdescent : baseEnd_431830 < baseStart_431830 := by decide
  rcases family_descends (prefixWord ++ tailWord_431830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432010 : List Nat := [3, 1, 2, 4, 2, 1, 2, 1, 5]
def baseStart_432010 : Nat := 118140960795 + 432010 * 2 ^ 59
def prefixEnd_432010 : Nat := 4983230072969 + 3 ^ 40 * 432010 * 2
def baseEnd_432010 : Nat := 98590567799537774483657

theorem tailTrace_432010 : CollatzResearch.WordTrace tailWord_432010 prefixEnd_432010 98590567799537774483657 := by
  unfold tailWord_432010
  simp only [CollatzResearch.WordTrace]
  refine ⟨3939174791227256569767371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10504466109939350852712989 3939174791227256569767371)
  ·
    refine ⟨5908762186840884854651057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3939174791227256569767371 5908762186840884854651057)
    ·
      refine ⟨4431571640130663640988293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5908762186840884854651057 4431571640130663640988293)
      ·
        refine ⟨830919682524499432685305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4431571640130663640988293 830919682524499432685305)
        ·
          refine ⟨623189761893374574513979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 830919682524499432685305 623189761893374574513979)
          ·
            refine ⟨934784642840061861770969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623189761893374574513979 934784642840061861770969)
            ·
              refine ⟨701088482130046396328227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 934784642840061861770969 701088482130046396328227)
              ·
                refine ⟨1051632723195069594492341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701088482130046396328227 1051632723195069594492341)
                ·
                  refine ⟨98590567799537774483657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1051632723195069594492341 98590567799537774483657)
                  ·
                    rfl

theorem cell21_432010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_432010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432010 prefixEnd_432010 := by exact prefixLift 432010
  have htrace : WordTrace (prefixWord ++ tailWord_432010) baseStart_432010 baseEnd_432010 := by
    simpa [prefixWord, tailWord_432010, baseEnd_432010] using wordTrace_append hprefix tailTrace_432010
  have hstable : (prefixWord ++ tailWord_432010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432010).length < 2 ^ (prefixWord ++ tailWord_432010).sum := by decide
  have hdescent : baseEnd_432010 < baseStart_432010 := by decide
  rcases family_descends (prefixWord ++ tailWord_432010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432021 : List Nat := [1, 3, 2, 1, 1, 3, 2, 8]
def baseStart_432021 : Nat := 118140960795 + 432021 * 2 ^ 59
def prefixEnd_432021 : Nat := 4983230072969 + 3 ^ 40 * 432021 * 2
def baseEnd_432021 : Nat := 32864359383134733266767

theorem tailTrace_432021 : CollatzResearch.WordTrace tailWord_432021 prefixEnd_432021 32864359383134733266767 := by
  unfold tailWord_432021
  simp only [CollatzResearch.WordTrace]
  refine ⟨15757100367869175157719917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10504733578579450105146611 15757100367869175157719917)
  ·
    refine ⟨5908912637950940684144969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15757100367869175157719917 5908912637950940684144969)
    ·
      refine ⟨4431684478463205513108727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5908912637950940684144969 4431684478463205513108727)
      ·
        refine ⟨6647526717694808269663091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4431684478463205513108727 6647526717694808269663091)
        ·
          refine ⟨9971290076542212404494637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6647526717694808269663091 9971290076542212404494637)
          ·
            refine ⟨3739233778703329651685489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9971290076542212404494637 3739233778703329651685489)
            ·
              refine ⟨2804425334027497238764117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3739233778703329651685489 2804425334027497238764117)
              ·
                refine ⟨32864359383134733266767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2804425334027497238764117 32864359383134733266767)
                ·
                  rfl

theorem cell21_432021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 8].length) (baseStart_432021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432021 prefixEnd_432021 := by exact prefixLift 432021
  have htrace : WordTrace (prefixWord ++ tailWord_432021) baseStart_432021 baseEnd_432021 := by
    simpa [prefixWord, tailWord_432021, baseEnd_432021] using wordTrace_append hprefix tailTrace_432021
  have hstable : (prefixWord ++ tailWord_432021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432021).length < 2 ^ (prefixWord ++ tailWord_432021).sum := by decide
  have hdescent : baseEnd_432021 < baseStart_432021 := by decide
  rcases family_descends (prefixWord ++ tailWord_432021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432030 : List Nat := [4, 3, 1, 3, 2, 1, 2, 5]
def baseStart_432030 : Nat := 118140960795 + 432030 * 2 ^ 59
def prefixEnd_432030 : Nat := 4983230072969 + 3 ^ 40 * 432030 * 2
def baseEnd_432030 : Nat := 32865044024007394716761

theorem tailTrace_432030 : CollatzResearch.WordTrace tailWord_432030 prefixEnd_432030 32865044024007394716761 := by
  unfold tailWord_432030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1969678578104571211849693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10504952416557713129865029 1969678578104571211849693)
  ·
    refine ⟨738629466789214204443635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1969678578104571211849693 738629466789214204443635)
    ·
      refine ⟨1107944200183821306665453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 738629466789214204443635 1107944200183821306665453)
      ·
        refine ⟨415479075068932989999545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1107944200183821306665453 415479075068932989999545)
        ·
          refine ⟨311609306301699742499659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415479075068932989999545 311609306301699742499659)
          ·
            refine ⟨467413959452549613749489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311609306301699742499659 467413959452549613749489)
            ·
              refine ⟨350560469589412210312117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467413959452549613749489 350560469589412210312117)
              ·
                refine ⟨32865044024007394716761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 350560469589412210312117 32865044024007394716761)
                ·
                  rfl

theorem cell21_432030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_432030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432030 prefixEnd_432030 := by exact prefixLift 432030
  have htrace : WordTrace (prefixWord ++ tailWord_432030) baseStart_432030 baseEnd_432030 := by
    simpa [prefixWord, tailWord_432030, baseEnd_432030] using wordTrace_append hprefix tailTrace_432030
  have hstable : (prefixWord ++ tailWord_432030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432030).length < 2 ^ (prefixWord ++ tailWord_432030).sum := by decide
  have hdescent : baseEnd_432030 < baseStart_432030 := by decide
  rcases family_descends (prefixWord ++ tailWord_432030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432097 : List Nat := [1, 2, 3, 1, 2, 1, 4, 7]
def baseStart_432097 : Nat := 118140960795 + 432097 * 2 ^ 59
def prefixEnd_432097 : Nat := 4983230072969 + 3 ^ 40 * 432097 * 2
def baseEnd_432097 : Nat := 32870140794948318844493

theorem tailTrace_432097 : CollatzResearch.WordTrace tailWord_432097 prefixEnd_432097 32870140794948318844493 := by
  unfold tailWord_432097
  simp only [CollatzResearch.WordTrace]
  refine ⟨15759872315593840137486545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10506581543729226758324363 15759872315593840137486545)
  ·
    refine ⟨11819904236695380103114909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15759872315593840137486545 11819904236695380103114909)
    ·
      refine ⟨4432464088760767538668091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11819904236695380103114909 4432464088760767538668091)
      ·
        refine ⟨6648696133141151308002137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4432464088760767538668091 6648696133141151308002137)
        ·
          refine ⟨4986522099855863481001603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6648696133141151308002137 4986522099855863481001603)
          ·
            refine ⟨7479783149783795221502405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4986522099855863481001603 7479783149783795221502405)
            ·
              refine ⟨1402459340584461604031701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7479783149783795221502405 1402459340584461604031701)
              ·
                refine ⟨32870140794948318844493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1402459340584461604031701 32870140794948318844493)
                ·
                  rfl

theorem cell21_432097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 7].length) (baseStart_432097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432097 prefixEnd_432097 := by exact prefixLift 432097
  have htrace : WordTrace (prefixWord ++ tailWord_432097) baseStart_432097 baseEnd_432097 := by
    simpa [prefixWord, tailWord_432097, baseEnd_432097] using wordTrace_append hprefix tailTrace_432097
  have hstable : (prefixWord ++ tailWord_432097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432097).length < 2 ^ (prefixWord ++ tailWord_432097).sum := by decide
  have hdescent : baseEnd_432097 < baseStart_432097 := by decide
  rcases family_descends (prefixWord ++ tailWord_432097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432162 : List Nat := [3, 3, 1, 1, 1, 2, 4, 3, 3]
def baseStart_432162 : Nat := 118140960795 + 432162 * 2 ^ 59
def prefixEnd_432162 : Nat := 4983230072969 + 3 ^ 40 * 432162 * 2
def baseEnd_432162 : Nat := 98625256270419287950013

theorem tailTrace_432162 : CollatzResearch.WordTrace tailWord_432162 prefixEnd_432162 98625256270419287950013 := by
  unfold tailWord_432162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3940560765089589059650685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10508162040238904159068493 3940560765089589059650685)
  ·
    refine ⟨1477710286908595897369007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3940560765089589059650685 1477710286908595897369007)
    ·
      refine ⟨2216565430362893846053511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1477710286908595897369007 2216565430362893846053511)
      ·
        refine ⟨3324848145544340769080267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2216565430362893846053511 3324848145544340769080267)
        ·
          refine ⟨4987272218316511153620401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3324848145544340769080267 4987272218316511153620401)
          ·
            refine ⟨3740454163737383365215301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4987272218316511153620401 3740454163737383365215301)
            ·
              refine ⟨701335155700759380977869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3740454163737383365215301 701335155700759380977869)
              ·
                refine ⟨263000683387784767866701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 701335155700759380977869 263000683387784767866701)
                ·
                  refine ⟨98625256270419287950013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263000683387784767866701 98625256270419287950013)
                  ·
                    rfl

theorem cell21_432162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_432162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432162 prefixEnd_432162 := by exact prefixLift 432162
  have htrace : WordTrace (prefixWord ++ tailWord_432162) baseStart_432162 baseEnd_432162 := by
    simpa [prefixWord, tailWord_432162, baseEnd_432162] using wordTrace_append hprefix tailTrace_432162
  have hstable : (prefixWord ++ tailWord_432162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432162).length < 2 ^ (prefixWord ++ tailWord_432162).sum := by decide
  have hdescent : baseEnd_432162 < baseStart_432162 := by decide
  rcases family_descends (prefixWord ++ tailWord_432162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432176 : List Nat := [2, 1, 1, 1, 2, 7, 1, 2, 4]
def baseStart_432176 : Nat := 118140960795 + 432176 * 2 ^ 59
def prefixEnd_432176 : Nat := 4983230072969 + 3 ^ 40 * 432176 * 2
def baseEnd_432176 : Nat := 98628451261158374716651

theorem tailTrace_432176 : CollatzResearch.WordTrace tailWord_432176 prefixEnd_432176 98628451261158374716651 := by
  unfold tailWord_432176
  simp only [CollatzResearch.WordTrace]
  refine ⟨7881376841153818314806191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10508502454871757753074921 7881376841153818314806191)
  ·
    refine ⟨11822065261730727472209287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7881376841153818314806191 11822065261730727472209287)
    ·
      refine ⟨17733097892596091208313931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11822065261730727472209287 17733097892596091208313931)
      ·
        refine ⟨26599646838894136812470897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17733097892596091208313931 26599646838894136812470897)
        ·
          refine ⟨19949735129170602609353173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26599646838894136812470897 19949735129170602609353173)
          ·
            refine ⟨467571917089935998656715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 19949735129170602609353173 467571917089935998656715)
            ·
              refine ⟨701357875634903997985073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467571917089935998656715 701357875634903997985073)
              ·
                refine ⟨526018406726177998488805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 701357875634903997985073 526018406726177998488805)
                ·
                  refine ⟨98628451261158374716651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 526018406726177998488805 98628451261158374716651)
                  ·
                    rfl

theorem cell21_432176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 4].length) (baseStart_432176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432176 prefixEnd_432176 := by exact prefixLift 432176
  have htrace : WordTrace (prefixWord ++ tailWord_432176) baseStart_432176 baseEnd_432176 := by
    simpa [prefixWord, tailWord_432176, baseEnd_432176] using wordTrace_append hprefix tailTrace_432176
  have hstable : (prefixWord ++ tailWord_432176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432176).length < 2 ^ (prefixWord ++ tailWord_432176).sum := by decide
  have hdescent : baseEnd_432176 < baseStart_432176 := by decide
  rcases family_descends (prefixWord ++ tailWord_432176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432187 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 9]
def baseStart_432187 : Nat := 118140960795 + 432187 * 2 ^ 59
def prefixEnd_432187 : Nat := 4983230072969 + 3 ^ 40 * 432187 * 2
def baseEnd_432187 : Nat := 98630961611024800033295

theorem tailTrace_432187 : CollatzResearch.WordTrace tailWord_432187 prefixEnd_432187 98630961611024800033295 := by
  unfold tailWord_432187
  simp only [CollatzResearch.WordTrace]
  refine ⟨15763154885267785508262815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10508769923511857005508543 15763154885267785508262815)
  ·
    refine ⟨23644732327901678262394223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15763154885267785508262815 23644732327901678262394223)
    ·
      refine ⟨35467098491852517393591335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23644732327901678262394223 35467098491852517393591335)
      ·
        refine ⟨53200647737778776090387003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35467098491852517393591335 53200647737778776090387003)
        ·
          refine ⟨79800971606668164135580505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53200647737778776090387003 79800971606668164135580505)
          ·
            refine ⟨59850728705001123101685379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79800971606668164135580505 59850728705001123101685379)
            ·
              refine ⟨89776093057501684652528069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59850728705001123101685379 89776093057501684652528069)
              ·
                refine ⟨16833017448281565872349013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89776093057501684652528069 16833017448281565872349013)
                ·
                  refine ⟨98630961611024800033295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16833017448281565872349013 98630961611024800033295)
                  ·
                    rfl

theorem cell21_432187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 9].length) (baseStart_432187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432187 prefixEnd_432187 := by exact prefixLift 432187
  have htrace : WordTrace (prefixWord ++ tailWord_432187) baseStart_432187 baseEnd_432187 := by
    simpa [prefixWord, tailWord_432187, baseEnd_432187] using wordTrace_append hprefix tailTrace_432187
  have hstable : (prefixWord ++ tailWord_432187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432187).length < 2 ^ (prefixWord ++ tailWord_432187).sum := by decide
  have hdescent : baseEnd_432187 < baseStart_432187 := by decide
  rcases family_descends (prefixWord ++ tailWord_432187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432193 : List Nat := [1, 2, 5, 1, 2, 2, 3, 1, 4]
def baseStart_432193 : Nat := 118140960795 + 432193 * 2 ^ 59
def prefixEnd_432193 : Nat := 4983230072969 + 3 ^ 40 * 432193 * 2
def baseEnd_432193 : Nat := 98632330892770122933283

theorem tailTrace_432193 : CollatzResearch.WordTrace tailWord_432193 prefixEnd_432193 98632330892770122933283 := by
  unfold tailWord_432193
  simp only [CollatzResearch.WordTrace]
  refine ⟨15763373723246048532981233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10508915815497365688654155 15763373723246048532981233)
  ·
    refine ⟨11822530292434536399735925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15763373723246048532981233 11822530292434536399735925)
    ·
      refine ⟨1108362214915737787475243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11822530292434536399735925 1108362214915737787475243)
      ·
        refine ⟨1662543322373606681212865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1108362214915737787475243 1662543322373606681212865)
        ·
          refine ⟨1246907491780205010909649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1662543322373606681212865 1246907491780205010909649)
          ·
            refine ⟨935180618835153758182237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1246907491780205010909649 935180618835153758182237)
            ·
              refine ⟨350692732063182659318339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 935180618835153758182237 350692732063182659318339)
              ·
                refine ⟨526039098094773988977509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350692732063182659318339 526039098094773988977509)
                ·
                  refine ⟨98632330892770122933283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 526039098094773988977509 98632330892770122933283)
                  ·
                    rfl

theorem cell21_432193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 4].length) (baseStart_432193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432193 prefixEnd_432193 := by exact prefixLift 432193
  have htrace : WordTrace (prefixWord ++ tailWord_432193) baseStart_432193 baseEnd_432193 := by
    simpa [prefixWord, tailWord_432193, baseEnd_432193] using wordTrace_append hprefix tailTrace_432193
  have hstable : (prefixWord ++ tailWord_432193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432193).length < 2 ^ (prefixWord ++ tailWord_432193).sum := by decide
  have hdescent : baseEnd_432193 < baseStart_432193 := by decide
  rcases family_descends (prefixWord ++ tailWord_432193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432204 : List Nat := [2, 2, 1, 3, 1, 1, 4, 2, 5]
def baseStart_432204 : Nat := 118140960795 + 432204 * 2 ^ 59
def prefixEnd_432204 : Nat := 4983230072969 + 3 ^ 40 * 432204 * 2
def baseEnd_432204 : Nat := 98634841242636548249927

theorem tailTrace_432204 : CollatzResearch.WordTrace tailWord_432204 prefixEnd_432204 98634841242636548249927 := by
  unfold tailWord_432204
  simp only [CollatzResearch.WordTrace]
  refine ⟨7881887463103098705815833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10509183284137464941087777 7881887463103098705815833)
  ·
    refine ⟨5911415597327324029361875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7881887463103098705815833 5911415597327324029361875)
    ·
      refine ⟨8867123395990986044042813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5911415597327324029361875 8867123395990986044042813)
      ·
        refine ⟨3325171273496619766516055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8867123395990986044042813 3325171273496619766516055)
        ·
          refine ⟨4987756910244929649774083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3325171273496619766516055 4987756910244929649774083)
          ·
            refine ⟨7481635365367394474661125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4987756910244929649774083 7481635365367394474661125)
            ·
              refine ⟨1402806631006386463998961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7481635365367394474661125 1402806631006386463998961)
              ·
                refine ⟨1052104973254789847999221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1402806631006386463998961 1052104973254789847999221)
                ·
                  refine ⟨98634841242636548249927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1052104973254789847999221 98634841242636548249927)
                  ·
                    rfl

theorem cell21_432204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_432204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432204 prefixEnd_432204 := by exact prefixLift 432204
  have htrace : WordTrace (prefixWord ++ tailWord_432204) baseStart_432204 baseEnd_432204 := by
    simpa [prefixWord, tailWord_432204, baseEnd_432204] using wordTrace_append hprefix tailTrace_432204
  have hstable : (prefixWord ++ tailWord_432204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432204).length < 2 ^ (prefixWord ++ tailWord_432204).sum := by decide
  have hdescent : baseEnd_432204 < baseStart_432204 := by decide
  rcases family_descends (prefixWord ++ tailWord_432204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432218 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 8]
def baseStart_432218 : Nat := 118140960795 + 432218 * 2 ^ 59
def prefixEnd_432218 : Nat := 4983230072969 + 3 ^ 40 * 432218 * 2
def baseEnd_432218 : Nat := 98638036233375635016565

theorem tailTrace_432218 : CollatzResearch.WordTrace tailWord_432218 prefixEnd_432218 98638036233375635016565 := by
  unfold tailWord_432218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3941071387038869450660327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10509523698770318535094205 3941071387038869450660327)
  ·
    refine ⟨5911607080558304175990491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3941071387038869450660327 5911607080558304175990491)
    ·
      refine ⟨8867410620837456263985737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5911607080558304175990491 8867410620837456263985737)
      ·
        refine ⟨6650557965628092197989303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8867410620837456263985737 6650557965628092197989303)
        ·
          refine ⟨9975836948442138296983955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6650557965628092197989303 9975836948442138296983955)
          ·
            refine ⟨14963755422663207445475933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9975836948442138296983955 14963755422663207445475933)
            ·
              refine ⟨5611408283498702792053475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14963755422663207445475933 5611408283498702792053475)
              ·
                refine ⟨8417112425248054188080213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5611408283498702792053475 8417112425248054188080213)
                ·
                  refine ⟨98638036233375635016565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8417112425248054188080213 98638036233375635016565)
                  ·
                    rfl

theorem cell21_432218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_432218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432218 prefixEnd_432218 := by exact prefixLift 432218
  have htrace : WordTrace (prefixWord ++ tailWord_432218) baseStart_432218 baseEnd_432218 := by
    simpa [prefixWord, tailWord_432218, baseEnd_432218] using wordTrace_append hprefix tailTrace_432218
  have hstable : (prefixWord ++ tailWord_432218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432218).length < 2 ^ (prefixWord ++ tailWord_432218).sum := by decide
  have hdescent : baseEnd_432218 < baseStart_432218 := by decide
  rcases family_descends (prefixWord ++ tailWord_432218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432249 : List Nat := [1, 2, 1, 3, 4, 1, 1, 8]
def baseStart_432249 : Nat := 118140960795 + 432249 * 2 ^ 59
def prefixEnd_432249 : Nat := 4983230072969 + 3 ^ 40 * 432249 * 2
def baseEnd_432249 : Nat := 32881703618575489999945

theorem tailTrace_432249 : CollatzResearch.WordTrace tailWord_432249 prefixEnd_432249 32881703618575489999945 := by
  unfold tailWord_432249
  simp only [CollatzResearch.WordTrace]
  refine ⟨15765416211043170097019801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10510277474028780064679867 15765416211043170097019801)
  ·
    refine ⟨11824062158282377572764851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15765416211043170097019801 11824062158282377572764851)
    ·
      refine ⟨17736093237423566359147277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11824062158282377572764851 17736093237423566359147277)
      ·
        refine ⟨6651034964033837384680229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17736093237423566359147277 6651034964033837384680229)
        ·
          refine ⟨1247069055756344509627543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6651034964033837384680229 1247069055756344509627543)
          ·
            refine ⟨1870603583634516764441315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1247069055756344509627543 1870603583634516764441315)
            ·
              refine ⟨2805905375451775146661973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1870603583634516764441315 2805905375451775146661973)
              ·
                refine ⟨32881703618575489999945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2805905375451775146661973 32881703618575489999945)
                ·
                  rfl

theorem cell21_432249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 8].length) (baseStart_432249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432249 prefixEnd_432249 := by exact prefixLift 432249
  have htrace : WordTrace (prefixWord ++ tailWord_432249) baseStart_432249 baseEnd_432249 := by
    simpa [prefixWord, tailWord_432249, baseEnd_432249] using wordTrace_append hprefix tailTrace_432249
  have hstable : (prefixWord ++ tailWord_432249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432249).length < 2 ^ (prefixWord ++ tailWord_432249).sum := by decide
  have hdescent : baseEnd_432249 < baseStart_432249 := by decide
  rcases family_descends (prefixWord ++ tailWord_432249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432252 : List Nat := [2, 2, 2, 1, 1, 4, 4, 1, 4]
def baseStart_432252 : Nat := 118140960795 + 432252 * 2 ^ 59
def prefixEnd_432252 : Nat := 4983230072969 + 3 ^ 40 * 432252 * 2
def baseEnd_432252 : Nat := 98645795496599131449829

theorem tailTrace_432252 : CollatzResearch.WordTrace tailWord_432252 prefixEnd_432252 98645795496599131449829 := by
  unfold tailWord_432252
  simp only [CollatzResearch.WordTrace]
  refine ⟨7882762815016150804689505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10510350420021534406252673 7882762815016150804689505)
  ·
    refine ⟨5912072111262113103517129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7882762815016150804689505 5912072111262113103517129)
    ·
      refine ⟨4434054083446584827637847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5912072111262113103517129 4434054083446584827637847)
      ·
        refine ⟨6651081125169877241456771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4434054083446584827637847 6651081125169877241456771)
        ·
          refine ⟨9976621687754815862185157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6651081125169877241456771 9976621687754815862185157)
          ·
            refine ⟨1870616566454027974159717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9976621687754815862185157 1870616566454027974159717)
            ·
              refine ⟨350740606210130245154947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1870616566454027974159717 350740606210130245154947)
              ·
                refine ⟨526110909315195367732421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350740606210130245154947 526110909315195367732421)
                ·
                  refine ⟨98645795496599131449829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 526110909315195367732421 98645795496599131449829)
                  ·
                    rfl

theorem cell21_432252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_432252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432252 prefixEnd_432252 := by exact prefixLift 432252
  have htrace : WordTrace (prefixWord ++ tailWord_432252) baseStart_432252 baseEnd_432252 := by
    simpa [prefixWord, tailWord_432252, baseEnd_432252] using wordTrace_append hprefix tailTrace_432252
  have hstable : (prefixWord ++ tailWord_432252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432252).length < 2 ^ (prefixWord ++ tailWord_432252).sum := by decide
  have hdescent : baseEnd_432252 < baseStart_432252 := by decide
  rcases family_descends (prefixWord ++ tailWord_432252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432311 : List Nat := [1, 1, 3, 1, 4, 2, 2, 3, 4]
def baseStart_432311 : Nat := 118140960795 + 432311 * 2 ^ 59
def prefixEnd_432311 : Nat := 4983230072969 + 3 ^ 40 * 432311 * 2
def baseEnd_432311 : Nat := 98659260100428139966375

theorem tailTrace_432311 : CollatzResearch.WordTrace tailWord_432311 prefixEnd_432311 98659260100428139966375 := by
  unfold tailWord_432311
  simp only [CollatzResearch.WordTrace]
  refine ⟨15767677536818554685776787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10511785024545703123851191 15767677536818554685776787)
  ·
    refine ⟨23651516305227832028665181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15767677536818554685776787 23651516305227832028665181)
    ·
      refine ⟨8869318614460437010749443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23651516305227832028665181 8869318614460437010749443)
      ·
        refine ⟨13303977921690655516124165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8869318614460437010749443 13303977921690655516124165)
        ·
          refine ⟨2494495860316997909273281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13303977921690655516124165 2494495860316997909273281)
          ·
            refine ⟨1870871895237748431954961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2494495860316997909273281 1870871895237748431954961)
            ·
              refine ⟨1403153921428311323966221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1870871895237748431954961 1403153921428311323966221)
              ·
                refine ⟨526182720535616746487333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1403153921428311323966221 526182720535616746487333)
                ·
                  refine ⟨98659260100428139966375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 526182720535616746487333 98659260100428139966375)
                  ·
                    rfl

theorem cell21_432311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 4].length) (baseStart_432311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432311 prefixEnd_432311 := by exact prefixLift 432311
  have htrace : WordTrace (prefixWord ++ tailWord_432311) baseStart_432311 baseEnd_432311 := by
    simpa [prefixWord, tailWord_432311, baseEnd_432311] using wordTrace_append hprefix tailTrace_432311
  have hstable : (prefixWord ++ tailWord_432311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432311).length < 2 ^ (prefixWord ++ tailWord_432311).sum := by decide
  have hdescent : baseEnd_432311 < baseStart_432311 := by decide
  rcases family_descends (prefixWord ++ tailWord_432311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432401 : List Nat := [1, 2, 2, 1, 1, 7, 7]
def baseStart_432401 : Nat := 118140960795 + 432401 * 2 ^ 59
def prefixEnd_432401 : Nat := 4983230072969 + 3 ^ 40 * 432401 * 2
def baseEnd_432401 : Nat := 10964422147400887051799

theorem tailTrace_432401 : CollatzResearch.WordTrace tailWord_432401 prefixEnd_432401 10964422147400887051799 := by
  unfold tailWord_432401
  simp only [CollatzResearch.WordTrace]
  refine ⟨15770960106492500056553057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10513973404328333371035371 15770960106492500056553057)
  ·
    refine ⟨11828220079869375042414793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15770960106492500056553057 11828220079869375042414793)
    ·
      refine ⟨8871165059902031281811095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11828220079869375042414793 8871165059902031281811095)
      ·
        refine ⟨13306747589853046922716643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8871165059902031281811095 13306747589853046922716643)
        ·
          refine ⟨19960121384779570384074965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13306747589853046922716643 19960121384779570384074965)
          ·
            refine ⟨467815344955771180876757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 19960121384779570384074965 467815344955771180876757)
            ·
              refine ⟨10964422147400887051799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 467815344955771180876757 10964422147400887051799)
              ·
                rfl

theorem cell21_432401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 7].length) (baseStart_432401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432401 prefixEnd_432401 := by exact prefixLift 432401
  have htrace : WordTrace (prefixWord ++ tailWord_432401) baseStart_432401 baseEnd_432401 := by
    simpa [prefixWord, tailWord_432401, baseEnd_432401] using wordTrace_append hprefix tailTrace_432401
  have hstable : (prefixWord ++ tailWord_432401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432401).length < 2 ^ (prefixWord ++ tailWord_432401).sum := by decide
  have hdescent : baseEnd_432401 < baseStart_432401 := by decide
  rcases family_descends (prefixWord ++ tailWord_432401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432418 : List Nat := [3, 3, 1, 1, 3, 2, 2, 6]
def baseStart_432418 : Nat := 118140960795 + 432418 * 2 ^ 59
def prefixEnd_432418 : Nat := 4983230072969 + 3 ^ 40 * 432418 * 2
def baseEnd_432418 : Nat := 32894559652739910560941

theorem tailTrace_432418 : CollatzResearch.WordTrace tailWord_432418 prefixEnd_432418 32894559652739910560941 := by
  unfold tailWord_432418
  simp only [CollatzResearch.WordTrace]
  refine ⟨3942895036857727989980477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10514386764953941306614605 3942895036857727989980477)
  ·
    refine ⟨1478585638821647996242679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3942895036857727989980477 1478585638821647996242679)
    ·
      refine ⟨2217878458232471994364019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1478585638821647996242679 2217878458232471994364019)
      ·
        refine ⟨3326817687348707991546029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2217878458232471994364019 3326817687348707991546029)
        ·
          refine ⟨1247556632755765496829761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3326817687348707991546029 1247556632755765496829761)
          ·
            refine ⟨935667474566824122622321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1247556632755765496829761 935667474566824122622321)
            ·
              refine ⟨701750605925118091966741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 935667474566824122622321 701750605925118091966741)
              ·
                refine ⟨32894559652739910560941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 701750605925118091966741 32894559652739910560941)
                ·
                  rfl

theorem cell21_432418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_432418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432418 prefixEnd_432418 := by exact prefixLift 432418
  have htrace : WordTrace (prefixWord ++ tailWord_432418) baseStart_432418 baseEnd_432418 := by
    simpa [prefixWord, tailWord_432418, baseEnd_432418] using wordTrace_append hprefix tailTrace_432418
  have hstable : (prefixWord ++ tailWord_432418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432418).length < 2 ^ (prefixWord ++ tailWord_432418).sum := by decide
  have hdescent : baseEnd_432418 < baseStart_432418 := by decide
  rcases family_descends (prefixWord ++ tailWord_432418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432421 : List Nat := [1, 3, 1, 2, 5, 2, 2, 1, 4]
def baseStart_432421 : Nat := 118140960795 + 432421 * 2 ^ 59
def prefixEnd_432421 : Nat := 4983230072969 + 3 ^ 40 * 432421 * 2
def baseEnd_432421 : Nat := 98684363599092393132817

theorem tailTrace_432421 : CollatzResearch.WordTrace tailWord_432421 prefixEnd_432421 98684363599092393132817 := by
  unfold tailWord_432421
  simp only [CollatzResearch.WordTrace]
  refine ⟨15771689566420043472281117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10514459710946695648187411 15771689566420043472281117)
  ·
    refine ⟨5914383587407516302105419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15771689566420043472281117 5914383587407516302105419)
    ·
      refine ⟨8871575381111274453158129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5914383587407516302105419 8871575381111274453158129)
      ·
        refine ⟨6653681535833455839868597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8871575381111274453158129 6653681535833455839868597)
        ·
          refine ⟨623782643984386484987681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6653681535833455839868597 623782643984386484987681)
          ·
            refine ⟨467836982988289863740761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623782643984386484987681 467836982988289863740761)
            ·
              refine ⟨350877737241217397805571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467836982988289863740761 350877737241217397805571)
              ·
                refine ⟨526316605861826096708357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350877737241217397805571 526316605861826096708357)
                ·
                  refine ⟨98684363599092393132817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 526316605861826096708357 98684363599092393132817)
                  ·
                    rfl

theorem cell21_432421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_432421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432421 prefixEnd_432421 := by exact prefixLift 432421
  have htrace : WordTrace (prefixWord ++ tailWord_432421) baseStart_432421 baseEnd_432421 := by
    simpa [prefixWord, tailWord_432421, baseEnd_432421] using wordTrace_append hprefix tailTrace_432421
  have hstable : (prefixWord ++ tailWord_432421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432421).length < 2 ^ (prefixWord ++ tailWord_432421).sum := by decide
  have hdescent : baseEnd_432421 < baseStart_432421 := by decide
  rcases family_descends (prefixWord ++ tailWord_432421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432466 : List Nat := [3, 2, 2, 1, 1, 1, 6, 2, 3]
def baseStart_432466 : Nat := 118140960795 + 432466 * 2 ^ 59
def prefixEnd_432466 : Nat := 4983230072969 + 3 ^ 40 * 432466 * 2
def baseEnd_432466 : Nat := 98694633212182314882725

theorem tailTrace_432466 : CollatzResearch.WordTrace tailWord_432466 prefixEnd_432466 98694633212182314882725 := by
  unfold tailWord_432466
  simp only [CollatzResearch.WordTrace]
  refine ⟨3943332712814254039417313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10515553900838010771779501 3943332712814254039417313)
  ·
    refine ⟨2957499534610690529562985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3943332712814254039417313 2957499534610690529562985)
    ·
      refine ⟨2218124650958017897172239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2957499534610690529562985 2218124650958017897172239)
      ·
        refine ⟨3327186976437026845758359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2218124650958017897172239 3327186976437026845758359)
        ·
          refine ⟨4990780464655540268637539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3327186976437026845758359 4990780464655540268637539)
          ·
            refine ⟨7486170696983310402956309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4990780464655540268637539 7486170696983310402956309)
            ·
              refine ⟨350914251421092675138577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7486170696983310402956309 350914251421092675138577)
              ·
                refine ⟨263185688565819506353933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350914251421092675138577 263185688565819506353933)
                ·
                  refine ⟨98694633212182314882725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263185688565819506353933 98694633212182314882725)
                  ·
                    rfl

theorem cell21_432466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_432466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432466 prefixEnd_432466 := by exact prefixLift 432466
  have htrace : WordTrace (prefixWord ++ tailWord_432466) baseStart_432466 baseEnd_432466 := by
    simpa [prefixWord, tailWord_432466, baseEnd_432466] using wordTrace_append hprefix tailTrace_432466
  have hstable : (prefixWord ++ tailWord_432466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432466).length < 2 ^ (prefixWord ++ tailWord_432466).sum := by decide
  have hdescent : baseEnd_432466 < baseStart_432466 := by decide
  rcases family_descends (prefixWord ++ tailWord_432466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432491 : List Nat := [1, 1, 1, 1, 2, 2, 2, 6, 5]
def baseStart_432491 : Nat := 118140960795 + 432491 * 2 ^ 59
def prefixEnd_432491 : Nat := 4983230072969 + 3 ^ 40 * 432491 * 2
def baseEnd_432491 : Nat := 98700338552787826966007

theorem tailTrace_432491 : CollatzResearch.WordTrace tailWord_432491 prefixEnd_432491 98700338552787826966007 := by
  unfold tailWord_432491
  simp only [CollatzResearch.WordTrace]
  refine ⟨15774242676166445427329327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10516161784110963618219551 15774242676166445427329327)
  ·
    refine ⟨23661364014249668140993991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15774242676166445427329327 23661364014249668140993991)
    ·
      refine ⟨35492046021374502211490987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23661364014249668140993991 35492046021374502211490987)
      ·
        refine ⟨53238069032061753317236481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35492046021374502211490987 53238069032061753317236481)
        ·
          refine ⟨39928551774046314987927361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53238069032061753317236481 39928551774046314987927361)
          ·
            refine ⟨29946413830534736240945521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39928551774046314987927361 29946413830534736240945521)
            ·
              refine ⟨22459810372901052180709141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29946413830534736240945521 22459810372901052180709141)
              ·
                refine ⟨1052803611229736820970741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22459810372901052180709141 1052803611229736820970741)
                ·
                  refine ⟨98700338552787826966007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1052803611229736820970741 98700338552787826966007)
                  ·
                    rfl

theorem cell21_432491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 5].length) (baseStart_432491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432491 prefixEnd_432491 := by exact prefixLift 432491
  have htrace : WordTrace (prefixWord ++ tailWord_432491) baseStart_432491 baseEnd_432491 := by
    simpa [prefixWord, tailWord_432491, baseEnd_432491] using wordTrace_append hprefix tailTrace_432491
  have hstable : (prefixWord ++ tailWord_432491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432491).length < 2 ^ (prefixWord ++ tailWord_432491).sum := by decide
  have hdescent : baseEnd_432491 < baseStart_432491 := by decide
  rcases family_descends (prefixWord ++ tailWord_432491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432514 : List Nat := [3, 4, 2, 1, 2, 2, 1, 2, 4]
def baseStart_432514 : Nat := 118140960795 + 432514 * 2 ^ 59
def prefixEnd_432514 : Nat := 4983230072969 + 3 ^ 40 * 432514 * 2
def baseEnd_432514 : Nat := 98705587466144898082627

theorem tailTrace_432514 : CollatzResearch.WordTrace tailWord_432514 prefixEnd_432514 98705587466144898082627 := by
  unfold tailWord_432514
  simp only [CollatzResearch.WordTrace]
  refine ⟨3943770388770780088854149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10516721036722080236944397 3943770388770780088854149)
  ·
    refine ⟨739456947894521266660153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3943770388770780088854149 739456947894521266660153)
    ·
      refine ⟨554592710920890949995115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 739456947894521266660153 554592710920890949995115)
      ·
        refine ⟨831889066381336424992673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554592710920890949995115 831889066381336424992673)
        ·
          refine ⟨623916799786002318744505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 831889066381336424992673 623916799786002318744505)
          ·
            refine ⟨467937599839501739058379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623916799786002318744505 467937599839501739058379)
            ·
              refine ⟨701906399759252608587569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467937599839501739058379 701906399759252608587569)
              ·
                refine ⟨526429799819439456440677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 701906399759252608587569 526429799819439456440677)
                ·
                  refine ⟨98705587466144898082627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 526429799819439456440677 98705587466144898082627)
                  ·
                    rfl

theorem cell21_432514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_432514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432514 prefixEnd_432514 := by exact prefixLift 432514
  have htrace : WordTrace (prefixWord ++ tailWord_432514) baseStart_432514 baseEnd_432514 := by
    simpa [prefixWord, tailWord_432514, baseEnd_432514] using wordTrace_append hprefix tailTrace_432514
  have hstable : (prefixWord ++ tailWord_432514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432514).length < 2 ^ (prefixWord ++ tailWord_432514).sum := by decide
  have hdescent : baseEnd_432514 < baseStart_432514 := by decide
  rcases family_descends (prefixWord ++ tailWord_432514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432584 : List Nat := [2, 1, 3, 1, 3, 2, 3, 1, 5]
def baseStart_432584 : Nat := 118140960795 + 432584 * 2 ^ 59
def prefixEnd_432584 : Nat := 4983230072969 + 3 ^ 40 * 432584 * 2
def baseEnd_432584 : Nat := 98721562419840331915817

theorem tailTrace_432584 : CollatzResearch.WordTrace tailWord_432584 prefixEnd_432584 98721562419840331915817 := by
  unfold tailWord_432584
  simp only [CollatzResearch.WordTrace]
  refine ⟨7888817332414761155232403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10518423109886348206976537 7888817332414761155232403)
  ·
    refine ⟨11833225998622141732848605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7888817332414761155232403 11833225998622141732848605)
    ·
      refine ⟨4437459749483303149818227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11833225998622141732848605 4437459749483303149818227)
      ·
        refine ⟨6656189624224954724727341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4437459749483303149818227 6656189624224954724727341)
        ·
          refine ⟨2496071109084358021772753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6656189624224954724727341 2496071109084358021772753)
          ·
            refine ⟨1872053331813268516329565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2496071109084358021772753 1872053331813268516329565)
            ·
              refine ⟨702019999429975693623587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1872053331813268516329565 702019999429975693623587)
              ·
                refine ⟨1053029999144963540435381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702019999429975693623587 1053029999144963540435381)
                ·
                  refine ⟨98721562419840331915817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1053029999144963540435381 98721562419840331915817)
                  ·
                    rfl

theorem cell21_432584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_432584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432584 prefixEnd_432584 := by exact prefixLift 432584
  have htrace : WordTrace (prefixWord ++ tailWord_432584) baseStart_432584 baseEnd_432584 := by
    simpa [prefixWord, tailWord_432584, baseEnd_432584] using wordTrace_append hprefix tailTrace_432584
  have hstable : (prefixWord ++ tailWord_432584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432584).length < 2 ^ (prefixWord ++ tailWord_432584).sum := by decide
  have hdescent : baseEnd_432584 < baseStart_432584 := by decide
  rcases family_descends (prefixWord ++ tailWord_432584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432629 : List Nat := [1, 3, 5, 1, 11]
def baseStart_432629 : Nat := 118140960795 + 432629 * 2 ^ 59
def prefixEnd_432629 : Nat := 4983230072969 + 3 ^ 40 * 432629 * 2
def baseEnd_432629 : Nat := 1218911506579385847725

theorem tailTrace_432629 : CollatzResearch.WordTrace tailWord_432629 prefixEnd_432629 1218911506579385847725 := by
  unfold tailWord_432629
  simp only [CollatzResearch.WordTrace]
  refine ⟨15779275949666494995852941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10519517299777663330568627 15779275949666494995852941)
  ·
    refine ⟨5917228481124935623444853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15779275949666494995852941 5917228481124935623444853)
    ·
      refine ⟨554740170105462714697955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5917228481124935623444853 554740170105462714697955)
      ·
        refine ⟨832110255158194072046933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554740170105462714697955 832110255158194072046933)
        ·
          refine ⟨1218911506579385847725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 832110255158194072046933 1218911506579385847725)
          ·
            rfl

theorem cell21_432629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 11].length) (baseStart_432629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432629 prefixEnd_432629 := by exact prefixLift 432629
  have htrace : WordTrace (prefixWord ++ tailWord_432629) baseStart_432629 baseEnd_432629 := by
    simpa [prefixWord, tailWord_432629, baseEnd_432629] using wordTrace_append hprefix tailTrace_432629
  have hstable : (prefixWord ++ tailWord_432629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432629).length < 2 ^ (prefixWord ++ tailWord_432629).sum := by decide
  have hdescent : baseEnd_432629 < baseStart_432629 := by decide
  rcases family_descends (prefixWord ++ tailWord_432629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432643 : List Nat := [1, 1, 1, 3, 2, 1, 4, 3, 5]
def baseStart_432643 : Nat := 118140960795 + 432643 * 2 ^ 59
def prefixEnd_432643 : Nat := 4983230072969 + 3 ^ 40 * 432643 * 2
def baseEnd_432643 : Nat := 98735027023669340432363

theorem tailTrace_432643 : CollatzResearch.WordTrace tailWord_432643 prefixEnd_432643 98735027023669340432363 := by
  unfold tailWord_432643
  simp only [CollatzResearch.WordTrace]
  refine ⟨15779786571615775386862583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10519857714410516924575055 15779786571615775386862583)
  ·
    refine ⟨23669679857423663080293875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15779786571615775386862583 23669679857423663080293875)
    ·
      refine ⟨35504519786135494620440813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23669679857423663080293875 35504519786135494620440813)
      ·
        refine ⟨13314194919800810482665305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35504519786135494620440813 13314194919800810482665305)
        ·
          refine ⟨9985646189850607861998979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13314194919800810482665305 9985646189850607861998979)
          ·
            refine ⟨14978469284775911792998469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9985646189850607861998979 14978469284775911792998469)
            ·
              refine ⟨2808462990895483461187213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14978469284775911792998469 2808462990895483461187213)
              ·
                refine ⟨1053173621585806297945205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2808462990895483461187213 1053173621585806297945205)
                ·
                  refine ⟨98735027023669340432363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1053173621585806297945205 98735027023669340432363)
                  ·
                    rfl

theorem cell21_432643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 5].length) (baseStart_432643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432643 prefixEnd_432643 := by exact prefixLift 432643
  have htrace : WordTrace (prefixWord ++ tailWord_432643) baseStart_432643 baseEnd_432643 := by
    simpa [prefixWord, tailWord_432643, baseEnd_432643] using wordTrace_append hprefix tailTrace_432643
  have hstable : (prefixWord ++ tailWord_432643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432643).length < 2 ^ (prefixWord ++ tailWord_432643).sum := by decide
  have hdescent : baseEnd_432643 < baseStart_432643 := by decide
  rcases family_descends (prefixWord ++ tailWord_432643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432663 : List Nat := [1, 1, 3, 6, 1, 1, 3, 5]
def baseStart_432663 : Nat := 118140960795 + 432663 * 2 ^ 59
def prefixEnd_432663 : Nat := 4983230072969 + 3 ^ 40 * 432663 * 2
def baseEnd_432663 : Nat := 32913197098717916699663

theorem tailTrace_432663 : CollatzResearch.WordTrace tailWord_432663 prefixEnd_432663 32913197098717916699663 := by
  unfold tailWord_432663
  simp only [CollatzResearch.WordTrace]
  refine ⟨15780516031543318802590643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10520344021028879201727095 15780516031543318802590643)
  ·
    refine ⟨23670774047314978203885965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15780516031543318802590643 23670774047314978203885965)
    ·
      refine ⟨8876540267743116826457237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23670774047314978203885965 8876540267743116826457237)
      ·
        refine ⟨416087825050458601240183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8876540267743116826457237 416087825050458601240183)
        ·
          refine ⟨624131737575687901860275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416087825050458601240183 624131737575687901860275)
          ·
            refine ⟨936197606363531852790413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624131737575687901860275 936197606363531852790413)
            ·
              refine ⟨351074102386324444796405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 936197606363531852790413 351074102386324444796405)
              ·
                refine ⟨32913197098717916699663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 351074102386324444796405 32913197098717916699663)
                ·
                  rfl

theorem cell21_432663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 5].length) (baseStart_432663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432663 prefixEnd_432663 := by exact prefixLift 432663
  have htrace : WordTrace (prefixWord ++ tailWord_432663) baseStart_432663 baseEnd_432663 := by
    simpa [prefixWord, tailWord_432663, baseEnd_432663] using wordTrace_append hprefix tailTrace_432663
  have hstable : (prefixWord ++ tailWord_432663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432663).length < 2 ^ (prefixWord ++ tailWord_432663).sum := by decide
  have hdescent : baseEnd_432663 < baseStart_432663 := by decide
  rcases family_descends (prefixWord ++ tailWord_432663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432674 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 6]
def baseStart_432674 : Nat := 118140960795 + 432674 * 2 ^ 59
def prefixEnd_432674 : Nat := 4983230072969 + 3 ^ 40 * 432674 * 2
def baseEnd_432674 : Nat := 98742101646020175415633

theorem tailTrace_432674 : CollatzResearch.WordTrace tailWord_432674 prefixEnd_432674 98742101646020175415633 := by
  unfold tailWord_432674
  simp only [CollatzResearch.WordTrace]
  refine ⟨3945229308625866920310269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10520611489668978454160717 3945229308625866920310269)
  ·
    refine ⟨1479460990734700095116351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3945229308625866920310269 1479460990734700095116351)
    ·
      refine ⟨2219191486102050142674527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1479460990734700095116351 2219191486102050142674527)
      ·
        refine ⟨3328787229153075214011791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2219191486102050142674527 3328787229153075214011791)
        ·
          refine ⟨4993180843729612821017687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3328787229153075214011791 4993180843729612821017687)
          ·
            refine ⟨7489771265594419231526531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4993180843729612821017687 7489771265594419231526531)
            ·
              refine ⟨11234656898391628847289797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7489771265594419231526531 11234656898391628847289797)
              ·
                refine ⟨2106498168448430408866837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11234656898391628847289797 2106498168448430408866837)
                ·
                  refine ⟨98742101646020175415633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2106498168448430408866837 98742101646020175415633)
                  ·
                    rfl

theorem cell21_432674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_432674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432674 prefixEnd_432674 := by exact prefixLift 432674
  have htrace : WordTrace (prefixWord ++ tailWord_432674) baseStart_432674 baseEnd_432674 := by
    simpa [prefixWord, tailWord_432674, baseEnd_432674] using wordTrace_append hprefix tailTrace_432674
  have hstable : (prefixWord ++ tailWord_432674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432674).length < 2 ^ (prefixWord ++ tailWord_432674).sum := by decide
  have hdescent : baseEnd_432674 < baseStart_432674 := by decide
  rcases family_descends (prefixWord ++ tailWord_432674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432694 : List Nat := [5, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_432694 : Nat := 118140960795 + 432694 * 2 ^ 59
def prefixEnd_432694 : Nat := 4983230072969 + 3 ^ 40 * 432694 * 2
def baseEnd_432694 : Nat := 98746665918504585082259

theorem tailTrace_432694 : CollatzResearch.WordTrace tailWord_432694 prefixEnd_432694 98746665918504585082259 := by
  unfold tailWord_432694
  simp only [CollatzResearch.WordTrace]
  refine ⟨986352918401938193560571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10521097796287340731312757 986352918401938193560571)
  ·
    refine ⟨1479529377602907290340857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 986352918401938193560571 1479529377602907290340857)
    ·
      refine ⟨1109647033202180467755643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1479529377602907290340857 1109647033202180467755643)
      ·
        refine ⟨1664470549803270701633465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1109647033202180467755643 1664470549803270701633465)
        ·
          refine ⟨1248352912352453026225099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1664470549803270701633465 1248352912352453026225099)
          ·
            refine ⟨1872529368528679539337649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248352912352453026225099 1872529368528679539337649)
            ·
              refine ⟨1404397026396509654503237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1872529368528679539337649 1404397026396509654503237)
              ·
                refine ⟨263324442449345560219357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1404397026396509654503237 263324442449345560219357)
                ·
                  refine ⟨98746665918504585082259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263324442449345560219357 98746665918504585082259)
                  ·
                    rfl

theorem cell21_432694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_432694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432694 prefixEnd_432694 := by exact prefixLift 432694
  have htrace : WordTrace (prefixWord ++ tailWord_432694) baseStart_432694 baseEnd_432694 := by
    simpa [prefixWord, tailWord_432694, baseEnd_432694] using wordTrace_append hprefix tailTrace_432694
  have hstable : (prefixWord ++ tailWord_432694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432694).length < 2 ^ (prefixWord ++ tailWord_432694).sum := by decide
  have hdescent : baseEnd_432694 < baseStart_432694 := by decide
  rcases family_descends (prefixWord ++ tailWord_432694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432719 : List Nat := [1, 1, 2, 1, 1, 2, 6, 2, 5]
def baseStart_432719 : Nat := 118140960795 + 432719 * 2 ^ 59
def prefixEnd_432719 : Nat := 4983230072969 + 3 ^ 40 * 432719 * 2
def baseEnd_432719 : Nat := 98752371259110097165541

theorem tailTrace_432719 : CollatzResearch.WordTrace tailWord_432719 prefixEnd_432719 98752371259110097165541 := by
  unfold tailWord_432719
  simp only [CollatzResearch.WordTrace]
  refine ⟨15782558519340440366629211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10521705679560293577752807 15782558519340440366629211)
  ·
    refine ⟨23673837779010660549943817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15782558519340440366629211 23673837779010660549943817)
    ·
      refine ⟨17755378334257995412457863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23673837779010660549943817 17755378334257995412457863)
      ·
        refine ⟨26633067501386993118686795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17755378334257995412457863 26633067501386993118686795)
        ·
          refine ⟨39949601252080489678030193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26633067501386993118686795 39949601252080489678030193)
          ·
            refine ⟨29962200939060367258522645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39949601252080489678030193 29962200939060367258522645)
            ·
              refine ⟨1404478169018454715243249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29962200939060367258522645 1404478169018454715243249)
              ·
                refine ⟨1053358626763841036432437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1404478169018454715243249 1053358626763841036432437)
                ·
                  refine ⟨98752371259110097165541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1053358626763841036432437 98752371259110097165541)
                  ·
                    rfl

theorem cell21_432719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 5].length) (baseStart_432719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432719 prefixEnd_432719 := by exact prefixLift 432719
  have htrace : WordTrace (prefixWord ++ tailWord_432719) baseStart_432719 baseEnd_432719 := by
    simpa [prefixWord, tailWord_432719, baseEnd_432719] using wordTrace_append hprefix tailTrace_432719
  have hstable : (prefixWord ++ tailWord_432719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432719).length < 2 ^ (prefixWord ++ tailWord_432719).sum := by decide
  have hdescent : baseEnd_432719 < baseStart_432719 := by decide
  rcases family_descends (prefixWord ++ tailWord_432719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432764 : List Nat := [2, 2, 2, 1, 1, 2, 3, 8]
def baseStart_432764 : Nat := 118140960795 + 432764 * 2 ^ 59
def prefixEnd_432764 : Nat := 4983230072969 + 3 ^ 40 * 432764 * 2
def baseEnd_432764 : Nat := 32920880290733339638483

theorem tailTrace_432764 : CollatzResearch.WordTrace tailWord_432764 prefixEnd_432764 32920880290733339638483 := by
  unfold tailWord_432764
  simp only [CollatzResearch.WordTrace]
  refine ⟨7892099902088706526008673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10522799869451608701344897 7892099902088706526008673)
  ·
    refine ⟨5919074926566529894506505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7892099902088706526008673 5919074926566529894506505)
    ·
      refine ⟨4439306194924897420879879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5919074926566529894506505 4439306194924897420879879)
      ·
        refine ⟨6658959292387346131319819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4439306194924897420879879 6658959292387346131319819)
        ·
          refine ⟨9988438938581019196979729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6658959292387346131319819 9988438938581019196979729)
          ·
            refine ⟨7491329203935764397734797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9988438938581019196979729 7491329203935764397734797)
            ·
              refine ⟨2809248451475911649150549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7491329203935764397734797 2809248451475911649150549)
              ·
                refine ⟨32920880290733339638483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2809248451475911649150549 32920880290733339638483)
                ·
                  rfl

theorem cell21_432764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 8].length) (baseStart_432764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432764 prefixEnd_432764 := by exact prefixLift 432764
  have htrace : WordTrace (prefixWord ++ tailWord_432764) baseStart_432764 baseEnd_432764 := by
    simpa [prefixWord, tailWord_432764, baseEnd_432764] using wordTrace_append hprefix tailTrace_432764
  have hstable : (prefixWord ++ tailWord_432764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432764).length < 2 ^ (prefixWord ++ tailWord_432764).sum := by decide
  have hdescent : baseEnd_432764 < baseStart_432764 := by decide
  rcases family_descends (prefixWord ++ tailWord_432764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432826 : List Nat := [3, 1, 1, 1, 2, 3, 1, 5, 4]
def baseStart_432826 : Nat := 118140960795 + 432826 * 2 ^ 59
def prefixEnd_432826 : Nat := 4983230072969 + 3 ^ 40 * 432826 * 2
def baseEnd_432826 : Nat := 98776790116901688881989

theorem tailTrace_432826 : CollatzResearch.WordTrace tailWord_432826 prefixEnd_432826 98776790116901688881989 := by
  unfold tailWord_432826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3946615282488199410193583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10524307419968531760516221 3946615282488199410193583)
  ·
    refine ⟨5919922923732299115290375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3946615282488199410193583 5919922923732299115290375)
    ·
      refine ⟨8879884385598448672935563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5919922923732299115290375 8879884385598448672935563)
      ·
        refine ⟨13319826578397673009403345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8879884385598448672935563 13319826578397673009403345)
        ·
          refine ⟨9989869933798254757052509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13319826578397673009403345 9989869933798254757052509)
          ·
            refine ⟨3746201225174345533894691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9989869933798254757052509 3746201225174345533894691)
            ·
              refine ⟨5619301837761518300842037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3746201225174345533894691 5619301837761518300842037)
              ·
                refine ⟨526809547290142340703941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5619301837761518300842037 526809547290142340703941)
                ·
                  refine ⟨98776790116901688881989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 526809547290142340703941 98776790116901688881989)
                  ·
                    rfl

theorem cell21_432826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_432826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432826 prefixEnd_432826 := by exact prefixLift 432826
  have htrace : WordTrace (prefixWord ++ tailWord_432826) baseStart_432826 baseEnd_432826 := by
    simpa [prefixWord, tailWord_432826, baseEnd_432826] using wordTrace_append hprefix tailTrace_432826
  have hstable : (prefixWord ++ tailWord_432826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432826).length < 2 ^ (prefixWord ++ tailWord_432826).sum := by decide
  have hdescent : baseEnd_432826 < baseStart_432826 := by decide
  rcases family_descends (prefixWord ++ tailWord_432826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432860 : List Nat := [2, 2, 5, 1, 1, 1, 3, 2, 4]
def baseStart_432860 : Nat := 118140960795 + 432860 * 2 ^ 59
def prefixEnd_432860 : Nat := 4983230072969 + 3 ^ 40 * 432860 * 2
def baseEnd_432860 : Nat := 98784549380125185315253

theorem tailTrace_432860 : CollatzResearch.WordTrace tailWord_432860 prefixEnd_432860 98784549380125185315253 := by
  unfold tailWord_432860
  simp only [CollatzResearch.WordTrace]
  refine ⟨7893850605914810723756017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10525134141219747631674689 7893850605914810723756017)
  ·
    refine ⟨5920387954436108042817013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7893850605914810723756017 5920387954436108042817013)
    ·
      refine ⟨555036370728385129014095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5920387954436108042817013 555036370728385129014095)
      ·
        refine ⟨832554556092577693521143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555036370728385129014095 832554556092577693521143)
        ·
          refine ⟨1248831834138866540281715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832554556092577693521143 1248831834138866540281715)
          ·
            refine ⟨1873247751208299810422573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248831834138866540281715 1873247751208299810422573)
            ·
              refine ⟨702467906703112428908465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1873247751208299810422573 702467906703112428908465)
              ·
                refine ⟨526850930027334321681349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702467906703112428908465 526850930027334321681349)
                ·
                  refine ⟨98784549380125185315253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 526850930027334321681349 98784549380125185315253)
                  ·
                    rfl

theorem cell21_432860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_432860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_432860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_432860 prefixEnd_432860 := by exact prefixLift 432860
  have htrace : WordTrace (prefixWord ++ tailWord_432860) baseStart_432860 baseEnd_432860 := by
    simpa [prefixWord, tailWord_432860, baseEnd_432860] using wordTrace_append hprefix tailTrace_432860
  have hstable : (prefixWord ++ tailWord_432860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432860).length < 2 ^ (prefixWord ++ tailWord_432860).sum := by decide
  have hdescent : baseEnd_432860 < baseStart_432860 := by decide
  rcases family_descends (prefixWord ++ tailWord_432860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433009 : List Nat := [1, 2, 2, 2, 1, 5, 3, 5]
def baseStart_433009 : Nat := 118140960795 + 433009 * 2 ^ 59
def prefixEnd_433009 : Nat := 4983230072969 + 3 ^ 40 * 433009 * 2
def baseEnd_433009 : Nat := 32939517736711345777205

theorem tailTrace_433009 : CollatzResearch.WordTrace tailWord_433009 prefixEnd_433009 32939517736711345777205 := by
  unfold tailWord_433009
  simp only [CollatzResearch.WordTrace]
  refine ⟨15793135688289819894686081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10528757125526546596457387 15793135688289819894686081)
  ·
    refine ⟨11844851766217364921014561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15793135688289819894686081 11844851766217364921014561)
    ·
      refine ⟨8883638824663023690760921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11844851766217364921014561 8883638824663023690760921)
      ·
        refine ⟨6662729118497267768070691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8883638824663023690760921 6662729118497267768070691)
        ·
          refine ⟨9994093677745901652106037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6662729118497267768070691 9994093677745901652106037)
          ·
            refine ⟨936946282288678279884941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9994093677745901652106037 936946282288678279884941)
            ·
              refine ⟨351354855858254354956853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 936946282288678279884941 351354855858254354956853)
              ·
                refine ⟨32939517736711345777205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 351354855858254354956853 32939517736711345777205)
                ·
                  rfl

theorem cell21_433009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 5].length) (baseStart_433009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_433009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_433009 prefixEnd_433009 := by exact prefixLift 433009
  have htrace : WordTrace (prefixWord ++ tailWord_433009) baseStart_433009 baseEnd_433009 := by
    simpa [prefixWord, tailWord_433009, baseEnd_433009] using wordTrace_append hprefix tailTrace_433009
  have hstable : (prefixWord ++ tailWord_433009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433009).length < 2 ^ (prefixWord ++ tailWord_433009).sum := by decide
  have hdescent : baseEnd_433009 < baseStart_433009 := by decide
  rcases family_descends (prefixWord ++ tailWord_433009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433046 : List Nat := [5, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_433046 : Nat := 118140960795 + 433046 * 2 ^ 59
def prefixEnd_433046 : Nat := 4983230072969 + 3 ^ 40 * 433046 * 2
def baseEnd_433046 : Nat := 98826997114230195214873

theorem tailTrace_433046 : CollatzResearch.WordTrace tailWord_433046 prefixEnd_433046 98826997114230195214873 := by
  unfold tailWord_433046
  simp only [CollatzResearch.WordTrace]
  refine ⟨987155324322235950861437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10529656792770516809188661 987155324322235950861437)
  ·
    refine ⟨370183246620838481573039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 987155324322235950861437 370183246620838481573039)
    ·
      refine ⟨555274869931257722359559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370183246620838481573039 555274869931257722359559)
      ·
        refine ⟨832912304896886583539339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555274869931257722359559 832912304896886583539339)
        ·
          refine ⟨1249368457345329875309009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832912304896886583539339 1249368457345329875309009)
          ·
            refine ⟨937026343008997406481757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1249368457345329875309009 937026343008997406481757)
            ·
              refine ⟨351384878628374027430659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 937026343008997406481757 351384878628374027430659)
              ·
                refine ⟨527077317942561041145989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351384878628374027430659 527077317942561041145989)
                ·
                  refine ⟨98826997114230195214873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 527077317942561041145989 98826997114230195214873)
                  ·
                    rfl

theorem cell21_433046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_433046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_433046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_433046 prefixEnd_433046 := by exact prefixLift 433046
  have htrace : WordTrace (prefixWord ++ tailWord_433046) baseStart_433046 baseEnd_433046 := by
    simpa [prefixWord, tailWord_433046, baseEnd_433046] using wordTrace_append hprefix tailTrace_433046
  have hstable : (prefixWord ++ tailWord_433046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433046).length < 2 ^ (prefixWord ++ tailWord_433046).sum := by decide
  have hdescent : baseEnd_433046 < baseStart_433046 := by decide
  rcases family_descends (prefixWord ++ tailWord_433046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433085 : List Nat := [1, 4, 1, 2, 4, 2, 7]
def baseStart_433085 : Nat := 118140960795 + 433085 * 2 ^ 59
def prefixEnd_433085 : Nat := 4983230072969 + 3 ^ 40 * 433085 * 2
def baseEnd_433085 : Nat := 10981766382841643784977

theorem tailTrace_433085 : CollatzResearch.WordTrace tailWord_433085 prefixEnd_433085 10981766382841643784977 := by
  unfold tailWord_433085
  simp only [CollatzResearch.WordTrace]
  refine ⟨15795907636014484874452709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10530605090676323249635139 15795907636014484874452709)
  ·
    refine ⟨2961732681752715913959883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15795907636014484874452709 2961732681752715913959883)
    ·
      refine ⟨4442599022629073870939825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2961732681752715913959883 4442599022629073870939825)
      ·
        refine ⟨3331949266971805403204869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4442599022629073870939825 3331949266971805403204869)
        ·
          refine ⟨624740487557213513100913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3331949266971805403204869 624740487557213513100913)
          ·
            refine ⟨468555365667910134825685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 624740487557213513100913 468555365667910134825685)
            ·
              refine ⟨10981766382841643784977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 468555365667910134825685 10981766382841643784977)
              ·
                rfl

theorem cell21_433085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 7].length) (baseStart_433085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_433085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_433085 prefixEnd_433085 := by exact prefixLift 433085
  have htrace : WordTrace (prefixWord ++ tailWord_433085) baseStart_433085 baseEnd_433085 := by
    simpa [prefixWord, tailWord_433085, baseEnd_433085] using wordTrace_append hprefix tailTrace_433085
  have hstable : (prefixWord ++ tailWord_433085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433085).length < 2 ^ (prefixWord ++ tailWord_433085).sum := by decide
  have hdescent : baseEnd_433085 < baseStart_433085 := by decide
  rcases family_descends (prefixWord ++ tailWord_433085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433099 : List Nat := [1, 1, 1, 1, 3, 5, 3, 1, 5]
def baseStart_433099 : Nat := 118140960795 + 433099 * 2 ^ 59
def prefixEnd_433099 : Nat := 4983230072969 + 3 ^ 40 * 433099 * 2
def baseEnd_433099 : Nat := 98839092436313880831431

theorem tailTrace_433099 : CollatzResearch.WordTrace tailWord_433099 prefixEnd_433099 98839092436313880831431 := by
  unfold tailWord_433099
  simp only [CollatzResearch.WordTrace]
  refine ⟨15796418257963765265462351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10530945505309176843641567 15796418257963765265462351)
  ·
    refine ⟨23694627386945647898193527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15796418257963765265462351 23694627386945647898193527)
    ·
      refine ⟨35541941080418471847290291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23694627386945647898193527 35541941080418471847290291)
      ·
        refine ⟨53312911620627707770935437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35541941080418471847290291 53312911620627707770935437)
        ·
          refine ⟨19992341857735390414100789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53312911620627707770935437 19992341857735390414100789)
          ·
            refine ⟨1874282049162692851321949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19992341857735390414100789 1874282049162692851321949)
            ·
              refine ⟨702855768436009819245731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1874282049162692851321949 702855768436009819245731)
              ·
                refine ⟨1054283652654014728868597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702855768436009819245731 1054283652654014728868597)
                ·
                  refine ⟨98839092436313880831431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1054283652654014728868597 98839092436313880831431)
                  ·
                    rfl

theorem cell21_433099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 5].length) (baseStart_433099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_433099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_433099 prefixEnd_433099 := by exact prefixLift 433099
  have htrace : WordTrace (prefixWord ++ tailWord_433099) baseStart_433099 baseEnd_433099 := by
    simpa [prefixWord, tailWord_433099, baseEnd_433099] using wordTrace_append hprefix tailTrace_433099
  have hstable : (prefixWord ++ tailWord_433099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433099).length < 2 ^ (prefixWord ++ tailWord_433099).sum := by decide
  have hdescent : baseEnd_433099 < baseStart_433099 := by decide
  rcases family_descends (prefixWord ++ tailWord_433099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433150 : List Nat := [4, 2, 2, 2, 2, 1, 1, 4, 3]
def baseStart_433150 : Nat := 118140960795 + 433150 * 2 ^ 59
def prefixEnd_433150 : Nat := 4983230072969 + 3 ^ 40 * 433150 * 2
def baseEnd_433150 : Nat := 98850731331149125481327

theorem tailTrace_433150 : CollatzResearch.WordTrace tailWord_433150 prefixEnd_433150 98850731331149125481327 := by
  unfold tailWord_433150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1974784797597375121946113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10532185587186000650379269 1974784797597375121946113)
  ·
    refine ⟨1481088598198031341459585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1974784797597375121946113 1481088598198031341459585)
    ·
      refine ⟨1110816448648523506094689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1481088598198031341459585 1110816448648523506094689)
      ·
        refine ⟨833112336486392629571017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1110816448648523506094689 833112336486392629571017)
        ·
          refine ⟨624834252364794472178263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 833112336486392629571017 624834252364794472178263)
          ·
            refine ⟨937251378547191708267395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624834252364794472178263 937251378547191708267395)
            ·
              refine ⟨1405877067820787562401093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937251378547191708267395 1405877067820787562401093)
              ·
                refine ⟨263601950216397667950205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1405877067820787562401093 263601950216397667950205)
                ·
                  refine ⟨98850731331149125481327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263601950216397667950205 98850731331149125481327)
                  ·
                    rfl

theorem cell21_433150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_433150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_433150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_433150 prefixEnd_433150 := by exact prefixLift 433150
  have htrace : WordTrace (prefixWord ++ tailWord_433150) baseStart_433150 baseEnd_433150 := by
    simpa [prefixWord, tailWord_433150, baseEnd_433150] using wordTrace_append hprefix tailTrace_433150
  have hstable : (prefixWord ++ tailWord_433150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433150).length < 2 ^ (prefixWord ++ tailWord_433150).sum := by decide
  have hdescent : baseEnd_433150 < baseStart_433150 := by decide
  rcases family_descends (prefixWord ++ tailWord_433150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433175 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 7]
def baseStart_433175 : Nat := 118140960795 + 433175 * 2 ^ 59
def prefixEnd_433175 : Nat := 4983230072969 + 3 ^ 40 * 433175 * 2
def baseEnd_433175 : Nat := 98856436671754637564609

theorem tailTrace_433175 : CollatzResearch.WordTrace tailWord_433175 prefixEnd_433175 98856436671754637564609 := by
  unfold tailWord_433175
  simp only [CollatzResearch.WordTrace]
  refine ⟨15799190205688430245228979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10532793470458953496819319 15799190205688430245228979)
  ·
    refine ⟨23698785308532645367843469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15799190205688430245228979 23698785308532645367843469)
    ·
      refine ⟨8887044490699742012941301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23698785308532645367843469 8887044490699742012941301)
      ·
        refine ⟨833160421003100813713247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8887044490699742012941301 833160421003100813713247)
        ·
          refine ⟨1249740631504651220569871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833160421003100813713247 1249740631504651220569871)
          ·
            refine ⟨1874610947256976830854807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1249740631504651220569871 1874610947256976830854807)
            ·
              refine ⟨2811916420885465246282211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1874610947256976830854807 2811916420885465246282211)
              ·
                refine ⟨4217874631328197869423317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2811916420885465246282211 4217874631328197869423317)
                ·
                  refine ⟨98856436671754637564609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4217874631328197869423317 98856436671754637564609)
                  ·
                    rfl

theorem cell21_433175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 7].length) (baseStart_433175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_433175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_433175 prefixEnd_433175 := by exact prefixLift 433175
  have htrace : WordTrace (prefixWord ++ tailWord_433175) baseStart_433175 baseEnd_433175 := by
    simpa [prefixWord, tailWord_433175, baseEnd_433175] using wordTrace_append hprefix tailTrace_433175
  have hstable : (prefixWord ++ tailWord_433175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433175).length < 2 ^ (prefixWord ++ tailWord_433175).sum := by decide
  have hdescent : baseEnd_433175 < baseStart_433175 := by decide
  rcases family_descends (prefixWord ++ tailWord_433175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433189 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 6]
def baseStart_433189 : Nat := 118140960795 + 433189 * 2 ^ 59
def prefixEnd_433189 : Nat := 4983230072969 + 3 ^ 40 * 433189 * 2
def baseEnd_433189 : Nat := 98859631662493724331247

theorem tailTrace_433189 : CollatzResearch.WordTrace tailWord_433189 prefixEnd_433189 98859631662493724331247 := by
  unfold tailWord_433189
  simp only [CollatzResearch.WordTrace]
  refine ⟨15799700827637710636238621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10533133885091807090825747 15799700827637710636238621)
  ·
    refine ⟨5924887810364141488589483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15799700827637710636238621 5924887810364141488589483)
    ·
      refine ⟨8887331715546212232884225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5924887810364141488589483 8887331715546212232884225)
      ·
        refine ⟨6665498786659659174663169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8887331715546212232884225 6665498786659659174663169)
        ·
          refine ⟨4999124089994744380997377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6665498786659659174663169 4999124089994744380997377)
          ·
            refine ⟨3749343067496058285748033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4999124089994744380997377 3749343067496058285748033)
            ·
              refine ⟨2812007300622043714311025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3749343067496058285748033 2812007300622043714311025)
              ·
                refine ⟨2109005475466532785733269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2812007300622043714311025 2109005475466532785733269)
                ·
                  refine ⟨98859631662493724331247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2109005475466532785733269 98859631662493724331247)
                  ·
                    rfl

theorem cell21_433189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_433189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_433189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_433189 prefixEnd_433189 := by exact prefixLift 433189
  have htrace : WordTrace (prefixWord ++ tailWord_433189) baseStart_433189 baseEnd_433189 := by
    simpa [prefixWord, tailWord_433189, baseEnd_433189] using wordTrace_append hprefix tailTrace_433189
  have hstable : (prefixWord ++ tailWord_433189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433189).length < 2 ^ (prefixWord ++ tailWord_433189).sum := by decide
  have hdescent : baseEnd_433189 < baseStart_433189 := by decide
  rcases family_descends (prefixWord ++ tailWord_433189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433223 : List Nat := [1, 1, 4, 1, 3, 3, 3, 1, 4]
def baseStart_433223 : Nat := 118140960795 + 433223 * 2 ^ 59
def prefixEnd_433223 : Nat := 4983230072969 + 3 ^ 40 * 433223 * 2
def baseEnd_433223 : Nat := 98867390925717220764511

theorem tailTrace_433223 : CollatzResearch.WordTrace tailWord_433223 prefixEnd_433223 98867390925717220764511 := by
  unfold tailWord_433223
  simp only [CollatzResearch.WordTrace]
  refine ⟨15800940909514534442976323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10533960606343022961984215 15800940909514534442976323)
  ·
    refine ⟨23701411364271801664464485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15800940909514534442976323 23701411364271801664464485)
    ·
      refine ⟨4444014630800962812087091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23701411364271801664464485 4444014630800962812087091)
      ·
        refine ⟨6666021946201444218130637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4444014630800962812087091 6666021946201444218130637)
        ·
          refine ⟨2499758229825541581798989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6666021946201444218130637 2499758229825541581798989)
          ·
            refine ⟨937409336184578093174621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2499758229825541581798989 937409336184578093174621)
            ·
              refine ⟨351528501069216784940483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 937409336184578093174621 351528501069216784940483)
              ·
                refine ⟨527292751603825177410725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351528501069216784940483 527292751603825177410725)
                ·
                  refine ⟨98867390925717220764511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 527292751603825177410725 98867390925717220764511)
                  ·
                    rfl

theorem cell21_433223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 4].length) (baseStart_433223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_433223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_433223 prefixEnd_433223 := by exact prefixLift 433223
  have htrace : WordTrace (prefixWord ++ tailWord_433223) baseStart_433223 baseEnd_433223 := by
    simpa [prefixWord, tailWord_433223, baseEnd_433223] using wordTrace_append hprefix tailTrace_433223
  have hstable : (prefixWord ++ tailWord_433223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433223).length < 2 ^ (prefixWord ++ tailWord_433223).sum := by decide
  have hdescent : baseEnd_433223 < baseStart_433223 := by decide
  rcases family_descends (prefixWord ++ tailWord_433223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433406 : List Nat := [4, 2, 2, 1, 1, 4, 2, 5]
def baseStart_433406 : Nat := 118140960795 + 433406 * 2 ^ 59
def prefixEnd_433406 : Nat := 4983230072969 + 3 ^ 40 * 433406 * 2
def baseEnd_433406 : Nat := 32969718006316523071379

theorem tailTrace_433406 : CollatzResearch.WordTrace tailWord_433406 prefixEnd_433406 32969718006316523071379 := by
  unfold tailWord_433406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1975951933481444587111009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10538410311901037797925381 1975951933481444587111009)
  ·
    refine ⟨1481963950111083440333257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1975951933481444587111009 1481963950111083440333257)
    ·
      refine ⟨1111472962583312580249943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1481963950111083440333257 1111472962583312580249943)
      ·
        refine ⟨1667209443874968870374915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1111472962583312580249943 1667209443874968870374915)
        ·
          refine ⟨2500814165812453305562373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1667209443874968870374915 2500814165812453305562373)
          ·
            refine ⟨468902656089834994792945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2500814165812453305562373 468902656089834994792945)
            ·
              refine ⟨351676992067376246094709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468902656089834994792945 351676992067376246094709)
              ·
                refine ⟨32969718006316523071379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 351676992067376246094709 32969718006316523071379)
                ·
                  rfl

theorem cell21_433406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_433406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_433406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_433406 prefixEnd_433406 := by exact prefixLift 433406
  have htrace : WordTrace (prefixWord ++ tailWord_433406) baseStart_433406 baseEnd_433406 := by
    simpa [prefixWord, tailWord_433406, baseEnd_433406] using wordTrace_append hprefix tailTrace_433406
  have hstable : (prefixWord ++ tailWord_433406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433406).length < 2 ^ (prefixWord ++ tailWord_433406).sum := by decide
  have hdescent : baseEnd_433406 < baseStart_433406 := by decide
  rcases family_descends (prefixWord ++ tailWord_433406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433420 : List Nat := [2, 2, 1, 2, 2, 3, 3, 3, 3]
def baseStart_433420 : Nat := 118140960795 + 433420 * 2 ^ 59
def prefixEnd_433420 : Nat := 4983230072969 + 3 ^ 40 * 433420 * 2
def baseEnd_433420 : Nat := 98912349009688655980775

theorem tailTrace_433420 : CollatzResearch.WordTrace tailWord_433420 prefixEnd_433420 98912349009688655980775 := by
  unfold tailWord_433420
  simp only [CollatzResearch.WordTrace]
  refine ⟨7904063044900418543948857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10538750726533891391931809 7904063044900418543948857)
  ·
    refine ⟨5928047283675313907961643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7904063044900418543948857 5928047283675313907961643)
    ·
      refine ⟨8892070925512970861942465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5928047283675313907961643 8892070925512970861942465)
      ·
        refine ⟨6669053194134728146456849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8892070925512970861942465 6669053194134728146456849)
        ·
          refine ⟨5001789895601046109842637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6669053194134728146456849 5001789895601046109842637)
          ·
            refine ⟨1875671210850392291190989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5001789895601046109842637 1875671210850392291190989)
            ·
              refine ⟨703376704068897109196621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1875671210850392291190989 703376704068897109196621)
              ·
                refine ⟨263766264025836415948733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 703376704068897109196621 263766264025836415948733)
                ·
                  refine ⟨98912349009688655980775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263766264025836415948733 98912349009688655980775)
                  ·
                    rfl

theorem cell21_433420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_433420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_433420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_433420 prefixEnd_433420 := by exact prefixLift 433420
  have htrace : WordTrace (prefixWord ++ tailWord_433420) baseStart_433420 baseEnd_433420 := by
    simpa [prefixWord, tailWord_433420, baseEnd_433420] using wordTrace_append hprefix tailTrace_433420
  have hstable : (prefixWord ++ tailWord_433420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433420).length < 2 ^ (prefixWord ++ tailWord_433420).sum := by decide
  have hdescent : baseEnd_433420 < baseStart_433420 := by decide
  rcases family_descends (prefixWord ++ tailWord_433420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433448 : List Nat := [2, 1, 5, 1, 2, 1, 1, 8]
def baseStart_433448 : Nat := 118140960795 + 433448 * 2 ^ 59
def prefixEnd_433448 : Nat := 4983230072969 + 3 ^ 40 * 433448 * 2
def baseEnd_433448 : Nat := 32972912997055609838017

theorem tailTrace_433448 : CollatzResearch.WordTrace tailWord_433448 prefixEnd_433448 32972912997055609838017 := by
  unfold tailWord_433448
  simp only [CollatzResearch.WordTrace]
  refine ⟨7904573666849698934958499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10539431555799598579944665 7904573666849698934958499)
  ·
    refine ⟨11856860500274548402437749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7904573666849698934958499 11856860500274548402437749)
    ·
      refine ⟨1111580671900738912728539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11856860500274548402437749 1111580671900738912728539)
      ·
        refine ⟨1667371007851108369092809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1111580671900738912728539 1667371007851108369092809)
        ·
          refine ⟨1250528255888331276819607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1667371007851108369092809 1250528255888331276819607)
          ·
            refine ⟨1875792383832496915229411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1250528255888331276819607 1875792383832496915229411)
            ·
              refine ⟨2813688575748745372844117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1875792383832496915229411 2813688575748745372844117)
              ·
                refine ⟨32972912997055609838017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2813688575748745372844117 32972912997055609838017)
                ·
                  rfl

theorem cell21_433448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 8].length) (baseStart_433448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_433448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_433448 prefixEnd_433448 := by exact prefixLift 433448
  have htrace : WordTrace (prefixWord ++ tailWord_433448) baseStart_433448 baseEnd_433448 := by
    simpa [prefixWord, tailWord_433448, baseEnd_433448] using wordTrace_append hprefix tailTrace_433448
  have hstable : (prefixWord ++ tailWord_433448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433448).length < 2 ^ (prefixWord ++ tailWord_433448).sum := by decide
  have hdescent : baseEnd_433448 < baseStart_433448 := by decide
  rcases family_descends (prefixWord ++ tailWord_433448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433589 : List Nat := [1, 3, 3, 2, 2, 3, 1, 3, 3]
def baseStart_433589 : Nat := 118140960795 + 433589 * 2 ^ 59
def prefixEnd_433589 : Nat := 4983230072969 + 3 ^ 40 * 433589 * 2
def baseEnd_433589 : Nat := 98950917112181917663763

theorem tailTrace_433589 : CollatzResearch.WordTrace tailWord_433589 prefixEnd_433589 98950917112181917663763 := by
  unfold tailWord_433589
  simp only [CollatzResearch.WordTrace]
  refine ⟨15814290026188578950799821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10542860017459052633866547 15814290026188578950799821)
  ·
    refine ⟨5930358759820717106549933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15814290026188578950799821 5930358759820717106549933)
    ·
      refine ⟨2223884534932768914956225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5930358759820717106549933 2223884534932768914956225)
      ·
        refine ⟨1667913401199576686217169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2223884534932768914956225 1667913401199576686217169)
        ·
          refine ⟨1250935050899682514662877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1667913401199576686217169 1250935050899682514662877)
          ·
            refine ⟨469100644087380942998579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1250935050899682514662877 469100644087380942998579)
            ·
              refine ⟨703650966131071414497869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469100644087380942998579 703650966131071414497869)
              ·
                refine ⟨263869112299151780436701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 703650966131071414497869 263869112299151780436701)
                ·
                  refine ⟨98950917112181917663763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263869112299151780436701 98950917112181917663763)
                  ·
                    rfl

theorem cell21_433589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_433589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_433589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_433589 prefixEnd_433589 := by exact prefixLift 433589
  have htrace : WordTrace (prefixWord ++ tailWord_433589) baseStart_433589 baseEnd_433589 := by
    simpa [prefixWord, tailWord_433589, baseEnd_433589] using wordTrace_append hprefix tailTrace_433589
  have hstable : (prefixWord ++ tailWord_433589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433589).length < 2 ^ (prefixWord ++ tailWord_433589).sum := by decide
  have hdescent : baseEnd_433589 < baseStart_433589 := by decide
  rcases family_descends (prefixWord ++ tailWord_433589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433620 : List Nat := [2, 4, 1, 2, 3, 2, 2, 1, 4]
def baseStart_433620 : Nat := 118140960795 + 433620 * 2 ^ 59
def prefixEnd_433620 : Nat := 4983230072969 + 3 ^ 40 * 433620 * 2
def baseEnd_433620 : Nat := 98957991734532752647033

theorem tailTrace_433620 : CollatzResearch.WordTrace tailWord_433620 prefixEnd_433620 98957991734532752647033 := by
  unfold tailWord_433620
  simp only [CollatzResearch.WordTrace]
  refine ⟨7907710344538135622589157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10543613792717514163452209 7907710344538135622589157)
  ·
    refine ⟨1482695689600900429235467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7907710344538135622589157 1482695689600900429235467)
    ·
      refine ⟨2224043534401350643853201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1482695689600900429235467 2224043534401350643853201)
      ·
        refine ⟨1668032650801012982889901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2224043534401350643853201 1668032650801012982889901)
        ·
          refine ⟨625512244050379868583713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1668032650801012982889901 625512244050379868583713)
          ·
            refine ⟨469134183037784901437785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 625512244050379868583713 469134183037784901437785)
            ·
              refine ⟨351850637278338676078339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469134183037784901437785 351850637278338676078339)
              ·
                refine ⟨527775955917508014117509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351850637278338676078339 527775955917508014117509)
                ·
                  refine ⟨98957991734532752647033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 527775955917508014117509 98957991734532752647033)
                  ·
                    rfl

theorem cell21_433620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_433620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_433620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_433620 prefixEnd_433620 := by exact prefixLift 433620
  have htrace : WordTrace (prefixWord ++ tailWord_433620) baseStart_433620 baseEnd_433620 := by
    simpa [prefixWord, tailWord_433620, baseEnd_433620] using wordTrace_append hprefix tailTrace_433620
  have hstable : (prefixWord ++ tailWord_433620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433620).length < 2 ^ (prefixWord ++ tailWord_433620).sum := by decide
  have hdescent : baseEnd_433620 < baseStart_433620 := by decide
  rcases family_descends (prefixWord ++ tailWord_433620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433721 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 6]
def baseStart_433721 : Nat := 118140960795 + 433721 * 2 ^ 59
def prefixEnd_433721 : Nat := 4983230072969 + 3 ^ 40 * 433721 * 2
def baseEnd_433721 : Nat := 98981041310579021463493

theorem tailTrace_433721 : CollatzResearch.WordTrace tailWord_433721 prefixEnd_433721 98981041310579021463493 := by
  unfold tailWord_433721
  simp only [CollatzResearch.WordTrace]
  refine ⟨15819104461710365494605017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10546069641140243663070011 15819104461710365494605017)
  ·
    refine ⟨11864328346282774120953763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15819104461710365494605017 11864328346282774120953763)
    ·
      refine ⟨17796492519424161181430645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11864328346282774120953763 17796492519424161181430645)
      ·
        refine ⟨1668421173696015110759123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17796492519424161181430645 1668421173696015110759123)
        ·
          refine ⟨2502631760544022666138685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1668421173696015110759123 2502631760544022666138685)
          ·
            refine ⟨938486910204008499802007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2502631760544022666138685 938486910204008499802007)
            ·
              refine ⟨1407730365306012749703011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938486910204008499802007 1407730365306012749703011)
              ·
                refine ⟨2111595547959019124554517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1407730365306012749703011 2111595547959019124554517)
                ·
                  refine ⟨98981041310579021463493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2111595547959019124554517 98981041310579021463493)
                  ·
                    rfl

theorem cell21_433721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_433721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_433721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_433721 prefixEnd_433721 := by exact prefixLift 433721
  have htrace : WordTrace (prefixWord ++ tailWord_433721) baseStart_433721 baseEnd_433721 := by
    simpa [prefixWord, tailWord_433721, baseEnd_433721] using wordTrace_append hprefix tailTrace_433721
  have hstable : (prefixWord ++ tailWord_433721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433721).length < 2 ^ (prefixWord ++ tailWord_433721).sum := by decide
  have hdescent : baseEnd_433721 < baseStart_433721 := by decide
  rcases family_descends (prefixWord ++ tailWord_433721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433738 : List Nat := [3, 1, 2, 1, 1, 3, 5, 1, 4]
def baseStart_433738 : Nat := 118140960795 + 433738 * 2 ^ 59
def prefixEnd_433738 : Nat := 4983230072969 + 3 ^ 40 * 433738 * 2
def baseEnd_433738 : Nat := 98984920942190769680125

theorem tailTrace_433738 : CollatzResearch.WordTrace tailWord_433738 prefixEnd_433738 98984920942190769680125 := by
  unfold tailWord_433738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3954931125662194349493467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10546483001765851598649245 3954931125662194349493467)
  ·
    refine ⟨5932396688493291524240201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3954931125662194349493467 5932396688493291524240201)
    ·
      refine ⟨4449297516369968643180151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5932396688493291524240201 4449297516369968643180151)
      ·
        refine ⟨6673946274554952964770227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4449297516369968643180151 6673946274554952964770227)
        ·
          refine ⟨10010919411832429447155341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6673946274554952964770227 10010919411832429447155341)
          ·
            refine ⟨3754094779437161042683253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10010919411832429447155341 3754094779437161042683253)
            ·
              refine ⟨351946385572233847751555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3754094779437161042683253 351946385572233847751555)
              ·
                refine ⟨527919578358350771627333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351946385572233847751555 527919578358350771627333)
                ·
                  refine ⟨98984920942190769680125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 527919578358350771627333 98984920942190769680125)
                  ·
                    rfl

theorem cell21_433738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_433738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_433738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_433738 prefixEnd_433738 := by exact prefixLift 433738
  have htrace : WordTrace (prefixWord ++ tailWord_433738) baseStart_433738 baseEnd_433738 := by
    simpa [prefixWord, tailWord_433738, baseEnd_433738] using wordTrace_append hprefix tailTrace_433738
  have hstable : (prefixWord ++ tailWord_433738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433738).length < 2 ^ (prefixWord ++ tailWord_433738).sum := by decide
  have hdescent : baseEnd_433738 < baseStart_433738 := by decide
  rcases family_descends (prefixWord ++ tailWord_433738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433797 : List Nat := [1, 3, 1, 1, 4, 1, 3, 3, 4]
def baseStart_433797 : Nat := 118140960795 + 433797 * 2 ^ 59
def prefixEnd_433797 : Nat := 4983230072969 + 3 ^ 40 * 433797 * 2
def baseEnd_433797 : Nat := 98998385546019778196671

theorem tailTrace_433797 : CollatzResearch.WordTrace tailWord_433797 prefixEnd_433797 98998385546019778196671 := by
  unfold tailWord_433797
  simp only [CollatzResearch.WordTrace]
  refine ⟨15821876409435030474371645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10547917606290020316247763 15821876409435030474371645)
  ·
    refine ⟨5933203653538136427889367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15821876409435030474371645 5933203653538136427889367)
    ·
      refine ⟨8899805480307204641834051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5933203653538136427889367 8899805480307204641834051)
      ·
        refine ⟨13349708220460806962751077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8899805480307204641834051 13349708220460806962751077)
        ·
          refine ⟨2503070291336401305515827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13349708220460806962751077 2503070291336401305515827)
          ·
            refine ⟨3754605437004601958273741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2503070291336401305515827 3754605437004601958273741)
            ·
              refine ⟨1407977038876725734352653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3754605437004601958273741 1407977038876725734352653)
              ·
                refine ⟨527991389578772150382245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1407977038876725734352653 527991389578772150382245)
                ·
                  refine ⟨98998385546019778196671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 527991389578772150382245 98998385546019778196671)
                  ·
                    rfl

theorem cell21_433797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_433797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_433797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_433797 prefixEnd_433797 := by exact prefixLift 433797
  have htrace : WordTrace (prefixWord ++ tailWord_433797) baseStart_433797 baseEnd_433797 := by
    simpa [prefixWord, tailWord_433797, baseEnd_433797] using wordTrace_append hprefix tailTrace_433797
  have hstable : (prefixWord ++ tailWord_433797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433797).length < 2 ^ (prefixWord ++ tailWord_433797).sum := by decide
  have hdescent : baseEnd_433797 < baseStart_433797 := by decide
  rcases family_descends (prefixWord ++ tailWord_433797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433845 : List Nat := [1, 3, 3, 3, 2, 2, 1, 6]
def baseStart_433845 : Nat := 118140960795 + 433845 * 2 ^ 59
def prefixEnd_433845 : Nat := 4983230072969 + 3 ^ 40 * 433845 * 2
def baseEnd_433845 : Nat := 33003113266660787132191

theorem tailTrace_433845 : CollatzResearch.WordTrace tailWord_433845 prefixEnd_433845 33003113266660787132191 := by
  unfold tailWord_433845
  simp only [CollatzResearch.WordTrace]
  refine ⟨15823627113261134672118989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10549084742174089781412659 15823627113261134672118989)
  ·
    refine ⟨5933860167472925502044621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15823627113261134672118989 5933860167472925502044621)
    ·
      refine ⟨2225197562802347063266733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5933860167472925502044621 2225197562802347063266733)
      ·
        refine ⟨834449086050880148725025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2225197562802347063266733 834449086050880148725025)
        ·
          refine ⟨625836814538160111543769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 834449086050880148725025 625836814538160111543769)
          ·
            refine ⟨469377610903620083657827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 625836814538160111543769 469377610903620083657827)
            ·
              refine ⟨704066416355430125486741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469377610903620083657827 704066416355430125486741)
              ·
                refine ⟨33003113266660787132191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 704066416355430125486741 33003113266660787132191)
                ·
                  rfl

theorem cell21_433845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 6].length) (baseStart_433845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_433845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_433845 prefixEnd_433845 := by exact prefixLift 433845
  have htrace : WordTrace (prefixWord ++ tailWord_433845) baseStart_433845 baseEnd_433845 := by
    simpa [prefixWord, tailWord_433845, baseEnd_433845] using wordTrace_append hprefix tailTrace_433845
  have hstable : (prefixWord ++ tailWord_433845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433845).length < 2 ^ (prefixWord ++ tailWord_433845).sum := by decide
  have hdescent : baseEnd_433845 < baseStart_433845 := by decide
  rcases family_descends (prefixWord ++ tailWord_433845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433876 : List Nat := [2, 4, 1, 3, 1, 1, 1, 5, 3]
def baseStart_433876 : Nat := 118140960795 + 433876 * 2 ^ 59
def prefixEnd_433876 : Nat := 4983230072969 + 3 ^ 40 * 433876 * 2
def baseEnd_433876 : Nat := 99016414422333196379843

theorem tailTrace_433876 : CollatzResearch.WordTrace tailWord_433876 prefixEnd_433876 99016414422333196379843 := by
  unfold tailWord_433876
  simp only [CollatzResearch.WordTrace]
  refine ⟨7912378888074413483248741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10549838517432551310998321 7912378888074413483248741)
  ·
    refine ⟨1483571041513952528109139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7912378888074413483248741 1483571041513952528109139)
    ·
      refine ⟨2225356562270928792163709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1483571041513952528109139 2225356562270928792163709)
      ·
        refine ⟨834508710851598297061391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2225356562270928792163709 834508710851598297061391)
        ·
          refine ⟨1251763066277397445592087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834508710851598297061391 1251763066277397445592087)
          ·
            refine ⟨1877644599416096168388131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251763066277397445592087 1877644599416096168388131)
            ·
              refine ⟨2816466899124144252582197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1877644599416096168388131 2816466899124144252582197)
              ·
                refine ⟨264043771792888523679581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2816466899124144252582197 264043771792888523679581)
                ·
                  refine ⟨99016414422333196379843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264043771792888523679581 99016414422333196379843)
                  ·
                    rfl

theorem cell21_433876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_433876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_433876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_433876 prefixEnd_433876 := by exact prefixLift 433876
  have htrace : WordTrace (prefixWord ++ tailWord_433876) baseStart_433876 baseEnd_433876 := by
    simpa [prefixWord, tailWord_433876, baseEnd_433876] using wordTrace_append hprefix tailTrace_433876
  have hstable : (prefixWord ++ tailWord_433876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433876).length < 2 ^ (prefixWord ++ tailWord_433876).sum := by decide
  have hdescent : baseEnd_433876 < baseStart_433876 := by decide
  rcases family_descends (prefixWord ++ tailWord_433876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433932 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 6]
def baseStart_433932 : Nat := 118140960795 + 433932 * 2 ^ 59
def prefixEnd_433932 : Nat := 4983230072969 + 3 ^ 40 * 433932 * 2
def baseEnd_433932 : Nat := 99029194385289543446395

theorem tailTrace_433932 : CollatzResearch.WordTrace tailWord_433932 prefixEnd_433932 99029194385289543446395 := by
  unfold tailWord_433932
  simp only [CollatzResearch.WordTrace]
  refine ⟨7913400131972974265268025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10551200175963965687024033 7913400131972974265268025)
  ·
    refine ⟨5935050098979730698951019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7913400131972974265268025 5935050098979730698951019)
    ·
      refine ⟨8902575148469596048426529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5935050098979730698951019 8902575148469596048426529)
      ·
        refine ⟨6676931361352197036319897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8902575148469596048426529 6676931361352197036319897)
        ·
          refine ⟨5007698521014147777239923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6676931361352197036319897 5007698521014147777239923)
          ·
            refine ⟨7511547781521221665859885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5007698521014147777239923 7511547781521221665859885)
            ·
              refine ⟨2816830418070458124697457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7511547781521221665859885 2816830418070458124697457)
              ·
                refine ⟨2112622813552843593523093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2816830418070458124697457 2112622813552843593523093)
                ·
                  refine ⟨99029194385289543446395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2112622813552843593523093 99029194385289543446395)
                  ·
                    rfl

theorem cell21_433932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_433932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_433932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_433932 prefixEnd_433932 := by exact prefixLift 433932
  have htrace : WordTrace (prefixWord ++ tailWord_433932) baseStart_433932 baseEnd_433932 := by
    simpa [prefixWord, tailWord_433932, baseEnd_433932] using wordTrace_append hprefix tailTrace_433932
  have hstable : (prefixWord ++ tailWord_433932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433932).length < 2 ^ (prefixWord ++ tailWord_433932).sum := by decide
  have hdescent : baseEnd_433932 < baseStart_433932 := by decide
  rcases family_descends (prefixWord ++ tailWord_433932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433952 : List Nat := [2, 1, 1, 5, 1, 1, 5, 2, 3]
def baseStart_433952 : Nat := 118140960795 + 433952 * 2 ^ 59
def prefixEnd_433952 : Nat := 4983230072969 + 3 ^ 40 * 433952 * 2
def baseEnd_433952 : Nat := 99033758657773953113021

theorem tailTrace_433952 : CollatzResearch.WordTrace tailWord_433952 prefixEnd_433952 99033758657773953113021 := by
  unfold tailWord_433952
  simp only [CollatzResearch.WordTrace]
  refine ⟨7913764861936745973132055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10551686482582327964176073 7913764861936745973132055)
  ·
    refine ⟨11870647292905118959698083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7913764861936745973132055 11870647292905118959698083)
    ·
      refine ⟨17805970939357678439547125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11870647292905118959698083 17805970939357678439547125)
      ·
        refine ⟨1669309775564782353707543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17805970939357678439547125 1669309775564782353707543)
        ·
          refine ⟨2503964663347173530561315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1669309775564782353707543 2503964663347173530561315)
          ·
            refine ⟨3755946995020760295841973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2503964663347173530561315 3755946995020760295841973)
            ·
              refine ⟨352120030783196277735185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3755946995020760295841973 352120030783196277735185)
              ·
                refine ⟨264090023087397208301389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352120030783196277735185 264090023087397208301389)
                ·
                  refine ⟨99033758657773953113021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264090023087397208301389 99033758657773953113021)
                  ·
                    rfl

theorem cell21_433952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 3].length) (baseStart_433952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_433952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_433952 prefixEnd_433952 := by exact prefixLift 433952
  have htrace : WordTrace (prefixWord ++ tailWord_433952) baseStart_433952 baseEnd_433952 := by
    simpa [prefixWord, tailWord_433952, baseEnd_433952] using wordTrace_append hprefix tailTrace_433952
  have hstable : (prefixWord ++ tailWord_433952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433952).length < 2 ^ (prefixWord ++ tailWord_433952).sum := by decide
  have hdescent : baseEnd_433952 < baseStart_433952 := by decide
  rcases family_descends (prefixWord ++ tailWord_433952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434053 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 7]
def baseStart_434053 : Nat := 118140960795 + 434053 * 2 ^ 59
def prefixEnd_434053 : Nat := 4983230072969 + 3 ^ 40 * 434053 * 2
def baseEnd_434053 : Nat := 99056808233820221929481

theorem tailTrace_434053 : CollatzResearch.WordTrace tailWord_434053 prefixEnd_434053 99056808233820221929481 := by
  unfold tailWord_434053
  simp only [CollatzResearch.WordTrace]
  refine ⟨15831213496507586195690813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10554142331005057463793875 15831213496507586195690813)
  ·
    refine ⟨5936705061190344823384055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15831213496507586195690813 5936705061190344823384055)
    ·
      refine ⟨8905057591785517235076083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5936705061190344823384055 8905057591785517235076083)
      ·
        refine ⟨13357586387678275852614125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8905057591785517235076083 13357586387678275852614125)
        ·
          refine ⟨5009094895379353444730297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13357586387678275852614125 5009094895379353444730297)
          ·
            refine ⟨3756821171534515083547723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5009094895379353444730297 3756821171534515083547723)
            ·
              refine ⟨5635231757301772625321585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3756821171534515083547723 5635231757301772625321585)
              ·
                refine ⟨4226423817976329468991189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5635231757301772625321585 4226423817976329468991189)
                ·
                  refine ⟨99056808233820221929481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4226423817976329468991189 99056808233820221929481)
                  ·
                    rfl

theorem cell21_434053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_434053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434053 prefixEnd_434053 := by exact prefixLift 434053
  have htrace : WordTrace (prefixWord ++ tailWord_434053) baseStart_434053 baseEnd_434053 := by
    simpa [prefixWord, tailWord_434053, baseEnd_434053] using wordTrace_append hprefix tailTrace_434053
  have hstable : (prefixWord ++ tailWord_434053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434053).length < 2 ^ (prefixWord ++ tailWord_434053).sum := by decide
  have hdescent : baseEnd_434053 < baseStart_434053 := by decide
  rcases family_descends (prefixWord ++ tailWord_434053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434129 : List Nat := [1, 2, 2, 1, 2, 1, 2, 5, 5]
def baseStart_434129 : Nat := 118140960795 + 434129 * 2 ^ 59
def prefixEnd_434129 : Nat := 4983230072969 + 3 ^ 40 * 434129 * 2
def baseEnd_434129 : Nat := 99074152469260978662659

theorem tailTrace_434129 : CollatzResearch.WordTrace tailWord_434129 prefixEnd_434129 99074152469260978662659 := by
  unfold tailWord_434129
  simp only [CollatzResearch.WordTrace]
  refine ⟨15833985444232251175457441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10555990296154834116971627 15833985444232251175457441)
  ·
    refine ⟨11875489083174188381593081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15833985444232251175457441 11875489083174188381593081)
    ·
      refine ⟨8906616812380641286194811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11875489083174188381593081 8906616812380641286194811)
      ·
        refine ⟨13359925218570961929292217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8906616812380641286194811 13359925218570961929292217)
        ·
          refine ⟨10019943913928221446969163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13359925218570961929292217 10019943913928221446969163)
          ·
            refine ⟨15029915870892332170453745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10019943913928221446969163 15029915870892332170453745)
            ·
              refine ⟨11272436903169249127840309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15029915870892332170453745 11272436903169249127840309)
              ·
                refine ⟨1056790959672117105735029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11272436903169249127840309 1056790959672117105735029)
                ·
                  refine ⟨99074152469260978662659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1056790959672117105735029 99074152469260978662659)
                  ·
                    rfl

theorem cell21_434129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_434129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434129 prefixEnd_434129 := by exact prefixLift 434129
  have htrace : WordTrace (prefixWord ++ tailWord_434129) baseStart_434129 baseEnd_434129 := by
    simpa [prefixWord, tailWord_434129, baseEnd_434129] using wordTrace_append hprefix tailTrace_434129
  have hstable : (prefixWord ++ tailWord_434129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434129).length < 2 ^ (prefixWord ++ tailWord_434129).sum := by decide
  have hdescent : baseEnd_434129 < baseStart_434129 := by decide
  rcases family_descends (prefixWord ++ tailWord_434129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434177 : List Nat := [1, 2, 4, 1, 2, 1, 4, 2, 4]
def baseStart_434177 : Nat := 118140960795 + 434177 * 2 ^ 59
def prefixEnd_434177 : Nat := 4983230072969 + 3 ^ 40 * 434177 * 2
def baseEnd_434177 : Nat := 99085106723223561862561

theorem tailTrace_434177 : CollatzResearch.WordTrace tailWord_434177 prefixEnd_434177 99085106723223561862561 := by
  unfold tailWord_434177
  simp only [CollatzResearch.WordTrace]
  refine ⟨15835736148058355373204785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10557157432038903582136523 15835736148058355373204785)
  ·
    refine ⟨11876802111043766529903589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15835736148058355373204785 11876802111043766529903589)
    ·
      refine ⟨2226900395820706224356923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11876802111043766529903589 2226900395820706224356923)
      ·
        refine ⟨3340350593731059336535385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2226900395820706224356923 3340350593731059336535385)
        ·
          refine ⟨2505262945298294502401539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3340350593731059336535385 2505262945298294502401539)
          ·
            refine ⟨3757894417947441753602309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505262945298294502401539 3757894417947441753602309)
            ·
              refine ⟨704605203365145328800433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3757894417947441753602309 704605203365145328800433)
              ·
                refine ⟨528453902523858996600325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 704605203365145328800433 528453902523858996600325)
                ·
                  refine ⟨99085106723223561862561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 528453902523858996600325 99085106723223561862561)
                  ·
                    rfl

theorem cell21_434177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_434177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434177 prefixEnd_434177 := by exact prefixLift 434177
  have htrace : WordTrace (prefixWord ++ tailWord_434177) baseStart_434177 baseEnd_434177 := by
    simpa [prefixWord, tailWord_434177, baseEnd_434177] using wordTrace_append hprefix tailTrace_434177
  have hstable : (prefixWord ++ tailWord_434177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434177).length < 2 ^ (prefixWord ++ tailWord_434177).sum := by decide
  have hdescent : baseEnd_434177 < baseStart_434177 := by decide
  rcases family_descends (prefixWord ++ tailWord_434177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434228 : List Nat := [2, 5, 1, 2, 3, 1, 1, 2, 4]
def baseStart_434228 : Nat := 118140960795 + 434228 * 2 ^ 59
def prefixEnd_434228 : Nat := 4983230072969 + 3 ^ 40 * 434228 * 2
def baseEnd_434228 : Nat := 99096745618058806512457

theorem tailTrace_434228 : CollatzResearch.WordTrace tailWord_434228 prefixEnd_434228 99096745618058806512457 := by
  unfold tailWord_434228
  simp only [CollatzResearch.WordTrace]
  refine ⟨7918798135436795541655669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10558397513915727388874225 7918798135436795541655669)
  ·
    refine ⟨742387325197199582030219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7918798135436795541655669 742387325197199582030219)
    ·
      refine ⟨1113580987795799373045329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 742387325197199582030219 1113580987795799373045329)
      ·
        refine ⟨835185740846849529783997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1113580987795799373045329 835185740846849529783997)
        ·
          refine ⟨313194652817568573668999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 835185740846849529783997 313194652817568573668999)
          ·
            refine ⟨469791979226352860503499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313194652817568573668999 469791979226352860503499)
            ·
              refine ⟨704687968839529290755249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469791979226352860503499 704687968839529290755249)
              ·
                refine ⟨528515976629646968066437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 704687968839529290755249 528515976629646968066437)
                ·
                  refine ⟨99096745618058806512457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 528515976629646968066437 99096745618058806512457)
                  ·
                    rfl

theorem cell21_434228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_434228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434228 prefixEnd_434228 := by exact prefixLift 434228
  have htrace : WordTrace (prefixWord ++ tailWord_434228) baseStart_434228 baseEnd_434228 := by
    simpa [prefixWord, tailWord_434228, baseEnd_434228] using wordTrace_append hprefix tailTrace_434228
  have hstable : (prefixWord ++ tailWord_434228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434228).length < 2 ^ (prefixWord ++ tailWord_434228).sum := by decide
  have hdescent : baseEnd_434228 < baseStart_434228 := by decide
  rcases family_descends (prefixWord ++ tailWord_434228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434236 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 6]
def baseStart_434236 : Nat := 118140960795 + 434236 * 2 ^ 59
def prefixEnd_434236 : Nat := 4983230072969 + 3 ^ 40 * 434236 * 2
def baseEnd_434236 : Nat := 99098571327052570379107

theorem tailTrace_434236 : CollatzResearch.WordTrace tailWord_434236 prefixEnd_434236 99098571327052570379107 := by
  unfold tailWord_434236
  simp only [CollatzResearch.WordTrace]
  refine ⟨7918944027422304224801281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10558592036563072299735041 7918944027422304224801281)
  ·
    refine ⟨5939208020566728168600961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7918944027422304224801281 5939208020566728168600961)
    ·
      refine ⟨4454406015425046126450721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5939208020566728168600961 4454406015425046126450721)
      ·
        refine ⟨3340804511568784594838041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4454406015425046126450721 3340804511568784594838041)
        ·
          refine ⟨2505603383676588446128531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3340804511568784594838041 2505603383676588446128531)
          ·
            refine ⟨3758405075514882669192797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505603383676588446128531 3758405075514882669192797)
            ·
              refine ⟨1409401903318081000947299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3758405075514882669192797 1409401903318081000947299)
              ·
                refine ⟨2114102854977121501420949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1409401903318081000947299 2114102854977121501420949)
                ·
                  refine ⟨99098571327052570379107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2114102854977121501420949 99098571327052570379107)
                  ·
                    rfl

theorem cell21_434236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_434236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434236 prefixEnd_434236 := by exact prefixLift 434236
  have htrace : WordTrace (prefixWord ++ tailWord_434236) baseStart_434236 baseEnd_434236 := by
    simpa [prefixWord, tailWord_434236, baseEnd_434236] using wordTrace_append hprefix tailTrace_434236
  have hstable : (prefixWord ++ tailWord_434236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434236).length < 2 ^ (prefixWord ++ tailWord_434236).sum := by decide
  have hdescent : baseEnd_434236 < baseStart_434236 := by decide
  rcases family_descends (prefixWord ++ tailWord_434236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434250 : List Nat := [3, 1, 2, 1, 1, 2, 1, 10]
def baseStart_434250 : Nat := 118140960795 + 434250 * 2 ^ 59
def prefixEnd_434250 : Nat := 4983230072969 + 3 ^ 40 * 434250 * 2
def baseEnd_434250 : Nat := 33033922105930552381915

theorem tailTrace_434250 : CollatzResearch.WordTrace tailWord_434250 prefixEnd_434250 33033922105930552381915 := by
  unfold tailWord_434250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3959599669198472210153051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10558932451195925893741469 3959599669198472210153051)
  ·
    refine ⟨5939399503797708315229577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3959599669198472210153051 5939399503797708315229577)
    ·
      refine ⟨4454549627848281236422183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5939399503797708315229577 4454549627848281236422183)
      ·
        refine ⟨6681824441772421854633275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4454549627848281236422183 6681824441772421854633275)
        ·
          refine ⟨10022736662658632781949913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6681824441772421854633275 10022736662658632781949913)
          ·
            refine ⟨7517052496993974586462435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10022736662658632781949913 7517052496993974586462435)
            ·
              refine ⟨11275578745490961879693653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7517052496993974586462435 11275578745490961879693653)
              ·
                refine ⟨33033922105930552381915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11275578745490961879693653 33033922105930552381915)
                ·
                  rfl

theorem cell21_434250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_434250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434250 prefixEnd_434250 := by exact prefixLift 434250
  have htrace : WordTrace (prefixWord ++ tailWord_434250) baseStart_434250 baseEnd_434250 := by
    simpa [prefixWord, tailWord_434250, baseEnd_434250] using wordTrace_append hprefix tailTrace_434250
  have hstable : (prefixWord ++ tailWord_434250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434250).length < 2 ^ (prefixWord ++ tailWord_434250).sum := by decide
  have hdescent : baseEnd_434250 < baseStart_434250 := by decide
  rcases family_descends (prefixWord ++ tailWord_434250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434343 : List Nat := [1, 1, 6, 2, 2, 9]
def baseStart_434343 : Nat := 118140960795 + 434343 * 2 ^ 59
def prefixEnd_434343 : Nat := 4983230072969 + 3 ^ 40 * 434343 * 2
def baseEnd_434343 : Nat := 3671221858697931929465

theorem tailTrace_434343 : CollatzResearch.WordTrace tailWord_434343 prefixEnd_434343 3671221858697931929465 := by
  unfold tailWord_434343
  simp only [CollatzResearch.WordTrace]
  refine ⟨15841790665456965723747683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10561193776971310482498455 15841790665456965723747683)
  ·
    refine ⟨23762685998185448585621525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15841790665456965723747683 23762685998185448585621525)
    ·
      refine ⟨1113875906164942902451009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23762685998185448585621525 1113875906164942902451009)
      ·
        refine ⟨835406929623707176838257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1113875906164942902451009 835406929623707176838257)
        ·
          refine ⟨626555197217780382628693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 835406929623707176838257 626555197217780382628693)
          ·
            refine ⟨3671221858697931929465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 626555197217780382628693 3671221858697931929465)
            ·
              rfl

theorem cell21_434343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 9].length) (baseStart_434343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434343 prefixEnd_434343 := by exact prefixLift 434343
  have htrace : WordTrace (prefixWord ++ tailWord_434343) baseStart_434343 baseEnd_434343 := by
    simpa [prefixWord, tailWord_434343, baseEnd_434343] using wordTrace_append hprefix tailTrace_434343
  have hstable : (prefixWord ++ tailWord_434343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434343).length < 2 ^ (prefixWord ++ tailWord_434343).sum := by decide
  have hdescent : baseEnd_434343 < baseStart_434343 := by decide
  rcases family_descends (prefixWord ++ tailWord_434343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434349 : List Nat := [1, 5, 2, 1, 2, 3, 2, 2, 3]
def baseStart_434349 : Nat := 118140960795 + 434349 * 2 ^ 59
def prefixEnd_434349 : Nat := 4983230072969 + 3 ^ 40 * 434349 * 2
def baseEnd_434349 : Nat := 99124359466589484995543

theorem tailTrace_434349 : CollatzResearch.WordTrace tailWord_434349 prefixEnd_434349 99124359466589484995543 := by
  unfold tailWord_434349
  simp only [CollatzResearch.WordTrace]
  refine ⟨15842009503435228748466101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10561339668956819165644067 15842009503435228748466101)
  ·
    refine ⟨1485188390947052695168697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15842009503435228748466101 1485188390947052695168697)
    ·
      refine ⟨1113891293210289521376523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1485188390947052695168697 1113891293210289521376523)
      ·
        refine ⟨1670836939815434282064785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1113891293210289521376523 1670836939815434282064785)
        ·
          refine ⟨1253127704861575711548589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1670836939815434282064785 1253127704861575711548589)
          ·
            refine ⟨469922889323090891830721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1253127704861575711548589 469922889323090891830721)
            ·
              refine ⟨352442166992318168873041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469922889323090891830721 352442166992318168873041)
              ·
                refine ⟨264331625244238626654781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352442166992318168873041 264331625244238626654781)
                ·
                  refine ⟨99124359466589484995543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264331625244238626654781 99124359466589484995543)
                  ·
                    rfl

theorem cell21_434349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_434349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434349 prefixEnd_434349 := by exact prefixLift 434349
  have htrace : WordTrace (prefixWord ++ tailWord_434349) baseStart_434349 baseEnd_434349 := by
    simpa [prefixWord, tailWord_434349, baseEnd_434349] using wordTrace_append hprefix tailTrace_434349
  have hstable : (prefixWord ++ tailWord_434349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434349).length < 2 ^ (prefixWord ++ tailWord_434349).sum := by decide
  have hdescent : baseEnd_434349 < baseStart_434349 := by decide
  rcases family_descends (prefixWord ++ tailWord_434349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434405 : List Nat := [1, 3, 1, 4, 2, 1, 3, 2, 4]
def baseStart_434405 : Nat := 118140960795 + 434405 * 2 ^ 59
def prefixEnd_434405 : Nat := 4983230072969 + 3 ^ 40 * 434405 * 2
def baseEnd_434405 : Nat := 99137139429545832062095

theorem tailTrace_434405 : CollatzResearch.WordTrace tailWord_434405 prefixEnd_434405 99137139429545832062095 := by
  unfold tailWord_434405
  simp only [CollatzResearch.WordTrace]
  refine ⟨15844051991232350312504669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10562701327488233541669779 15844051991232350312504669)
  ·
    refine ⟨5941519496712131367189251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15844051991232350312504669 5941519496712131367189251)
    ·
      refine ⟨8912279245068197050783877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5941519496712131367189251 8912279245068197050783877)
      ·
        refine ⟨1671052358450286947021977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8912279245068197050783877 1671052358450286947021977)
        ·
          refine ⟨1253289268837715210266483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1671052358450286947021977 1253289268837715210266483)
          ·
            refine ⟨1879933903256572815399725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253289268837715210266483 1879933903256572815399725)
            ·
              refine ⟨704975213721214805774897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1879933903256572815399725 704975213721214805774897)
              ·
                refine ⟨528731410290911104331173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 704975213721214805774897 528731410290911104331173)
                ·
                  refine ⟨99137139429545832062095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 528731410290911104331173 99137139429545832062095)
                  ·
                    rfl

theorem cell21_434405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_434405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434405 prefixEnd_434405 := by exact prefixLift 434405
  have htrace : WordTrace (prefixWord ++ tailWord_434405) baseStart_434405 baseEnd_434405 := by
    simpa [prefixWord, tailWord_434405, baseEnd_434405] using wordTrace_append hprefix tailTrace_434405
  have hstable : (prefixWord ++ tailWord_434405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434405).length < 2 ^ (prefixWord ++ tailWord_434405).sum := by decide
  have hdescent : baseEnd_434405 < baseStart_434405 := by decide
  rcases family_descends (prefixWord ++ tailWord_434405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434433 : List Nat := [1, 2, 4, 1, 1, 2, 1, 4, 5]
def baseStart_434433 : Nat := 118140960795 + 434433 * 2 ^ 59
def prefixEnd_434433 : Nat := 4983230072969 + 3 ^ 40 * 434433 * 2
def baseEnd_434433 : Nat := 99143529411024005595371

theorem tailTrace_434433 : CollatzResearch.WordTrace tailWord_434433 prefixEnd_434433 99143529411024005595371 := by
  unfold tailWord_434433
  simp only [CollatzResearch.WordTrace]
  refine ⟨15845073235130911094523953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10563382156753940729682635 15845073235130911094523953)
  ·
    refine ⟨11883804926348183320892965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15845073235130911094523953 11883804926348183320892965)
    ·
      refine ⟨2228213423690284372667431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11883804926348183320892965 2228213423690284372667431)
      ·
        refine ⟨3342320135535426559001147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2228213423690284372667431 3342320135535426559001147)
        ·
          refine ⟨5013480203303139838501721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3342320135535426559001147 5013480203303139838501721)
          ·
            refine ⟨3760110152477354878876291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5013480203303139838501721 3760110152477354878876291)
            ·
              refine ⟨5640165228716032318314437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3760110152477354878876291 5640165228716032318314437)
              ·
                refine ⟨1057530980384256059683957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5640165228716032318314437 1057530980384256059683957)
                ·
                  refine ⟨99143529411024005595371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1057530980384256059683957 99143529411024005595371)
                  ·
                    rfl

theorem cell21_434433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_434433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434433 prefixEnd_434433 := by exact prefixLift 434433
  have htrace : WordTrace (prefixWord ++ tailWord_434433) baseStart_434433 baseEnd_434433 := by
    simpa [prefixWord, tailWord_434433, baseEnd_434433] using wordTrace_append hprefix tailTrace_434433
  have hstable : (prefixWord ++ tailWord_434433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434433).length < 2 ^ (prefixWord ++ tailWord_434433).sum := by decide
  have hdescent : baseEnd_434433 < baseStart_434433 := by decide
  rcases family_descends (prefixWord ++ tailWord_434433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434464 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 6]
def baseStart_434464 : Nat := 118140960795 + 434464 * 2 ^ 59
def prefixEnd_434464 : Nat := 4983230072969 + 3 ^ 40 * 434464 * 2
def baseEnd_434464 : Nat := 99150604033374840578641

theorem tailTrace_434464 : CollatzResearch.WordTrace tailWord_434464 prefixEnd_434464 99150604033374840578641 := by
  unfold tailWord_434464
  simp only [CollatzResearch.WordTrace]
  refine ⟨7923101949009301694451223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10564135932012402259268297 7923101949009301694451223)
  ·
    refine ⟨11884652923513952541676835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7923101949009301694451223 11884652923513952541676835)
    ·
      refine ⟨17826979385270928812515253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11884652923513952541676835 17826979385270928812515253)
      ·
        refine ⟨1671279317369149576173305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17826979385270928812515253 1671279317369149576173305)
        ·
          refine ⟨1253459488026862182129979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1671279317369149576173305 1253459488026862182129979)
          ·
            refine ⟨1880189232040293273194969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253459488026862182129979 1880189232040293273194969)
            ·
              refine ⟨1410141924030219954896227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1880189232040293273194969 1410141924030219954896227)
              ·
                refine ⟨2115212886045329932344341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410141924030219954896227 2115212886045329932344341)
                ·
                  refine ⟨99150604033374840578641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2115212886045329932344341 99150604033374840578641)
                  ·
                    rfl

theorem cell21_434464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_434464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434464 prefixEnd_434464 := by exact prefixLift 434464
  have htrace : WordTrace (prefixWord ++ tailWord_434464) baseStart_434464 baseEnd_434464 := by
    simpa [prefixWord, tailWord_434464, baseEnd_434464] using wordTrace_append hprefix tailTrace_434464
  have hstable : (prefixWord ++ tailWord_434464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434464).length < 2 ^ (prefixWord ++ tailWord_434464).sum := by decide
  have hdescent : baseEnd_434464 < baseStart_434464 := by decide
  rcases family_descends (prefixWord ++ tailWord_434464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434467 : List Nat := [1, 1, 1, 4, 2, 2, 5, 2, 3]
def baseStart_434467 : Nat := 118140960795 + 434467 * 2 ^ 59
def prefixEnd_434467 : Nat := 4983230072969 + 3 ^ 40 * 434467 * 2
def baseEnd_434467 : Nat := 99151288674247502028635

theorem tailTrace_434467 : CollatzResearch.WordTrace tailWord_434467 prefixEnd_434467 99151288674247502028635 := by
  unfold tailWord_434467
  simp only [CollatzResearch.WordTrace]
  refine ⟨15846313317007734901261655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10564208878005156600841103 15846313317007734901261655)
  ·
    refine ⟨23769469975511602351892483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15846313317007734901261655 23769469975511602351892483)
    ·
      refine ⟨35654204963267403527838725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23769469975511602351892483 35654204963267403527838725)
      ·
        refine ⟨6685163430612638161469761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35654204963267403527838725 6685163430612638161469761)
        ·
          refine ⟨5013872572959478621102321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6685163430612638161469761 5013872572959478621102321)
          ·
            refine ⟨3760404429719608965826741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5013872572959478621102321 3760404429719608965826741)
            ·
              refine ⟨352537915286213340546257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3760404429719608965826741 352537915286213340546257)
              ·
                refine ⟨264403436464660005409693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352537915286213340546257 264403436464660005409693)
                ·
                  refine ⟨99151288674247502028635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264403436464660005409693 99151288674247502028635)
                  ·
                    rfl

theorem cell21_434467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 3].length) (baseStart_434467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434467 prefixEnd_434467 := by exact prefixLift 434467
  have htrace : WordTrace (prefixWord ++ tailWord_434467) baseStart_434467 baseEnd_434467 := by
    simpa [prefixWord, tailWord_434467, baseEnd_434467] using wordTrace_append hprefix tailTrace_434467
  have hstable : (prefixWord ++ tailWord_434467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434467).length < 2 ^ (prefixWord ++ tailWord_434467).sum := by decide
  have hdescent : baseEnd_434467 < baseStart_434467 := by decide
  rcases family_descends (prefixWord ++ tailWord_434467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434481 : List Nat := [1, 2, 2, 3, 4, 1, 1, 3, 4]
def baseStart_434481 : Nat := 118140960795 + 434481 * 2 ^ 59
def prefixEnd_434481 : Nat := 4983230072969 + 3 ^ 40 * 434481 * 2
def baseEnd_434481 : Nat := 99154483664986588795273

theorem tailTrace_434481 : CollatzResearch.WordTrace tailWord_434481 prefixEnd_434481 99154483664986588795273 := by
  unfold tailWord_434481
  simp only [CollatzResearch.WordTrace]
  refine ⟨15846823938957015292271297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10564549292638010194847531 15846823938957015292271297)
  ·
    refine ⟨11885117954217761469203473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15846823938957015292271297 11885117954217761469203473)
    ·
      refine ⟨8913838465663321101902605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11885117954217761469203473 8913838465663321101902605)
      ·
        refine ⟨3342689424623745413213477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8913838465663321101902605 3342689424623745413213477)
        ·
          refine ⟨626754267116952264977527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3342689424623745413213477 626754267116952264977527)
          ·
            refine ⟨940131400675428397466291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626754267116952264977527 940131400675428397466291)
            ·
              refine ⟨1410197101013142596199437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940131400675428397466291 1410197101013142596199437)
              ·
                refine ⟨528823912879928473574789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1410197101013142596199437 528823912879928473574789)
                ·
                  refine ⟨99154483664986588795273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 528823912879928473574789 99154483664986588795273)
                  ·
                    rfl

theorem cell21_434481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_434481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434481 prefixEnd_434481 := by exact prefixLift 434481
  have htrace : WordTrace (prefixWord ++ tailWord_434481) baseStart_434481 baseEnd_434481 := by
    simpa [prefixWord, tailWord_434481, baseEnd_434481] using wordTrace_append hprefix tailTrace_434481
  have hstable : (prefixWord ++ tailWord_434481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434481).length < 2 ^ (prefixWord ++ tailWord_434481).sum := by decide
  have hdescent : baseEnd_434481 < baseStart_434481 := by decide
  rcases family_descends (prefixWord ++ tailWord_434481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434574 : List Nat := [4, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_434574 : Nat := 118140960795 + 434574 * 2 ^ 59
def prefixEnd_434574 : Nat := 4983230072969 + 3 ^ 40 * 434574 * 2
def baseEnd_434574 : Nat := 99175707532039093745083

theorem tailTrace_434574 : CollatzResearch.WordTrace tailWord_434574 prefixEnd_434574 99175707532039093745083 := by
  unfold tailWord_434574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1981276990952511521925847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10566810618413394783604517 1981276990952511521925847)
  ·
    refine ⟨2971915486428767282888771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1981276990952511521925847 2971915486428767282888771)
    ·
      refine ⟨4457873229643150924333157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2971915486428767282888771 4457873229643150924333157)
      ·
        refine ⟨835851230558090798312467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4457873229643150924333157 835851230558090798312467)
        ·
          refine ⟨1253776845837136197468701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835851230558090798312467 1253776845837136197468701)
          ·
            refine ⟨470166317188926074050763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1253776845837136197468701 470166317188926074050763)
            ·
              refine ⟨705249475783389111076145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470166317188926074050763 705249475783389111076145)
              ·
                refine ⟨528937106837541833307109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705249475783389111076145 528937106837541833307109)
                ·
                  refine ⟨99175707532039093745083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 528937106837541833307109 99175707532039093745083)
                  ·
                    rfl

theorem cell21_434574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_434574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434574 prefixEnd_434574 := by exact prefixLift 434574
  have htrace : WordTrace (prefixWord ++ tailWord_434574) baseStart_434574 baseEnd_434574 := by
    simpa [prefixWord, tailWord_434574, baseEnd_434574] using wordTrace_append hprefix tailTrace_434574
  have hstable : (prefixWord ++ tailWord_434574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434574).length < 2 ^ (prefixWord ++ tailWord_434574).sum := by decide
  have hdescent : baseEnd_434574 < baseStart_434574 := by decide
  rcases family_descends (prefixWord ++ tailWord_434574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434585 : List Nat := [1, 2, 1, 2, 1, 4, 4, 1, 5]
def baseStart_434585 : Nat := 118140960795 + 434585 * 2 ^ 59
def prefixEnd_434585 : Nat := 4983230072969 + 3 ^ 40 * 434585 * 2
def baseEnd_434585 : Nat := 99178217881905519061727

theorem tailTrace_434585 : CollatzResearch.WordTrace tailWord_434585 prefixEnd_434585 99178217881905519061727 := by
  unfold tailWord_434585
  simp only [CollatzResearch.WordTrace]
  refine ⟨15850617130580241054057209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10567078087053494036038139 15850617130580241054057209)
  ·
    refine ⟨11887962847935180790542907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15850617130580241054057209 11887962847935180790542907)
    ·
      refine ⟨17831944271902771185814361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11887962847935180790542907 17831944271902771185814361)
      ·
        refine ⟨13373958203927078389360771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17831944271902771185814361 13373958203927078389360771)
        ·
          refine ⟨20060937305890617584041157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13373958203927078389360771 20060937305890617584041157)
          ·
            refine ⟨3761425744854490797007717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20060937305890617584041157 3761425744854490797007717)
            ·
              refine ⟨705267327160217024438947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3761425744854490797007717 705267327160217024438947)
              ·
                refine ⟨1057900990740325536658421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705267327160217024438947 1057900990740325536658421)
                ·
                  refine ⟨99178217881905519061727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1057900990740325536658421 99178217881905519061727)
                  ·
                    rfl

theorem cell21_434585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_434585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434585 prefixEnd_434585 := by exact prefixLift 434585
  have htrace : WordTrace (prefixWord ++ tailWord_434585) baseStart_434585 baseEnd_434585 := by
    simpa [prefixWord, tailWord_434585, baseEnd_434585] using wordTrace_append hprefix tailTrace_434585
  have hstable : (prefixWord ++ tailWord_434585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434585).length < 2 ^ (prefixWord ++ tailWord_434585).sum := by decide
  have hdescent : baseEnd_434585 < baseStart_434585 := by decide
  rcases family_descends (prefixWord ++ tailWord_434585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434605 : List Nat := [1, 5, 2, 2, 2, 2, 2, 5]
def baseStart_434605 : Nat := 118140960795 + 434605 * 2 ^ 59
def prefixEnd_434605 : Nat := 4983230072969 + 3 ^ 40 * 434605 * 2
def baseEnd_434605 : Nat := 33060927384796642909451

theorem tailTrace_434605 : CollatzResearch.WordTrace tailWord_434605 prefixEnd_434605 33060927384796642909451 := by
  unfold tailWord_434605
  simp only [CollatzResearch.WordTrace]
  refine ⟨15851346590507784469785269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10567564393671856313190179 15851346590507784469785269)
  ·
    refine ⟨1486063742860104794042369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15851346590507784469785269 1486063742860104794042369)
    ·
      refine ⟨1114547807145078595531777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1486063742860104794042369 1114547807145078595531777)
      ·
        refine ⟨835910855358808946648833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1114547807145078595531777 835910855358808946648833)
        ·
          refine ⟨626933141519106709986625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 835910855358808946648833 626933141519106709986625)
          ·
            refine ⟨470199856139330032489969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 626933141519106709986625 470199856139330032489969)
            ·
              refine ⟨352649892104497524367477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470199856139330032489969 352649892104497524367477)
              ·
                refine ⟨33060927384796642909451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 352649892104497524367477 33060927384796642909451)
                ·
                  rfl

theorem cell21_434605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 5].length) (baseStart_434605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434605 prefixEnd_434605 := by exact prefixLift 434605
  have htrace : WordTrace (prefixWord ++ tailWord_434605) baseStart_434605 baseEnd_434605 := by
    simpa [prefixWord, tailWord_434605, baseEnd_434605] using wordTrace_append hprefix tailTrace_434605
  have hstable : (prefixWord ++ tailWord_434605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434605).length < 2 ^ (prefixWord ++ tailWord_434605).sum := by decide
  have hdescent : baseEnd_434605 < baseStart_434605 := by decide
  rcases family_descends (prefixWord ++ tailWord_434605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434636 : List Nat := [2, 2, 1, 4, 3, 1, 3, 2, 3]
def baseStart_434636 : Nat := 118140960795 + 434636 * 2 ^ 59
def prefixEnd_434636 : Nat := 4983230072969 + 3 ^ 40 * 434636 * 2
def baseEnd_434636 : Nat := 99189856776740763711623

theorem tailTrace_434636 : CollatzResearch.WordTrace tailWord_434636 prefixEnd_434636 99189856776740763711623 := by
  unfold tailWord_434636
  simp only [CollatzResearch.WordTrace]
  refine ⟨7926238626697738382081881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10568318168930317842775841 7926238626697738382081881)
  ·
    refine ⟨5944678970023303786561411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7926238626697738382081881 5944678970023303786561411)
    ·
      refine ⟨8917018455034955679842117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5944678970023303786561411 8917018455034955679842117)
      ·
        refine ⟨1671940960319054189970397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8917018455034955679842117 1671940960319054189970397)
        ·
          refine ⟨626977860119645321238899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1671940960319054189970397 626977860119645321238899)
          ·
            refine ⟨940466790179467981858349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626977860119645321238899 940466790179467981858349)
            ·
              refine ⟨352675046317300493196881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 940466790179467981858349 352675046317300493196881)
              ·
                refine ⟨264506284737975369897661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352675046317300493196881 264506284737975369897661)
                ·
                  refine ⟨99189856776740763711623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264506284737975369897661 99189856776740763711623)
                  ·
                    rfl

theorem cell21_434636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_434636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434636 prefixEnd_434636 := by exact prefixLift 434636
  have htrace : WordTrace (prefixWord ++ tailWord_434636) baseStart_434636 baseEnd_434636 := by
    simpa [prefixWord, tailWord_434636, baseEnd_434636] using wordTrace_append hprefix tailTrace_434636
  have hstable : (prefixWord ++ tailWord_434636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434636).length < 2 ^ (prefixWord ++ tailWord_434636).sum := by decide
  have hdescent : baseEnd_434636 < baseStart_434636 := by decide
  rcases family_descends (prefixWord ++ tailWord_434636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434695 : List Nat := [1, 1, 4, 3, 3, 1, 1, 4, 3]
def baseStart_434695 : Nat := 118140960795 + 434695 * 2 ^ 59
def prefixEnd_434695 : Nat := 4983230072969 + 3 ^ 40 * 434695 * 2
def baseEnd_434695 : Nat := 99203321380569772228169

theorem tailTrace_434695 : CollatzResearch.WordTrace tailWord_434695 prefixEnd_434695 99203321380569772228169 := by
  unfold tailWord_434695
  simp only [CollatzResearch.WordTrace]
  refine ⟨15854629160181729840561539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10569752773454486560374359 15854629160181729840561539)
  ·
    refine ⟨23781943740272594760842309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15854629160181729840561539 23781943740272594760842309)
    ·
      refine ⟨4459114451301111517657933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23781943740272594760842309 4459114451301111517657933)
      ·
        refine ⟨1672167919237916819121725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4459114451301111517657933 1672167919237916819121725)
        ·
          refine ⟨627062969714218807170647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1672167919237916819121725 627062969714218807170647)
          ·
            refine ⟨940594454571328210755971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627062969714218807170647 940594454571328210755971)
            ·
              refine ⟨1410891681856992316133957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940594454571328210755971 1410891681856992316133957)
              ·
                refine ⟨264542190348186059275117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1410891681856992316133957 264542190348186059275117)
                ·
                  refine ⟨99203321380569772228169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264542190348186059275117 99203321380569772228169)
                  ·
                    rfl

theorem cell21_434695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 3].length) (baseStart_434695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434695 prefixEnd_434695 := by exact prefixLift 434695
  have htrace : WordTrace (prefixWord ++ tailWord_434695) baseStart_434695 baseEnd_434695 := by
    simpa [prefixWord, tailWord_434695, baseEnd_434695] using wordTrace_append hprefix tailTrace_434695
  have hstable : (prefixWord ++ tailWord_434695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434695).length < 2 ^ (prefixWord ++ tailWord_434695).sum := by decide
  have hdescent : baseEnd_434695 < baseStart_434695 := by decide
  rcases family_descends (prefixWord ++ tailWord_434695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434723 : List Nat := [1, 1, 1, 4, 4, 2, 3, 5]
def baseStart_434723 : Nat := 118140960795 + 434723 * 2 ^ 59
def prefixEnd_434723 : Nat := 4983230072969 + 3 ^ 40 * 434723 * 2
def baseEnd_434723 : Nat := 33069903787349315253815

theorem tailTrace_434723 : CollatzResearch.WordTrace tailWord_434723 prefixEnd_434723 33069903787349315253815 := by
  unfold tailWord_434723
  simp only [CollatzResearch.WordTrace]
  refine ⟨15855650404080290622580823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10570433602720193748387215 15855650404080290622580823)
  ·
    refine ⟨23783475606120435933871235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15855650404080290622580823 23783475606120435933871235)
    ·
      refine ⟨35675213409180653900806853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23783475606120435933871235 35675213409180653900806853)
      ·
        refine ⟨6689102514221372606401285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35675213409180653900806853 6689102514221372606401285)
        ·
          refine ⟨1254206721416507363700241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6689102514221372606401285 1254206721416507363700241)
          ·
            refine ⟨940655041062380522775181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1254206721416507363700241 940655041062380522775181)
            ·
              refine ⟨352745640398392696040693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 940655041062380522775181 352745640398392696040693)
              ·
                refine ⟨33069903787349315253815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 352745640398392696040693 33069903787349315253815)
                ·
                  rfl

theorem cell21_434723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 5].length) (baseStart_434723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434723 prefixEnd_434723 := by exact prefixLift 434723
  have htrace : WordTrace (prefixWord ++ tailWord_434723) baseStart_434723 baseEnd_434723 := by
    simpa [prefixWord, tailWord_434723, baseEnd_434723] using wordTrace_append hprefix tailTrace_434723
  have hstable : (prefixWord ++ tailWord_434723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434723).length < 2 ^ (prefixWord ++ tailWord_434723).sum := by decide
  have hdescent : baseEnd_434723 < baseStart_434723 := by decide
  rcases family_descends (prefixWord ++ tailWord_434723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434740 : List Nat := [2, 5, 1, 3, 1, 1, 8]
def baseStart_434740 : Nat := 118140960795 + 434740 * 2 ^ 59
def prefixEnd_434740 : Nat := 4983230072969 + 3 ^ 40 * 434740 * 2
def baseEnd_434740 : Nat := 11023732332628854886453

theorem tailTrace_434740 : CollatzResearch.WordTrace tailWord_434740 prefixEnd_434740 11023732332628854886453 := by
  unfold tailWord_434740
  simp only [CollatzResearch.WordTrace]
  refine ⟨7928135222509351262974837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10570846963345801683966449 7928135222509351262974837)
  ·
    refine ⟨743262677110251680903891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7928135222509351262974837 743262677110251680903891)
    ·
      refine ⟨1114894015665377521355837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 743262677110251680903891 1114894015665377521355837)
      ·
        refine ⟨418085255874516570508439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1114894015665377521355837 418085255874516570508439)
        ·
          refine ⟨627127883811774855762659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418085255874516570508439 627127883811774855762659)
          ·
            refine ⟨940691825717662283643989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627127883811774855762659 940691825717662283643989)
            ·
              refine ⟨11023732332628854886453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 940691825717662283643989 11023732332628854886453)
              ·
                rfl

theorem cell21_434740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 8].length) (baseStart_434740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434740 prefixEnd_434740 := by exact prefixLift 434740
  have htrace : WordTrace (prefixWord ++ tailWord_434740) baseStart_434740 baseEnd_434740 := by
    simpa [prefixWord, tailWord_434740, baseEnd_434740] using wordTrace_append hprefix tailTrace_434740
  have hstable : (prefixWord ++ tailWord_434740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434740).length < 2 ^ (prefixWord ++ tailWord_434740).sum := by decide
  have hdescent : baseEnd_434740 < baseStart_434740 := by decide
  rcases family_descends (prefixWord ++ tailWord_434740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434751 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 6]
def baseStart_434751 : Nat := 118140960795 + 434751 * 2 ^ 59
def prefixEnd_434751 : Nat := 4983230072969 + 3 ^ 40 * 434751 * 2
def baseEnd_434751 : Nat := 99216101343526119294721

theorem tailTrace_434751 : CollatzResearch.WordTrace tailWord_434751 prefixEnd_434751 99216101343526119294721 := by
  unfold tailWord_434751
  simp only [CollatzResearch.WordTrace]
  refine ⟨15856671647978851404600107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10571114431985900936400071 15856671647978851404600107)
  ·
    refine ⟨23785007471968277106900161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15856671647978851404600107 23785007471968277106900161)
    ·
      refine ⟨17838755603976207830175121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23785007471968277106900161 17838755603976207830175121)
      ·
        refine ⟨13379066702982155872631341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17838755603976207830175121 13379066702982155872631341)
        ·
          refine ⟨5017150013618308452236753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13379066702982155872631341 5017150013618308452236753)
          ·
            refine ⟨3762862510213731339177565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5017150013618308452236753 3762862510213731339177565)
            ·
              refine ⟨1411073441330149252191587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3762862510213731339177565 1411073441330149252191587)
              ·
                refine ⟨2116610161995223878287381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411073441330149252191587 2116610161995223878287381)
                ·
                  refine ⟨99216101343526119294721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2116610161995223878287381 99216101343526119294721)
                  ·
                    rfl

theorem cell21_434751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 6].length) (baseStart_434751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434751 prefixEnd_434751 := by exact prefixLift 434751
  have htrace : WordTrace (prefixWord ++ tailWord_434751) baseStart_434751 baseEnd_434751 := by
    simpa [prefixWord, tailWord_434751, baseEnd_434751] using wordTrace_append hprefix tailTrace_434751
  have hstable : (prefixWord ++ tailWord_434751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434751).length < 2 ^ (prefixWord ++ tailWord_434751).sum := by decide
  have hdescent : baseEnd_434751 < baseStart_434751 := by decide
  rcases family_descends (prefixWord ++ tailWord_434751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434796 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 7]
def baseStart_434796 : Nat := 118140960795 + 434796 * 2 ^ 59
def prefixEnd_434796 : Nat := 4983230072969 + 3 ^ 40 * 434796 * 2
def baseEnd_434796 : Nat := 99226370956616041044629

theorem tailTrace_434796 : CollatzResearch.WordTrace tailWord_434796 prefixEnd_434796 99226370956616041044629 := by
  unfold tailWord_434796
  simp only [CollatzResearch.WordTrace]
  refine ⟨7929156466407912044994121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10572208621877216059992161 7929156466407912044994121)
  ·
    refine ⟨5946867349805934033745591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7929156466407912044994121 5946867349805934033745591)
    ·
      refine ⟨8920301024708901050618387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5946867349805934033745591 8920301024708901050618387)
      ·
        refine ⟨13380451537063351575927581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8920301024708901050618387 13380451537063351575927581)
        ·
          refine ⟨5017669326398756840972843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13380451537063351575927581 5017669326398756840972843)
          ·
            refine ⟨7526503989598135261459265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5017669326398756840972843 7526503989598135261459265)
            ·
              refine ⟨5644877992198601446094449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7526503989598135261459265 5644877992198601446094449)
              ·
                refine ⟨4233658494148951084570837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5644877992198601446094449 4233658494148951084570837)
                ·
                  refine ⟨99226370956616041044629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4233658494148951084570837 99226370956616041044629)
                  ·
                    rfl

theorem cell21_434796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_434796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434796 prefixEnd_434796 := by exact prefixLift 434796
  have htrace : WordTrace (prefixWord ++ tailWord_434796) baseStart_434796 baseEnd_434796 := by
    simpa [prefixWord, tailWord_434796, baseEnd_434796] using wordTrace_append hprefix tailTrace_434796
  have hstable : (prefixWord ++ tailWord_434796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434796).length < 2 ^ (prefixWord ++ tailWord_434796).sum := by decide
  have hdescent : baseEnd_434796 < baseStart_434796 := by decide
  rcases family_descends (prefixWord ++ tailWord_434796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434841 : List Nat := [1, 2, 1, 2, 1, 2, 3, 9]
def baseStart_434841 : Nat := 118140960795 + 434841 * 2 ^ 59
def prefixEnd_434841 : Nat := 4983230072969 + 3 ^ 40 * 434841 * 2
def baseEnd_434841 : Nat := 33078880189901987598179

theorem tailTrace_434841 : CollatzResearch.WordTrace tailWord_434841 prefixEnd_434841 33078880189901987598179 := by
  unfold tailWord_434841
  simp only [CollatzResearch.WordTrace]
  refine ⟨15859954217652796775376377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10573302811768531183584251 15859954217652796775376377)
  ·
    refine ⟨11894965663239597581532283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15859954217652796775376377 11894965663239597581532283)
    ·
      refine ⟨17842448494859396372298425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11894965663239597581532283 17842448494859396372298425)
      ·
        refine ⟨13381836371144547279223819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17842448494859396372298425 13381836371144547279223819)
        ·
          refine ⟨20072754556716820918835729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13381836371144547279223819 20072754556716820918835729)
          ·
            refine ⟨15054565917537615689126797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20072754556716820918835729 15054565917537615689126797)
            ·
              refine ⟨5645462219076605883422549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15054565917537615689126797 5645462219076605883422549)
              ·
                refine ⟨33078880189901987598179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5645462219076605883422549 33078880189901987598179)
                ·
                  rfl

theorem cell21_434841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 9].length) (baseStart_434841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434841 prefixEnd_434841 := by exact prefixLift 434841
  have htrace : WordTrace (prefixWord ++ tailWord_434841) baseStart_434841 baseEnd_434841 := by
    simpa [prefixWord, tailWord_434841, baseEnd_434841] using wordTrace_append hprefix tailTrace_434841
  have hstable : (prefixWord ++ tailWord_434841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434841).length < 2 ^ (prefixWord ++ tailWord_434841).sum := by decide
  have hdescent : baseEnd_434841 < baseStart_434841 := by decide
  rcases family_descends (prefixWord ++ tailWord_434841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434861 : List Nat := [1, 5, 2, 1, 1, 3, 2, 2, 4]
def baseStart_434861 : Nat := 118140960795 + 434861 * 2 ^ 59
def prefixEnd_434861 : Nat := 4983230072969 + 3 ^ 40 * 434861 * 2
def baseEnd_434861 : Nat := 99241204842190372461163

theorem tailTrace_434861 : CollatzResearch.WordTrace tailWord_434861 prefixEnd_434861 99241204842190372461163 := by
  unfold tailWord_434861
  simp only [CollatzResearch.WordTrace]
  refine ⟨15860683677580340191104437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10573789118386893460736291 15860683677580340191104437)
  ·
    refine ⟨1486939094773156892916041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15860683677580340191104437 1486939094773156892916041)
    ·
      refine ⟨1115204321079867669687031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1486939094773156892916041 1115204321079867669687031)
      ·
        refine ⟨1672806481619801504530547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1115204321079867669687031 1672806481619801504530547)
        ·
          refine ⟨2509209722429702256795821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1672806481619801504530547 2509209722429702256795821)
          ·
            refine ⟨940953645911138346298433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2509209722429702256795821 940953645911138346298433)
            ·
              refine ⟨705715234433353759723825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 940953645911138346298433 705715234433353759723825)
              ·
                refine ⟨529286425825015319792869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705715234433353759723825 529286425825015319792869)
                ·
                  refine ⟨99241204842190372461163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 529286425825015319792869 99241204842190372461163)
                  ·
                    rfl

theorem cell21_434861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_434861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434861 prefixEnd_434861 := by exact prefixLift 434861
  have htrace : WordTrace (prefixWord ++ tailWord_434861) baseStart_434861 baseEnd_434861 := by
    simpa [prefixWord, tailWord_434861, baseEnd_434861] using wordTrace_append hprefix tailTrace_434861
  have hstable : (prefixWord ++ tailWord_434861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434861).length < 2 ^ (prefixWord ++ tailWord_434861).sum := by decide
  have hdescent : baseEnd_434861 < baseStart_434861 := by decide
  rcases family_descends (prefixWord ++ tailWord_434861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434906 : List Nat := [3, 1, 1, 2, 2, 2, 4, 3, 3]
def baseStart_434906 : Nat := 118140960795 + 434906 * 2 ^ 59
def prefixEnd_434906 : Nat := 4983230072969 + 3 ^ 40 * 434906 * 2
def baseEnd_434906 : Nat := 99251474455280294211071

theorem tailTrace_434906 : CollatzResearch.WordTrace tailWord_434906 prefixEnd_434906 99251474455280294211071 := by
  unfold tailWord_434906
  simp only [CollatzResearch.WordTrace]
  refine ⟨3965581240604328219123143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10574883308278208584328381 3965581240604328219123143)
  ·
    refine ⟨5948371860906492328684715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3965581240604328219123143 5948371860906492328684715)
    ·
      refine ⟨8922557791359738493027073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5948371860906492328684715 8922557791359738493027073)
      ·
        refine ⟨6691918343519803869770305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8922557791359738493027073 6691918343519803869770305)
        ·
          refine ⟨5018938757639852902327729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6691918343519803869770305 5018938757639852902327729)
          ·
            refine ⟨3764204068229889676745797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5018938757639852902327729 3764204068229889676745797)
            ·
              refine ⟨705788262793104314389837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3764204068229889676745797 705788262793104314389837)
              ·
                refine ⟨264670598547414117896189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 705788262793104314389837 264670598547414117896189)
                ·
                  refine ⟨99251474455280294211071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264670598547414117896189 99251474455280294211071)
                  ·
                    rfl

theorem cell21_434906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_434906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434906 prefixEnd_434906 := by exact prefixLift 434906
  have htrace : WordTrace (prefixWord ++ tailWord_434906) baseStart_434906 baseEnd_434906 := by
    simpa [prefixWord, tailWord_434906, baseEnd_434906] using wordTrace_append hprefix tailTrace_434906
  have hstable : (prefixWord ++ tailWord_434906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434906).length < 2 ^ (prefixWord ++ tailWord_434906).sum := by decide
  have hdescent : baseEnd_434906 < baseStart_434906 := by decide
  rcases family_descends (prefixWord ++ tailWord_434906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434920 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 6]
def baseStart_434920 : Nat := 118140960795 + 434920 * 2 ^ 59
def prefixEnd_434920 : Nat := 4983230072969 + 3 ^ 40 * 434920 * 2
def baseEnd_434920 : Nat := 99254669446019380977709

theorem tailTrace_434920 : CollatzResearch.WordTrace tailWord_434920 prefixEnd_434920 99254669446019380977709 := by
  unfold tailWord_434920
  simp only [CollatzResearch.WordTrace]
  refine ⟨7931417792183296633751107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10575223722911062178334809 7931417792183296633751107)
  ·
    refine ⟨11897126688274944950626661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7931417792183296633751107 11897126688274944950626661)
    ·
      refine ⟨2230711254051552178242499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11897126688274944950626661 2230711254051552178242499)
      ·
        refine ⟨3346066881077328267363749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2230711254051552178242499 3346066881077328267363749)
        ·
          refine ⟨627387540201999050130703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3346066881077328267363749 627387540201999050130703)
          ·
            refine ⟨941081310302998575196055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627387540201999050130703 941081310302998575196055)
            ·
              refine ⟨1411621965454497862794083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941081310302998575196055 1411621965454497862794083)
              ·
                refine ⟨2117432948181746794191125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411621965454497862794083 2117432948181746794191125)
                ·
                  refine ⟨99254669446019380977709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2117432948181746794191125 99254669446019380977709)
                  ·
                    rfl

theorem cell21_434920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_434920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434920 prefixEnd_434920 := by exact prefixLift 434920
  have htrace : WordTrace (prefixWord ++ tailWord_434920) baseStart_434920 baseEnd_434920 := by
    simpa [prefixWord, tailWord_434920, baseEnd_434920] using wordTrace_append hprefix tailTrace_434920
  have hstable : (prefixWord ++ tailWord_434920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434920).length < 2 ^ (prefixWord ++ tailWord_434920).sum := by decide
  have hdescent : baseEnd_434920 < baseStart_434920 := by decide
  rcases family_descends (prefixWord ++ tailWord_434920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434934 : List Nat := [5, 1, 1, 1, 1, 2, 2, 8]
def baseStart_434934 : Nat := 118140960795 + 434934 * 2 ^ 59
def prefixEnd_434934 : Nat := 4983230072969 + 3 ^ 40 * 434934 * 2
def baseEnd_434934 : Nat := 33085954812252822581449

theorem tailTrace_434934 : CollatzResearch.WordTrace tailWord_434934 prefixEnd_434934 33085954812252822581449 := by
  unfold tailWord_434934
  simp only [CollatzResearch.WordTrace]
  refine ⟨991459137894742103656991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10575564137543915772341237 991459137894742103656991)
  ·
    refine ⟨1487188706842113155485487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 991459137894742103656991 1487188706842113155485487)
    ·
      refine ⟨2230783060263169733228231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1487188706842113155485487 2230783060263169733228231)
      ·
        refine ⟨3346174590394754599842347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2230783060263169733228231 3346174590394754599842347)
        ·
          refine ⟨5019261885592131899763521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3346174590394754599842347 5019261885592131899763521)
          ·
            refine ⟨3764446414194098924822641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5019261885592131899763521 3764446414194098924822641)
            ·
              refine ⟨2823334810645574193616981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3764446414194098924822641 2823334810645574193616981)
              ·
                refine ⟨33085954812252822581449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2823334810645574193616981 33085954812252822581449)
                ·
                  rfl

theorem cell21_434934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_434934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434934 prefixEnd_434934 := by exact prefixLift 434934
  have htrace : WordTrace (prefixWord ++ tailWord_434934) baseStart_434934 baseEnd_434934 := by
    simpa [prefixWord, tailWord_434934, baseEnd_434934] using wordTrace_append hprefix tailTrace_434934
  have hstable : (prefixWord ++ tailWord_434934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434934).length < 2 ^ (prefixWord ++ tailWord_434934).sum := by decide
  have hdescent : baseEnd_434934 < baseStart_434934 := by decide
  rcases family_descends (prefixWord ++ tailWord_434934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434951 : List Nat := [1, 1, 4, 4, 1, 1, 4, 5]
def baseStart_434951 : Nat := 118140960795 + 434951 * 2 ^ 59
def prefixEnd_434951 : Nat := 4983230072969 + 3 ^ 40 * 434951 * 2
def baseEnd_434951 : Nat := 33087248022790071986993

theorem tailTrace_434951 : CollatzResearch.WordTrace tailWord_434951 prefixEnd_434951 33087248022790071986993 := by
  unfold tailWord_434951
  simp only [CollatzResearch.WordTrace]
  refine ⟨15863966247254285561880707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10575977498169523707920471 15863966247254285561880707)
  ·
    refine ⟨23795949370881428342821061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15863966247254285561880707 23795949370881428342821061)
    ·
      refine ⟨4461740507040267814278949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23795949370881428342821061 4461740507040267814278949)
      ·
        refine ⟨836576345070050215177303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4461740507040267814278949 836576345070050215177303)
        ·
          refine ⟨1254864517605075322765955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836576345070050215177303 1254864517605075322765955)
          ·
            refine ⟨1882296776407612984148933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254864517605075322765955 1882296776407612984148933)
            ·
              refine ⟨352930645576427434527925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1882296776407612984148933 352930645576427434527925)
              ·
                refine ⟨33087248022790071986993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 352930645576427434527925 33087248022790071986993)
                ·
                  rfl

theorem cell21_434951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 5].length) (baseStart_434951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434951 prefixEnd_434951 := by exact prefixLift 434951
  have htrace : WordTrace (prefixWord ++ tailWord_434951) baseStart_434951 baseEnd_434951 := by
    simpa [prefixWord, tailWord_434951, baseEnd_434951] using wordTrace_append hprefix tailTrace_434951
  have hstable : (prefixWord ++ tailWord_434951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434951).length < 2 ^ (prefixWord ++ tailWord_434951).sum := by decide
  have hdescent : baseEnd_434951 < baseStart_434951 := by decide
  rcases family_descends (prefixWord ++ tailWord_434951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434979 : List Nat := [1, 1, 1, 4, 2, 1, 1, 6, 4]
def baseStart_434979 : Nat := 118140960795 + 434979 * 2 ^ 59
def prefixEnd_434979 : Nat := 4983230072969 + 3 ^ 40 * 434979 * 2
def baseEnd_434979 : Nat := 99268134049848389494255

theorem tailTrace_434979 : CollatzResearch.WordTrace tailWord_434979 prefixEnd_434979 99268134049848389494255 := by
  unfold tailWord_434979
  simp only [CollatzResearch.WordTrace]
  refine ⟨15864987491152846343899991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10576658327435230895933327 15864987491152846343899991)
  ·
    refine ⟨23797481236729269515849987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15864987491152846343899991 23797481236729269515849987)
    ·
      refine ⟨35696221855093904273774981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23797481236729269515849987 35696221855093904273774981)
      ·
        refine ⟨6693041597830107051332809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35696221855093904273774981 6693041597830107051332809)
        ·
          refine ⟨5019781198372580288499607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6693041597830107051332809 5019781198372580288499607)
          ·
            refine ⟨7529671797558870432749411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5019781198372580288499607 7529671797558870432749411)
            ·
              refine ⟨11294507696338305649124117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7529671797558870432749411 11294507696338305649124117)
              ·
                refine ⟨529430048265858077302693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11294507696338305649124117 529430048265858077302693)
                ·
                  refine ⟨99268134049848389494255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 529430048265858077302693 99268134049848389494255)
                  ·
                    rfl

theorem cell21_434979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 4].length) (baseStart_434979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_434979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_434979 prefixEnd_434979 := by exact prefixLift 434979
  have htrace : WordTrace (prefixWord ++ tailWord_434979) baseStart_434979 baseEnd_434979 := by
    simpa [prefixWord, tailWord_434979, baseEnd_434979] using wordTrace_append hprefix tailTrace_434979
  have hstable : (prefixWord ++ tailWord_434979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434979).length < 2 ^ (prefixWord ++ tailWord_434979).sum := by decide
  have hdescent : baseEnd_434979 < baseStart_434979 := by decide
  rcases family_descends (prefixWord ++ tailWord_434979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435069 : List Nat := [1, 4, 1, 1, 2, 1, 2, 9]
def baseStart_435069 : Nat := 118140960795 + 435069 * 2 ^ 59
def prefixEnd_435069 : Nat := 4983230072969 + 3 ^ 40 * 435069 * 2
def baseEnd_435069 : Nat := 33096224425342744331357

theorem tailTrace_435069 : CollatzResearch.WordTrace tailWord_435069 prefixEnd_435069 33096224425342744331357 := by
  unfold tailWord_435069
  simp only [CollatzResearch.WordTrace]
  refine ⟨15868270060826791714676261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10578846707217861143117507 15868270060826791714676261)
  ·
    refine ⟨2975300636405023446501799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15868270060826791714676261 2975300636405023446501799)
    ·
      refine ⟨4462950954607535169752699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2975300636405023446501799 4462950954607535169752699)
      ·
        refine ⟨6694426431911302754629049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4462950954607535169752699 6694426431911302754629049)
        ·
          refine ⟨5020819823933477065971787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6694426431911302754629049 5020819823933477065971787)
          ·
            refine ⟨7531229735900215598957681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5020819823933477065971787 7531229735900215598957681)
            ·
              refine ⟨5648422301925161699218261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7531229735900215598957681 5648422301925161699218261)
              ·
                refine ⟨33096224425342744331357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5648422301925161699218261 33096224425342744331357)
                ·
                  rfl

theorem cell21_435069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 9].length) (baseStart_435069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435069 prefixEnd_435069 := by exact prefixLift 435069
  have htrace : WordTrace (prefixWord ++ tailWord_435069) baseStart_435069 baseEnd_435069 := by
    simpa [prefixWord, tailWord_435069, baseEnd_435069] using wordTrace_append hprefix tailTrace_435069
  have hstable : (prefixWord ++ tailWord_435069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435069).length < 2 ^ (prefixWord ++ tailWord_435069).sum := by decide
  have hdescent : baseEnd_435069 < baseStart_435069 := by decide
  rcases family_descends (prefixWord ++ tailWord_435069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435126 : List Nat := [5, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_435126 : Nat := 118140960795 + 435126 * 2 ^ 59
def prefixEnd_435126 : Nat := 4983230072969 + 3 ^ 40 * 435126 * 2
def baseEnd_435126 : Nat := 99301681452608800543955

theorem tailTrace_435126 : CollatzResearch.WordTrace tailWord_435126 prefixEnd_435126 99301681452608800543955 := by
  unfold tailWord_435126
  simp only [CollatzResearch.WordTrace]
  refine ⟨991896813851268153093827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10580232681080193633000821 991896813851268153093827)
  ·
    refine ⟨1487845220776902229640741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 991896813851268153093827 1487845220776902229640741)
    ·
      refine ⟨278970978895669168057639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1487845220776902229640741 278970978895669168057639)
      ·
        refine ⟨418456468343503752086459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278970978895669168057639 418456468343503752086459)
        ·
          refine ⟨627684702515255628129689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418456468343503752086459 627684702515255628129689)
          ·
            refine ⟨470763526886441721097267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 627684702515255628129689 470763526886441721097267)
            ·
              refine ⟨706145290329662581645901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470763526886441721097267 706145290329662581645901)
              ·
                refine ⟨264804483873623468117213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 706145290329662581645901 264804483873623468117213)
                ·
                  refine ⟨99301681452608800543955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264804483873623468117213 99301681452608800543955)
                  ·
                    rfl

theorem cell21_435126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_435126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435126 prefixEnd_435126 := by exact prefixLift 435126
  have htrace : WordTrace (prefixWord ++ tailWord_435126) baseStart_435126 baseEnd_435126 := by
    simpa [prefixWord, tailWord_435126, baseEnd_435126] using wordTrace_append hprefix tailTrace_435126
  have hstable : (prefixWord ++ tailWord_435126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435126).length < 2 ^ (prefixWord ++ tailWord_435126).sum := by decide
  have hdescent : baseEnd_435126 < baseStart_435126 := by decide
  rcases family_descends (prefixWord ++ tailWord_435126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435162 : List Nat := [3, 1, 1, 2, 4, 2, 2, 6]
def baseStart_435162 : Nat := 118140960795 + 435162 * 2 ^ 59
def prefixEnd_435162 : Nat := 4983230072969 + 3 ^ 40 * 435162 * 2
def baseEnd_435162 : Nat := 33103299047693579314627

theorem tailTrace_435162 : CollatzResearch.WordTrace tailWord_435162 prefixEnd_435162 33103299047693579314627 := by
  unfold tailWord_435162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3967915512372467149452935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10581108032993245731874493 3967915512372467149452935)
  ·
    refine ⟨5951873268558700724179403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3967915512372467149452935 5951873268558700724179403)
    ·
      refine ⟨8927809902838051086269105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5951873268558700724179403 8927809902838051086269105)
      ·
        refine ⟨6695857427128538314701829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8927809902838051086269105 6695857427128538314701829)
        ·
          refine ⟨1255473267586600934006593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6695857427128538314701829 1255473267586600934006593)
          ·
            refine ⟨941604950689950700504945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1255473267586600934006593 941604950689950700504945)
            ·
              refine ⟨706203713017463025378709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 941604950689950700504945 706203713017463025378709)
              ·
                refine ⟨33103299047693579314627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 706203713017463025378709 33103299047693579314627)
                ·
                  rfl

theorem cell21_435162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_435162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435162 prefixEnd_435162 := by exact prefixLift 435162
  have htrace : WordTrace (prefixWord ++ tailWord_435162) baseStart_435162 baseEnd_435162 := by
    simpa [prefixWord, tailWord_435162, baseEnd_435162] using wordTrace_append hprefix tailTrace_435162
  have hstable : (prefixWord ++ tailWord_435162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435162).length < 2 ^ (prefixWord ++ tailWord_435162).sum := by decide
  have hdescent : baseEnd_435162 < baseStart_435162 := by decide
  rcases family_descends (prefixWord ++ tailWord_435162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435165 : List Nat := [1, 4, 3, 1, 2, 1, 4, 1, 4]
def baseStart_435165 : Nat := 118140960795 + 435165 * 2 ^ 59
def prefixEnd_435165 : Nat := 4983230072969 + 3 ^ 40 * 435165 * 2
def baseEnd_435165 : Nat := 99310581783953399393875

theorem tailTrace_435165 : CollatzResearch.WordTrace tailWord_435165 prefixEnd_435165 99310581783953399393875 := by
  unfold tailWord_435165
  simp only [CollatzResearch.WordTrace]
  refine ⟨15871771468479000110170949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10581180978986000073447299 15871771468479000110170949)
  ·
    refine ⟨2975957150339812520657053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15871771468479000110170949 2975957150339812520657053)
    ·
      refine ⟨1115983931377429695246395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2975957150339812520657053 1115983931377429695246395)
      ·
        refine ⟨1673975897066144542869593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1115983931377429695246395 1673975897066144542869593)
        ·
          refine ⟨1255481922799608407152195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1673975897066144542869593 1255481922799608407152195)
          ·
            refine ⟨1883222884199412610728293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255481922799608407152195 1883222884199412610728293)
            ·
              refine ⟨353104290787389864511555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1883222884199412610728293 353104290787389864511555)
              ·
                refine ⟨529656436181084796767333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353104290787389864511555 529656436181084796767333)
                ·
                  refine ⟨99310581783953399393875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 529656436181084796767333 99310581783953399393875)
                  ·
                    rfl

theorem cell21_435165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_435165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_435165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_435165 prefixEnd_435165 := by exact prefixLift 435165
  have htrace : WordTrace (prefixWord ++ tailWord_435165) baseStart_435165 baseEnd_435165 := by
    simpa [prefixWord, tailWord_435165, baseEnd_435165] using wordTrace_append hprefix tailTrace_435165
  have hstable : (prefixWord ++ tailWord_435165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435165).length < 2 ^ (prefixWord ++ tailWord_435165).sum := by decide
  have hdescent : baseEnd_435165 < baseStart_435165 := by decide
  rcases family_descends (prefixWord ++ tailWord_435165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
