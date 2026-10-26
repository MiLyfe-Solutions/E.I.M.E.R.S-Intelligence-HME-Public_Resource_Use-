import V185TrunkScan20Chunk009

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_61397 : List Nat := [1, 3, 2, 3, 2, 3, 1, 1, 4]
def baseStart_61397 : Nat := 118140960795 + 61397 * 2 ^ 59
def prefixEnd_61397 : Nat := 4983230072969 + 3 ^ 40 * 61397 * 2
def baseEnd_61397 : Nat := 28023263772623571249019

theorem tailTrace_61397 : CollatzResearch.WordTrace tailWord_61397 prefixEnd_61397 28023263772623571249019 := by
  unfold tailWord_61397
  simp only [CollatzResearch.WordTrace]
  refine ⟨2239332558576629617894445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1492888372384419745262963 2239332558576629617894445)
  ·
    refine ⟨839749709466236106710417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2239332558576629617894445 839749709466236106710417)
    ·
      refine ⟨629812282099677080032813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 839749709466236106710417 629812282099677080032813)
      ·
        refine ⟨236179605787378905012305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 629812282099677080032813 236179605787378905012305)
        ·
          refine ⟨177134704340534178759229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236179605787378905012305 177134704340534178759229)
          ·
            refine ⟨66425514127700317034711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177134704340534178759229 66425514127700317034711)
            ·
              refine ⟨99638271191550475552067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66425514127700317034711 99638271191550475552067)
              ·
                refine ⟨149457406787325713328101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99638271191550475552067 149457406787325713328101)
                ·
                  refine ⟨28023263772623571249019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149457406787325713328101 28023263772623571249019)
                  ·
                    rfl

theorem cell20_61397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_61397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61397 prefixEnd_61397 := by exact prefixLift 61397
  have htrace : WordTrace (prefixWord ++ tailWord_61397) baseStart_61397 baseEnd_61397 := by
    simpa [prefixWord, tailWord_61397, baseEnd_61397] using wordTrace_append hprefix tailTrace_61397
  have hstable : (prefixWord ++ tailWord_61397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61397).length < 2 ^ (prefixWord ++ tailWord_61397).sum := by decide
  have hdescent : baseEnd_61397 < baseStart_61397 := by decide
  rcases family_descends (prefixWord ++ tailWord_61397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61411 : List Nat := [1, 1, 1, 6, 1, 3, 1, 3, 3]
def baseStart_61411 : Nat := 118140960795 + 61411 * 2 ^ 59
def prefixEnd_61411 : Nat := 4983230072969 + 3 ^ 40 * 61411 * 2
def baseEnd_61411 : Nat := 28029653754101744782295

theorem tailTrace_61411 : CollatzResearch.WordTrace tailWord_61411 prefixEnd_61411 28029653754101744782295 := by
  unfold tailWord_61411
  simp only [CollatzResearch.WordTrace]
  refine ⟨2239843180525910008904087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1493228787017273339269391 2239843180525910008904087)
  ·
    refine ⟨3359764770788865013356131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2239843180525910008904087 3359764770788865013356131)
    ·
      refine ⟨5039647156183297520034197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3359764770788865013356131 5039647156183297520034197)
      ·
        refine ⟨236233460446092071251603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5039647156183297520034197 236233460446092071251603)
        ·
          refine ⟨354350190669138106877405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236233460446092071251603 354350190669138106877405)
          ·
            refine ⟨132881321500926790079027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354350190669138106877405 132881321500926790079027)
            ·
              refine ⟨199321982251390185118541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132881321500926790079027 199321982251390185118541)
              ·
                refine ⟨74745743344271319419453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199321982251390185118541 74745743344271319419453)
                ·
                  refine ⟨28029653754101744782295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74745743344271319419453 28029653754101744782295)
                  ·
                    rfl

theorem cell20_61411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 3].length) (baseStart_61411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61411 prefixEnd_61411 := by exact prefixLift 61411
  have htrace : WordTrace (prefixWord ++ tailWord_61411) baseStart_61411 baseEnd_61411 := by
    simpa [prefixWord, tailWord_61411, baseEnd_61411] using wordTrace_append hprefix tailTrace_61411
  have hstable : (prefixWord ++ tailWord_61411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61411).length < 2 ^ (prefixWord ++ tailWord_61411).sum := by decide
  have hdescent : baseEnd_61411 < baseStart_61411 := by decide
  rcases family_descends (prefixWord ++ tailWord_61411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61456 : List Nat := [2, 1, 1, 1, 1, 1, 1, 10, 2]
def baseStart_61456 : Nat := 118140960795 + 61456 * 2 ^ 59
def prefixEnd_61456 : Nat := 4983230072969 + 3 ^ 40 * 61456 * 2
def baseEnd_61456 : Nat := 28050192980281588282111

theorem tailTrace_61456 : CollatzResearch.WordTrace tailWord_61456 prefixEnd_61456 28050192980281588282111 := by
  unfold tailWord_61456
  simp only [CollatzResearch.WordTrace]
  refine ⟨1120742232681441347146111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1494322976908588462861481 1120742232681441347146111)
  ·
    refine ⟨1681113349022162020719167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1120742232681441347146111 1681113349022162020719167)
    ·
      refine ⟨2521670023533243031078751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1681113349022162020719167 2521670023533243031078751)
      ·
        refine ⟨3782505035299864546618127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2521670023533243031078751 3782505035299864546618127)
        ·
          refine ⟨5673757552949796819927191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3782505035299864546618127 5673757552949796819927191)
          ·
            refine ⟨8510636329424695229890787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5673757552949796819927191 8510636329424695229890787)
            ·
              refine ⟨12765954494137042844836181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8510636329424695229890787 12765954494137042844836181)
              ·
                refine ⟨37400257307042117709481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12765954494137042844836181 37400257307042117709481)
                ·
                  refine ⟨28050192980281588282111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37400257307042117709481 28050192980281588282111)
                  ·
                    rfl

theorem cell20_61456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 2].length) (baseStart_61456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61456 prefixEnd_61456 := by exact prefixLift 61456
  have htrace : WordTrace (prefixWord ++ tailWord_61456) baseStart_61456 baseEnd_61456 := by
    simpa [prefixWord, tailWord_61456, baseEnd_61456] using wordTrace_append hprefix tailTrace_61456
  have hstable : (prefixWord ++ tailWord_61456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61456).length < 2 ^ (prefixWord ++ tailWord_61456).sum := by decide
  have hdescent : baseEnd_61456 < baseStart_61456 := by decide
  rcases family_descends (prefixWord ++ tailWord_61456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61477 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 6]
def baseStart_61477 : Nat := 118140960795 + 61477 * 2 ^ 59
def prefixEnd_61477 : Nat := 4983230072969 + 3 ^ 40 * 61477 * 2
def baseEnd_61477 : Nat := 28059777952498848582025

theorem tailTrace_61477 : CollatzResearch.WordTrace tailWord_61477 prefixEnd_61477 28059777952498848582025 := by
  unfold tailWord_61477
  simp only [CollatzResearch.WordTrace]
  refine ⟨2242250398286803280806685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1494833598857868853871123 2242250398286803280806685)
  ·
    refine ⟨840843899357551230302507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2242250398286803280806685 840843899357551230302507)
    ·
      refine ⟨1261265849036326845453761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 840843899357551230302507 1261265849036326845453761)
      ·
        refine ⟨945949386777245134090321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1261265849036326845453761 945949386777245134090321)
        ·
          refine ⟨709462040082933850567741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 945949386777245134090321 709462040082933850567741)
          ·
            refine ⟨266048265031100193962903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 709462040082933850567741 266048265031100193962903)
            ·
              refine ⟨399072397546650290944355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266048265031100193962903 399072397546650290944355)
              ·
                refine ⟨598608596319975436416533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399072397546650290944355 598608596319975436416533)
                ·
                  refine ⟨28059777952498848582025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 598608596319975436416533 28059777952498848582025)
                  ·
                    rfl

theorem cell20_61477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_61477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61477 prefixEnd_61477 := by exact prefixLift 61477
  have htrace : WordTrace (prefixWord ++ tailWord_61477) baseStart_61477 baseEnd_61477 := by
    simpa [prefixWord, tailWord_61477, baseEnd_61477] using wordTrace_append hprefix tailTrace_61477
  have hstable : (prefixWord ++ tailWord_61477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61477).length < 2 ^ (prefixWord ++ tailWord_61477).sum := by decide
  have hdescent : baseEnd_61477 < baseStart_61477 := by decide
  rcases family_descends (prefixWord ++ tailWord_61477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61494 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_61494 : Nat := 118140960795 + 61494 * 2 ^ 59
def prefixEnd_61494 : Nat := 4983230072969 + 3 ^ 40 * 61494 * 2
def baseEnd_61494 : Nat := 28067537215722345015289

theorem tailTrace_61494 : CollatzResearch.WordTrace tailWord_61494 prefixEnd_61494 28067537215722345015289 := by
  unfold tailWord_61494
  simp only [CollatzResearch.WordTrace]
  refine ⟨140179402451575949010971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1495246959483476789450357 140179402451575949010971)
  ·
    refine ⟨210269103677363923516457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140179402451575949010971 210269103677363923516457)
    ·
      refine ⟨157701827758022942637343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210269103677363923516457 157701827758022942637343)
      ·
        refine ⟨236552741637034413956015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157701827758022942637343 236552741637034413956015)
        ·
          refine ⟨354829112455551620934023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236552741637034413956015 354829112455551620934023)
          ·
            refine ⟨532243668683327431401035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354829112455551620934023 532243668683327431401035)
            ·
              refine ⟨798365503024991147101553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532243668683327431401035 798365503024991147101553)
              ·
                refine ⟨598774127268743360326165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798365503024991147101553 598774127268743360326165)
                ·
                  refine ⟨28067537215722345015289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 598774127268743360326165 28067537215722345015289)
                  ·
                    rfl

theorem cell20_61494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_61494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61494 prefixEnd_61494 := by exact prefixLift 61494
  have htrace : WordTrace (prefixWord ++ tailWord_61494) baseStart_61494 baseEnd_61494 := by
    simpa [prefixWord, tailWord_61494, baseEnd_61494] using wordTrace_append hprefix tailTrace_61494
  have hstable : (prefixWord ++ tailWord_61494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61494).length < 2 ^ (prefixWord ++ tailWord_61494).sum := by decide
  have hdescent : baseEnd_61494 < baseStart_61494 := by decide
  rcases family_descends (prefixWord ++ tailWord_61494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61532 : List Nat := [2, 2, 4, 1, 1, 2, 2, 2, 4]
def baseStart_61532 : Nat := 118140960795 + 61532 * 2 ^ 59
def prefixEnd_61532 : Nat := 4983230072969 + 3 ^ 40 * 61532 * 2
def baseEnd_61532 : Nat := 28084881451163101748467

theorem tailTrace_61532 : CollatzResearch.WordTrace tailWord_61532 prefixEnd_61532 28084881451163101748467 := by
  unfold tailWord_61532
  simp only [CollatzResearch.WordTrace]
  refine ⟨1122128206543773837029425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1496170942058365116039233 1122128206543773837029425)
  ·
    refine ⟨841596154907830377772069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1122128206543773837029425 841596154907830377772069)
    ·
      refine ⟨157799279045218195832263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 841596154907830377772069 157799279045218195832263)
      ·
        refine ⟨236698918567827293748395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157799279045218195832263 236698918567827293748395)
        ·
          refine ⟨355048377851740940622593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236698918567827293748395 355048377851740940622593)
          ·
            refine ⟨266286283388805705466945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355048377851740940622593 266286283388805705466945)
            ·
              refine ⟨199714712541604279100209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266286283388805705466945 199714712541604279100209)
              ·
                refine ⟨149786034406203209325157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199714712541604279100209 149786034406203209325157)
                ·
                  refine ⟨28084881451163101748467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149786034406203209325157 28084881451163101748467)
                  ·
                    rfl

theorem cell20_61532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_61532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61532 prefixEnd_61532 := by exact prefixLift 61532
  have htrace : WordTrace (prefixWord ++ tailWord_61532) baseStart_61532 baseEnd_61532 := by
    simpa [prefixWord, tailWord_61532, baseEnd_61532] using wordTrace_append hprefix tailTrace_61532
  have hstable : (prefixWord ++ tailWord_61532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61532).length < 2 ^ (prefixWord ++ tailWord_61532).sum := by decide
  have hdescent : baseEnd_61532 < baseStart_61532 := by decide
  rcases family_descends (prefixWord ++ tailWord_61532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61539 : List Nat := [1, 1, 1, 5, 1, 1, 6, 4]
def baseStart_61539 : Nat := 118140960795 + 61539 * 2 ^ 59
def prefixEnd_61539 : Nat := 4983230072969 + 3 ^ 40 * 61539 * 2
def baseEnd_61539 : Nat := 9362692147300729505035

theorem tailTrace_61539 : CollatzResearch.WordTrace tailWord_61539 prefixEnd_61539 9362692147300729505035 := by
  unfold tailWord_61539
  simp only [CollatzResearch.WordTrace]
  refine ⟨2244511724062187869563671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1496341149374791913042447 2244511724062187869563671)
  ·
    refine ⟨3366767586093281804345507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2244511724062187869563671 3366767586093281804345507)
    ·
      refine ⟨5050151379139922706518261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3366767586093281804345507 5050151379139922706518261)
      ·
        refine ⟨473451691794367753736087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5050151379139922706518261 473451691794367753736087)
        ·
          refine ⟨710177537691551630604131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473451691794367753736087 710177537691551630604131)
          ·
            refine ⟨1065266306537327445906197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710177537691551630604131 1065266306537327445906197)
            ·
              refine ⟨49934358118937224026853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1065266306537327445906197 49934358118937224026853)
              ·
                refine ⟨9362692147300729505035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49934358118937224026853 9362692147300729505035)
                ·
                  rfl

theorem cell20_61539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 4].length) (baseStart_61539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61539 prefixEnd_61539 := by exact prefixLift 61539
  have htrace : WordTrace (prefixWord ++ tailWord_61539) baseStart_61539 baseEnd_61539 := by
    simpa [prefixWord, tailWord_61539, baseEnd_61539] using wordTrace_append hprefix tailTrace_61539
  have hstable : (prefixWord ++ tailWord_61539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61539).length < 2 ^ (prefixWord ++ tailWord_61539).sum := by decide
  have hdescent : baseEnd_61539 < baseStart_61539 := by decide
  rcases family_descends (prefixWord ++ tailWord_61539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61584 : List Nat := [2, 1, 1, 1, 1, 1, 7, 3, 3]
def baseStart_61584 : Nat := 118140960795 + 61584 * 2 ^ 59
def prefixEnd_61584 : Nat := 4983230072969 + 3 ^ 40 * 61584 * 2
def baseEnd_61584 : Nat := 28108615668082032014921

theorem tailTrace_61584 : CollatzResearch.WordTrace tailWord_61584 prefixEnd_61584 28108615668082032014921 := by
  unfold tailWord_61584
  simp only [CollatzResearch.WordTrace]
  refine ⟨1123076504449580277475903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1497435339266107036634537 1123076504449580277475903)
  ·
    refine ⟨1684614756674370416213855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1123076504449580277475903 1684614756674370416213855)
    ·
      refine ⟨2526922135011555624320783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1684614756674370416213855 2526922135011555624320783)
      ·
        refine ⟨3790383202517333436481175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2526922135011555624320783 3790383202517333436481175)
        ·
          refine ⟨5685574803776000154721763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3790383202517333436481175 5685574803776000154721763)
          ·
            refine ⟨8528362205664000232082645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5685574803776000154721763 8528362205664000232082645)
            ·
              refine ⟨199883489195250005439437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 8528362205664000232082645 199883489195250005439437)
              ·
                refine ⟨74956308448218752039789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199883489195250005439437 74956308448218752039789)
                ·
                  refine ⟨28108615668082032014921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74956308448218752039789 28108615668082032014921)
                  ·
                    rfl

theorem cell20_61584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_61584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61584 prefixEnd_61584 := by exact prefixLift 61584
  have htrace : WordTrace (prefixWord ++ tailWord_61584) baseStart_61584 baseEnd_61584 := by
    simpa [prefixWord, tailWord_61584, baseEnd_61584] using wordTrace_append hprefix tailTrace_61584
  have hstable : (prefixWord ++ tailWord_61584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61584).length < 2 ^ (prefixWord ++ tailWord_61584).sum := by decide
  have hdescent : baseEnd_61584 < baseStart_61584 := by decide
  rcases family_descends (prefixWord ++ tailWord_61584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61629 : List Nat := [1, 4, 1, 2, 1, 1, 1, 5, 4]
def baseStart_61629 : Nat := 118140960795 + 61629 * 2 ^ 59
def prefixEnd_61629 : Nat := 4983230072969 + 3 ^ 40 * 61629 * 2
def baseEnd_61629 : Nat := 28129154894261875514737

theorem tailTrace_61629 : CollatzResearch.WordTrace tailWord_61629 prefixEnd_61629 28129154894261875514737 := by
  unfold tailWord_61629
  simp only [CollatzResearch.WordTrace]
  refine ⟨2247794293736133240339941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1498529529157422160226627 2247794293736133240339941)
  ·
    refine ⟨421461430075524982563739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2247794293736133240339941 421461430075524982563739)
    ·
      refine ⟨632192145113287473845609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421461430075524982563739 632192145113287473845609)
      ·
        refine ⟨474144108834965605384207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 632192145113287473845609 474144108834965605384207)
        ·
          refine ⟨711216163252448408076311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474144108834965605384207 711216163252448408076311)
          ·
            refine ⟨1066824244878672612114467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711216163252448408076311 1066824244878672612114467)
            ·
              refine ⟨1600236367318008918171701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066824244878672612114467 1600236367318008918171701)
              ·
                refine ⟨150022159436063336078597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1600236367318008918171701 150022159436063336078597)
                ·
                  refine ⟨28129154894261875514737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150022159436063336078597 28129154894261875514737)
                  ·
                    rfl

theorem cell20_61629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_61629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61629 prefixEnd_61629 := by exact prefixLift 61629
  have htrace : WordTrace (prefixWord ++ tailWord_61629) baseStart_61629 baseEnd_61629 := by
    simpa [prefixWord, tailWord_61629, baseEnd_61629] using wordTrace_append hprefix tailTrace_61629
  have hstable : (prefixWord ++ tailWord_61629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61629).length < 2 ^ (prefixWord ++ tailWord_61629).sum := by decide
  have hdescent : baseEnd_61629 < baseStart_61629 := by decide
  rcases family_descends (prefixWord ++ tailWord_61629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61646 : List Nat := [4, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_61646 : Nat := 118140960795 + 61646 * 2 ^ 59
def prefixEnd_61646 : Nat := 4983230072969 + 3 ^ 40 * 61646 * 2
def baseEnd_61646 : Nat := 28136914157485371948001

theorem tailTrace_61646 : CollatzResearch.WordTrace tailWord_61646 prefixEnd_61646 28136914157485371948001 := by
  unfold tailWord_61646
  simp only [CollatzResearch.WordTrace]
  refine ⟨281051791834318142963599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1498942889783030095805861 281051791834318142963599)
  ·
    refine ⟨421577687751477214445399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281051791834318142963599 421577687751477214445399)
    ·
      refine ⟨632366531627215821668099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421577687751477214445399 632366531627215821668099)
      ·
        refine ⟨948549797440823732502149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632366531627215821668099 948549797440823732502149)
        ·
          refine ⟨177853087020154449844153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 948549797440823732502149 177853087020154449844153)
          ·
            refine ⟨133389815265115837383115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177853087020154449844153 133389815265115837383115)
            ·
              refine ⟨200084722897673756074673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133389815265115837383115 200084722897673756074673)
              ·
                refine ⟨150063542173255317056005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200084722897673756074673 150063542173255317056005)
                ·
                  refine ⟨28136914157485371948001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150063542173255317056005 28136914157485371948001)
                  ·
                    rfl

theorem cell20_61646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_61646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61646 prefixEnd_61646 := by exact prefixLift 61646
  have htrace : WordTrace (prefixWord ++ tailWord_61646) baseStart_61646 baseEnd_61646 := by
    simpa [prefixWord, tailWord_61646, baseEnd_61646] using wordTrace_append hprefix tailTrace_61646
  have hstable : (prefixWord ++ tailWord_61646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61646).length < 2 ^ (prefixWord ++ tailWord_61646).sum := by decide
  have hdescent : baseEnd_61646 < baseStart_61646 := by decide
  rcases family_descends (prefixWord ++ tailWord_61646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61674 : List Nat := [3, 1, 3, 1, 1, 2, 9]
def baseStart_61674 : Nat := 118140960795 + 61674 * 2 ^ 59
def prefixEnd_61674 : Nat := 4983230072969 + 3 ^ 40 * 61674 * 2
def baseEnd_61674 : Nat := 3127743791160191001617

theorem tailTrace_61674 : CollatzResearch.WordTrace tailWord_61674 prefixEnd_61674 3127743791160191001617 := by
  unfold tailWord_61674
  simp only [CollatzResearch.WordTrace]
  refine ⟨562358894643276481432019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1499623719048737283818717 562358894643276481432019)
  ·
    refine ⟨843538341964914722148029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 562358894643276481432019 843538341964914722148029)
    ·
      refine ⟨316326878236843020805511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 843538341964914722148029 316326878236843020805511)
      ·
        refine ⟨474490317355264531208267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316326878236843020805511 474490317355264531208267)
        ·
          refine ⟨711735476032896796812401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474490317355264531208267 711735476032896796812401)
          ·
            refine ⟨533801607024672597609301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 711735476032896796812401 533801607024672597609301)
            ·
              refine ⟨3127743791160191001617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 533801607024672597609301 3127743791160191001617)
              ·
                rfl

theorem cell20_61674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 9].length) (baseStart_61674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61674 prefixEnd_61674 := by exact prefixLift 61674
  have htrace : WordTrace (prefixWord ++ tailWord_61674) baseStart_61674 baseEnd_61674 := by
    simpa [prefixWord, tailWord_61674, baseEnd_61674] using wordTrace_append hprefix tailTrace_61674
  have hstable : (prefixWord ++ tailWord_61674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61674).length < 2 ^ (prefixWord ++ tailWord_61674).sum := by decide
  have hdescent : baseEnd_61674 < baseStart_61674 := by decide
  rcases family_descends (prefixWord ++ tailWord_61674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61677 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 5]
def baseStart_61677 : Nat := 118140960795 + 61677 * 2 ^ 59
def prefixEnd_61677 : Nat := 4983230072969 + 3 ^ 40 * 61677 * 2
def baseEnd_61677 : Nat := 28151063402187041914541

theorem tailTrace_61677 : CollatzResearch.WordTrace tailWord_61677 prefixEnd_61677 28151063402187041914541 := by
  unfold tailWord_61677
  simp only [CollatzResearch.WordTrace]
  refine ⟨2249544997562237438087285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1499696665041491625391523 2249544997562237438087285)
  ·
    refine ⟨210894843521459759820683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2249544997562237438087285 210894843521459759820683)
    ·
      refine ⟨316342265282189639731025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210894843521459759820683 316342265282189639731025)
      ·
        refine ⟨237256698961642229798269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316342265282189639731025 237256698961642229798269)
        ·
          refine ⟨88971262110615836174351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237256698961642229798269 88971262110615836174351)
          ·
            refine ⟨133456893165923754261527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88971262110615836174351 133456893165923754261527)
            ·
              refine ⟨200185339748885631392291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133456893165923754261527 200185339748885631392291)
              ·
                refine ⟨300278009623328447088437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200185339748885631392291 300278009623328447088437)
                ·
                  refine ⟨28151063402187041914541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 300278009623328447088437 28151063402187041914541)
                  ·
                    rfl

theorem cell20_61677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_61677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61677 prefixEnd_61677 := by exact prefixLift 61677
  have htrace : WordTrace (prefixWord ++ tailWord_61677) baseStart_61677 baseEnd_61677 := by
    simpa [prefixWord, tailWord_61677, baseEnd_61677] using wordTrace_append hprefix tailTrace_61677
  have hstable : (prefixWord ++ tailWord_61677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61677).length < 2 ^ (prefixWord ++ tailWord_61677).sum := by decide
  have hdescent : baseEnd_61677 < baseStart_61677 := by decide
  rcases family_descends (prefixWord ++ tailWord_61677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61694 : List Nat := [4, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_61694 : Nat := 118140960795 + 61694 * 2 ^ 59
def prefixEnd_61694 : Nat := 4983230072969 + 3 ^ 40 * 61694 * 2
def baseEnd_61694 : Nat := 28158822665410538347805

theorem tailTrace_61694 : CollatzResearch.WordTrace tailWord_61694 prefixEnd_61694 28158822665410538347805 := by
  unfold tailWord_61694
  simp only [CollatzResearch.WordTrace]
  refine ⟨281270629812581167682017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1500110025667099560970757 281270629812581167682017)
  ·
    refine ⟨210952972359435875761513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281270629812581167682017 210952972359435875761513)
    ·
      refine ⟨158214729269576906821135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210952972359435875761513 158214729269576906821135)
      ·
        refine ⟨237322093904365360231703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158214729269576906821135 237322093904365360231703)
        ·
          refine ⟨355983140856548040347555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237322093904365360231703 355983140856548040347555)
          ·
            refine ⟨533974711284822060521333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355983140856548040347555 533974711284822060521333)
            ·
              refine ⟨50060129182952068173875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 533974711284822060521333 50060129182952068173875)
              ·
                refine ⟨75090193774428102260813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50060129182952068173875 75090193774428102260813)
                ·
                  refine ⟨28158822665410538347805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75090193774428102260813 28158822665410538347805)
                  ·
                    rfl

theorem cell20_61694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_61694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61694 prefixEnd_61694 := by exact prefixLift 61694
  have htrace : WordTrace (prefixWord ++ tailWord_61694) baseStart_61694 baseEnd_61694 := by
    simpa [prefixWord, tailWord_61694, baseEnd_61694] using wordTrace_append hprefix tailTrace_61694
  have hstable : (prefixWord ++ tailWord_61694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61694).length < 2 ^ (prefixWord ++ tailWord_61694).sum := by decide
  have hdescent : baseEnd_61694 < baseStart_61694 := by decide
  rcases family_descends (prefixWord ++ tailWord_61694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61705 : List Nat := [1, 2, 1, 1, 3, 4, 2, 2, 4]
def baseStart_61705 : Nat := 118140960795 + 61705 * 2 ^ 59
def prefixEnd_61705 : Nat := 4983230072969 + 3 ^ 40 * 61705 * 2
def baseEnd_61705 : Nat := 28163843365143388981093

theorem tailTrace_61705 : CollatzResearch.WordTrace tailWord_61705 prefixEnd_61705 28163843365143388981093 := by
  unfold tailWord_61705
  simp only [CollatzResearch.WordTrace]
  refine ⟨2250566241460798220106569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1500377494307198813404379 2250566241460798220106569)
  ·
    refine ⟨1687924681095598665079927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2250566241460798220106569 1687924681095598665079927)
    ·
      refine ⟨2531887021643397997619891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1687924681095598665079927 2531887021643397997619891)
      ·
        refine ⟨3797830532465096996429837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2531887021643397997619891 3797830532465096996429837)
        ·
          refine ⟨1424186449674411373661189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3797830532465096996429837 1424186449674411373661189)
          ·
            refine ⟨267034959313952132561473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1424186449674411373661189 267034959313952132561473)
            ·
              refine ⟨200276219485464099421105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267034959313952132561473 200276219485464099421105)
              ·
                refine ⟨150207164614098074565829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200276219485464099421105 150207164614098074565829)
                ·
                  refine ⟨28163843365143388981093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150207164614098074565829 28163843365143388981093)
                  ·
                    rfl

theorem cell20_61705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_61705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61705 prefixEnd_61705 := by exact prefixLift 61705
  have htrace : WordTrace (prefixWord ++ tailWord_61705) baseStart_61705 baseEnd_61705 := by
    simpa [prefixWord, tailWord_61705, baseEnd_61705] using wordTrace_append hprefix tailTrace_61705
  have hstable : (prefixWord ++ tailWord_61705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61705).length < 2 ^ (prefixWord ++ tailWord_61705).sum := by decide
  have hdescent : baseEnd_61705 < baseStart_61705 := by decide
  rcases family_descends (prefixWord ++ tailWord_61705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61735 : List Nat := [1, 1, 8, 1, 1, 2, 1, 1, 4]
def baseStart_61735 : Nat := 118140960795 + 61735 * 2 ^ 59
def prefixEnd_61735 : Nat := 4983230072969 + 3 ^ 40 * 61735 * 2
def baseEnd_61735 : Nat := 28177536182596617980971

theorem tailTrace_61735 : CollatzResearch.WordTrace tailWord_61735 prefixEnd_61735 28177536182596617980971 := by
  unfold tailWord_61735
  simp only [CollatzResearch.WordTrace]
  refine ⟨2251660431352113343698659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1501106954234742229132439 2251660431352113343698659)
  ·
    refine ⟨3377490647028170015547989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2251660431352113343698659 3377490647028170015547989)
    ·
      refine ⟨39579968519861367369703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 3377490647028170015547989 39579968519861367369703)
      ·
        refine ⟨59369952779792051054555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39579968519861367369703 59369952779792051054555)
        ·
          refine ⟨89054929169688076581833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59369952779792051054555 89054929169688076581833)
          ·
            refine ⟨66791196877266057436375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89054929169688076581833 66791196877266057436375)
            ·
              refine ⟨100186795315899086154563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66791196877266057436375 100186795315899086154563)
              ·
                refine ⟨150280192973848629231845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100186795315899086154563 150280192973848629231845)
                ·
                  refine ⟨28177536182596617980971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150280192973848629231845 28177536182596617980971)
                  ·
                    rfl

theorem cell20_61735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 4].length) (baseStart_61735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61735 prefixEnd_61735 := by exact prefixLift 61735
  have htrace : WordTrace (prefixWord ++ tailWord_61735) baseStart_61735 baseEnd_61735 := by
    simpa [prefixWord, tailWord_61735, baseEnd_61735] using wordTrace_append hprefix tailTrace_61735
  have hstable : (prefixWord ++ tailWord_61735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61735).length < 2 ^ (prefixWord ++ tailWord_61735).sum := by decide
  have hdescent : baseEnd_61735 < baseStart_61735 := by decide
  rcases family_descends (prefixWord ++ tailWord_61735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61743 : List Nat := [1, 1, 2, 1, 2, 1, 7, 1, 4]
def baseStart_61743 : Nat := 118140960795 + 61743 * 2 ^ 59
def prefixEnd_61743 : Nat := 4983230072969 + 3 ^ 40 * 61743 * 2
def baseEnd_61743 : Nat := 28181187600584145714271

theorem tailTrace_61743 : CollatzResearch.WordTrace tailWord_61743 prefixEnd_61743 28181187600584145714271 := by
  unfold tailWord_61743
  simp only [CollatzResearch.WordTrace]
  refine ⟨2251952215323130709989883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1501301476882087139993255 2251952215323130709989883)
  ·
    refine ⟨3377928322984696064984825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2251952215323130709989883 3377928322984696064984825)
    ·
      refine ⟨2533446242238522048738619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3377928322984696064984825 2533446242238522048738619)
      ·
        refine ⟨3800169363357783073107929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2533446242238522048738619 3800169363357783073107929)
        ·
          refine ⟨2850127022518337304830947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3800169363357783073107929 2850127022518337304830947)
          ·
            refine ⟨4275190533777505957246421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2850127022518337304830947 4275190533777505957246421)
            ·
              refine ⟨100199778135410295872963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4275190533777505957246421 100199778135410295872963)
              ·
                refine ⟨150299667203115443809445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100199778135410295872963 150299667203115443809445)
                ·
                  refine ⟨28181187600584145714271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150299667203115443809445 28181187600584145714271)
                  ·
                    rfl

theorem cell20_61743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 4].length) (baseStart_61743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61743 prefixEnd_61743 := by exact prefixLift 61743
  have htrace : WordTrace (prefixWord ++ tailWord_61743) baseStart_61743 baseEnd_61743 := by
    simpa [prefixWord, tailWord_61743, baseEnd_61743] using wordTrace_append hprefix tailTrace_61743
  have hstable : (prefixWord ++ tailWord_61743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61743).length < 2 ^ (prefixWord ++ tailWord_61743).sum := by decide
  have hdescent : baseEnd_61743 < baseStart_61743 := by decide
  rcases family_descends (prefixWord ++ tailWord_61743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61753 : List Nat := [1, 2, 1, 6, 1, 2, 1, 3, 3]
def baseStart_61753 : Nat := 118140960795 + 61753 * 2 ^ 59
def prefixEnd_61753 : Nat := 4983230072969 + 3 ^ 40 * 61753 * 2
def baseEnd_61753 : Nat := 28185751873068555380897

theorem tailTrace_61753 : CollatzResearch.WordTrace tailWord_61753 prefixEnd_61753 28185751873068555380897 := by
  unfold tailWord_61753
  simp only [CollatzResearch.WordTrace]
  refine ⟨2252316945286902417853913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1501544630191268278569275 2252316945286902417853913)
  ·
    refine ⟨1689237708965176813390435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2252316945286902417853913 1689237708965176813390435)
    ·
      refine ⟨2533856563447765220085653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1689237708965176813390435 2533856563447765220085653)
      ·
        refine ⟨118774526411613994691515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2533856563447765220085653 118774526411613994691515)
        ·
          refine ⟨178161789617420992037273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118774526411613994691515 178161789617420992037273)
          ·
            refine ⟨133621342213065744027955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178161789617420992037273 133621342213065744027955)
            ·
              refine ⟨200432013319598616041933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133621342213065744027955 200432013319598616041933)
              ·
                refine ⟨75162004994849481015725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200432013319598616041933 75162004994849481015725)
                ·
                  refine ⟨28185751873068555380897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75162004994849481015725 28185751873068555380897)
                  ·
                    rfl

theorem cell20_61753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_61753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61753 prefixEnd_61753 := by exact prefixLift 61753
  have htrace : WordTrace (prefixWord ++ tailWord_61753) baseStart_61753 baseEnd_61753 := by
    simpa [prefixWord, tailWord_61753, baseEnd_61753] using wordTrace_append hprefix tailTrace_61753
  have hstable : (prefixWord ++ tailWord_61753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61753).length < 2 ^ (prefixWord ++ tailWord_61753).sum := by decide
  have hdescent : baseEnd_61753 < baseStart_61753 := by decide
  rcases family_descends (prefixWord ++ tailWord_61753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61794 : List Nat := [3, 3, 2, 1, 1, 2, 4, 2, 2]
def baseStart_61794 : Nat := 118140960795 + 61794 * 2 ^ 59
def prefixEnd_61794 : Nat := 4983230072969 + 3 ^ 40 * 61794 * 2
def baseEnd_61794 : Nat := 28204465390254635014063

theorem tailTrace_61794 : CollatzResearch.WordTrace tailWord_61794 prefixEnd_61794 28204465390254635014063 := by
  unfold tailWord_61794
  simp only [CollatzResearch.WordTrace]
  refine ⟨563453084534591605024109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1502541558758910946730957 563453084534591605024109)
  ·
    refine ⟨211294906700471851884041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 563453084534591605024109 211294906700471851884041)
    ·
      refine ⟨158471180025353888913031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211294906700471851884041 158471180025353888913031)
      ·
        refine ⟨237706770038030833369547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158471180025353888913031 237706770038030833369547)
        ·
          refine ⟨356560155057046250054321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237706770038030833369547 356560155057046250054321)
          ·
            refine ⟨267420116292784687540741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356560155057046250054321 267420116292784687540741)
            ·
              refine ⟨50141271804897128913889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267420116292784687540741 50141271804897128913889)
              ·
                refine ⟨37605953853672846685417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50141271804897128913889 37605953853672846685417)
                ·
                  refine ⟨28204465390254635014063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37605953853672846685417 28204465390254635014063)
                  ·
                    rfl

theorem cell20_61794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_61794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61794 prefixEnd_61794 := by exact prefixLift 61794
  have htrace : WordTrace (prefixWord ++ tailWord_61794) baseStart_61794 baseEnd_61794 := by
    simpa [prefixWord, tailWord_61794, baseEnd_61794] using wordTrace_append hprefix tailTrace_61794
  have hstable : (prefixWord ++ tailWord_61794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61794).length < 2 ^ (prefixWord ++ tailWord_61794).sum := by decide
  have hdescent : baseEnd_61794 < baseStart_61794 := by decide
  rcases family_descends (prefixWord ++ tailWord_61794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61819 : List Nat := [1, 1, 1, 1, 1, 8, 1, 2, 4]
def baseStart_61819 : Nat := 118140960795 + 61819 * 2 ^ 59
def prefixEnd_61819 : Nat := 4983230072969 + 3 ^ 40 * 61819 * 2
def baseEnd_61819 : Nat := 28215876071465659180627

theorem tailTrace_61819 : CollatzResearch.WordTrace tailWord_61819 prefixEnd_61819 28215876071465659180627 := by
  unfold tailWord_61819
  simp only [CollatzResearch.WordTrace]
  refine ⟨2254724163047795689756511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1503149442031863793171007 2254724163047795689756511)
  ·
    refine ⟨3382086244571693534634767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2254724163047795689756511 3382086244571693534634767)
    ·
      refine ⟨5073129366857540301952151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3382086244571693534634767 5073129366857540301952151)
      ·
        refine ⟨7609694050286310452928227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5073129366857540301952151 7609694050286310452928227)
        ·
          refine ⟨11414541075429465679392341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7609694050286310452928227 11414541075429465679392341)
          ·
            refine ⟨133764153227689050930379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 11414541075429465679392341 133764153227689050930379)
            ·
              refine ⟨200646229841533576395569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133764153227689050930379 200646229841533576395569)
              ·
                refine ⟨150484672381150182296677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200646229841533576395569 150484672381150182296677)
                ·
                  refine ⟨28215876071465659180627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150484672381150182296677 28215876071465659180627)
                  ·
                    rfl

theorem cell20_61819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 4].length) (baseStart_61819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61819 prefixEnd_61819 := by exact prefixLift 61819
  have htrace : WordTrace (prefixWord ++ tailWord_61819) baseStart_61819 baseEnd_61819 := by
    simpa [prefixWord, tailWord_61819, baseEnd_61819] using wordTrace_append hprefix tailTrace_61819
  have hstable : (prefixWord ++ tailWord_61819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61819).length < 2 ^ (prefixWord ++ tailWord_61819).sum := by decide
  have hdescent : baseEnd_61819 < baseStart_61819 := by decide
  rcases family_descends (prefixWord ++ tailWord_61819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61836 : List Nat := [2, 2, 1, 2, 1, 4, 1, 5, 2]
def baseStart_61836 : Nat := 118140960795 + 61836 * 2 ^ 59
def prefixEnd_61836 : Nat := 4983230072969 + 3 ^ 40 * 61836 * 2
def baseEnd_61836 : Nat := 28223635334689155613891

theorem tailTrace_61836 : CollatzResearch.WordTrace tailWord_61836 prefixEnd_61836 28223635334689155613891 := by
  unfold tailWord_61836
  simp only [CollatzResearch.WordTrace]
  refine ⟨1127672101993103796562681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1503562802657471728750241 1127672101993103796562681)
  ·
    refine ⟨845754076494827847422011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1127672101993103796562681 845754076494827847422011)
    ·
      refine ⟨1268631114742241771133017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 845754076494827847422011 1268631114742241771133017)
      ·
        refine ⟨951473336056681328349763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1268631114742241771133017 951473336056681328349763)
        ·
          refine ⟨1427210004085021992524645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951473336056681328349763 1427210004085021992524645)
          ·
            refine ⟨267601875765941623598371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1427210004085021992524645 267601875765941623598371)
            ·
              refine ⟨401402813648912435397557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267601875765941623598371 401402813648912435397557)
              ·
                refine ⟨37631513779585540818521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 401402813648912435397557 37631513779585540818521)
                ·
                  refine ⟨28223635334689155613891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37631513779585540818521 28223635334689155613891)
                  ·
                    rfl

theorem cell20_61836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_61836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61836 prefixEnd_61836 := by exact prefixLift 61836
  have htrace : WordTrace (prefixWord ++ tailWord_61836) baseStart_61836 baseEnd_61836 := by
    simpa [prefixWord, tailWord_61836, baseEnd_61836] using wordTrace_append hprefix tailTrace_61836
  have hstable : (prefixWord ++ tailWord_61836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61836).length < 2 ^ (prefixWord ++ tailWord_61836).sum := by decide
  have hdescent : baseEnd_61836 < baseStart_61836 := by decide
  rcases family_descends (prefixWord ++ tailWord_61836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61850 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_61850 : Nat := 118140960795 + 61850 * 2 ^ 59
def prefixEnd_61850 : Nat := 4983230072969 + 3 ^ 40 * 61850 * 2
def baseEnd_61850 : Nat := 28230025316167329147167

theorem tailTrace_61850 : CollatzResearch.WordTrace tailWord_61850 prefixEnd_61850 28230025316167329147167 := by
  unfold tailWord_61850
  simp only [CollatzResearch.WordTrace]
  refine ⟨563963706483871996033751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1503903217290325322756669 563963706483871996033751)
  ·
    refine ⟨845945559725807994050627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 563963706483871996033751 845945559725807994050627)
    ·
      refine ⟨1268918339588711991075941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 845945559725807994050627 1268918339588711991075941)
      ·
        refine ⟨237922188672883498326739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1268918339588711991075941 237922188672883498326739)
        ·
          refine ⟨356883283009325247490109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237922188672883498326739 356883283009325247490109)
          ·
            refine ⟨133831231128496967808791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356883283009325247490109 133831231128496967808791)
            ·
              refine ⟨200746846692745451713187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133831231128496967808791 200746846692745451713187)
              ·
                refine ⟨301120270039118177569781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200746846692745451713187 301120270039118177569781)
                ·
                  refine ⟨28230025316167329147167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 301120270039118177569781 28230025316167329147167)
                  ·
                    rfl

theorem cell20_61850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_61850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61850 prefixEnd_61850 := by exact prefixLift 61850
  have htrace : WordTrace (prefixWord ++ tailWord_61850) baseStart_61850 baseEnd_61850 := by
    simpa [prefixWord, tailWord_61850, baseEnd_61850] using wordTrace_append hprefix tailTrace_61850
  have hstable : (prefixWord ++ tailWord_61850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61850).length < 2 ^ (prefixWord ++ tailWord_61850).sum := by decide
  have hdescent : baseEnd_61850 < baseStart_61850 := by decide
  rcases family_descends (prefixWord ++ tailWord_61850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61877 : List Nat := [1, 3, 3, 2, 4, 1, 2, 4]
def baseStart_61877 : Nat := 118140960795 + 61877 * 2 ^ 59
def prefixEnd_61877 : Nat := 4983230072969 + 3 ^ 40 * 61877 * 2
def baseEnd_61877 : Nat := 9414116283958411749019

theorem tailTrace_61877 : CollatzResearch.WordTrace tailWord_61877 prefixEnd_61877 9414116283958411749019 := by
  unfold tailWord_61877
  simp only [CollatzResearch.WordTrace]
  refine ⟨2256839596837671595367885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1504559731225114396911923 2256839596837671595367885)
  ·
    refine ⟨846314848814126848262957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2256839596837671595367885 846314848814126848262957)
    ·
      refine ⟨317368068305297568098609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 846314848814126848262957 317368068305297568098609)
      ·
        refine ⟨238026051228973176073957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317368068305297568098609 238026051228973176073957)
        ·
          refine ⟨44629884605432470513867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238026051228973176073957 44629884605432470513867)
          ·
            refine ⟨66944826908148705770801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44629884605432470513867 66944826908148705770801)
            ·
              refine ⟨50208620181111529328101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66944826908148705770801 50208620181111529328101)
              ·
                refine ⟨9414116283958411749019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50208620181111529328101 9414116283958411749019)
                ·
                  rfl

theorem cell20_61877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 4].length) (baseStart_61877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61877 prefixEnd_61877 := by exact prefixLift 61877
  have htrace : WordTrace (prefixWord ++ tailWord_61877) baseStart_61877 baseEnd_61877 := by
    simpa [prefixWord, tailWord_61877, baseEnd_61877] using wordTrace_append hprefix tailTrace_61877
  have hstable : (prefixWord ++ tailWord_61877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61877).length < 2 ^ (prefixWord ++ tailWord_61877).sum := by decide
  have hdescent : baseEnd_61877 < baseStart_61877 := by decide
  rcases family_descends (prefixWord ++ tailWord_61877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61881 : List Nat := [1, 2, 1, 4, 3, 1, 4, 4]
def baseStart_61881 : Nat := 118140960795 + 61881 * 2 ^ 59
def prefixEnd_61881 : Nat := 4983230072969 + 3 ^ 40 * 61881 * 2
def baseEnd_61881 : Nat := 9414724853622999704569

theorem tailTrace_61881 : CollatzResearch.WordTrace tailWord_61881 prefixEnd_61881 9414724853622999704569 := by
  unfold tailWord_61881
  simp only [CollatzResearch.WordTrace]
  refine ⟨2256985488823180278513497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1504656992548786852342331 2256985488823180278513497)
  ·
    refine ⟨1692739116617385208885123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2256985488823180278513497 1692739116617385208885123)
    ·
      refine ⟨2539108674926077813327685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1692739116617385208885123 2539108674926077813327685)
      ·
        refine ⟨476082876548639589998941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2539108674926077813327685 476082876548639589998941)
        ·
          refine ⟨178531078705739846249603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 476082876548639589998941 178531078705739846249603)
          ·
            refine ⟨267796618058609769374405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178531078705739846249603 267796618058609769374405)
            ·
              refine ⟨50211865885989331757701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267796618058609769374405 50211865885989331757701)
              ·
                refine ⟨9414724853622999704569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50211865885989331757701 9414724853622999704569)
                ·
                  rfl

theorem cell20_61881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 4].length) (baseStart_61881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61881 prefixEnd_61881 := by exact prefixLift 61881
  have htrace : WordTrace (prefixWord ++ tailWord_61881) baseStart_61881 baseEnd_61881 := by
    simpa [prefixWord, tailWord_61881, baseEnd_61881] using wordTrace_append hprefix tailTrace_61881
  have hstable : (prefixWord ++ tailWord_61881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61881).length < 2 ^ (prefixWord ++ tailWord_61881).sum := by decide
  have hdescent : baseEnd_61881 < baseStart_61881 := by decide
  rcases family_descends (prefixWord ++ tailWord_61881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61908 : List Nat := [2, 4, 1, 2, 2, 2, 3, 2, 2]
def baseStart_61908 : Nat := 118140960795 + 61908 * 2 ^ 59
def prefixEnd_61908 : Nat := 4983230072969 + 3 ^ 40 * 61908 * 2
def baseEnd_61908 : Nat := 28256498096576905213597

theorem tailTrace_61908 : CollatzResearch.WordTrace tailWord_61908 prefixEnd_61908 28256498096576905213597 := by
  unfold tailWord_61908
  simp only [CollatzResearch.WordTrace]
  refine ⟨1128985129862681944873189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1505313506483575926497585 1128985129862681944873189)
  ·
    refine ⟨211684711849252864663723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1128985129862681944873189 211684711849252864663723)
    ·
      refine ⟨317527067773879296995585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211684711849252864663723 317527067773879296995585)
      ·
        refine ⟨238145300830409472746689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317527067773879296995585 238145300830409472746689)
        ·
          refine ⟨178608975622807104560017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238145300830409472746689 178608975622807104560017)
          ·
            refine ⟨133956731717105328420013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178608975622807104560017 133956731717105328420013)
            ·
              refine ⟨50233774393914498157505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133956731717105328420013 50233774393914498157505)
              ·
                refine ⟨37675330795435873618129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50233774393914498157505 37675330795435873618129)
                ·
                  refine ⟨28256498096576905213597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37675330795435873618129 28256498096576905213597)
                  ·
                    rfl

theorem cell20_61908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_61908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61908 prefixEnd_61908 := by exact prefixLift 61908
  have htrace : WordTrace (prefixWord ++ tailWord_61908) baseStart_61908 baseEnd_61908 := by
    simpa [prefixWord, tailWord_61908, baseEnd_61908] using wordTrace_append hprefix tailTrace_61908
  have hstable : (prefixWord ++ tailWord_61908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61908).length < 2 ^ (prefixWord ++ tailWord_61908).sum := by decide
  have hdescent : baseEnd_61908 < baseStart_61908 := by decide
  rcases family_descends (prefixWord ++ tailWord_61908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61964 : List Nat := [2, 2, 1, 2, 4, 1, 1, 4, 3]
def baseStart_61964 : Nat := 118140960795 + 61964 * 2 ^ 59
def prefixEnd_61964 : Nat := 4983230072969 + 3 ^ 40 * 61964 * 2
def baseEnd_61964 : Nat := 28282058022489599346701

theorem tailTrace_61964 : CollatzResearch.WordTrace tailWord_61964 prefixEnd_61964 28282058022489599346701 := by
  unfold tailWord_61964
  simp only [CollatzResearch.WordTrace]
  refine ⟨1130006373761242726892473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1506675165014990302523297 1130006373761242726892473)
  ·
    refine ⟨847504780320932045169355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1130006373761242726892473 847504780320932045169355)
    ·
      refine ⟨1271257170481398067754033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 847504780320932045169355 1271257170481398067754033)
      ·
        refine ⟨953442877861048550815525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1271257170481398067754033 953442877861048550815525)
        ·
          refine ⟨178770539598946603277911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 953442877861048550815525 178770539598946603277911)
          ·
            refine ⟨268155809398419904916867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178770539598946603277911 268155809398419904916867)
            ·
              refine ⟨402233714097629857375301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268155809398419904916867 402233714097629857375301)
              ·
                refine ⟨75418821393305598257869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 402233714097629857375301 75418821393305598257869)
                ·
                  refine ⟨28282058022489599346701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75418821393305598257869 28282058022489599346701)
                  ·
                    rfl

theorem cell20_61964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_61964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61964 prefixEnd_61964 := by exact prefixLift 61964
  have htrace : WordTrace (prefixWord ++ tailWord_61964) baseStart_61964 baseEnd_61964 := by
    simpa [prefixWord, tailWord_61964, baseEnd_61964] using wordTrace_append hprefix tailTrace_61964
  have hstable : (prefixWord ++ tailWord_61964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61964).length < 2 ^ (prefixWord ++ tailWord_61964).sum := by decide
  have hdescent : baseEnd_61964 < baseStart_61964 := by decide
  rcases family_descends (prefixWord ++ tailWord_61964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61978 : List Nat := [3, 1, 1, 3, 1, 1, 5, 5]
def baseStart_61978 : Nat := 118140960795 + 61978 * 2 ^ 59
def prefixEnd_61978 : Nat := 4983230072969 + 3 ^ 40 * 61978 * 2
def baseEnd_61978 : Nat := 9429482667989257626659

theorem tailTrace_61978 : CollatzResearch.WordTrace tailWord_61978 prefixEnd_61978 9429482667989257626659 := by
  unfold tailWord_61978
  simp only [CollatzResearch.WordTrace]
  refine ⟨565130842367941461198647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1507015579647843896529725 565130842367941461198647)
  ·
    refine ⟨847696263551912191797971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 565130842367941461198647 847696263551912191797971)
    ·
      refine ⟨1271544395327868287696957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 847696263551912191797971 1271544395327868287696957)
      ·
        refine ⟨476829148247950607886359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1271544395327868287696957 476829148247950607886359)
        ·
          refine ⟨715243722371925911829539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476829148247950607886359 715243722371925911829539)
          ·
            refine ⟨1072865583557888867744309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715243722371925911829539 1072865583557888867744309)
            ·
              refine ⟨100581148458552081351029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1072865583557888867744309 100581148458552081351029)
              ·
                refine ⟨9429482667989257626659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100581148458552081351029 9429482667989257626659)
                ·
                  rfl

theorem cell20_61978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_61978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61978 prefixEnd_61978 := by exact prefixLift 61978
  have htrace : WordTrace (prefixWord ++ tailWord_61978) baseStart_61978 baseEnd_61978 := by
    simpa [prefixWord, tailWord_61978, baseEnd_61978] using wordTrace_append hprefix tailTrace_61978
  have hstable : (prefixWord ++ tailWord_61978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61978).length < 2 ^ (prefixWord ++ tailWord_61978).sum := by decide
  have hdescent : baseEnd_61978 < baseStart_61978 := by decide
  rcases family_descends (prefixWord ++ tailWord_61978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61991 : List Nat := [1, 1, 7, 2, 1, 1, 3, 4]
def baseStart_61991 : Nat := 118140960795 + 61991 * 2 ^ 59
def prefixEnd_61991 : Nat := 4983230072969 + 3 ^ 40 * 61991 * 2
def baseEnd_61991 : Nat := 9431460519399168482197

theorem tailTrace_61991 : CollatzResearch.WordTrace tailWord_61991 prefixEnd_61991 9431460519399168482197 := by
  unfold tailWord_61991
  simp only [CollatzResearch.WordTrace]
  refine ⟨2260997518424669065017827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1507331678949779376678551 2260997518424669065017827)
  ·
    refine ⟨3391496277637003597526741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2260997518424669065017827 3391496277637003597526741)
    ·
      refine ⟨79488194007117271817033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 3391496277637003597526741 79488194007117271817033)
      ·
        refine ⟨59616145505337953862775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79488194007117271817033 59616145505337953862775)
        ·
          refine ⟨89424218258006930794163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59616145505337953862775 89424218258006930794163)
          ·
            refine ⟨134136327387010396191245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89424218258006930794163 134136327387010396191245)
            ·
              refine ⟨50301122770128898571717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134136327387010396191245 50301122770128898571717)
              ·
                refine ⟨9431460519399168482197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50301122770128898571717 9431460519399168482197)
                ·
                  rfl

theorem cell20_61991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 4].length) (baseStart_61991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61991 prefixEnd_61991 := by exact prefixLift 61991
  have htrace : WordTrace (prefixWord ++ tailWord_61991) baseStart_61991 baseEnd_61991 := by
    simpa [prefixWord, tailWord_61991, baseEnd_61991] using wordTrace_append hprefix tailTrace_61991
  have hstable : (prefixWord ++ tailWord_61991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61991).length < 2 ^ (prefixWord ++ tailWord_61991).sum := by decide
  have hdescent : baseEnd_61991 < baseStart_61991 := by decide
  rcases family_descends (prefixWord ++ tailWord_61991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62022 : List Nat := [6, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_62022 : Nat := 118140960795 + 62022 * 2 ^ 59
def prefixEnd_62022 : Nat := 4983230072969 + 3 ^ 40 * 62022 * 2
def baseEnd_62022 : Nat := 28308530802899175413131

theorem tailTrace_62022 : CollatzResearch.WordTrace tailWord_62022 prefixEnd_62022 28308530802899175413131 := by
  unfold tailWord_62022
  simp only [CollatzResearch.WordTrace]
  refine ⟨70691505666011292481135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1508085454208240906264213 70691505666011292481135)
  ·
    refine ⟨106037258499016938721703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70691505666011292481135 106037258499016938721703)
    ·
      refine ⟨159055887748525408082555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106037258499016938721703 159055887748525408082555)
      ·
        refine ⟨238583831622788112123833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159055887748525408082555 238583831622788112123833)
        ·
          refine ⟨178937873717091084092875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238583831622788112123833 178937873717091084092875)
          ·
            refine ⟨268406810575636626139313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178937873717091084092875 268406810575636626139313)
            ·
              refine ⟨201305107931727469604485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268406810575636626139313 201305107931727469604485)
              ·
                refine ⟨37744707737198900550841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201305107931727469604485 37744707737198900550841)
                ·
                  refine ⟨28308530802899175413131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37744707737198900550841 28308530802899175413131)
                  ·
                    rfl

theorem cell20_62022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_62022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62022 prefixEnd_62022 := by exact prefixLift 62022
  have htrace : WordTrace (prefixWord ++ tailWord_62022) baseStart_62022 baseEnd_62022 := by
    simpa [prefixWord, tailWord_62022, baseEnd_62022] using wordTrace_append hprefix tailTrace_62022
  have hstable : (prefixWord ++ tailWord_62022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62022).length < 2 ^ (prefixWord ++ tailWord_62022).sum := by decide
  have hdescent : baseEnd_62022 < baseStart_62022 := by decide
  rcases family_descends (prefixWord ++ tailWord_62022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62026 : List Nat := [3, 1, 2, 1, 1, 4, 2, 4, 2]
def baseStart_62026 : Nat := 118140960795 + 62026 * 2 ^ 59
def prefixEnd_62026 : Nat := 4983230072969 + 3 ^ 40 * 62026 * 2
def baseEnd_62026 : Nat := 28310356511892939279781

theorem tailTrace_62026 : CollatzResearch.WordTrace tailWord_62026 prefixEnd_62026 28310356511892939279781 := by
  unfold tailWord_62026
  simp only [CollatzResearch.WordTrace]
  refine ⟨565568518324467510635483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1508182715531913361694621 565568518324467510635483)
  ·
    refine ⟨848352777486701265953225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 565568518324467510635483 848352777486701265953225)
    ·
      refine ⟨636264583115025949464919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 848352777486701265953225 636264583115025949464919)
      ·
        refine ⟨954396874672538924197379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636264583115025949464919 954396874672538924197379)
        ·
          refine ⟨1431595312008808386296069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954396874672538924197379 1431595312008808386296069)
          ·
            refine ⟨268424121001651572430513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1431595312008808386296069 268424121001651572430513)
            ·
              refine ⟨201318090751238679322885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268424121001651572430513 201318090751238679322885)
              ·
                refine ⟨37747142015857252373041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201318090751238679322885 37747142015857252373041)
                ·
                  refine ⟨28310356511892939279781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37747142015857252373041 28310356511892939279781)
                  ·
                    rfl

theorem cell20_62026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_62026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62026 prefixEnd_62026 := by exact prefixLift 62026
  have htrace : WordTrace (prefixWord ++ tailWord_62026) baseStart_62026 baseEnd_62026 := by
    simpa [prefixWord, tailWord_62026, baseEnd_62026] using wordTrace_append hprefix tailTrace_62026
  have hstable : (prefixWord ++ tailWord_62026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62026).length < 2 ^ (prefixWord ++ tailWord_62026).sum := by decide
  have hdescent : baseEnd_62026 < baseStart_62026 := by decide
  rcases family_descends (prefixWord ++ tailWord_62026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62050 : List Nat := [3, 3, 2, 3, 1, 1, 1, 6]
def baseStart_62050 : Nat := 118140960795 + 62050 * 2 ^ 59
def prefixEnd_62050 : Nat := 4983230072969 + 3 ^ 40 * 62050 * 2
def baseEnd_62050 : Nat := 9440436921951840826561

theorem tailTrace_62050 : CollatzResearch.WordTrace tailWord_62050 prefixEnd_62050 9440436921951840826561 := by
  unfold tailWord_62050
  simp only [CollatzResearch.WordTrace]
  refine ⟨565787356302730535353901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1508766283473948094277069 565787356302730535353901)
  ·
    refine ⟨212170258613523950757713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 565787356302730535353901 212170258613523950757713)
    ·
      refine ⟨159127693960142963068285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212170258613523950757713 159127693960142963068285)
      ·
        refine ⟨59672885235053611150607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159127693960142963068285 59672885235053611150607)
        ·
          refine ⟨89509327852580416725911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59672885235053611150607 89509327852580416725911)
          ·
            refine ⟨134263991778870625088867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89509327852580416725911 134263991778870625088867)
            ·
              refine ⟨201395987668305937633301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134263991778870625088867 201395987668305937633301)
              ·
                refine ⟨9440436921951840826561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201395987668305937633301 9440436921951840826561)
                ·
                  rfl

theorem cell20_62050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_62050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62050 prefixEnd_62050 := by exact prefixLift 62050
  have htrace : WordTrace (prefixWord ++ tailWord_62050) baseStart_62050 baseEnd_62050 := by
    simpa [prefixWord, tailWord_62050, baseEnd_62050] using wordTrace_append hprefix tailTrace_62050
  have hstable : (prefixWord ++ tailWord_62050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62050).length < 2 ^ (prefixWord ++ tailWord_62050).sum := by decide
  have hdescent : baseEnd_62050 < baseStart_62050 := by decide
  rcases family_descends (prefixWord ++ tailWord_62050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62081 : List Nat := [1, 2, 4, 2, 1, 1, 5, 2, 2]
def baseStart_62081 : Nat := 118140960795 + 62081 * 2 ^ 59
def prefixEnd_62081 : Nat := 4983230072969 + 3 ^ 40 * 62081 * 2
def baseEnd_62081 : Nat := 28335460010557192446223

theorem tailTrace_62081 : CollatzResearch.WordTrace tailWord_62081 prefixEnd_62081 28335460010557192446223 := by
  unfold tailWord_62081
  simp only [CollatzResearch.WordTrace]
  refine ⟨2264280088098614435794097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1509520058732409623862731 2264280088098614435794097)
  ·
    refine ⟨1698210066073960826845573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2264280088098614435794097 1698210066073960826845573)
    ·
      refine ⟨318414387388867655033545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1698210066073960826845573 318414387388867655033545)
      ·
        refine ⟨238810790541650741275159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318414387388867655033545 238810790541650741275159)
        ·
          refine ⟨358216185812476111912739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238810790541650741275159 358216185812476111912739)
          ·
            refine ⟨537324278718714167869109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358216185812476111912739 537324278718714167869109)
            ·
              refine ⟨50374151129879453237729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 537324278718714167869109 50374151129879453237729)
              ·
                refine ⟨37780613347409589928297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50374151129879453237729 37780613347409589928297)
                ·
                  refine ⟨28335460010557192446223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37780613347409589928297 28335460010557192446223)
                  ·
                    rfl

theorem cell20_62081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 2].length) (baseStart_62081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62081 prefixEnd_62081 := by exact prefixLift 62081
  have htrace : WordTrace (prefixWord ++ tailWord_62081) baseStart_62081 baseEnd_62081 := by
    simpa [prefixWord, tailWord_62081, baseEnd_62081] using wordTrace_append hprefix tailTrace_62081
  have hstable : (prefixWord ++ tailWord_62081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62081).length < 2 ^ (prefixWord ++ tailWord_62081).sum := by decide
  have hdescent : baseEnd_62081 < baseStart_62081 := by decide
  rcases family_descends (prefixWord ++ tailWord_62081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62085 : List Nat := [1, 3, 1, 1, 4, 2, 3, 1, 4]
def baseStart_62085 : Nat := 118140960795 + 62085 * 2 ^ 59
def prefixEnd_62085 : Nat := 4983230072969 + 3 ^ 40 * 62085 * 2
def baseEnd_62085 : Nat := 28337285719550956312873

theorem tailTrace_62085 : CollatzResearch.WordTrace tailWord_62085 prefixEnd_62085 28337285719550956312873 := by
  unfold tailWord_62085
  simp only [CollatzResearch.WordTrace]
  refine ⟨2264425980084123118939709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1509617320056082079293139 2264425980084123118939709)
  ·
    refine ⟨849159742531546169602391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2264425980084123118939709 849159742531546169602391)
    ·
      refine ⟨1273739613797319254403587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 849159742531546169602391 1273739613797319254403587)
      ·
        refine ⟨1910609420695978881605381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1273739613797319254403587 1910609420695978881605381)
        ·
          refine ⟨358239266380496040301009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1910609420695978881605381 358239266380496040301009)
          ·
            refine ⟨268679449785372030225757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358239266380496040301009 268679449785372030225757)
            ·
              refine ⟨100754793669514511334659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268679449785372030225757 100754793669514511334659)
              ·
                refine ⟨151132190504271767001989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100754793669514511334659 151132190504271767001989)
                ·
                  refine ⟨28337285719550956312873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151132190504271767001989 28337285719550956312873)
                  ·
                    rfl

theorem cell20_62085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_62085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62085 prefixEnd_62085 := by exact prefixLift 62085
  have htrace : WordTrace (prefixWord ++ tailWord_62085) baseStart_62085 baseEnd_62085 := by
    simpa [prefixWord, tailWord_62085, baseEnd_62085] using wordTrace_append hprefix tailTrace_62085
  have hstable : (prefixWord ++ tailWord_62085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62085).length < 2 ^ (prefixWord ++ tailWord_62085).sum := by decide
  have hdescent : baseEnd_62085 < baseStart_62085 := by decide
  rcases family_descends (prefixWord ++ tailWord_62085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62099 : List Nat := [1, 1, 1, 2, 1, 2, 2, 7, 3]
def baseStart_62099 : Nat := 118140960795 + 62099 * 2 ^ 59
def prefixEnd_62099 : Nat := 4983230072969 + 3 ^ 40 * 62099 * 2
def baseEnd_62099 : Nat := 28343675701029129846149

theorem tailTrace_62099 : CollatzResearch.WordTrace tailWord_62099 prefixEnd_62099 28343675701029129846149 := by
  unfold tailWord_62099
  simp only [CollatzResearch.WordTrace]
  refine ⟨2264936602033403509949351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1509957734688935673299567 2264936602033403509949351)
  ·
    refine ⟨3397404903050105264924027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2264936602033403509949351 3397404903050105264924027)
    ·
      refine ⟨5096107354575157897386041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3397404903050105264924027 5096107354575157897386041)
      ·
        refine ⟨3822080515931368423039531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5096107354575157897386041 3822080515931368423039531)
        ·
          refine ⟨5733120773897052634559297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3822080515931368423039531 5733120773897052634559297)
          ·
            refine ⟨4299840580422789475919473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5733120773897052634559297 4299840580422789475919473)
            ·
              refine ⟨3224880435317092106939605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4299840580422789475919473 3224880435317092106939605)
              ·
                refine ⟨75583135202744346256397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3224880435317092106939605 75583135202744346256397)
                ·
                  refine ⟨28343675701029129846149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75583135202744346256397 28343675701029129846149)
                  ·
                    rfl

theorem cell20_62099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 3].length) (baseStart_62099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62099 prefixEnd_62099 := by exact prefixLift 62099
  have htrace : WordTrace (prefixWord ++ tailWord_62099) baseStart_62099 baseEnd_62099 := by
    simpa [prefixWord, tailWord_62099, baseEnd_62099] using wordTrace_append hprefix tailTrace_62099
  have hstable : (prefixWord ++ tailWord_62099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62099).length < 2 ^ (prefixWord ++ tailWord_62099).sum := by decide
  have hdescent : baseEnd_62099 < baseStart_62099 := by decide
  rcases family_descends (prefixWord ++ tailWord_62099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62133 : List Nat := [1, 3, 3, 3, 1, 2, 2, 2, 3]
def baseStart_62133 : Nat := 118140960795 + 62133 * 2 ^ 59
def prefixEnd_62133 : Nat := 4983230072969 + 3 ^ 40 * 62133 * 2
def baseEnd_62133 : Nat := 28359194227476122712677

theorem tailTrace_62133 : CollatzResearch.WordTrace tailWord_62133 prefixEnd_62133 28359194227476122712677 := by
  unfold tailWord_62133
  simp only [CollatzResearch.WordTrace]
  refine ⟨2266176683910227316687053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1510784455940151544458035 2266176683910227316687053)
  ·
    refine ⟨849816256466335243757645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2266176683910227316687053 849816256466335243757645)
    ·
      refine ⟨318681096174875716409117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 849816256466335243757645 318681096174875716409117)
      ·
        refine ⟨119505411065578393653419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318681096174875716409117 119505411065578393653419)
        ·
          refine ⟨179258116598367590480129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119505411065578393653419 179258116598367590480129)
          ·
            refine ⟨134443587448775692860097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179258116598367590480129 134443587448775692860097)
            ·
              refine ⟨100832690586581769645073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134443587448775692860097 100832690586581769645073)
              ·
                refine ⟨75624517939936327233805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100832690586581769645073 75624517939936327233805)
                ·
                  refine ⟨28359194227476122712677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75624517939936327233805 28359194227476122712677)
                  ·
                    rfl

theorem cell20_62133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_62133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62133 prefixEnd_62133 := by exact prefixLift 62133
  have htrace : WordTrace (prefixWord ++ tailWord_62133) baseStart_62133 baseEnd_62133 := by
    simpa [prefixWord, tailWord_62133, baseEnd_62133] using wordTrace_append hprefix tailTrace_62133
  have hstable : (prefixWord ++ tailWord_62133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62133).length < 2 ^ (prefixWord ++ tailWord_62133).sum := by decide
  have hdescent : baseEnd_62133 < baseStart_62133 := by decide
  rcases family_descends (prefixWord ++ tailWord_62133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62140 : List Nat := [2, 2, 2, 3, 1, 1, 3, 4, 2]
def baseStart_62140 : Nat := 118140960795 + 62140 * 2 ^ 59
def prefixEnd_62140 : Nat := 4983230072969 + 3 ^ 40 * 62140 * 2
def baseEnd_62140 : Nat := 28362389218215209479315

theorem tailTrace_62140 : CollatzResearch.WordTrace tailWord_62140 prefixEnd_62140 28362389218215209479315 := by
  unfold tailWord_62140
  simp only [CollatzResearch.WordTrace]
  refine ⟨1133215997442433756095937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1510954663256578341461249 1133215997442433756095937)
  ·
    refine ⟨849911998081825317071953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1133215997442433756095937 849911998081825317071953)
    ·
      refine ⟨637433998561368987803965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 849911998081825317071953 637433998561368987803965)
      ·
        refine ⟨239037749460513370426487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 637433998561368987803965 239037749460513370426487)
        ·
          refine ⟨358556624190770055639731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239037749460513370426487 358556624190770055639731)
          ·
            refine ⟨537834936286155083459597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358556624190770055639731 537834936286155083459597)
            ·
              refine ⟨201688101107308156297349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 537834936286155083459597 201688101107308156297349)
              ·
                refine ⟨37816518957620279305753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201688101107308156297349 37816518957620279305753)
                ·
                  refine ⟨28362389218215209479315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37816518957620279305753 28362389218215209479315)
                  ·
                    rfl

theorem cell20_62140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_62140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62140 prefixEnd_62140 := by exact prefixLift 62140
  have htrace : WordTrace (prefixWord ++ tailWord_62140) baseStart_62140 baseEnd_62140 := by
    simpa [prefixWord, tailWord_62140, baseEnd_62140] using wordTrace_append hprefix tailTrace_62140
  have hstable : (prefixWord ++ tailWord_62140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62140).length < 2 ^ (prefixWord ++ tailWord_62140).sum := by decide
  have hdescent : baseEnd_62140 < baseStart_62140 := by decide
  rcases family_descends (prefixWord ++ tailWord_62140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62151 : List Nat := [1, 1, 4, 1, 1, 1, 2, 9]
def baseStart_62151 : Nat := 118140960795 + 62151 * 2 ^ 59
def prefixEnd_62151 : Nat := 4983230072969 + 3 ^ 40 * 62151 * 2
def baseEnd_62151 : Nat := 9455803305982686704201

theorem tailTrace_62151 : CollatzResearch.WordTrace tailWord_62151 prefixEnd_62151 9455803305982686704201 := by
  unfold tailWord_62151
  simp only [CollatzResearch.WordTrace]
  refine ⟨2266833197845016390842307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1511222131896677593894871 2266833197845016390842307)
  ·
    refine ⟨3400249796767524586263461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2266833197845016390842307 3400249796767524586263461)
    ·
      refine ⟨637546836893910859924399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3400249796767524586263461 637546836893910859924399)
      ·
        refine ⟨956320255340866289886599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637546836893910859924399 956320255340866289886599)
        ·
          refine ⟨1434480383011299434829899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956320255340866289886599 1434480383011299434829899)
          ·
            refine ⟨2151720574516949152244849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1434480383011299434829899 2151720574516949152244849)
            ·
              refine ⟨1613790430887711864183637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2151720574516949152244849 1613790430887711864183637)
              ·
                refine ⟨9455803305982686704201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1613790430887711864183637 9455803305982686704201)
                ·
                  rfl

theorem cell20_62151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 9].length) (baseStart_62151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62151 prefixEnd_62151 := by exact prefixLift 62151
  have htrace : WordTrace (prefixWord ++ tailWord_62151) baseStart_62151 baseEnd_62151 := by
    simpa [prefixWord, tailWord_62151, baseEnd_62151] using wordTrace_append hprefix tailTrace_62151
  have hstable : (prefixWord ++ tailWord_62151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62151).length < 2 ^ (prefixWord ++ tailWord_62151).sum := by decide
  have hdescent : baseEnd_62151 < baseStart_62151 := by decide
  rcases family_descends (prefixWord ++ tailWord_62151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62154 : List Nat := [3, 1, 2, 1, 4, 1, 2, 3, 3]
def baseStart_62154 : Nat := 118140960795 + 62154 * 2 ^ 59
def prefixEnd_62154 : Nat := 4983230072969 + 3 ^ 40 * 62154 * 2
def baseEnd_62154 : Nat := 28368779199693383012591

theorem tailTrace_62154 : CollatzResearch.WordTrace tailWord_62154 prefixEnd_62154 28368779199693383012591 := by
  unfold tailWord_62154
  simp only [CollatzResearch.WordTrace]
  refine ⟨566735654208536975800379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1511295077889431935467677 566735654208536975800379)
  ·
    refine ⟨850103481312805463700569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 566735654208536975800379 850103481312805463700569)
    ·
      refine ⟨637577610984604097775427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 850103481312805463700569 637577610984604097775427)
      ·
        refine ⟨956366416476906146663141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637577610984604097775427 956366416476906146663141)
        ·
          refine ⟨179318703089419902499339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 956366416476906146663141 179318703089419902499339)
          ·
            refine ⟨268978054634129853749009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179318703089419902499339 268978054634129853749009)
            ·
              refine ⟨201733540975597390311757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268978054634129853749009 201733540975597390311757)
              ·
                refine ⟨75650077865849021366909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201733540975597390311757 75650077865849021366909)
                ·
                  refine ⟨28368779199693383012591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75650077865849021366909 28368779199693383012591)
                  ·
                    rfl

theorem cell20_62154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_62154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62154 prefixEnd_62154 := by exact prefixLift 62154
  have htrace : WordTrace (prefixWord ++ tailWord_62154) baseStart_62154 baseEnd_62154 := by
    simpa [prefixWord, tailWord_62154, baseEnd_62154] using wordTrace_append hprefix tailTrace_62154
  have hstable : (prefixWord ++ tailWord_62154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62154).length < 2 ^ (prefixWord ++ tailWord_62154).sum := by decide
  have hdescent : baseEnd_62154 < baseStart_62154 := by decide
  rcases family_descends (prefixWord ++ tailWord_62154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62157 : List Nat := [1, 6, 2, 1, 2, 1, 1, 2, 4]
def baseStart_62157 : Nat := 118140960795 + 62157 * 2 ^ 59
def prefixEnd_62157 : Nat := 4983230072969 + 3 ^ 40 * 62157 * 2
def baseEnd_62157 : Nat := 28370148481438705912579

theorem tailTrace_62157 : CollatzResearch.WordTrace tailWord_62157 prefixEnd_62157 28370148481438705912579 := by
  unfold tailWord_62157
  simp only [CollatzResearch.WordTrace]
  refine ⟨2267052035823279415560725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1511368023882186277040483 2267052035823279415560725)
  ·
    refine ⟨106268064179216222604409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2267052035823279415560725 106268064179216222604409)
    ·
      refine ⟨79701048134412166953307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106268064179216222604409 79701048134412166953307)
      ·
        refine ⟨119551572201618250429961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79701048134412166953307 119551572201618250429961)
        ·
          refine ⟨89663679151213687822471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119551572201618250429961 89663679151213687822471)
          ·
            refine ⟨134495518726820531733707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89663679151213687822471 134495518726820531733707)
            ·
              refine ⟨201743278090230797600561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134495518726820531733707 201743278090230797600561)
              ·
                refine ⟨151307458567673098200421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201743278090230797600561 151307458567673098200421)
                ·
                  refine ⟨28370148481438705912579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151307458567673098200421 28370148481438705912579)
                  ·
                    rfl

theorem cell20_62157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_62157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62157 prefixEnd_62157 := by exact prefixLift 62157
  have htrace : WordTrace (prefixWord ++ tailWord_62157) baseStart_62157 baseEnd_62157 := by
    simpa [prefixWord, tailWord_62157, baseEnd_62157] using wordTrace_append hprefix tailTrace_62157
  have hstable : (prefixWord ++ tailWord_62157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62157).length < 2 ^ (prefixWord ++ tailWord_62157).sum := by decide
  have hdescent : baseEnd_62157 < baseStart_62157 := by decide
  rcases family_descends (prefixWord ++ tailWord_62157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62164 : List Nat := [2, 4, 1, 3, 2, 1, 3, 4]
def baseStart_62164 : Nat := 118140960795 + 62164 * 2 ^ 59
def prefixEnd_62164 : Nat := 4983230072969 + 3 ^ 40 * 62164 * 2
def baseEnd_62164 : Nat := 9457781157392597559739

theorem tailTrace_62164 : CollatzResearch.WordTrace tailWord_62164 prefixEnd_62164 9457781157392597559739 := by
  unfold tailWord_62164
  simp only [CollatzResearch.WordTrace]
  refine ⟨1133653673398959805532773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1511538231198613074043697 1133653673398959805532773)
  ·
    refine ⟨212560063762304963537395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1133653673398959805532773 212560063762304963537395)
    ·
      refine ⟨318840095643457445306093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212560063762304963537395 318840095643457445306093)
      ·
        refine ⟨119565035866296541989785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318840095643457445306093 119565035866296541989785)
        ·
          refine ⟨89673776899722406492339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119565035866296541989785 89673776899722406492339)
          ·
            refine ⟨134510665349583609738509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89673776899722406492339 134510665349583609738509)
            ·
              refine ⟨50441499506093853651941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134510665349583609738509 50441499506093853651941)
              ·
                refine ⟨9457781157392597559739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50441499506093853651941 9457781157392597559739)
                ·
                  rfl

theorem cell20_62164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_62164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62164 prefixEnd_62164 := by exact prefixLift 62164
  have htrace : WordTrace (prefixWord ++ tailWord_62164) baseStart_62164 baseEnd_62164 := by
    simpa [prefixWord, tailWord_62164, baseEnd_62164] using wordTrace_append hprefix tailTrace_62164
  have hstable : (prefixWord ++ tailWord_62164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62164).length < 2 ^ (prefixWord ++ tailWord_62164).sum := by decide
  have hdescent : baseEnd_62164 < baseStart_62164 := by decide
  rcases family_descends (prefixWord ++ tailWord_62164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62213 : List Nat := [1, 3, 1, 1, 2, 1, 1, 7, 3]
def baseStart_62213 : Nat := 118140960795 + 62213 * 2 ^ 59
def prefixEnd_62213 : Nat := 4983230072969 + 3 ^ 40 * 62213 * 2
def baseEnd_62213 : Nat := 28395708407351400045683

theorem tailTrace_62213 : CollatzResearch.WordTrace tailWord_62213 prefixEnd_62213 28395708407351400045683 := by
  unfold tailWord_62213
  simp only [CollatzResearch.WordTrace]
  refine ⟨2269094523620400979599293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1512729682413600653066195 2269094523620400979599293)
  ·
    refine ⟨850910446357650367349735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2269094523620400979599293 850910446357650367349735)
    ·
      refine ⟨1276365669536475551024603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 850910446357650367349735 1276365669536475551024603)
      ·
        refine ⟨1914548504304713326536905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1276365669536475551024603 1914548504304713326536905)
        ·
          refine ⟨1435911378228534994902679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1914548504304713326536905 1435911378228534994902679)
          ·
            refine ⟨2153867067342802492354019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1435911378228534994902679 2153867067342802492354019)
            ·
              refine ⟨3230800601014203738531029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2153867067342802492354019 3230800601014203738531029)
              ·
                refine ⟨75721889086270400121821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3230800601014203738531029 75721889086270400121821)
                ·
                  refine ⟨28395708407351400045683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75721889086270400121821 28395708407351400045683)
                  ·
                    rfl

theorem cell20_62213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_62213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62213 prefixEnd_62213 := by exact prefixLift 62213
  have htrace : WordTrace (prefixWord ++ tailWord_62213) baseStart_62213 baseEnd_62213 := by
    simpa [prefixWord, tailWord_62213, baseEnd_62213] using wordTrace_append hprefix tailTrace_62213
  have hstable : (prefixWord ++ tailWord_62213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62213).length < 2 ^ (prefixWord ++ tailWord_62213).sum := by decide
  have hdescent : baseEnd_62213 < baseStart_62213 := by decide
  rcases family_descends (prefixWord ++ tailWord_62213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62227 : List Nat := [1, 1, 1, 2, 1, 3, 5, 6]
def baseStart_62227 : Nat := 118140960795 + 62227 * 2 ^ 59
def prefixEnd_62227 : Nat := 4983230072969 + 3 ^ 40 * 62227 * 2
def baseEnd_62227 : Nat := 9467366129609857859653

theorem tailTrace_62227 : CollatzResearch.WordTrace tailWord_62227 prefixEnd_62227 9467366129609857859653 := by
  unfold tailWord_62227
  simp only [CollatzResearch.WordTrace]
  refine ⟨2269605145569681370608935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1513070097046454247072623 2269605145569681370608935)
  ·
    refine ⟨3404407718354522055913403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2269605145569681370608935 3404407718354522055913403)
    ·
      refine ⟨5106611577531783083870105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3404407718354522055913403 5106611577531783083870105)
      ·
        refine ⟨3829958683148837312902579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5106611577531783083870105 3829958683148837312902579)
        ·
          refine ⟨5744938024723255969353869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3829958683148837312902579 5744938024723255969353869)
          ·
            refine ⟨2154351759271220988507701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5744938024723255969353869 2154351759271220988507701)
            ·
              refine ⟨201970477431676967672597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2154351759271220988507701 201970477431676967672597)
              ·
                refine ⟨9467366129609857859653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201970477431676967672597 9467366129609857859653)
                ·
                  rfl

theorem cell20_62227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 6].length) (baseStart_62227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62227 prefixEnd_62227 := by exact prefixLift 62227
  have htrace : WordTrace (prefixWord ++ tailWord_62227) baseStart_62227 baseEnd_62227 := by
    simpa [prefixWord, tailWord_62227, baseEnd_62227] using wordTrace_append hprefix tailTrace_62227
  have hstable : (prefixWord ++ tailWord_62227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62227).length < 2 ^ (prefixWord ++ tailWord_62227).sum := by decide
  have hdescent : baseEnd_62227 < baseStart_62227 := by decide
  rcases family_descends (prefixWord ++ tailWord_62227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62250 : List Nat := [3, 1, 4, 3, 2, 1, 1, 1, 4]
def baseStart_62250 : Nat := 118140960795 + 62250 * 2 ^ 59
def prefixEnd_62250 : Nat := 4983230072969 + 3 ^ 40 * 62250 * 2
def baseEnd_62250 : Nat := 28412596215543715812199

theorem tailTrace_62250 : CollatzResearch.WordTrace tailWord_62250 prefixEnd_62250 28412596215543715812199 := by
  unfold tailWord_62250
  simp only [CollatzResearch.WordTrace]
  refine ⟨567611006121589074674051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1513629349657570865797469 567611006121589074674051)
  ·
    refine ⟨851416509182383612011077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 567611006121589074674051 851416509182383612011077)
    ·
      refine ⟨159640595471696927252077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 851416509182383612011077 159640595471696927252077)
      ·
        refine ⟨59865223301886347719529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159640595471696927252077 59865223301886347719529)
        ·
          refine ⟨44898917476414760789647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59865223301886347719529 44898917476414760789647)
          ·
            refine ⟨67348376214622141184471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44898917476414760789647 67348376214622141184471)
            ·
              refine ⟨101022564321933211776707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67348376214622141184471 101022564321933211776707)
              ·
                refine ⟨151533846482899817665061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101022564321933211776707 151533846482899817665061)
                ·
                  refine ⟨28412596215543715812199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151533846482899817665061 28412596215543715812199)
                  ·
                    rfl

theorem cell20_62250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_62250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62250 prefixEnd_62250 := by exact prefixLift 62250
  have htrace : WordTrace (prefixWord ++ tailWord_62250) baseStart_62250 baseEnd_62250 := by
    simpa [prefixWord, tailWord_62250, baseEnd_62250] using wordTrace_append hprefix tailTrace_62250
  have hstable : (prefixWord ++ tailWord_62250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62250).length < 2 ^ (prefixWord ++ tailWord_62250).sum := by decide
  have hdescent : baseEnd_62250 < baseStart_62250 := by decide
  rcases family_descends (prefixWord ++ tailWord_62250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62254 : List Nat := [4, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_62254 : Nat := 118140960795 + 62254 * 2 ^ 59
def prefixEnd_62254 : Nat := 4983230072969 + 3 ^ 40 * 62254 * 2
def baseEnd_62254 : Nat := 28414421924537479678849

theorem tailTrace_62254 : CollatzResearch.WordTrace tailWord_62254 prefixEnd_62254 28414421924537479678849 := by
  unfold tailWord_62254
  simp only [CollatzResearch.WordTrace]
  refine ⟨283823739558983122730227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1513726610981243321227877 283823739558983122730227)
  ·
    refine ⟨425735609338474684095341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283823739558983122730227 425735609338474684095341)
    ·
      refine ⟨159650853501928006535753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425735609338474684095341 159650853501928006535753)
      ·
        refine ⟨119738140126446004901815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159650853501928006535753 119738140126446004901815)
        ·
          refine ⟨179607210189669007352723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119738140126446004901815 179607210189669007352723)
          ·
            refine ⟨269410815284503511029085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179607210189669007352723 269410815284503511029085)
            ·
              refine ⟨101029055731688816635907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269410815284503511029085 101029055731688816635907)
              ·
                refine ⟨151543583597533224953861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101029055731688816635907 151543583597533224953861)
                ·
                  refine ⟨28414421924537479678849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151543583597533224953861 28414421924537479678849)
                  ·
                    rfl

theorem cell20_62254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_62254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62254 prefixEnd_62254 := by exact prefixLift 62254
  have htrace : WordTrace (prefixWord ++ tailWord_62254) baseStart_62254 baseEnd_62254 := by
    simpa [prefixWord, tailWord_62254, baseEnd_62254] using wordTrace_append hprefix tailTrace_62254
  have hstable : (prefixWord ++ tailWord_62254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62254).length < 2 ^ (prefixWord ++ tailWord_62254).sum := by decide
  have hdescent : baseEnd_62254 < baseStart_62254 := by decide
  rcases family_descends (prefixWord ++ tailWord_62254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62365 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 5]
def baseStart_62365 : Nat := 118140960795 + 62365 * 2 ^ 59
def prefixEnd_62365 : Nat := 4983230072969 + 3 ^ 40 * 62365 * 2
def baseEnd_62365 : Nat := 28465085349114426978395

theorem tailTrace_62365 : CollatzResearch.WordTrace tailWord_62365 prefixEnd_62365 28465085349114426978395 := by
  unfold tailWord_62365
  simp only [CollatzResearch.WordTrace]
  refine ⟨2274638419069730939132549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1516425612713153959421699 2274638419069730939132549)
  ·
    refine ⟨426494703575574551087353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2274638419069730939132549 426494703575574551087353)
    ·
      refine ⟨319871027681680913315515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426494703575574551087353 319871027681680913315515)
      ·
        refine ⟨479806541522521369973273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319871027681680913315515 479806541522521369973273)
        ·
          refine ⟨359854906141891027479955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479806541522521369973273 359854906141891027479955)
          ·
            refine ⟨539782359212836541219933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359854906141891027479955 539782359212836541219933)
            ·
              refine ⟨202418384704813702957475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 539782359212836541219933 202418384704813702957475)
              ·
                refine ⟨303627577057220554436213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202418384704813702957475 303627577057220554436213)
                ·
                  refine ⟨28465085349114426978395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 303627577057220554436213 28465085349114426978395)
                  ·
                    rfl

theorem cell20_62365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_62365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62365 prefixEnd_62365 := by exact prefixLift 62365
  have htrace : WordTrace (prefixWord ++ tailWord_62365) baseStart_62365 baseEnd_62365 := by
    simpa [prefixWord, tailWord_62365, baseEnd_62365] using wordTrace_append hprefix tailTrace_62365
  have hstable : (prefixWord ++ tailWord_62365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62365).length < 2 ^ (prefixWord ++ tailWord_62365).sum := by decide
  have hdescent : baseEnd_62365 < baseStart_62365 := by decide
  rcases family_descends (prefixWord ++ tailWord_62365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62437 : List Nat := [1, 3, 1, 6, 1, 1, 1, 3, 3]
def baseStart_62437 : Nat := 118140960795 + 62437 * 2 ^ 59
def prefixEnd_62437 : Nat := 4983230072969 + 3 ^ 40 * 62437 * 2
def baseEnd_62437 : Nat := 28497948111002176578101

theorem tailTrace_62437 : CollatzResearch.WordTrace tailWord_62437 prefixEnd_62437 28497948111002176578101 := by
  unfold tailWord_62437
  simp only [CollatzResearch.WordTrace]
  refine ⟨2277264474808887235753565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1518176316539258157169043 2277264474808887235753565)
  ·
    refine ⟨853974178053332713407587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2277264474808887235753565 853974178053332713407587)
    ·
      refine ⟨1280961267079999070111381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 853974178053332713407587 1280961267079999070111381)
      ·
        refine ⟨60045059394374956411471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1280961267079999070111381 60045059394374956411471)
        ·
          refine ⟨90067589091562434617207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60045059394374956411471 90067589091562434617207)
          ·
            refine ⟨135101383637343651925811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90067589091562434617207 135101383637343651925811)
            ·
              refine ⟨202652075456015477888717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135101383637343651925811 202652075456015477888717)
              ·
                refine ⟨75994528296005804208269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202652075456015477888717 75994528296005804208269)
                ·
                  refine ⟨28497948111002176578101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75994528296005804208269 28497948111002176578101)
                  ·
                    rfl

theorem cell20_62437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_62437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62437 prefixEnd_62437 := by exact prefixLift 62437
  have htrace : WordTrace (prefixWord ++ tailWord_62437) baseStart_62437 baseEnd_62437 := by
    simpa [prefixWord, tailWord_62437, baseEnd_62437] using wordTrace_append hprefix tailTrace_62437
  have hstable : (prefixWord ++ tailWord_62437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62437).length < 2 ^ (prefixWord ++ tailWord_62437).sum := by decide
  have hdescent : baseEnd_62437 < baseStart_62437 := by decide
  rcases family_descends (prefixWord ++ tailWord_62437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62503 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 6]
def baseStart_62503 : Nat := 118140960795 + 62503 * 2 ^ 59
def prefixEnd_62503 : Nat := 4983230072969 + 3 ^ 40 * 62503 * 2
def baseEnd_62503 : Nat := 28528072309399280377831

theorem tailTrace_62503 : CollatzResearch.WordTrace tailWord_62503 prefixEnd_62503 28528072309399280377831 := by
  unfold tailWord_62503
  simp only [CollatzResearch.WordTrace]
  refine ⟨2279671692569780507656163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1519781128379853671770775 2279671692569780507656163)
  ·
    refine ⟨3419507538854670761484245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2279671692569780507656163 3419507538854670761484245)
    ·
      refine ⟨80144707941906345972287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 3419507538854670761484245 80144707941906345972287)
      ·
        refine ⟨120217061912859518958431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80144707941906345972287 120217061912859518958431)
        ·
          refine ⟨180325592869289278437647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120217061912859518958431 180325592869289278437647)
          ·
            refine ⟨270488389303933917656471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180325592869289278437647 270488389303933917656471)
            ·
              refine ⟨405732583955900876484707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270488389303933917656471 405732583955900876484707)
              ·
                refine ⟨608598875933851314727061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405732583955900876484707 608598875933851314727061)
                ·
                  refine ⟨28528072309399280377831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 608598875933851314727061 28528072309399280377831)
                  ·
                    rfl

theorem cell20_62503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 6].length) (baseStart_62503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62503 prefixEnd_62503 := by exact prefixLift 62503
  have htrace : WordTrace (prefixWord ++ tailWord_62503) baseStart_62503 baseEnd_62503 := by
    simpa [prefixWord, tailWord_62503, baseEnd_62503] using wordTrace_append hprefix tailTrace_62503
  have hstable : (prefixWord ++ tailWord_62503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62503).length < 2 ^ (prefixWord ++ tailWord_62503).sum := by decide
  have hdescent : baseEnd_62503 < baseStart_62503 := by decide
  rcases family_descends (prefixWord ++ tailWord_62503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62520 : List Nat := [2, 1, 2, 1, 5, 2, 2, 3, 2]
def baseStart_62520 : Nat := 118140960795 + 62520 * 2 ^ 59
def prefixEnd_62520 : Nat := 4983230072969 + 3 ^ 40 * 62520 * 2
def baseEnd_62520 : Nat := 28535831572622776811095

theorem tailTrace_62520 : CollatzResearch.WordTrace tailWord_62520 prefixEnd_62520 28535831572622776811095 := by
  unfold tailWord_62520
  simp only [CollatzResearch.WordTrace]
  refine ⟨1140145866754096205512507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1520194489005461607350009 1140145866754096205512507)
  ·
    refine ⟨1710218800131144308268761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1140145866754096205512507 1710218800131144308268761)
    ·
      refine ⟨1282664100098358231201571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1710218800131144308268761 1282664100098358231201571)
      ·
        refine ⟨1923996150147537346802357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1282664100098358231201571 1923996150147537346802357)
        ·
          refine ⟨180374639076331626262721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1923996150147537346802357 180374639076331626262721)
          ·
            refine ⟨135280979307248719697041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180374639076331626262721 135280979307248719697041)
            ·
              refine ⟨101460734480436539772781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135280979307248719697041 101460734480436539772781)
              ·
                refine ⟨38047775430163702414793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101460734480436539772781 38047775430163702414793)
                ·
                  refine ⟨28535831572622776811095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38047775430163702414793 28535831572622776811095)
                  ·
                    rfl

theorem cell20_62520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 2].length) (baseStart_62520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62520 prefixEnd_62520 := by exact prefixLift 62520
  have htrace : WordTrace (prefixWord ++ tailWord_62520) baseStart_62520 baseEnd_62520 := by
    simpa [prefixWord, tailWord_62520, baseEnd_62520] using wordTrace_append hprefix tailTrace_62520
  have hstable : (prefixWord ++ tailWord_62520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62520).length < 2 ^ (prefixWord ++ tailWord_62520).sum := by decide
  have hdescent : baseEnd_62520 < baseStart_62520 := by decide
  rcases family_descends (prefixWord ++ tailWord_62520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62541 : List Nat := [1, 6, 1, 1, 1, 2, 1, 3, 4]
def baseStart_62541 : Nat := 118140960795 + 62541 * 2 ^ 59
def prefixEnd_62541 : Nat := 4983230072969 + 3 ^ 40 * 62541 * 2
def baseEnd_62541 : Nat := 28545416544840037111009

theorem tailTrace_62541 : CollatzResearch.WordTrace tailWord_62541 prefixEnd_62541 28545416544840037111009 := by
  unfold tailWord_62541
  simp only [CollatzResearch.WordTrace]
  refine ⟨2281057666432112997539477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1520705110954741998359651 2281057666432112997539477)
  ·
    refine ⟨106924578114005296759663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2281057666432112997539477 106924578114005296759663)
    ·
      refine ⟨160386867171007945139495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106924578114005296759663 160386867171007945139495)
      ·
        refine ⟨240580300756511917709243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160386867171007945139495 240580300756511917709243)
        ·
          refine ⟨360870451134767876563865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240580300756511917709243 360870451134767876563865)
          ·
            refine ⟨270652838351075907422899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360870451134767876563865 270652838351075907422899)
            ·
              refine ⟨405979257526613861134349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270652838351075907422899 405979257526613861134349)
              ·
                refine ⟨152242221572480197925381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405979257526613861134349 152242221572480197925381)
                ·
                  refine ⟨28545416544840037111009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152242221572480197925381 28545416544840037111009)
                  ·
                    rfl

theorem cell20_62541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_62541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62541 prefixEnd_62541 := by exact prefixLift 62541
  have htrace : WordTrace (prefixWord ++ tailWord_62541) baseStart_62541 baseEnd_62541 := by
    simpa [prefixWord, tailWord_62541, baseEnd_62541] using wordTrace_append hprefix tailTrace_62541
  have hstable : (prefixWord ++ tailWord_62541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62541).length < 2 ^ (prefixWord ++ tailWord_62541).sum := by decide
  have hdescent : baseEnd_62541 < baseStart_62541 := by decide
  rcases family_descends (prefixWord ++ tailWord_62541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62569 : List Nat := [1, 2, 1, 1, 1, 7, 1, 6]
def baseStart_62569 : Nat := 118140960795 + 62569 * 2 ^ 59
def prefixEnd_62569 : Nat := 4983230072969 + 3 ^ 40 * 62569 * 2
def baseEnd_62569 : Nat := 9519398835932128059187

theorem tailTrace_62569 : CollatzResearch.WordTrace tailWord_62569 prefixEnd_62569 9519398835932128059187 := by
  unfold tailWord_62569
  simp only [CollatzResearch.WordTrace]
  refine ⟨2282078910330673779558761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1521385940220449186372507 2282078910330673779558761)
  ·
    refine ⟨1711559182748005334669071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2282078910330673779558761 1711559182748005334669071)
    ·
      refine ⟨2567338774122008002003607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1711559182748005334669071 2567338774122008002003607)
      ·
        refine ⟨3851008161183012003005411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2567338774122008002003607 3851008161183012003005411)
        ·
          refine ⟨5776512241774518004508117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3851008161183012003005411 5776512241774518004508117)
          ·
            refine ⟨135387005666590265730659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 5776512241774518004508117 135387005666590265730659)
            ·
              refine ⟨203080508499885398595989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135387005666590265730659 203080508499885398595989)
              ·
                refine ⟨9519398835932128059187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 203080508499885398595989 9519398835932128059187)
                ·
                  rfl

theorem cell20_62569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 6].length) (baseStart_62569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62569 prefixEnd_62569 := by exact prefixLift 62569
  have htrace : WordTrace (prefixWord ++ tailWord_62569) baseStart_62569 baseEnd_62569 := by
    simpa [prefixWord, tailWord_62569, baseEnd_62569] using wordTrace_append hprefix tailTrace_62569
  have hstable : (prefixWord ++ tailWord_62569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62569).length < 2 ^ (prefixWord ++ tailWord_62569).sum := by decide
  have hdescent : baseEnd_62569 < baseStart_62569 := by decide
  rcases family_descends (prefixWord ++ tailWord_62569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62576 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 7]
def baseStart_62576 : Nat := 118140960795 + 62576 * 2 ^ 59
def prefixEnd_62576 : Nat := 4983230072969 + 3 ^ 40 * 62576 * 2
def baseEnd_62576 : Nat := 28561391498535470944199

theorem tailTrace_62576 : CollatzResearch.WordTrace tailWord_62576 prefixEnd_62576 28561391498535470944199 := by
  unfold tailWord_62576
  simp only [CollatzResearch.WordTrace]
  refine ⟨1141167110652656987531791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1521556147536875983375721 1141167110652656987531791)
  ·
    refine ⟨1711750665978985481297687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1141167110652656987531791 1711750665978985481297687)
    ·
      refine ⟨2567625998968478221946531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1711750665978985481297687 2567625998968478221946531)
      ·
        refine ⟨3851438998452717332919797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2567625998968478221946531 3851438998452717332919797)
        ·
          refine ⟨361072406104942249961231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3851438998452717332919797 361072406104942249961231)
          ·
            refine ⟨541608609157413374941847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361072406104942249961231 541608609157413374941847)
            ·
              refine ⟨812412913736120062412771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541608609157413374941847 812412913736120062412771)
              ·
                refine ⟨1218619370604180093619157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812412913736120062412771 1218619370604180093619157)
                ·
                  refine ⟨28561391498535470944199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1218619370604180093619157 28561391498535470944199)
                  ·
                    rfl

theorem cell20_62576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_62576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62576 prefixEnd_62576 := by exact prefixLift 62576
  have htrace : WordTrace (prefixWord ++ tailWord_62576) baseStart_62576 baseEnd_62576 := by
    simpa [prefixWord, tailWord_62576, baseEnd_62576] using wordTrace_append hprefix tailTrace_62576
  have hstable : (prefixWord ++ tailWord_62576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62576).length < 2 ^ (prefixWord ++ tailWord_62576).sum := by decide
  have hdescent : baseEnd_62576 < baseStart_62576 := by decide
  rcases family_descends (prefixWord ++ tailWord_62576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62593 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 5]
def baseStart_62593 : Nat := 118140960795 + 62593 * 2 ^ 59
def prefixEnd_62593 : Nat := 4983230072969 + 3 ^ 40 * 62593 * 2
def baseEnd_62593 : Nat := 28569150761758967377463

theorem tailTrace_62593 : CollatzResearch.WordTrace tailWord_62593 prefixEnd_62593 28569150761758967377463 := by
  unfold tailWord_62593
  simp only [CollatzResearch.WordTrace]
  refine ⟨2282954262243725878432433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1521969508162483918954955 2282954262243725878432433)
  ·
    refine ⟨1712215696682794408824325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2282954262243725878432433 1712215696682794408824325)
    ·
      refine ⟨321040443128023951654561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1712215696682794408824325 321040443128023951654561)
      ·
        refine ⟨240780332346017963740921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321040443128023951654561 240780332346017963740921)
        ·
          refine ⟨180585249259513472805691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240780332346017963740921 180585249259513472805691)
          ·
            refine ⟨270877873889270209208537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180585249259513472805691 270877873889270209208537)
            ·
              refine ⟨203158405416952656906403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270877873889270209208537 203158405416952656906403)
              ·
                refine ⟨304737608125428985359605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203158405416952656906403 304737608125428985359605)
                ·
                  refine ⟨28569150761758967377463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 304737608125428985359605 28569150761758967377463)
                  ·
                    rfl

theorem cell20_62593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_62593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62593 prefixEnd_62593 := by exact prefixLift 62593
  have htrace : WordTrace (prefixWord ++ tailWord_62593) baseStart_62593 baseEnd_62593 := by
    simpa [prefixWord, tailWord_62593, baseEnd_62593] using wordTrace_append hprefix tailTrace_62593
  have hstable : (prefixWord ++ tailWord_62593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62593).length < 2 ^ (prefixWord ++ tailWord_62593).sum := by decide
  have hdescent : baseEnd_62593 < baseStart_62593 := by decide
  rcases family_descends (prefixWord ++ tailWord_62593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62610 : List Nat := [3, 2, 3, 1, 1, 3, 1, 3, 3]
def baseStart_62610 : Nat := 118140960795 + 62610 * 2 ^ 59
def prefixEnd_62610 : Nat := 4983230072969 + 3 ^ 40 * 62610 * 2
def baseEnd_62610 : Nat := 28576910024982463810727

theorem tailTrace_62610 : CollatzResearch.WordTrace tailWord_62610 prefixEnd_62610 28576910024982463810727 := by
  unfold tailWord_62610
  simp only [CollatzResearch.WordTrace]
  refine ⟨570893575795534445450321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1522382868788091854534189 570893575795534445450321)
  ·
    refine ⟨428170181846650834087741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 570893575795534445450321 428170181846650834087741)
    ·
      refine ⟨160563818192494062782903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428170181846650834087741 160563818192494062782903)
      ·
        refine ⟨240845727288741094174355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160563818192494062782903 240845727288741094174355)
        ·
          refine ⟨361268590933111641261533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240845727288741094174355 361268590933111641261533)
          ·
            refine ⟨135475721599916865473075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361268590933111641261533 135475721599916865473075)
            ·
              refine ⟨203213582399875298209613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135475721599916865473075 203213582399875298209613)
              ·
                refine ⟨76205093399953236828605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203213582399875298209613 76205093399953236828605)
                ·
                  refine ⟨28576910024982463810727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76205093399953236828605 28576910024982463810727)
                  ·
                    rfl

theorem cell20_62610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_62610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62610 prefixEnd_62610 := by exact prefixLift 62610
  have htrace : WordTrace (prefixWord ++ tailWord_62610) baseStart_62610 baseEnd_62610 := by
    simpa [prefixWord, tailWord_62610, baseEnd_62610] using wordTrace_append hprefix tailTrace_62610
  have hstable : (prefixWord ++ tailWord_62610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62610).length < 2 ^ (prefixWord ++ tailWord_62610).sum := by decide
  have hdescent : baseEnd_62610 < baseStart_62610 := by decide
  rcases family_descends (prefixWord ++ tailWord_62610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62703 : List Nat := [1, 1, 2, 1, 8, 1, 1, 2, 3]
def baseStart_62703 : Nat := 118140960795 + 62703 * 2 ^ 59
def prefixEnd_62703 : Nat := 4983230072969 + 3 ^ 40 * 62703 * 2
def baseEnd_62703 : Nat := 28619357759087473710347

theorem tailTrace_62703 : CollatzResearch.WordTrace tailWord_62703 prefixEnd_62703 28619357759087473710347 := by
  unfold tailWord_62703
  simp only [CollatzResearch.WordTrace]
  refine ⟨2286966291845214664936763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1524644194563476443291175 2286966291845214664936763)
  ·
    refine ⟨3430449437767821997405145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2286966291845214664936763 3430449437767821997405145)
    ·
      refine ⟨2572837078325866498053859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3430449437767821997405145 2572837078325866498053859)
      ·
        refine ⟨3859255617488799747080789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2572837078325866498053859 3859255617488799747080789)
        ·
          refine ⟨45225651767446872036103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 3859255617488799747080789 45225651767446872036103)
          ·
            refine ⟨67838477651170308054155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45225651767446872036103 67838477651170308054155)
            ·
              refine ⟨101757716476755462081233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67838477651170308054155 101757716476755462081233)
              ·
                refine ⟨76318287357566596560925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101757716476755462081233 76318287357566596560925)
                ·
                  refine ⟨28619357759087473710347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76318287357566596560925 28619357759087473710347)
                  ·
                    rfl

theorem cell20_62703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 3].length) (baseStart_62703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62703 prefixEnd_62703 := by exact prefixLift 62703
  have htrace : WordTrace (prefixWord ++ tailWord_62703) baseStart_62703 baseEnd_62703 := by
    simpa [prefixWord, tailWord_62703, baseEnd_62703] using wordTrace_append hprefix tailTrace_62703
  have hstable : (prefixWord ++ tailWord_62703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62703).length < 2 ^ (prefixWord ++ tailWord_62703).sum := by decide
  have hdescent : baseEnd_62703 < baseStart_62703 := by decide
  rcases family_descends (prefixWord ++ tailWord_62703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62707 : List Nat := [1, 1, 1, 2, 2, 5, 3, 2, 3]
def baseStart_62707 : Nat := 118140960795 + 62707 * 2 ^ 59
def prefixEnd_62707 : Nat := 4983230072969 + 3 ^ 40 * 62707 * 2
def baseEnd_62707 : Nat := 28621183468081237576997

theorem tailTrace_62707 : CollatzResearch.WordTrace tailWord_62707 prefixEnd_62707 28621183468081237576997 := by
  unfold tailWord_62707
  simp only [CollatzResearch.WordTrace]
  refine ⟨2287112183830723348082375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1524741455887148898721583 2287112183830723348082375)
  ·
    refine ⟨3430668275746085022123563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2287112183830723348082375 3430668275746085022123563)
    ·
      refine ⟨5146002413619127533185345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3430668275746085022123563 5146002413619127533185345)
      ·
        refine ⟨3859501810214345649889009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5146002413619127533185345 3859501810214345649889009)
        ·
          refine ⟨2894626357660759237416757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3859501810214345649889009 2894626357660759237416757)
          ·
            refine ⟨271371221030696178507821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2894626357660759237416757 271371221030696178507821)
            ·
              refine ⟨101764207886511066940433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271371221030696178507821 101764207886511066940433)
              ·
                refine ⟨76323155914883300205325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101764207886511066940433 76323155914883300205325)
                ·
                  refine ⟨28621183468081237576997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76323155914883300205325 28621183468081237576997)
                  ·
                    rfl

theorem cell20_62707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 3].length) (baseStart_62707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62707 prefixEnd_62707 := by exact prefixLift 62707
  have htrace : WordTrace (prefixWord ++ tailWord_62707) baseStart_62707 baseEnd_62707 := by
    simpa [prefixWord, tailWord_62707, baseEnd_62707] using wordTrace_append hprefix tailTrace_62707
  have hstable : (prefixWord ++ tailWord_62707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62707).length < 2 ^ (prefixWord ++ tailWord_62707).sum := by decide
  have hdescent : baseEnd_62707 < baseStart_62707 := by decide
  rcases family_descends (prefixWord ++ tailWord_62707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62714 : List Nat := [3, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_62714 : Nat := 118140960795 + 62714 * 2 ^ 59
def prefixEnd_62714 : Nat := 4983230072969 + 3 ^ 40 * 62714 * 2
def baseEnd_62714 : Nat := 28624378458820324343635

theorem tailTrace_62714 : CollatzResearch.WordTrace tailWord_62714 prefixEnd_62714 28624378458820324343635 := by
  unfold tailWord_62714
  simp only [CollatzResearch.WordTrace]
  refine ⟨571841873701340885896799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1524911663203575695724797 571841873701340885896799)
  ·
    refine ⟨857762810552011328845199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 571841873701340885896799 857762810552011328845199)
    ·
      refine ⟨1286644215828016993267799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 857762810552011328845199 1286644215828016993267799)
      ·
        refine ⟨1929966323742025489901699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1286644215828016993267799 1929966323742025489901699)
        ·
          refine ⟨2894949485613038234852549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1929966323742025489901699 2894949485613038234852549)
          ·
            refine ⟨542803028552444669034853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2894949485613038234852549 542803028552444669034853)
            ·
              refine ⟨101775567853583375444035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 542803028552444669034853 101775567853583375444035)
              ·
                refine ⟨152663351780375063166053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101775567853583375444035 152663351780375063166053)
                ·
                  refine ⟨28624378458820324343635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152663351780375063166053 28624378458820324343635)
                  ·
                    rfl

theorem cell20_62714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_62714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62714 prefixEnd_62714 := by exact prefixLift 62714
  have htrace : WordTrace (prefixWord ++ tailWord_62714) baseStart_62714 baseEnd_62714 := by
    simpa [prefixWord, tailWord_62714, baseEnd_62714] using wordTrace_append hprefix tailTrace_62714
  have hstable : (prefixWord ++ tailWord_62714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62714).length < 2 ^ (prefixWord ++ tailWord_62714).sum := by decide
  have hdescent : baseEnd_62714 < baseStart_62714 := by decide
  rcases family_descends (prefixWord ++ tailWord_62714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62769 : List Nat := [1, 2, 2, 3, 3, 3, 1, 1, 4]
def baseStart_62769 : Nat := 118140960795 + 62769 * 2 ^ 59
def prefixEnd_62769 : Nat := 4983230072969 + 3 ^ 40 * 62769 * 2
def baseEnd_62769 : Nat := 28649481957484577510077

theorem tailTrace_62769 : CollatzResearch.WordTrace tailWord_62769 prefixEnd_62769 28649481957484577510077 := by
  unfold tailWord_62769
  simp only [CollatzResearch.WordTrace]
  refine ⟨2289373509606107936839361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1526249006404071957892907 2289373509606107936839361)
  ·
    refine ⟨1717030132204580952629521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2289373509606107936839361 1717030132204580952629521)
    ·
      refine ⟨1287772599153435714472141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1717030132204580952629521 1287772599153435714472141)
      ·
        refine ⟨482914724682538392927053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1287772599153435714472141 482914724682538392927053)
        ·
          refine ⟨181093021755951897347645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482914724682538392927053 181093021755951897347645)
          ·
            refine ⟨67909883158481961505367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181093021755951897347645 67909883158481961505367)
            ·
              refine ⟨101864824737722942258051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67909883158481961505367 101864824737722942258051)
              ·
                refine ⟨152797237106584413387077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101864824737722942258051 152797237106584413387077)
                ·
                  refine ⟨28649481957484577510077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152797237106584413387077 28649481957484577510077)
                  ·
                    rfl

theorem cell20_62769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 4].length) (baseStart_62769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62769 prefixEnd_62769 := by exact prefixLift 62769
  have htrace : WordTrace (prefixWord ++ tailWord_62769) baseStart_62769 baseEnd_62769 := by
    simpa [prefixWord, tailWord_62769, baseEnd_62769] using wordTrace_append hprefix tailTrace_62769
  have hstable : (prefixWord ++ tailWord_62769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62769).length < 2 ^ (prefixWord ++ tailWord_62769).sum := by decide
  have hdescent : baseEnd_62769 < baseStart_62769 := by decide
  rcases family_descends (prefixWord ++ tailWord_62769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62783 : List Nat := [1, 1, 2, 2, 4, 3, 1, 3, 3]
def baseStart_62783 : Nat := 118140960795 + 62783 * 2 ^ 59
def prefixEnd_62783 : Nat := 4983230072969 + 3 ^ 40 * 62783 * 2
def baseEnd_62783 : Nat := 28655871938962751043353

theorem tailTrace_62783 : CollatzResearch.WordTrace tailWord_62783 prefixEnd_62783 28655871938962751043353 := by
  unfold tailWord_62783
  simp only [CollatzResearch.WordTrace]
  refine ⟨2289884131555388327849003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1526589421036925551899335 2289884131555388327849003)
  ·
    refine ⟨3434826197333082491773505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2289884131555388327849003 3434826197333082491773505)
    ·
      refine ⟨2576119647999811868830129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3434826197333082491773505 2576119647999811868830129)
      ·
        refine ⟨1932089735999858901622597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2576119647999811868830129 1932089735999858901622597)
        ·
          refine ⟨362266825499973544054237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1932089735999858901622597 362266825499973544054237)
          ·
            refine ⟨135850059562490079020339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 362266825499973544054237 135850059562490079020339)
            ·
              refine ⟨203775089343735118530509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135850059562490079020339 203775089343735118530509)
              ·
                refine ⟨76415658503900669448941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203775089343735118530509 76415658503900669448941)
                ·
                  refine ⟨28655871938962751043353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76415658503900669448941 28655871938962751043353)
                  ·
                    rfl

theorem cell20_62783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 3].length) (baseStart_62783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62783 prefixEnd_62783 := by exact prefixLift 62783
  have htrace : WordTrace (prefixWord ++ tailWord_62783) baseStart_62783 baseEnd_62783 := by
    simpa [prefixWord, tailWord_62783, baseEnd_62783] using wordTrace_append hprefix tailTrace_62783
  have hstable : (prefixWord ++ tailWord_62783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62783).length < 2 ^ (prefixWord ++ tailWord_62783).sum := by decide
  have hdescent : baseEnd_62783 < baseStart_62783 := by decide
  rcases family_descends (prefixWord ++ tailWord_62783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62821 : List Nat := [1, 3, 1, 3, 1, 2, 4, 2, 3]
def baseStart_62821 : Nat := 118140960795 + 62821 * 2 ^ 59
def prefixEnd_62821 : Nat := 4983230072969 + 3 ^ 40 * 62821 * 2
def baseEnd_62821 : Nat := 28673216174403507776531

theorem tailTrace_62821 : CollatzResearch.WordTrace tailWord_62821 prefixEnd_62821 28673216174403507776531 := by
  unfold tailWord_62821
  simp only [CollatzResearch.WordTrace]
  refine ⟨2291270105417720817732317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1527513403611813878488211 2291270105417720817732317)
  ·
    refine ⟨859226289531645306649619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2291270105417720817732317 859226289531645306649619)
    ·
      refine ⟨1288839434297467959974429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 859226289531645306649619 1288839434297467959974429)
      ·
        refine ⟨483314787861550484990411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1288839434297467959974429 483314787861550484990411)
        ·
          refine ⟨724972181792325727485617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483314787861550484990411 724972181792325727485617)
          ·
            refine ⟨543729136344244295614213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724972181792325727485617 543729136344244295614213)
            ·
              refine ⟨101949213064545805427665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 543729136344244295614213 101949213064545805427665)
              ·
                refine ⟨76461909798409354070749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101949213064545805427665 76461909798409354070749)
                ·
                  refine ⟨28673216174403507776531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76461909798409354070749 28673216174403507776531)
                  ·
                    rfl

theorem cell20_62821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_62821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62821 prefixEnd_62821 := by exact prefixLift 62821
  have htrace : WordTrace (prefixWord ++ tailWord_62821) baseStart_62821 baseEnd_62821 := by
    simpa [prefixWord, tailWord_62821, baseEnd_62821] using wordTrace_append hprefix tailTrace_62821
  have hstable : (prefixWord ++ tailWord_62821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62821).length < 2 ^ (prefixWord ++ tailWord_62821).sum := by decide
  have hdescent : baseEnd_62821 < baseStart_62821 := by decide
  rcases family_descends (prefixWord ++ tailWord_62821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62824 : List Nat := [2, 1, 4, 2, 3, 1, 1, 4, 2]
def baseStart_62824 : Nat := 118140960795 + 62824 * 2 ^ 59
def prefixEnd_62824 : Nat := 4983230072969 + 3 ^ 40 * 62824 * 2
def baseEnd_62824 : Nat := 28674585456148830676519

theorem tailTrace_62824 : CollatzResearch.WordTrace tailWord_62824 prefixEnd_62824 28674585456148830676519 := by
  unfold tailWord_62824
  simp only [CollatzResearch.WordTrace]
  refine ⟨1145689762203426165045763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1527586349604568220061017 1145689762203426165045763)
  ·
    refine ⟨1718534643305139247568645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1145689762203426165045763 1718534643305139247568645)
    ·
      refine ⟨322225245619713608919121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1718534643305139247568645 322225245619713608919121)
      ·
        refine ⟨241668934214785206689341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322225245619713608919121 241668934214785206689341)
        ·
          refine ⟨90625850330544452508503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241668934214785206689341 90625850330544452508503)
          ·
            refine ⟨135938775495816678762755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90625850330544452508503 135938775495816678762755)
            ·
              refine ⟨203908163243725018144133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135938775495816678762755 203908163243725018144133)
              ·
                refine ⟨38232780608198440902025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203908163243725018144133 38232780608198440902025)
                ·
                  refine ⟨28674585456148830676519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38232780608198440902025 28674585456148830676519)
                  ·
                    rfl

theorem cell20_62824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4, 2].length) (baseStart_62824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62824 prefixEnd_62824 := by exact prefixLift 62824
  have htrace : WordTrace (prefixWord ++ tailWord_62824) baseStart_62824 baseEnd_62824 := by
    simpa [prefixWord, tailWord_62824, baseEnd_62824] using wordTrace_append hprefix tailTrace_62824
  have hstable : (prefixWord ++ tailWord_62824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62824).length < 2 ^ (prefixWord ++ tailWord_62824).sum := by decide
  have hdescent : baseEnd_62824 < baseStart_62824 := by decide
  rcases family_descends (prefixWord ++ tailWord_62824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62852 : List Nat := [2, 3, 2, 1, 1, 4, 3, 4]
def baseStart_62852 : Nat := 118140960795 + 62852 * 2 ^ 59
def prefixEnd_62852 : Nat := 4983230072969 + 3 ^ 40 * 62852 * 2
def baseEnd_62852 : Nat := 9562455139701725914357

theorem tailTrace_62852 : CollatzResearch.WordTrace tailWord_62852 prefixEnd_62852 9562455139701725914357 := by
  unfold tailWord_62852
  simp only [CollatzResearch.WordTrace]
  refine ⟨1146200384152706556055405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1528267178870275408073873 1146200384152706556055405)
  ·
    refine ⟨429825144057264958520777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1146200384152706556055405 429825144057264958520777)
    ·
      refine ⟨322368858042948718890583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429825144057264958520777 322368858042948718890583)
      ·
        refine ⟨483553287064423078335875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322368858042948718890583 483553287064423078335875)
        ·
          refine ⟨725329930596634617503813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483553287064423078335875 725329930596634617503813)
          ·
            refine ⟨135999361986868990781965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 725329930596634617503813 135999361986868990781965)
            ·
              refine ⟨50999760745075871543237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135999361986868990781965 50999760745075871543237)
              ·
                refine ⟨9562455139701725914357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50999760745075871543237 9562455139701725914357)
                ·
                  rfl

theorem cell20_62852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_62852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62852 prefixEnd_62852 := by exact prefixLift 62852
  have htrace : WordTrace (prefixWord ++ tailWord_62852) baseStart_62852 baseEnd_62852 := by
    simpa [prefixWord, tailWord_62852, baseEnd_62852] using wordTrace_append hprefix tailTrace_62852
  have hstable : (prefixWord ++ tailWord_62852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62852).length < 2 ^ (prefixWord ++ tailWord_62852).sum := by decide
  have hdescent : baseEnd_62852 < baseStart_62852 := by decide
  rcases family_descends (prefixWord ++ tailWord_62852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62876 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 5]
def baseStart_62876 : Nat := 118140960795 + 62876 * 2 ^ 59
def prefixEnd_62876 : Nat := 4983230072969 + 3 ^ 40 * 62876 * 2
def baseEnd_62876 : Nat := 28698319673067760942973

theorem tailTrace_62876 : CollatzResearch.WordTrace tailWord_62876 prefixEnd_62876 28698319673067760942973 := by
  unfold tailWord_62876
  simp only [CollatzResearch.WordTrace]
  refine ⟨1146638060109232605492241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1528850746812310140656321 1146638060109232605492241)
  ·
    refine ⟨859978545081924454119181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1146638060109232605492241 859978545081924454119181)
    ·
      refine ⟨322491954405721670294693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 859978545081924454119181 322491954405721670294693)
      ·
        refine ⟨60467241451072813180255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322491954405721670294693 60467241451072813180255)
        ·
          refine ⟨90700862176609219770383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60467241451072813180255 90700862176609219770383)
          ·
            refine ⟨136051293264913829655575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90700862176609219770383 136051293264913829655575)
            ·
              refine ⟨204076939897370744483363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136051293264913829655575 204076939897370744483363)
              ·
                refine ⟨306115409846056116725045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204076939897370744483363 306115409846056116725045)
                ·
                  refine ⟨28698319673067760942973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 306115409846056116725045 28698319673067760942973)
                  ·
                    rfl

theorem cell20_62876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_62876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62876 prefixEnd_62876 := by exact prefixLift 62876
  have htrace : WordTrace (prefixWord ++ tailWord_62876) baseStart_62876 baseEnd_62876 := by
    simpa [prefixWord, tailWord_62876, baseEnd_62876] using wordTrace_append hprefix tailTrace_62876
  have hstable : (prefixWord ++ tailWord_62876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62876).length < 2 ^ (prefixWord ++ tailWord_62876).sum := by decide
  have hdescent : baseEnd_62876 < baseStart_62876 := by decide
  rcases family_descends (prefixWord ++ tailWord_62876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62880 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 5]
def baseStart_62880 : Nat := 118140960795 + 62880 * 2 ^ 59
def prefixEnd_62880 : Nat := 4983230072969 + 3 ^ 40 * 62880 * 2
def baseEnd_62880 : Nat := 28700145382061524809623

theorem tailTrace_62880 : CollatzResearch.WordTrace tailWord_62880 prefixEnd_62880 28700145382061524809623 := by
  unfold tailWord_62880
  simp only [CollatzResearch.WordTrace]
  refine ⟨1146711006101986947065047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1528948008135982596086729 1146711006101986947065047)
  ·
    refine ⟨1720066509152980420597571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1146711006101986947065047 1720066509152980420597571)
    ·
      refine ⟨2580099763729470630896357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1720066509152980420597571 2580099763729470630896357)
      ·
        refine ⟨483768705699275743293067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2580099763729470630896357 483768705699275743293067)
        ·
          refine ⟨725653058548913614939601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483768705699275743293067 725653058548913614939601)
          ·
            refine ⟨544239793911685211204701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 725653058548913614939601 544239793911685211204701)
            ·
              refine ⟨204089922716881954201763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 544239793911685211204701 204089922716881954201763)
              ·
                refine ⟨306134884075322931302645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204089922716881954201763 306134884075322931302645)
                ·
                  refine ⟨28700145382061524809623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 306134884075322931302645 28700145382061524809623)
                  ·
                    rfl

theorem cell20_62880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_62880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62880 prefixEnd_62880 := by exact prefixLift 62880
  have htrace : WordTrace (prefixWord ++ tailWord_62880) baseStart_62880 baseEnd_62880 := by
    simpa [prefixWord, tailWord_62880, baseEnd_62880] using wordTrace_append hprefix tailTrace_62880
  have hstable : (prefixWord ++ tailWord_62880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62880).length < 2 ^ (prefixWord ++ tailWord_62880).sum := by decide
  have hdescent : baseEnd_62880 < baseStart_62880 := by decide
  rcases family_descends (prefixWord ++ tailWord_62880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62893 : List Nat := [1, 5, 2, 2, 1, 2, 3, 1, 3]
def baseStart_62893 : Nat := 118140960795 + 62893 * 2 ^ 59
def prefixEnd_62893 : Nat := 4983230072969 + 3 ^ 40 * 62893 * 2
def baseEnd_62893 : Nat := 28706078936291257376237

theorem tailTrace_62893 : CollatzResearch.WordTrace tailWord_62893 prefixEnd_62893 28706078936291257376237 := by
  unfold tailWord_62893
  simp only [CollatzResearch.WordTrace]
  refine ⟨2293896161156877114353333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1529264107437918076235555 2293896161156877114353333)
  ·
    refine ⟨215052765108457229470625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2293896161156877114353333 215052765108457229470625)
    ·
      refine ⟨161289573831342922102969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215052765108457229470625 161289573831342922102969)
      ·
        refine ⟨120967180373507191577227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161289573831342922102969 120967180373507191577227)
        ·
          refine ⟨181450770560260787365841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120967180373507191577227 181450770560260787365841)
          ·
            refine ⟨136088077920195590524381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181450770560260787365841 136088077920195590524381)
            ·
              refine ⟨51033029220073346446643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136088077920195590524381 51033029220073346446643)
              ·
                refine ⟨76549543830110019669965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51033029220073346446643 76549543830110019669965)
                ·
                  refine ⟨28706078936291257376237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76549543830110019669965 28706078936291257376237)
                  ·
                    rfl

theorem cell20_62893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_62893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62893 prefixEnd_62893 := by exact prefixLift 62893
  have htrace : WordTrace (prefixWord ++ tailWord_62893) baseStart_62893 baseEnd_62893 := by
    simpa [prefixWord, tailWord_62893, baseEnd_62893] using wordTrace_append hprefix tailTrace_62893
  have hstable : (prefixWord ++ tailWord_62893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62893).length < 2 ^ (prefixWord ++ tailWord_62893).sum := by decide
  have hdescent : baseEnd_62893 < baseStart_62893 := by decide
  rcases family_descends (prefixWord ++ tailWord_62893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62938 : List Nat := [3, 1, 1, 2, 3, 3, 3, 2, 2]
def baseStart_62938 : Nat := 118140960795 + 62938 * 2 ^ 59
def prefixEnd_62938 : Nat := 4983230072969 + 3 ^ 40 * 62938 * 2
def baseEnd_62938 : Nat := 28726618162471100876053

theorem tailTrace_62938 : CollatzResearch.WordTrace tailWord_62938 prefixEnd_62938 28726618162471100876053 := by
  unfold tailWord_62938
  simp only [CollatzResearch.WordTrace]
  refine ⟨573884361498462449935367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1530358297329233199827645 573884361498462449935367)
  ·
    refine ⟨860826542247693674903051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 573884361498462449935367 860826542247693674903051)
    ·
      refine ⟨1291239813371540512354577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 860826542247693674903051 1291239813371540512354577)
      ·
        refine ⟨968429860028655384265933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1291239813371540512354577 968429860028655384265933)
        ·
          refine ⟨363161197510745769099725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 968429860028655384265933 363161197510745769099725)
          ·
            refine ⟨136185449066529663412397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363161197510745769099725 136185449066529663412397)
            ·
              refine ⟨51069543399948623779649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136185449066529663412397 51069543399948623779649)
              ·
                refine ⟨38302157549961467834737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51069543399948623779649 38302157549961467834737)
                ·
                  refine ⟨28726618162471100876053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38302157549961467834737 28726618162471100876053)
                  ·
                    rfl

theorem cell20_62938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_62938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62938 prefixEnd_62938 := by exact prefixLift 62938
  have htrace : WordTrace (prefixWord ++ tailWord_62938) baseStart_62938 baseEnd_62938 := by
    simpa [prefixWord, tailWord_62938, baseEnd_62938] using wordTrace_append hprefix tailTrace_62938
  have hstable : (prefixWord ++ tailWord_62938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62938).length < 2 ^ (prefixWord ++ tailWord_62938).sum := by decide
  have hdescent : baseEnd_62938 < baseStart_62938 := by decide
  rcases family_descends (prefixWord ++ tailWord_62938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62949 : List Nat := [1, 3, 1, 5, 1, 1, 1, 7]
def baseStart_62949 : Nat := 118140960795 + 62949 * 2 ^ 59
def prefixEnd_62949 : Nat := 4983230072969 + 3 ^ 40 * 62949 * 2
def baseEnd_62949 : Nat := 9577212954067983836447

theorem tailTrace_62949 : CollatzResearch.WordTrace tailWord_62949 prefixEnd_62949 9577212954067983836447 := by
  unfold tailWord_62949
  simp only [CollatzResearch.WordTrace]
  refine ⟨2295938648953998678391901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1530625765969332452261267 2295938648953998678391901)
  ·
    refine ⟨860976993357749504396963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2295938648953998678391901 860976993357749504396963)
    ·
      refine ⟨1291465490036624256595445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 860976993357749504396963 1291465490036624256595445)
      ·
        refine ⟨121074889690933524055823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1291465490036624256595445 121074889690933524055823)
        ·
          refine ⟨181612334536400286083735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121074889690933524055823 181612334536400286083735)
          ·
            refine ⟨272418501804600429125603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181612334536400286083735 272418501804600429125603)
            ·
              refine ⟨408627752706900643688405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272418501804600429125603 408627752706900643688405)
              ·
                refine ⟨9577212954067983836447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 408627752706900643688405 9577212954067983836447)
                ·
                  rfl

theorem cell20_62949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 7].length) (baseStart_62949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62949 prefixEnd_62949 := by exact prefixLift 62949
  have htrace : WordTrace (prefixWord ++ tailWord_62949) baseStart_62949 baseEnd_62949 := by
    simpa [prefixWord, tailWord_62949, baseEnd_62949] using wordTrace_append hprefix tailTrace_62949
  have hstable : (prefixWord ++ tailWord_62949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62949).length < 2 ^ (prefixWord ++ tailWord_62949).sum := by decide
  have hdescent : baseEnd_62949 < baseStart_62949 := by decide
  rcases family_descends (prefixWord ++ tailWord_62949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62970 : List Nat := [3, 1, 1, 1, 1, 2, 3, 8]
def baseStart_62970 : Nat := 118140960795 + 62970 * 2 ^ 59
def prefixEnd_62970 : Nat := 4983230072969 + 3 ^ 40 * 62970 * 2
def baseEnd_62970 : Nat := 9580407944807070603085

theorem tailTrace_62970 : CollatzResearch.WordTrace tailWord_62970 prefixEnd_62970 9580407944807070603085 := by
  unfold tailWord_62970
  simp only [CollatzResearch.WordTrace]
  refine ⟨574176145469479816226591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1531136387918612843270909 574176145469479816226591)
  ·
    refine ⟨861264218204219724339887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 574176145469479816226591 861264218204219724339887)
    ·
      refine ⟨1291896327306329586509831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 861264218204219724339887 1291896327306329586509831)
      ·
        refine ⟨1937844490959494379764747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1291896327306329586509831 1937844490959494379764747)
        ·
          refine ⟨2906766736439241569647121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1937844490959494379764747 2906766736439241569647121)
          ·
            refine ⟨2180075052329431177235341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2906766736439241569647121 2180075052329431177235341)
            ·
              refine ⟨817528144623536691463253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2180075052329431177235341 817528144623536691463253)
              ·
                refine ⟨9580407944807070603085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 817528144623536691463253 9580407944807070603085)
                ·
                  rfl

theorem cell20_62970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_62970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62970 prefixEnd_62970 := by exact prefixLift 62970
  have htrace : WordTrace (prefixWord ++ tailWord_62970) baseStart_62970 baseEnd_62970 := by
    simpa [prefixWord, tailWord_62970, baseEnd_62970] using wordTrace_append hprefix tailTrace_62970
  have hstable : (prefixWord ++ tailWord_62970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62970).length < 2 ^ (prefixWord ++ tailWord_62970).sum := by decide
  have hdescent : baseEnd_62970 < baseStart_62970 := by decide
  rcases family_descends (prefixWord ++ tailWord_62970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62987 : List Nat := [1, 1, 1, 1, 9, 7]
def baseStart_62987 : Nat := 118140960795 + 62987 * 2 ^ 59
def prefixEnd_62987 : Nat := 4983230072969 + 3 ^ 40 * 62987 * 2
def baseEnd_62987 : Nat := 1064777151764618823797

theorem tailTrace_62987 : CollatzResearch.WordTrace tailWord_62987 prefixEnd_62987 1064777151764618823797 := by
  unfold tailWord_62987
  simp only [CollatzResearch.WordTrace]
  refine ⟨2297324622816331168275215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1531549748544220778850143 2297324622816331168275215)
  ·
    refine ⟨3445986934224496752412823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2297324622816331168275215 3445986934224496752412823)
    ·
      refine ⟨5168980401336745128619235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3445986934224496752412823 5168980401336745128619235)
      ·
        refine ⟨7753470602005117692928853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5168980401336745128619235 7753470602005117692928853)
        ·
          refine ⟨45430491808623736482005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 7753470602005117692928853 45430491808623736482005)
          ·
            refine ⟨1064777151764618823797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 45430491808623736482005 1064777151764618823797)
            ·
              rfl

theorem cell20_62987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 7].length) (baseStart_62987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62987 prefixEnd_62987 := by exact prefixLift 62987
  have htrace : WordTrace (prefixWord ++ tailWord_62987) baseStart_62987 baseEnd_62987 := by
    simpa [prefixWord, tailWord_62987, baseEnd_62987] using wordTrace_append hprefix tailTrace_62987
  have hstable : (prefixWord ++ tailWord_62987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62987).length < 2 ^ (prefixWord ++ tailWord_62987).sum := by decide
  have hdescent : baseEnd_62987 < baseStart_62987 := by decide
  rcases family_descends (prefixWord ++ tailWord_62987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62989 : List Nat := [1, 7, 1, 1, 2, 2, 2, 2, 2]
def baseStart_62989 : Nat := 118140960795 + 62989 * 2 ^ 59
def prefixEnd_62989 : Nat := 4983230072969 + 3 ^ 40 * 62989 * 2
def baseEnd_62989 : Nat := 28749895952141590175845

theorem tailTrace_62989 : CollatzResearch.WordTrace tailWord_62989 prefixEnd_62989 28749895952141590175845 := by
  unfold tailWord_62989
  simp only [CollatzResearch.WordTrace]
  refine ⟨2297397568809085509848021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1531598379206057006565347 2297397568809085509848021)
  ·
    refine ⟨53845255518962941637063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 2297397568809085509848021 53845255518962941637063)
    ·
      refine ⟨80767883278444412455595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53845255518962941637063 80767883278444412455595)
      ·
        refine ⟨121151824917666618683393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80767883278444412455595 121151824917666618683393)
        ·
          refine ⟨90863868688249964012545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121151824917666618683393 90863868688249964012545)
          ·
            refine ⟨68147901516187473009409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90863868688249964012545 68147901516187473009409)
            ·
              refine ⟨51110926137140604757057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68147901516187473009409 51110926137140604757057)
              ·
                refine ⟨38333194602855453567793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51110926137140604757057 38333194602855453567793)
                ·
                  refine ⟨28749895952141590175845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38333194602855453567793 28749895952141590175845)
                  ·
                    rfl

theorem cell20_62989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_62989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62989 prefixEnd_62989 := by exact prefixLift 62989
  have htrace : WordTrace (prefixWord ++ tailWord_62989) baseStart_62989 baseEnd_62989 := by
    simpa [prefixWord, tailWord_62989, baseEnd_62989] using wordTrace_append hprefix tailTrace_62989
  have hstable : (prefixWord ++ tailWord_62989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62989).length < 2 ^ (prefixWord ++ tailWord_62989).sum := by decide
  have hdescent : baseEnd_62989 < baseStart_62989 := by decide
  rcases family_descends (prefixWord ++ tailWord_62989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62990 : List Nat := [4, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_62990 : Nat := 118140960795 + 62990 * 2 ^ 59
def prefixEnd_62990 : Nat := 4983230072969 + 3 ^ 40 * 62990 * 2
def baseEnd_62990 : Nat := 28750352379390031142507

theorem tailTrace_62990 : CollatzResearch.WordTrace tailWord_62990 prefixEnd_62990 28750352379390031142507 := by
  unfold tailWord_62990
  simp only [CollatzResearch.WordTrace]
  refine ⟨287179255225682835079303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1531622694536975120422949 287179255225682835079303)
  ·
    refine ⟨430768882838524252618955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287179255225682835079303 430768882838524252618955)
    ·
      refine ⟨646153324257786378928433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430768882838524252618955 646153324257786378928433)
      ·
        refine ⟨484614993193339784196325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646153324257786378928433 484614993193339784196325)
        ·
          refine ⟨90865311223751209536811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 484614993193339784196325 90865311223751209536811)
          ·
            refine ⟨136297966835626814305217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90865311223751209536811 136297966835626814305217)
            ·
              refine ⟨102223475126720110728913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136297966835626814305217 102223475126720110728913)
              ·
                refine ⟨76667606345040083046685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102223475126720110728913 76667606345040083046685)
                ·
                  refine ⟨28750352379390031142507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76667606345040083046685 28750352379390031142507)
                  ·
                    rfl

theorem cell20_62990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_62990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62990 prefixEnd_62990 := by exact prefixLift 62990
  have htrace : WordTrace (prefixWord ++ tailWord_62990) baseStart_62990 baseEnd_62990 := by
    simpa [prefixWord, tailWord_62990, baseEnd_62990] using wordTrace_append hprefix tailTrace_62990
  have hstable : (prefixWord ++ tailWord_62990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62990).length < 2 ^ (prefixWord ++ tailWord_62990).sum := by decide
  have hdescent : baseEnd_62990 < baseStart_62990 := by decide
  rcases family_descends (prefixWord ++ tailWord_62990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62997 : List Nat := [1, 3, 2, 1, 3, 3, 1, 4, 2]
def baseStart_62997 : Nat := 118140960795 + 62997 * 2 ^ 59
def prefixEnd_62997 : Nat := 4983230072969 + 3 ^ 40 * 62997 * 2
def baseEnd_62997 : Nat := 28753547370129117909145

theorem tailTrace_62997 : CollatzResearch.WordTrace tailWord_62997 prefixEnd_62997 28753547370129117909145 := by
  unfold tailWord_62997
  simp only [CollatzResearch.WordTrace]
  refine ⟨2297689352780102876139245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1531792901853401917426163 2297689352780102876139245)
  ·
    refine ⟨861633507292538578552217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2297689352780102876139245 861633507292538578552217)
    ·
      refine ⟨646225130469403933914163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 861633507292538578552217 646225130469403933914163)
      ·
        refine ⟨969337695704105900871245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646225130469403933914163 969337695704105900871245)
        ·
          refine ⟨363501635889039712826717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 969337695704105900871245 363501635889039712826717)
          ·
            refine ⟨136313113458389892310019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363501635889039712826717 136313113458389892310019)
            ·
              refine ⟨204469670187584838465029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136313113458389892310019 204469670187584838465029)
              ·
                refine ⟨38338063160172157212193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204469670187584838465029 38338063160172157212193)
                ·
                  refine ⟨28753547370129117909145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38338063160172157212193 28753547370129117909145)
                  ·
                    rfl

theorem cell20_62997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_62997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_62997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_62997 prefixEnd_62997 := by exact prefixLift 62997
  have htrace : WordTrace (prefixWord ++ tailWord_62997) baseStart_62997 baseEnd_62997 := by
    simpa [prefixWord, tailWord_62997, baseEnd_62997] using wordTrace_append hprefix tailTrace_62997
  have hstable : (prefixWord ++ tailWord_62997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62997).length < 2 ^ (prefixWord ++ tailWord_62997).sum := by decide
  have hdescent : baseEnd_62997 < baseStart_62997 := by decide
  rcases family_descends (prefixWord ++ tailWord_62997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63018 : List Nat := [3, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_63018 : Nat := 118140960795 + 63018 * 2 ^ 59
def prefixEnd_63018 : Nat := 4983230072969 + 3 ^ 40 * 63018 * 2
def baseEnd_63018 : Nat := 28763132342346378209059

theorem tailTrace_63018 : CollatzResearch.WordTrace tailWord_63018 prefixEnd_63018 28763132342346378209059 := by
  unfold tailWord_63018
  simp only [CollatzResearch.WordTrace]
  refine ⟨574613821426005865663427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1532303523802682308435805 574613821426005865663427)
  ·
    refine ⟨861920732139008798495141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 574613821426005865663427 861920732139008798495141)
    ·
      refine ⟨161610137276064149717839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 861920732139008798495141 161610137276064149717839)
      ·
        refine ⟨242415205914096224576759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161610137276064149717839 242415205914096224576759)
        ·
          refine ⟨363622808871144336865139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242415205914096224576759 363622808871144336865139)
          ·
            refine ⟨545434213306716505297709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363622808871144336865139 545434213306716505297709)
            ·
              refine ⟨204537829990018689486641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 545434213306716505297709 204537829990018689486641)
              ·
                refine ⟨153403372492514017114981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204537829990018689486641 153403372492514017114981)
                ·
                  refine ⟨28763132342346378209059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153403372492514017114981 28763132342346378209059)
                  ·
                    rfl

theorem cell20_63018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_63018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63018 prefixEnd_63018 := by exact prefixLift 63018
  have htrace : WordTrace (prefixWord ++ tailWord_63018) baseStart_63018 baseEnd_63018 := by
    simpa [prefixWord, tailWord_63018, baseEnd_63018] using wordTrace_append hprefix tailTrace_63018
  have hstable : (prefixWord ++ tailWord_63018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63018).length < 2 ^ (prefixWord ++ tailWord_63018).sum := by decide
  have hdescent : baseEnd_63018 < baseStart_63018 := by decide
  rcases family_descends (prefixWord ++ tailWord_63018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63056 : List Nat := [2, 1, 1, 1, 1, 3, 3, 6, 2]
def baseStart_63056 : Nat := 118140960795 + 63056 * 2 ^ 59
def prefixEnd_63056 : Nat := 4983230072969 + 3 ^ 40 * 63056 * 2
def baseEnd_63056 : Nat := 28780476577787134942237

theorem tailTrace_63056 : CollatzResearch.WordTrace tailWord_63056 prefixEnd_63056 28780476577787134942237 := by
  unfold tailWord_63056
  simp only [CollatzResearch.WordTrace]
  refine ⟨1149920629783177976268511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1533227506377570635024681 1149920629783177976268511)
  ·
    refine ⟨1724880944674766964402767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1149920629783177976268511 1724880944674766964402767)
    ·
      refine ⟨2587321417012150446604151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1724880944674766964402767 2587321417012150446604151)
      ·
        refine ⟨3880982125518225669906227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2587321417012150446604151 3880982125518225669906227)
        ·
          refine ⟨5821473188277338504859341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3880982125518225669906227 5821473188277338504859341)
          ·
            refine ⟨2183052445604001939322253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5821473188277338504859341 2183052445604001939322253)
            ·
              refine ⟨818644667101500727245845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2183052445604001939322253 818644667101500727245845)
              ·
                refine ⟨38373968770382846589649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 818644667101500727245845 38373968770382846589649)
                ·
                  refine ⟨28780476577787134942237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38373968770382846589649 28780476577787134942237)
                  ·
                    rfl

theorem cell20_63056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 2].length) (baseStart_63056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63056 prefixEnd_63056 := by exact prefixLift 63056
  have htrace : WordTrace (prefixWord ++ tailWord_63056) baseStart_63056 baseEnd_63056 := by
    simpa [prefixWord, tailWord_63056, baseEnd_63056] using wordTrace_append hprefix tailTrace_63056
  have hstable : (prefixWord ++ tailWord_63056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63056).length < 2 ^ (prefixWord ++ tailWord_63056).sum := by decide
  have hdescent : baseEnd_63056 < baseStart_63056 := by decide
  rcases family_descends (prefixWord ++ tailWord_63056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63080 : List Nat := [2, 1, 4, 3, 1, 1, 4, 4]
def baseStart_63080 : Nat := 118140960795 + 63080 * 2 ^ 59
def prefixEnd_63080 : Nat := 4983230072969 + 3 ^ 40 * 63080 * 2
def baseEnd_63080 : Nat := 9597143610583239380713

theorem tailTrace_63080 : CollatzResearch.WordTrace tailWord_63080 prefixEnd_63080 9597143610583239380713 := by
  unfold tailWord_63080
  simp only [CollatzResearch.WordTrace]
  refine ⟨1150358305739704025705347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1533811074319605367607129 1150358305739704025705347)
  ·
    refine ⟨1725537458609556038558021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1150358305739704025705347 1725537458609556038558021)
    ·
      refine ⟨323538273489291757229629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1725537458609556038558021 323538273489291757229629)
      ·
        refine ⟨121326852558484408961111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323538273489291757229629 121326852558484408961111)
        ·
          refine ⟨181990278837726613441667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121326852558484408961111 181990278837726613441667)
          ·
            refine ⟨272985418256589920162501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181990278837726613441667 272985418256589920162501)
            ·
              refine ⟨51184765923110610030469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272985418256589920162501 51184765923110610030469)
              ·
                refine ⟨9597143610583239380713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51184765923110610030469 9597143610583239380713)
                ·
                  rfl

theorem cell20_63080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_63080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63080 prefixEnd_63080 := by exact prefixLift 63080
  have htrace : WordTrace (prefixWord ++ tailWord_63080) baseStart_63080 baseEnd_63080 := by
    simpa [prefixWord, tailWord_63080, baseEnd_63080] using wordTrace_append hprefix tailTrace_63080
  have hstable : (prefixWord ++ tailWord_63080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63080).length < 2 ^ (prefixWord ++ tailWord_63080).sum := by decide
  have hdescent : baseEnd_63080 < baseStart_63080 := by decide
  rcases family_descends (prefixWord ++ tailWord_63080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63090 : List Nat := [3, 2, 1, 2, 3, 3, 1, 3, 2]
def baseStart_63090 : Nat := 118140960795 + 63090 * 2 ^ 59
def prefixEnd_63090 : Nat := 4983230072969 + 3 ^ 40 * 63090 * 2
def baseEnd_63090 : Nat := 28795995104234127808765

theorem tailTrace_63090 : CollatzResearch.WordTrace tailWord_63090 prefixEnd_63090 28795995104234127808765 := by
  unfold tailWord_63090
  simp only [CollatzResearch.WordTrace]
  refine ⟨575270335360794939818681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1534054227628786506183149 575270335360794939818681)
  ·
    refine ⟨431452751520596204864011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 575270335360794939818681 431452751520596204864011)
    ·
      refine ⟨647179127280894307296017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431452751520596204864011 647179127280894307296017)
      ·
        refine ⟨485384345460670730472013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 647179127280894307296017 485384345460670730472013)
        ·
          refine ⟨182019129547751523927005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 485384345460670730472013 182019129547751523927005)
          ·
            refine ⟨68257173580406821472627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182019129547751523927005 68257173580406821472627)
            ·
              refine ⟨102385760370610232208941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68257173580406821472627 102385760370610232208941)
              ·
                refine ⟨38394660138978837078353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102385760370610232208941 38394660138978837078353)
                ·
                  refine ⟨28795995104234127808765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38394660138978837078353 28795995104234127808765)
                  ·
                    rfl

theorem cell20_63090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_63090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63090 prefixEnd_63090 := by exact prefixLift 63090
  have htrace : WordTrace (prefixWord ++ tailWord_63090) baseStart_63090 baseEnd_63090 := by
    simpa [prefixWord, tailWord_63090, baseEnd_63090] using wordTrace_append hprefix tailTrace_63090
  have hstable : (prefixWord ++ tailWord_63090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63090).length < 2 ^ (prefixWord ++ tailWord_63090).sum := by decide
  have hdescent : baseEnd_63090 < baseStart_63090 := by decide
  rcases family_descends (prefixWord ++ tailWord_63090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63101 : List Nat := [1, 4, 1, 1, 4, 3, 6]
def baseStart_63101 : Nat := 118140960795 + 63101 * 2 ^ 59
def prefixEnd_63101 : Nat := 4983230072969 + 3 ^ 40 * 63101 * 2
def baseEnd_63101 : Nat := 3200112867107442049117

theorem tailTrace_63101 : CollatzResearch.WordTrace tailWord_63101 prefixEnd_63101 3200112867107442049117 := by
  unfold tailWord_63101
  simp only [CollatzResearch.WordTrace]
  refine ⟨2301482544403328637925157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1534321696268885758616771 2301482544403328637925157)
  ·
    refine ⟨431527977075624119610967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2301482544403328637925157 431527977075624119610967)
    ·
      refine ⟨647291965613436179416451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431527977075624119610967 647291965613436179416451)
      ·
        refine ⟨970937948420154269124677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647291965613436179416451 970937948420154269124677)
        ·
          refine ⟨182050865328778925460877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 970937948420154269124677 182050865328778925460877)
          ·
            refine ⟨68269074498292097047829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182050865328778925460877 68269074498292097047829)
            ·
              refine ⟨3200112867107442049117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68269074498292097047829 3200112867107442049117)
              ·
                rfl

theorem cell20_63101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 6].length) (baseStart_63101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63101 prefixEnd_63101 := by exact prefixLift 63101
  have htrace : WordTrace (prefixWord ++ tailWord_63101) baseStart_63101 baseEnd_63101 := by
    simpa [prefixWord, tailWord_63101, baseEnd_63101] using wordTrace_append hprefix tailTrace_63101
  have hstable : (prefixWord ++ tailWord_63101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63101).length < 2 ^ (prefixWord ++ tailWord_63101).sum := by decide
  have hdescent : baseEnd_63101 < baseStart_63101 := by decide
  rcases family_descends (prefixWord ++ tailWord_63101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63129 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 7]
def baseStart_63129 : Nat := 118140960795 + 63129 * 2 ^ 59
def prefixEnd_63129 : Nat := 4983230072969 + 3 ^ 40 * 63129 * 2
def baseEnd_63129 : Nat := 28813795766923325508605

theorem tailTrace_63129 : CollatzResearch.WordTrace tailWord_63129 prefixEnd_63129 28813795766923325508605 := by
  unfold tailWord_63129
  simp only [CollatzResearch.WordTrace]
  refine ⟨2302503788301889419944441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1535002525534592946629627 2302503788301889419944441)
  ·
    refine ⟨1726877841226417064958331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2302503788301889419944441 1726877841226417064958331)
    ·
      refine ⟨2590316761839625597437497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1726877841226417064958331 2590316761839625597437497)
      ·
        refine ⟨1942737571379719198078123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2590316761839625597437497 1942737571379719198078123)
        ·
          refine ⟨2914106357069578797117185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1942737571379719198078123 2914106357069578797117185)
          ·
            refine ⟨2185579767802184097837889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2914106357069578797117185 2185579767802184097837889)
            ·
              refine ⟨1639184825851638073378417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2185579767802184097837889 1639184825851638073378417)
              ·
                refine ⟨1229388619388728555033813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1639184825851638073378417 1229388619388728555033813)
                ·
                  refine ⟨28813795766923325508605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1229388619388728555033813 28813795766923325508605)
                  ·
                    rfl

theorem cell20_63129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_63129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63129 prefixEnd_63129 := by exact prefixLift 63129
  have htrace : WordTrace (prefixWord ++ tailWord_63129) baseStart_63129 baseEnd_63129 := by
    simpa [prefixWord, tailWord_63129, baseEnd_63129] using wordTrace_append hprefix tailTrace_63129
  have hstable : (prefixWord ++ tailWord_63129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63129).length < 2 ^ (prefixWord ++ tailWord_63129).sum := by decide
  have hdescent : baseEnd_63129 < baseStart_63129 := by decide
  rcases family_descends (prefixWord ++ tailWord_63129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63149 : List Nat := [1, 5, 2, 1, 1, 1, 2, 5, 2]
def baseStart_63149 : Nat := 118140960795 + 63149 * 2 ^ 59
def prefixEnd_63149 : Nat := 4983230072969 + 3 ^ 40 * 63149 * 2
def baseEnd_63149 : Nat := 28822924311892144841857

theorem tailTrace_63149 : CollatzResearch.WordTrace tailWord_63149 prefixEnd_63149 28822924311892144841857 := by
  unfold tailWord_63149
  simp only [CollatzResearch.WordTrace]
  refine ⟨2303233248229432835672501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1535488832152955223781667 2303233248229432835672501)
  ·
    refine ⟨215928117021509328344297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2303233248229432835672501 215928117021509328344297)
    ·
      refine ⟨161946087766131996258223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215928117021509328344297 161946087766131996258223)
      ·
        refine ⟨242919131649197994387335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161946087766131996258223 242919131649197994387335)
        ·
          refine ⟨364378697473796991581003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242919131649197994387335 364378697473796991581003)
          ·
            refine ⟨546568046210695487371505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364378697473796991581003 546568046210695487371505)
            ·
              refine ⟨409926034658021615528629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546568046210695487371505 409926034658021615528629)
              ·
                refine ⟨38430565749189526455809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 409926034658021615528629 38430565749189526455809)
                ·
                  refine ⟨28822924311892144841857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38430565749189526455809 28822924311892144841857)
                  ·
                    rfl

theorem cell20_63149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_63149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63149 prefixEnd_63149 := by exact prefixLift 63149
  have htrace : WordTrace (prefixWord ++ tailWord_63149) baseStart_63149 baseEnd_63149 := by
    simpa [prefixWord, tailWord_63149, baseEnd_63149] using wordTrace_append hprefix tailTrace_63149
  have hstable : (prefixWord ++ tailWord_63149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63149).length < 2 ^ (prefixWord ++ tailWord_63149).sum := by decide
  have hdescent : baseEnd_63149 < baseStart_63149 := by decide
  rcases family_descends (prefixWord ++ tailWord_63149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63166 : List Nat := [4, 2, 1, 1, 2, 2, 4, 2, 2]
def baseStart_63166 : Nat := 118140960795 + 63166 * 2 ^ 59
def prefixEnd_63166 : Nat := 4983230072969 + 3 ^ 40 * 63166 * 2
def baseEnd_63166 : Nat := 28830683575115641275121

theorem tailTrace_63166 : CollatzResearch.WordTrace tailWord_63166 prefixEnd_63166 28830683575115641275121 := by
  unfold tailWord_63166
  simp only [CollatzResearch.WordTrace]
  refine ⟨287981661145980592380169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1535902192778563159360901 287981661145980592380169)
  ·
    refine ⟨215986245859485444285127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287981661145980592380169 215986245859485444285127)
    ·
      refine ⟨323979368789228166427691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215986245859485444285127 323979368789228166427691)
      ·
        refine ⟨485969053183842249641537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323979368789228166427691 485969053183842249641537)
        ·
          refine ⟨364476789887881687231153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485969053183842249641537 364476789887881687231153)
          ·
            refine ⟨273357592415911265423365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364476789887881687231153 273357592415911265423365)
            ·
              refine ⟨51254548577983362266881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273357592415911265423365 51254548577983362266881)
              ·
                refine ⟨38440911433487521700161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51254548577983362266881 38440911433487521700161)
                ·
                  refine ⟨28830683575115641275121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38440911433487521700161 28830683575115641275121)
                  ·
                    rfl

theorem cell20_63166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_63166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63166 prefixEnd_63166 := by exact prefixLift 63166
  have htrace : WordTrace (prefixWord ++ tailWord_63166) baseStart_63166 baseEnd_63166 := by
    simpa [prefixWord, tailWord_63166, baseEnd_63166] using wordTrace_append hprefix tailTrace_63166
  have hstable : (prefixWord ++ tailWord_63166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63166).length < 2 ^ (prefixWord ++ tailWord_63166).sum := by decide
  have hdescent : baseEnd_63166 < baseStart_63166 := by decide
  rcases family_descends (prefixWord ++ tailWord_63166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63190 : List Nat := [5, 2, 1, 3, 1, 1, 3, 4]
def baseStart_63190 : Nat := 118140960795 + 63190 * 2 ^ 59
def prefixEnd_63190 : Nat := 4983230072969 + 3 ^ 40 * 63190 * 2
def baseEnd_63190 : Nat := 9613879276359408158341

theorem tailTrace_63190 : CollatzResearch.WordTrace tailWord_63190 prefixEnd_63190 9613879276359408158341 := by
  unfold tailWord_63190
  simp only [CollatzResearch.WordTrace]
  refine ⟨144045540067556052369689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1536485760720597891943349 144045540067556052369689)
  ·
    refine ⟨108034155050667039277267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144045540067556052369689 108034155050667039277267)
    ·
      refine ⟨162051232576000558915901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108034155050667039277267 162051232576000558915901)
      ·
        refine ⟨60769212216000209593463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162051232576000558915901 60769212216000209593463)
        ·
          refine ⟨91153818324000314390195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60769212216000209593463 91153818324000314390195)
          ·
            refine ⟨136730727486000471585293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91153818324000314390195 136730727486000471585293)
            ·
              refine ⟨51274022807250176844485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136730727486000471585293 51274022807250176844485)
              ·
                refine ⟨9613879276359408158341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51274022807250176844485 9613879276359408158341)
                ·
                  rfl

theorem cell20_63190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_63190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63190 prefixEnd_63190 := by exact prefixLift 63190
  have htrace : WordTrace (prefixWord ++ tailWord_63190) baseStart_63190 baseEnd_63190 := by
    simpa [prefixWord, tailWord_63190, baseEnd_63190] using wordTrace_append hprefix tailTrace_63190
  have hstable : (prefixWord ++ tailWord_63190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63190).length < 2 ^ (prefixWord ++ tailWord_63190).sum := by decide
  have hdescent : baseEnd_63190 < baseStart_63190 := by decide
  rcases family_descends (prefixWord ++ tailWord_63190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63191 : List Nat := [1, 1, 3, 2, 1, 3, 3, 2, 4]
def baseStart_63191 : Nat := 118140960795 + 63191 * 2 ^ 59
def prefixEnd_63191 : Nat := 4983230072969 + 3 ^ 40 * 63191 * 2
def baseEnd_63191 : Nat := 28842094256326665441685

theorem tailTrace_63191 : CollatzResearch.WordTrace tailWord_63191 prefixEnd_63191 28842094256326665441685 := by
  unfold tailWord_63191
  simp only [CollatzResearch.WordTrace]
  refine ⟨2304765114077274008701427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1536510076051516005800951 2304765114077274008701427)
  ·
    refine ⟨3457147671115911013052141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2304765114077274008701427 3457147671115911013052141)
    ·
      refine ⟨1296430376668466629894553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3457147671115911013052141 1296430376668466629894553)
      ·
        refine ⟨972322782501349972420915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1296430376668466629894553 972322782501349972420915)
        ·
          refine ⟨1458484173752024958631373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972322782501349972420915 1458484173752024958631373)
          ·
            refine ⟨546931565157009359486765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1458484173752024958631373 546931565157009359486765)
            ·
              refine ⟨205099336933878509807537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 546931565157009359486765 205099336933878509807537)
              ·
                refine ⟨153824502700408882355653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205099336933878509807537 153824502700408882355653)
                ·
                  refine ⟨28842094256326665441685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153824502700408882355653 28842094256326665441685)
                  ·
                    rfl

theorem cell20_63191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_63191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63191 prefixEnd_63191 := by exact prefixLift 63191
  have htrace : WordTrace (prefixWord ++ tailWord_63191) baseStart_63191 baseEnd_63191 := by
    simpa [prefixWord, tailWord_63191, baseEnd_63191] using wordTrace_append hprefix tailTrace_63191
  have hstable : (prefixWord ++ tailWord_63191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63191).length < 2 ^ (prefixWord ++ tailWord_63191).sum := by decide
  have hdescent : baseEnd_63191 < baseStart_63191 := by decide
  rcases family_descends (prefixWord ++ tailWord_63191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63253 : List Nat := [1, 3, 2, 1, 2, 3, 4, 4]
def baseStart_63253 : Nat := 118140960795 + 63253 * 2 ^ 59
def prefixEnd_63253 : Nat := 4983230072969 + 3 ^ 40 * 63253 * 2
def baseEnd_63253 : Nat := 9623464248576668458255

theorem tailTrace_63253 : CollatzResearch.WordTrace tailWord_63253 prefixEnd_63253 9623464248576668458255 := by
  unfold tailWord_63253
  simp only [CollatzResearch.WordTrace]
  refine ⟨2307026439852658597458413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1538017626568439064972275 2307026439852658597458413)
  ·
    refine ⟨865134914944746974046905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2307026439852658597458413 865134914944746974046905)
    ·
      refine ⟨648851186208560230535179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 865134914944746974046905 648851186208560230535179)
      ·
        refine ⟨973276779312840345802769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648851186208560230535179 973276779312840345802769)
        ·
          refine ⟨729957584484630259352077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 973276779312840345802769 729957584484630259352077)
          ·
            refine ⟨273734094181736347257029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 729957584484630259352077 273734094181736347257029)
            ·
              refine ⟨51325142659075565110693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273734094181736347257029 51325142659075565110693)
              ·
                refine ⟨9623464248576668458255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51325142659075565110693 9623464248576668458255)
                ·
                  rfl

theorem cell20_63253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 4].length) (baseStart_63253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63253 prefixEnd_63253 := by exact prefixLift 63253
  have htrace : WordTrace (prefixWord ++ tailWord_63253) baseStart_63253 baseEnd_63253 := by
    simpa [prefixWord, tailWord_63253, baseEnd_63253] using wordTrace_append hprefix tailTrace_63253
  have hstable : (prefixWord ++ tailWord_63253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63253).length < 2 ^ (prefixWord ++ tailWord_63253).sum := by decide
  have hdescent : baseEnd_63253 < baseStart_63253 := by decide
  rcases family_descends (prefixWord ++ tailWord_63253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63294 : List Nat := [4, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_63294 : Nat := 118140960795 + 63294 * 2 ^ 59
def prefixEnd_63294 : Nat := 4983230072969 + 3 ^ 40 * 63294 * 2
def baseEnd_63294 : Nat := 28889106262916085007931

theorem tailTrace_63294 : CollatzResearch.WordTrace tailWord_63294 prefixEnd_63294 28889106262916085007931 := by
  unfold tailWord_63294
  simp only [CollatzResearch.WordTrace]
  refine ⟨288565229088015324962617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1539014555136081733133957 288565229088015324962617)
  ·
    refine ⟨216423921816011493721963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288565229088015324962617 216423921816011493721963)
    ·
      refine ⟨324635882724017240582945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216423921816011493721963 324635882724017240582945)
      ·
        refine ⟨243476912043012930437209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324635882724017240582945 243476912043012930437209)
        ·
          refine ⟨182607684032259697827907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243476912043012930437209 182607684032259697827907)
          ·
            refine ⟨273911526048389546741861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182607684032259697827907 273911526048389546741861)
            ·
              refine ⟨51358411134073040014099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273911526048389546741861 51358411134073040014099)
              ·
                refine ⟨77037616701109560021149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51358411134073040014099 77037616701109560021149)
                ·
                  refine ⟨28889106262916085007931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77037616701109560021149 28889106262916085007931)
                  ·
                    rfl

theorem cell20_63294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_63294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63294 prefixEnd_63294 := by exact prefixLift 63294
  have htrace : WordTrace (prefixWord ++ tailWord_63294) baseStart_63294 baseEnd_63294 := by
    simpa [prefixWord, tailWord_63294, baseEnd_63294] using wordTrace_append hprefix tailTrace_63294
  have hstable : (prefixWord ++ tailWord_63294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63294).length < 2 ^ (prefixWord ++ tailWord_63294).sum := by decide
  have hdescent : baseEnd_63294 < baseStart_63294 := by decide
  rcases family_descends (prefixWord ++ tailWord_63294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63322 : List Nat := [3, 1, 1, 2, 1, 3, 2, 5, 2]
def baseStart_63322 : Nat := 118140960795 + 63322 * 2 ^ 59
def prefixEnd_63322 : Nat := 4983230072969 + 3 ^ 40 * 63322 * 2
def baseEnd_63322 : Nat := 28901886225872432074483

theorem tailTrace_63322 : CollatzResearch.WordTrace tailWord_63322 prefixEnd_63322 28901886225872432074483 := by
  unfold tailWord_63322
  simp only [CollatzResearch.WordTrace]
  refine ⟨577385769150670845430055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1539695384401788921146813 577385769150670845430055)
  ·
    refine ⟨866078653726006268145083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 577385769150670845430055 866078653726006268145083)
    ·
      refine ⟨1299117980589009402217625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 866078653726006268145083 1299117980589009402217625)
      ·
        refine ⟨974338485441757051663219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1299117980589009402217625 974338485441757051663219)
        ·
          refine ⟨1461507728162635577494829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974338485441757051663219 1461507728162635577494829)
          ·
            refine ⟨548065398060988341560561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1461507728162635577494829 548065398060988341560561)
            ·
              refine ⟨411049048545741256170421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548065398060988341560561 411049048545741256170421)
              ·
                refine ⟨38535848301163242765977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 411049048545741256170421 38535848301163242765977)
                ·
                  refine ⟨28901886225872432074483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38535848301163242765977 28901886225872432074483)
                  ·
                    rfl

theorem cell20_63322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_63322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63322 prefixEnd_63322 := by exact prefixLift 63322
  have htrace : WordTrace (prefixWord ++ tailWord_63322) baseStart_63322 baseEnd_63322 := by
    simpa [prefixWord, tailWord_63322, baseEnd_63322] using wordTrace_append hprefix tailTrace_63322
  have hstable : (prefixWord ++ tailWord_63322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63322).length < 2 ^ (prefixWord ++ tailWord_63322).sum := by decide
  have hdescent : baseEnd_63322 < baseStart_63322 := by decide
  rcases family_descends (prefixWord ++ tailWord_63322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63357 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 7]
def baseStart_63357 : Nat := 118140960795 + 63357 * 2 ^ 59
def prefixEnd_63357 : Nat := 4983230072969 + 3 ^ 40 * 63357 * 2
def baseEnd_63357 : Nat := 28917861179567865907673

theorem tailTrace_63357 : CollatzResearch.WordTrace tailWord_63357 prefixEnd_63357 28917861179567865907673 := by
  unfold tailWord_63357
  simp only [CollatzResearch.WordTrace]
  refine ⟨2310819631475884359244325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1540546420983922906162883 2310819631475884359244325)
  ·
    refine ⟨433278680901728317358311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2310819631475884359244325 433278680901728317358311)
    ·
      refine ⟨649918021352592476037467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433278680901728317358311 649918021352592476037467)
      ·
        refine ⟨974877032028888714056201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649918021352592476037467 974877032028888714056201)
        ·
          refine ⟨731157774021666535542151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 974877032028888714056201 731157774021666535542151)
          ·
            refine ⟨1096736661032499803313227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731157774021666535542151 1096736661032499803313227)
            ·
              refine ⟨1645104991548749704969841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096736661032499803313227 1645104991548749704969841)
              ·
                refine ⟨1233828743661562278727381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1645104991548749704969841 1233828743661562278727381)
                ·
                  refine ⟨28917861179567865907673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1233828743661562278727381 28917861179567865907673)
                  ·
                    rfl

theorem cell20_63357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_63357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63357 prefixEnd_63357 := by exact prefixLift 63357
  have htrace : WordTrace (prefixWord ++ tailWord_63357) baseStart_63357 baseEnd_63357 := by
    simpa [prefixWord, tailWord_63357, baseEnd_63357] using wordTrace_append hprefix tailTrace_63357
  have hstable : (prefixWord ++ tailWord_63357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63357).length < 2 ^ (prefixWord ++ tailWord_63357).sum := by decide
  have hdescent : baseEnd_63357 < baseStart_63357 := by decide
  rcases family_descends (prefixWord ++ tailWord_63357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63422 : List Nat := [4, 2, 1, 1, 1, 5, 2, 4]
def baseStart_63422 : Nat := 118140960795 + 63422 * 2 ^ 59
def prefixEnd_63422 : Nat := 4983230072969 + 3 ^ 40 * 63422 * 2
def baseEnd_63422 : Nat := 9649176316905509580247

theorem tailTrace_63422 : CollatzResearch.WordTrace tailWord_63422 prefixEnd_63422 9649176316905509580247 := by
  unfold tailWord_63422
  simp only [CollatzResearch.WordTrace]
  refine ⟨289148797030050057545065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1542126917493600306907013 289148797030050057545065)
  ·
    refine ⟨216861597772537543158799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289148797030050057545065 216861597772537543158799)
    ·
      refine ⟨325292396658806314738199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216861597772537543158799 325292396658806314738199)
      ·
        refine ⟨487938594988209472107299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325292396658806314738199 487938594988209472107299)
        ·
          refine ⟨731907892482314208160949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487938594988209472107299 731907892482314208160949)
          ·
            refine ⟨68616364920216957015089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 731907892482314208160949 68616364920216957015089)
            ·
              refine ⟨51462273690162717761317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68616364920216957015089 51462273690162717761317)
              ·
                refine ⟨9649176316905509580247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51462273690162717761317 9649176316905509580247)
                ·
                  rfl

theorem cell20_63422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_63422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63422 prefixEnd_63422 := by exact prefixLift 63422
  have htrace : WordTrace (prefixWord ++ tailWord_63422) baseStart_63422 baseEnd_63422 := by
    simpa [prefixWord, tailWord_63422, baseEnd_63422] using wordTrace_append hprefix tailTrace_63422
  have hstable : (prefixWord ++ tailWord_63422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63422).length < 2 ^ (prefixWord ++ tailWord_63422).sum := by decide
  have hdescent : baseEnd_63422 < baseStart_63422 := by decide
  rcases family_descends (prefixWord ++ tailWord_63422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63440 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 6]
def baseStart_63440 : Nat := 118140960795 + 63440 * 2 ^ 59
def prefixEnd_63440 : Nat := 4983230072969 + 3 ^ 40 * 63440 * 2
def baseEnd_63440 : Nat := 28955744641188466140667

theorem tailTrace_63440 : CollatzResearch.WordTrace tailWord_63440 prefixEnd_63440 28955744641188466140667 := by
  unfold tailWord_63440
  simp only [CollatzResearch.WordTrace]
  refine ⟨1156923445087594767257887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1542564593450126356343849 1156923445087594767257887)
  ·
    refine ⟨1735385167631392150886831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1156923445087594767257887 1735385167631392150886831)
    ·
      refine ⟨2603077751447088226330247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1735385167631392150886831 2603077751447088226330247)
      ·
        refine ⟨3904616627170632339495371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2603077751447088226330247 3904616627170632339495371)
        ·
          refine ⟨5856924940755948509243057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3904616627170632339495371 5856924940755948509243057)
          ·
            refine ⟨4392693705566961381932293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5856924940755948509243057 4392693705566961381932293)
            ·
              refine ⟨823630069793805259112305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4392693705566961381932293 823630069793805259112305)
              ·
                refine ⟨617722552345353944334229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 823630069793805259112305 617722552345353944334229)
                ·
                  refine ⟨28955744641188466140667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 617722552345353944334229 28955744641188466140667)
                  ·
                    rfl

theorem cell20_63440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_63440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63440 prefixEnd_63440 := by exact prefixLift 63440
  have htrace : WordTrace (prefixWord ++ tailWord_63440) baseStart_63440 baseEnd_63440 := by
    simpa [prefixWord, tailWord_63440, baseEnd_63440] using wordTrace_append hprefix tailTrace_63440
  have hstable : (prefixWord ++ tailWord_63440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63440).length < 2 ^ (prefixWord ++ tailWord_63440).sum := by decide
  have hdescent : baseEnd_63440 < baseStart_63440 := by decide
  rcases family_descends (prefixWord ++ tailWord_63440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63453 : List Nat := [1, 4, 3, 1, 3, 2, 1, 1, 4]
def baseStart_63453 : Nat := 118140960795 + 63453 * 2 ^ 59
def prefixEnd_63453 : Nat := 4983230072969 + 3 ^ 40 * 63453 * 2
def baseEnd_63453 : Nat := 28961678195418198707281

theorem tailTrace_63453 : CollatzResearch.WordTrace tailWord_63453 prefixEnd_63453 28961678195418198707281 := by
  unfold tailWord_63453
  simp only [CollatzResearch.WordTrace]
  refine ⟨2314321039128092754739013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1542880692752061836492675 2314321039128092754739013)
  ·
    refine ⟨433935194836517391513565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2314321039128092754739013 433935194836517391513565)
    ·
      refine ⟨162725698063694021817587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433935194836517391513565 162725698063694021817587)
      ·
        refine ⟨244088547095541032726381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162725698063694021817587 244088547095541032726381)
        ·
          refine ⟨91533205160827887272393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244088547095541032726381 91533205160827887272393)
          ·
            refine ⟨68649903870620915454295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91533205160827887272393 68649903870620915454295)
            ·
              refine ⟨102974855805931373181443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68649903870620915454295 102974855805931373181443)
              ·
                refine ⟨154462283708897059772165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102974855805931373181443 154462283708897059772165)
                ·
                  refine ⟨28961678195418198707281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154462283708897059772165 28961678195418198707281)
                  ·
                    rfl

theorem cell20_63453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_63453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63453 prefixEnd_63453 := by exact prefixLift 63453
  have htrace : WordTrace (prefixWord ++ tailWord_63453) baseStart_63453 baseEnd_63453 := by
    simpa [prefixWord, tailWord_63453, baseEnd_63453] using wordTrace_append hprefix tailTrace_63453
  have hstable : (prefixWord ++ tailWord_63453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63453).length < 2 ^ (prefixWord ++ tailWord_63453).sum := by decide
  have hdescent : baseEnd_63453 < baseStart_63453 := by decide
  rcases family_descends (prefixWord ++ tailWord_63453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63457 : List Nat := [1, 2, 3, 1, 2, 1, 5, 1, 4]
def baseStart_63457 : Nat := 118140960795 + 63457 * 2 ^ 59
def prefixEnd_63457 : Nat := 4983230072969 + 3 ^ 40 * 63457 * 2
def baseEnd_63457 : Nat := 28963503904411962573931

theorem tailTrace_63457 : CollatzResearch.WordTrace tailWord_63457 prefixEnd_63457 28963503904411962573931 := by
  unfold tailWord_63457
  simp only [CollatzResearch.WordTrace]
  refine ⟨2314466931113601437884625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1542977954075734291923083 2314466931113601437884625)
  ·
    refine ⟨1735850198335201078413469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2314466931113601437884625 1735850198335201078413469)
    ·
      refine ⟨650943824375700404405051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1735850198335201078413469 650943824375700404405051)
      ·
        refine ⟨976415736563550606607577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650943824375700404405051 976415736563550606607577)
        ·
          refine ⟨732311802422662954955683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 976415736563550606607577 732311802422662954955683)
          ·
            refine ⟨1098467703633994432433525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732311802422662954955683 1098467703633994432433525)
            ·
              refine ⟨102981347215686978040643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1098467703633994432433525 102981347215686978040643)
              ·
                refine ⟨154472020823530467060965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102981347215686978040643 154472020823530467060965)
                ·
                  refine ⟨28963503904411962573931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154472020823530467060965 28963503904411962573931)
                  ·
                    rfl

theorem cell20_63457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_63457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63457 prefixEnd_63457 := by exact prefixLift 63457
  have htrace : WordTrace (prefixWord ++ tailWord_63457) baseStart_63457 baseEnd_63457 := by
    simpa [prefixWord, tailWord_63457, baseEnd_63457] using wordTrace_append hprefix tailTrace_63457
  have hstable : (prefixWord ++ tailWord_63457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63457).length < 2 ^ (prefixWord ++ tailWord_63457).sum := by decide
  have hdescent : baseEnd_63457 < baseStart_63457 := by decide
  rcases family_descends (prefixWord ++ tailWord_63457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63463 : List Nat := [1, 1, 5, 2, 4, 1, 2, 1, 3]
def baseStart_63463 : Nat := 118140960795 + 63463 * 2 ^ 59
def prefixEnd_63463 : Nat := 4983230072969 + 3 ^ 40 * 63463 * 2
def baseEnd_63463 : Nat := 28966242467902608373907

theorem tailTrace_63463 : CollatzResearch.WordTrace tailWord_63463 prefixEnd_63463 28966242467902608373907 := by
  unfold tailWord_63463
  simp only [CollatzResearch.WordTrace]
  refine ⟨2314685769091864462603043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1543123846061242975068695 2314685769091864462603043)
  ·
    refine ⟨3472028653637796693904565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2314685769091864462603043 3472028653637796693904565)
    ·
      refine ⟨325502686278543440053553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3472028653637796693904565 325502686278543440053553)
      ·
        refine ⟨244127014708907580040165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325502686278543440053553 244127014708907580040165)
        ·
          refine ⟨45773815257920171257531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244127014708907580040165 45773815257920171257531)
          ·
            refine ⟨68660722886880256886297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45773815257920171257531 68660722886880256886297)
            ·
              refine ⟨51495542165160192664723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68660722886880256886297 51495542165160192664723)
              ·
                refine ⟨77243313247740288997085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51495542165160192664723 77243313247740288997085)
                ·
                  refine ⟨28966242467902608373907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77243313247740288997085 28966242467902608373907)
                  ·
                    rfl

theorem cell20_63463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 3].length) (baseStart_63463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63463 prefixEnd_63463 := by exact prefixLift 63463
  have htrace : WordTrace (prefixWord ++ tailWord_63463) baseStart_63463 baseEnd_63463 := by
    simpa [prefixWord, tailWord_63463, baseEnd_63463] using wordTrace_append hprefix tailTrace_63463
  have hstable : (prefixWord ++ tailWord_63463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63463).length < 2 ^ (prefixWord ++ tailWord_63463).sum := by decide
  have hdescent : baseEnd_63463 < baseStart_63463 := by decide
  rcases family_descends (prefixWord ++ tailWord_63463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63494 : List Nat := [6, 2, 1, 2, 2, 7]
def baseStart_63494 : Nat := 118140960795 + 63494 * 2 ^ 59
def prefixEnd_63494 : Nat := 4983230072969 + 3 ^ 40 * 63494 * 2
def baseEnd_63494 : Nat := 1073347841207565864461

theorem tailTrace_63494 : CollatzResearch.WordTrace tailWord_63494 prefixEnd_63494 1073347841207565864461 := by
  unfold tailWord_63494
  simp only [CollatzResearch.WordTrace]
  refine ⟨72369263499361148655673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1543877621319704504654357 72369263499361148655673)
  ·
    refine ⟨54276947624520861491755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72369263499361148655673 54276947624520861491755)
    ·
      refine ⟨81415421436781292237633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54276947624520861491755 81415421436781292237633)
      ·
        refine ⟨61061566077585969178225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81415421436781292237633 61061566077585969178225)
        ·
          refine ⟨45796174558189476883669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61061566077585969178225 45796174558189476883669)
          ·
            refine ⟨1073347841207565864461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 45796174558189476883669 1073347841207565864461)
            ·
              rfl

theorem cell20_63494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 7].length) (baseStart_63494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63494 prefixEnd_63494 := by exact prefixLift 63494
  have htrace : WordTrace (prefixWord ++ tailWord_63494) baseStart_63494 baseEnd_63494 := by
    simpa [prefixWord, tailWord_63494, baseEnd_63494] using wordTrace_append hprefix tailTrace_63494
  have hstable : (prefixWord ++ tailWord_63494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63494).length < 2 ^ (prefixWord ++ tailWord_63494).sum := by decide
  have hdescent : baseEnd_63494 < baseStart_63494 := by decide
  rcases family_descends (prefixWord ++ tailWord_63494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63512 : List Nat := [2, 1, 2, 3, 2, 1, 3, 4, 2]
def baseStart_63512 : Nat := 118140960795 + 63512 * 2 ^ 59
def prefixEnd_63512 : Nat := 4983230072969 + 3 ^ 40 * 63512 * 2
def baseEnd_63512 : Nat := 28988607403076215740373

theorem tailTrace_63512 : CollatzResearch.WordTrace tailWord_63512 prefixEnd_63512 28988607403076215740373 := by
  unfold tailWord_63512
  simp only [CollatzResearch.WordTrace]
  refine ⟨1158236472957172915568395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1544315297276230554091193 1158236472957172915568395)
  ·
    refine ⟨1737354709435759373352593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1158236472957172915568395 1737354709435759373352593)
    ·
      refine ⟨1303016032076819530014445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1737354709435759373352593 1303016032076819530014445)
      ·
        refine ⟨488631012028807323755417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1303016032076819530014445 488631012028807323755417)
        ·
          refine ⟨366473259021605492816563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488631012028807323755417 366473259021605492816563)
          ·
            refine ⟨549709888532408239224845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366473259021605492816563 549709888532408239224845)
            ·
              refine ⟨206141208199653089709317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 549709888532408239224845 206141208199653089709317)
              ·
                refine ⟨38651476537434954320497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206141208199653089709317 38651476537434954320497)
                ·
                  refine ⟨28988607403076215740373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38651476537434954320497 28988607403076215740373)
                  ·
                    rfl

theorem cell20_63512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 2].length) (baseStart_63512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63512 prefixEnd_63512 := by exact prefixLift 63512
  have htrace : WordTrace (prefixWord ++ tailWord_63512) baseStart_63512 baseEnd_63512 := by
    simpa [prefixWord, tailWord_63512, baseEnd_63512] using wordTrace_append hprefix tailTrace_63512
  have hstable : (prefixWord ++ tailWord_63512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63512).length < 2 ^ (prefixWord ++ tailWord_63512).sum := by decide
  have hdescent : baseEnd_63512 < baseStart_63512 := by decide
  rcases family_descends (prefixWord ++ tailWord_63512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63561 : List Nat := [1, 2, 1, 1, 2, 2, 11]
def baseStart_63561 : Nat := 118140960795 + 63561 * 2 ^ 59
def prefixEnd_63561 : Nat := 4983230072969 + 3 ^ 40 * 63561 * 2
def baseEnd_63561 : Nat := 3223441370916647011871

theorem tailTrace_63561 : CollatzResearch.WordTrace tailWord_63561 prefixEnd_63561 3223441370916647011871 := by
  unfold tailWord_63561
  simp only [CollatzResearch.WordTrace]
  refine ⟨2318260122736827199670537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1545506748491218133113691 2318260122736827199670537)
  ·
    refine ⟨1738695092052620399752903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2318260122736827199670537 1738695092052620399752903)
    ·
      refine ⟨2608042638078930599629355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1738695092052620399752903 2608042638078930599629355)
      ·
        refine ⟨3912063957118395899444033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2608042638078930599629355 3912063957118395899444033)
        ·
          refine ⟨2934047967838796924583025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3912063957118395899444033 2934047967838796924583025)
          ·
            refine ⟨2200535975879097693437269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2934047967838796924583025 2200535975879097693437269)
            ·
              refine ⟨3223441370916647011871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2200535975879097693437269 3223441370916647011871)
              ·
                rfl

theorem cell20_63561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 11].length) (baseStart_63561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63561 prefixEnd_63561 := by exact prefixLift 63561
  have htrace : WordTrace (prefixWord ++ tailWord_63561) baseStart_63561 baseEnd_63561 := by
    simpa [prefixWord, tailWord_63561, baseEnd_63561] using wordTrace_append hprefix tailTrace_63561
  have hstable : (prefixWord ++ tailWord_63561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63561).length < 2 ^ (prefixWord ++ tailWord_63561).sum := by decide
  have hdescent : baseEnd_63561 < baseStart_63561 := by decide
  rcases family_descends (prefixWord ++ tailWord_63561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63564 : List Nat := [2, 2, 1, 3, 1, 1, 5, 2, 3]
def baseStart_63564 : Nat := 118140960795 + 63564 * 2 ^ 59
def prefixEnd_63564 : Nat := 4983230072969 + 3 ^ 40 * 63564 * 2
def baseEnd_63564 : Nat := 29012341619995146006827

theorem tailTrace_63564 : CollatzResearch.WordTrace tailWord_63564 prefixEnd_63564 29012341619995146006827 := by
  unfold tailWord_63564
  simp only [CollatzResearch.WordTrace]
  refine ⟨1159184770862979356014873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1545579694483972474686497 1159184770862979356014873)
  ·
    refine ⟨869388578147234517011155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1159184770862979356014873 869388578147234517011155)
    ·
      refine ⟨1304082867220851775516733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 869388578147234517011155 1304082867220851775516733)
      ·
        refine ⟨489031075207819415818775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1304082867220851775516733 489031075207819415818775)
        ·
          refine ⟨733546612811729123728163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489031075207819415818775 733546612811729123728163)
          ·
            refine ⟨1100319919217593685592245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733546612811729123728163 1100319919217593685592245)
            ·
              refine ⟨103154992426649408024273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1100319919217593685592245 103154992426649408024273)
              ·
                refine ⟨77366244319987056018205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103154992426649408024273 77366244319987056018205)
                ·
                  refine ⟨29012341619995146006827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77366244319987056018205 29012341619995146006827)
                  ·
                    rfl

theorem cell20_63564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_63564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63564 prefixEnd_63564 := by exact prefixLift 63564
  have htrace : WordTrace (prefixWord ++ tailWord_63564) baseStart_63564 baseEnd_63564 := by
    simpa [prefixWord, tailWord_63564, baseEnd_63564] using wordTrace_append hprefix tailTrace_63564
  have hstable : (prefixWord ++ tailWord_63564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63564).length < 2 ^ (prefixWord ++ tailWord_63564).sum := by decide
  have hdescent : baseEnd_63564 < baseStart_63564 := by decide
  rcases family_descends (prefixWord ++ tailWord_63564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63623 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 5]
def baseStart_63623 : Nat := 118140960795 + 63623 * 2 ^ 59
def prefixEnd_63623 : Nat := 4983230072969 + 3 ^ 40 * 63623 * 2
def baseEnd_63623 : Nat := 29039270827653163039919

theorem tailTrace_63623 : CollatzResearch.WordTrace tailWord_63623 prefixEnd_63623 29039270827653163039919 := by
  unfold tailWord_63623
  simp only [CollatzResearch.WordTrace]
  refine ⟨2320521448512211788427523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1547014299008141192285015 2320521448512211788427523)
  ·
    refine ⟨3480782172768317682641285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2320521448512211788427523 3480782172768317682641285)
    ·
      refine ⟨652646657394059565495241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3480782172768317682641285 652646657394059565495241)
      ·
        refine ⟨489484993045544674121431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 652646657394059565495241 489484993045544674121431)
        ·
          refine ⟨734227489568317011182147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489484993045544674121431 734227489568317011182147)
          ·
            refine ⟨1101341234352475516773221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734227489568317011182147 1101341234352475516773221)
            ·
              refine ⟨206501481441089159394979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1101341234352475516773221 206501481441089159394979)
              ·
                refine ⟨309752222161633739092469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206501481441089159394979 309752222161633739092469)
                ·
                  refine ⟨29039270827653163039919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 309752222161633739092469 29039270827653163039919)
                  ·
                    rfl

theorem cell20_63623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_63623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63623 prefixEnd_63623 := by exact prefixLift 63623
  have htrace : WordTrace (prefixWord ++ tailWord_63623) baseStart_63623 baseEnd_63623 := by
    simpa [prefixWord, tailWord_63623, baseEnd_63623] using wordTrace_append hprefix tailTrace_63623
  have hstable : (prefixWord ++ tailWord_63623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63623).length < 2 ^ (prefixWord ++ tailWord_63623).sum := by decide
  have hdescent : baseEnd_63623 < baseStart_63623 := by decide
  rcases family_descends (prefixWord ++ tailWord_63623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63626 : List Nat := [3, 1, 2, 3, 1, 4, 1, 1, 4]
def baseStart_63626 : Nat := 118140960795 + 63626 * 2 ^ 59
def prefixEnd_63626 : Nat := 4983230072969 + 3 ^ 40 * 63626 * 2
def baseEnd_63626 : Nat := 29040640109398485939907

theorem tailTrace_63626 : CollatzResearch.WordTrace tailWord_63626 prefixEnd_63626 29040640109398485939907 := by
  unfold tailWord_63626
  simp only [CollatzResearch.WordTrace]
  refine ⟨580157716875335825196683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1547087245000895533857821 580157716875335825196683)
  ·
    refine ⟨870236575313003737795025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 580157716875335825196683 870236575313003737795025)
    ·
      refine ⟨652677431484752803346269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 870236575313003737795025 652677431484752803346269)
      ·
        refine ⟨244754036806782301254851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 652677431484752803346269 244754036806782301254851)
        ·
          refine ⟨367131055210173451882277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244754036806782301254851 367131055210173451882277)
          ·
            refine ⟨68837072851907522227927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367131055210173451882277 68837072851907522227927)
            ·
              refine ⟨103255609277861283341891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68837072851907522227927 103255609277861283341891)
              ·
                refine ⟨154883413916791925012837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103255609277861283341891 154883413916791925012837)
                ·
                  refine ⟨29040640109398485939907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154883413916791925012837 29040640109398485939907)
                  ·
                    rfl

theorem cell20_63626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_63626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63626 prefixEnd_63626 := by exact prefixLift 63626
  have htrace : WordTrace (prefixWord ++ tailWord_63626) baseStart_63626 baseEnd_63626 := by
    simpa [prefixWord, tailWord_63626, baseEnd_63626] using wordTrace_append hprefix tailTrace_63626
  have hstable : (prefixWord ++ tailWord_63626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63626).length < 2 ^ (prefixWord ++ tailWord_63626).sum := by decide
  have hdescent : baseEnd_63626 < baseStart_63626 := by decide
  rcases family_descends (prefixWord ++ tailWord_63626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63636 : List Nat := [2, 4, 2, 3, 1, 1, 1, 3, 3]
def baseStart_63636 : Nat := 118140960795 + 63636 * 2 ^ 59
def prefixEnd_63636 : Nat := 4983230072969 + 3 ^ 40 * 63636 * 2
def baseEnd_63636 : Nat := 29045204381882895606533

theorem tailTrace_63636 : CollatzResearch.WordTrace tailWord_63636 prefixEnd_63636 29045204381882895606533 := by
  unfold tailWord_63636
  simp only [CollatzResearch.WordTrace]
  refine ⟨1160497798732557504325381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1547330398310076672433841 1160497798732557504325381)
  ·
    refine ⟨217593337262354532061009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1160497798732557504325381 217593337262354532061009)
    ·
      refine ⟨163195002946765899045757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217593337262354532061009 163195002946765899045757)
      ·
        refine ⟨61198126105037212142159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163195002946765899045757 61198126105037212142159)
        ·
          refine ⟨91797189157555818213239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61198126105037212142159 91797189157555818213239)
          ·
            refine ⟨137695783736333727319859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91797189157555818213239 137695783736333727319859)
            ·
              refine ⟨206543675604500590979789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137695783736333727319859 206543675604500590979789)
              ·
                refine ⟨77453878351687721617421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206543675604500590979789 77453878351687721617421)
                ·
                  refine ⟨29045204381882895606533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77453878351687721617421 29045204381882895606533)
                  ·
                    rfl

theorem cell20_63636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_63636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63636 prefixEnd_63636 := by exact prefixLift 63636
  have htrace : WordTrace (prefixWord ++ tailWord_63636) baseStart_63636 baseEnd_63636 := by
    simpa [prefixWord, tailWord_63636, baseEnd_63636] using wordTrace_append hprefix tailTrace_63636
  have hstable : (prefixWord ++ tailWord_63636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63636).length < 2 ^ (prefixWord ++ tailWord_63636).sum := by decide
  have hdescent : baseEnd_63636 < baseStart_63636 := by decide
  rcases family_descends (prefixWord ++ tailWord_63636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63702 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_63702 : Nat := 118140960795 + 63702 * 2 ^ 59
def prefixEnd_63702 : Nat := 4983230072969 + 3 ^ 40 * 63702 * 2
def baseEnd_63702 : Nat := 29075328580279999406263

theorem tailTrace_63702 : CollatzResearch.WordTrace tailWord_63702 prefixEnd_63702 29075328580279999406263 := by
  unfold tailWord_63702
  simp only [CollatzResearch.WordTrace]
  refine ⟨145212675951625517534585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1548935210150672187035573 145212675951625517534585)
  ·
    refine ⟨108909506963719138150939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145212675951625517534585 108909506963719138150939)
    ·
      refine ⟨163364260445578707226409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108909506963719138150939 163364260445578707226409)
      ·
        refine ⟨122523195334184030419807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163364260445578707226409 122523195334184030419807)
        ·
          refine ⟨183784793001276045629711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122523195334184030419807 183784793001276045629711)
          ·
            refine ⟨275677189501914068444567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183784793001276045629711 275677189501914068444567)
            ·
              refine ⟨413515784252871102666851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275677189501914068444567 413515784252871102666851)
              ·
                refine ⟨620273676379306654000277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413515784252871102666851 620273676379306654000277)
                ·
                  refine ⟨29075328580279999406263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 620273676379306654000277 29075328580279999406263)
                  ·
                    rfl

theorem cell20_63702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_63702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63702 prefixEnd_63702 := by exact prefixLift 63702
  have htrace : WordTrace (prefixWord ++ tailWord_63702) baseStart_63702 baseEnd_63702 := by
    simpa [prefixWord, tailWord_63702, baseEnd_63702] using wordTrace_append hprefix tailTrace_63702
  have hstable : (prefixWord ++ tailWord_63702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63702).length < 2 ^ (prefixWord ++ tailWord_63702).sum := by decide
  have hdescent : baseEnd_63702 < baseStart_63702 := by decide
  rcases family_descends (prefixWord ++ tailWord_63702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63706 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_63706 : Nat := 118140960795 + 63706 * 2 ^ 59
def prefixEnd_63706 : Nat := 4983230072969 + 3 ^ 40 * 63706 * 2
def baseEnd_63706 : Nat := 29077154289273763272913

theorem tailTrace_63706 : CollatzResearch.WordTrace tailWord_63706 prefixEnd_63706 29077154289273763272913 := by
  unfold tailWord_63706
  simp only [CollatzResearch.WordTrace]
  refine ⟨580887176802879240924743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1549032471474344642465981 580887176802879240924743)
  ·
    refine ⟨871330765204318861387115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 580887176802879240924743 871330765204318861387115)
    ·
      refine ⟨1306996147806478292080673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 871330765204318861387115 1306996147806478292080673)
      ·
        refine ⟨980247110854858719060505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1306996147806478292080673 980247110854858719060505)
        ·
          refine ⟨735185333141144039295379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 980247110854858719060505 735185333141144039295379)
          ·
            refine ⟨1102777999711716058943069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735185333141144039295379 1102777999711716058943069)
            ·
              refine ⟨413541749891893522103651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1102777999711716058943069 413541749891893522103651)
              ·
                refine ⟨620312624837840283155477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413541749891893522103651 620312624837840283155477)
                ·
                  refine ⟨29077154289273763272913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 620312624837840283155477 29077154289273763272913)
                  ·
                    rfl

theorem cell20_63706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_63706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63706 prefixEnd_63706 := by exact prefixLift 63706
  have htrace : WordTrace (prefixWord ++ tailWord_63706) baseStart_63706 baseEnd_63706 := by
    simpa [prefixWord, tailWord_63706, baseEnd_63706] using wordTrace_append hprefix tailTrace_63706
  have hstable : (prefixWord ++ tailWord_63706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63706).length < 2 ^ (prefixWord ++ tailWord_63706).sum := by decide
  have hdescent : baseEnd_63706 < baseStart_63706 := by decide
  rcases family_descends (prefixWord ++ tailWord_63706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63719 : List Nat := [1, 1, 5, 3, 1, 2, 2, 3, 2]
def baseStart_63719 : Nat := 118140960795 + 63719 * 2 ^ 59
def prefixEnd_63719 : Nat := 4983230072969 + 3 ^ 40 * 63719 * 2
def baseEnd_63719 : Nat := 29083087843503495839527

theorem tailTrace_63719 : CollatzResearch.WordTrace tailWord_63719 prefixEnd_63719 29083087843503495839527 := by
  unfold tailWord_63719
  simp only [CollatzResearch.WordTrace]
  refine ⟨2324022856164420183922211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1549348570776280122614807 2324022856164420183922211)
  ·
    refine ⟨3486034284246630275883317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2324022856164420183922211 3486034284246630275883317)
    ·
      refine ⟨326815714148121588364061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3486034284246630275883317 326815714148121588364061)
      ·
        refine ⟨122555892805545595636523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326815714148121588364061 122555892805545595636523)
        ·
          refine ⟨183833839208318393454785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122555892805545595636523 183833839208318393454785)
          ·
            refine ⟨137875379406238795091089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183833839208318393454785 137875379406238795091089)
            ·
              refine ⟨103406534554679096318317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137875379406238795091089 103406534554679096318317)
              ·
                refine ⟨38777450458004661119369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103406534554679096318317 38777450458004661119369)
                ·
                  refine ⟨29083087843503495839527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38777450458004661119369 29083087843503495839527)
                  ·
                    rfl

theorem cell20_63719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 2].length) (baseStart_63719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63719 prefixEnd_63719 := by exact prefixLift 63719
  have htrace : WordTrace (prefixWord ++ tailWord_63719) baseStart_63719 baseEnd_63719 := by
    simpa [prefixWord, tailWord_63719, baseEnd_63719] using wordTrace_append hprefix tailTrace_63719
  have hstable : (prefixWord ++ tailWord_63719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63719).length < 2 ^ (prefixWord ++ tailWord_63719).sum := by decide
  have hdescent : baseEnd_63719 < baseStart_63719 := by decide
  rcases family_descends (prefixWord ++ tailWord_63719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63730 : List Nat := [3, 2, 1, 3, 2, 2, 7]
def baseStart_63730 : Nat := 118140960795 + 63730 * 2 ^ 59
def prefixEnd_63730 : Nat := 4983230072969 + 3 ^ 40 * 63730 * 2
def baseEnd_63730 : Nat := 3232012060359594052535

theorem tailTrace_63730 : CollatzResearch.WordTrace tailWord_63730 prefixEnd_63730 3232012060359594052535 := by
  unfold tailWord_63730
  simp only [CollatzResearch.WordTrace]
  refine ⟨581106014781142265643161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1549616039416379375048429 581106014781142265643161)
  ·
    refine ⟨435829511085856699232371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 581106014781142265643161 435829511085856699232371)
    ·
      refine ⟨653744266628785048848557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435829511085856699232371 653744266628785048848557)
      ·
        refine ⟨245154099985794393318209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 653744266628785048848557 245154099985794393318209)
        ·
          refine ⟨183865574989345794988657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245154099985794393318209 183865574989345794988657)
          ·
            refine ⟨137899181242009346241493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183865574989345794988657 137899181242009346241493)
            ·
              refine ⟨3232012060359594052535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 137899181242009346241493 3232012060359594052535)
              ·
                rfl

theorem cell20_63730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 7].length) (baseStart_63730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63730 prefixEnd_63730 := by exact prefixLift 63730
  have htrace : WordTrace (prefixWord ++ tailWord_63730) baseStart_63730 baseEnd_63730 := by
    simpa [prefixWord, tailWord_63730, baseEnd_63730] using wordTrace_append hprefix tailTrace_63730
  have hstable : (prefixWord ++ tailWord_63730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63730).length < 2 ^ (prefixWord ++ tailWord_63730).sum := by decide
  have hdescent : baseEnd_63730 < baseStart_63730 := by decide
  rcases family_descends (prefixWord ++ tailWord_63730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63737 : List Nat := [1, 2, 1, 3, 1, 1, 2, 6, 3]
def baseStart_63737 : Nat := 118140960795 + 63737 * 2 ^ 59
def prefixEnd_63737 : Nat := 4983230072969 + 3 ^ 40 * 63737 * 2
def baseEnd_63737 : Nat := 29091303533975433239453

theorem tailTrace_63737 : CollatzResearch.WordTrace tailWord_63737 prefixEnd_63737 29091303533975433239453 := by
  unfold tailWord_63737
  simp only [CollatzResearch.WordTrace]
  refine ⟨2324679370099209258077465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1549786246732806172051643 2324679370099209258077465)
  ·
    refine ⟨1743509527574406943558099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2324679370099209258077465 1743509527574406943558099)
    ·
      refine ⟨2615264291361610415337149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1743509527574406943558099 2615264291361610415337149)
      ·
        refine ⟨980724109260603905751431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2615264291361610415337149 980724109260603905751431)
        ·
          refine ⟨1471086163890905858627147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 980724109260603905751431 1471086163890905858627147)
          ·
            refine ⟨2206629245836358787940721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1471086163890905858627147 2206629245836358787940721)
            ·
              refine ⟨1654971934377269090955541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2206629245836358787940721 1654971934377269090955541)
              ·
                refine ⟨77576809423934488638541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1654971934377269090955541 77576809423934488638541)
                ·
                  refine ⟨29091303533975433239453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77576809423934488638541 29091303533975433239453)
                  ·
                    rfl

theorem cell20_63737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_63737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63737 prefixEnd_63737 := by exact prefixLift 63737
  have htrace : WordTrace (prefixWord ++ tailWord_63737) baseStart_63737 baseEnd_63737 := by
    simpa [prefixWord, tailWord_63737, baseEnd_63737] using wordTrace_append hprefix tailTrace_63737
  have hstable : (prefixWord ++ tailWord_63737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63737).length < 2 ^ (prefixWord ++ tailWord_63737).sum := by decide
  have hdescent : baseEnd_63737 < baseStart_63737 := by decide
  rcases family_descends (prefixWord ++ tailWord_63737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63740 : List Nat := [2, 2, 2, 1, 4, 1, 2, 4, 2]
def baseStart_63740 : Nat := 118140960795 + 63740 * 2 ^ 59
def prefixEnd_63740 : Nat := 4983230072969 + 3 ^ 40 * 63740 * 2
def baseEnd_63740 : Nat := 29092672815720756139441

theorem tailTrace_63740 : CollatzResearch.WordTrace tailWord_63740 prefixEnd_63740 29092672815720756139441 := by
  unfold tailWord_63740
  simp only [CollatzResearch.WordTrace]
  refine ⟨1162394394544170385218337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1549859192725560513624449 1162394394544170385218337)
  ·
    refine ⟨871795795908127788913753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1162394394544170385218337 871795795908127788913753)
    ·
      refine ⟨653846846931095841685315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 871795795908127788913753 653846846931095841685315)
      ·
        refine ⟨980770270396643762527973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653846846931095841685315 980770270396643762527973)
        ·
          refine ⟨183894425699370705473995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 980770270396643762527973 183894425699370705473995)
          ·
            refine ⟨275841638549056058210993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183894425699370705473995 275841638549056058210993)
            ·
              refine ⟨206881228911792043658245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275841638549056058210993 206881228911792043658245)
              ·
                refine ⟨38790230420961008185921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206881228911792043658245 38790230420961008185921)
                ·
                  refine ⟨29092672815720756139441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38790230420961008185921 29092672815720756139441)
                  ·
                    rfl

theorem cell20_63740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_63740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63740 prefixEnd_63740 := by exact prefixLift 63740
  have htrace : WordTrace (prefixWord ++ tailWord_63740) baseStart_63740 baseEnd_63740 := by
    simpa [prefixWord, tailWord_63740, baseEnd_63740] using wordTrace_append hprefix tailTrace_63740
  have hstable : (prefixWord ++ tailWord_63740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63740).length < 2 ^ (prefixWord ++ tailWord_63740).sum := by decide
  have hdescent : baseEnd_63740 < baseStart_63740 := by decide
  rcases family_descends (prefixWord ++ tailWord_63740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63744 : List Nat := [2, 1, 1, 2, 1, 1, 5, 3, 4]
def baseStart_63744 : Nat := 118140960795 + 63744 * 2 ^ 59
def prefixEnd_63744 : Nat := 4983230072969 + 3 ^ 40 * 63744 * 2
def baseEnd_63744 : Nat := 29094498524714520006091

theorem tailTrace_63744 : CollatzResearch.WordTrace tailWord_63744 prefixEnd_63744 29094498524714520006091 := by
  unfold tailWord_63744
  simp only [CollatzResearch.WordTrace]
  refine ⟨1162467340536924726791143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1549956454049232969054857 1162467340536924726791143)
  ·
    refine ⟨1743701010805387090186715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1162467340536924726791143 1743701010805387090186715)
    ·
      refine ⟨2615551516208080635280073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1743701010805387090186715 2615551516208080635280073)
      ·
        refine ⟨1961663637156060476460055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2615551516208080635280073 1961663637156060476460055)
        ·
          refine ⟨2942495455734090714690083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1961663637156060476460055 2942495455734090714690083)
          ·
            refine ⟨4413743183601136072035125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2942495455734090714690083 4413743183601136072035125)
            ·
              refine ⟨413788423462606506753293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4413743183601136072035125 413788423462606506753293)
              ·
                refine ⟨155170658798477440032485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 413788423462606506753293 155170658798477440032485)
                ·
                  refine ⟨29094498524714520006091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155170658798477440032485 29094498524714520006091)
                  ·
                    rfl

theorem cell20_63744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_63744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63744 prefixEnd_63744 := by exact prefixLift 63744
  have htrace : WordTrace (prefixWord ++ tailWord_63744) baseStart_63744 baseEnd_63744 := by
    simpa [prefixWord, tailWord_63744, baseEnd_63744] using wordTrace_append hprefix tailTrace_63744
  have hstable : (prefixWord ++ tailWord_63744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63744).length < 2 ^ (prefixWord ++ tailWord_63744).sum := by decide
  have hdescent : baseEnd_63744 < baseStart_63744 := by decide
  rcases family_descends (prefixWord ++ tailWord_63744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63774 : List Nat := [4, 3, 2, 1, 1, 1, 3, 3, 2]
def baseStart_63774 : Nat := 118140960795 + 63774 * 2 ^ 59
def prefixEnd_63774 : Nat := 4983230072969 + 3 ^ 40 * 63774 * 2
def baseEnd_63774 : Nat := 29108191342167749005969

theorem tailTrace_63774 : CollatzResearch.WordTrace tailWord_63774 prefixEnd_63774 29108191342167749005969 := by
  unfold tailWord_63774
  simp only [CollatzResearch.WordTrace]
  refine ⟨290753608870645572146797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1550685913976776384782917 290753608870645572146797)
  ·
    refine ⟨109032603326492089555049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290753608870645572146797 109032603326492089555049)
    ·
      refine ⟨81774452494869067166287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109032603326492089555049 81774452494869067166287)
      ·
        refine ⟨122661678742303600749431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81774452494869067166287 122661678742303600749431)
        ·
          refine ⟨183992518113455401124147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122661678742303600749431 183992518113455401124147)
          ·
            refine ⟨275988777170183101686221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183992518113455401124147 275988777170183101686221)
            ·
              refine ⟨103495791438818663132333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275988777170183101686221 103495791438818663132333)
              ·
                refine ⟨38810921789556998674625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103495791438818663132333 38810921789556998674625)
                ·
                  refine ⟨29108191342167749005969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38810921789556998674625 29108191342167749005969)
                  ·
                    rfl

theorem cell20_63774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_63774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63774 prefixEnd_63774 := by exact prefixLift 63774
  have htrace : WordTrace (prefixWord ++ tailWord_63774) baseStart_63774 baseEnd_63774 := by
    simpa [prefixWord, tailWord_63774, baseEnd_63774] using wordTrace_append hprefix tailTrace_63774
  have hstable : (prefixWord ++ tailWord_63774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63774).length < 2 ^ (prefixWord ++ tailWord_63774).sum := by decide
  have hdescent : baseEnd_63774 < baseStart_63774 := by decide
  rcases family_descends (prefixWord ++ tailWord_63774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63775 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 5]
def baseStart_63775 : Nat := 118140960795 + 63775 * 2 ^ 59
def prefixEnd_63775 : Nat := 4983230072969 + 3 ^ 40 * 63775 * 2
def baseEnd_63775 : Nat := 29108647769416189972631

theorem tailTrace_63775 : CollatzResearch.WordTrace tailWord_63775 prefixEnd_63775 29108647769416189972631 := by
  unfold tailWord_63775
  simp only [CollatzResearch.WordTrace]
  refine ⟨2326065343961541747960779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1550710229307694498640519 2326065343961541747960779)
  ·
    refine ⟨3489098015942312621941169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2326065343961541747960779 3489098015942312621941169)
    ·
      refine ⟨2616823511956734466455877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3489098015942312621941169 2616823511956734466455877)
      ·
        refine ⟨490654408491887712460477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2616823511956734466455877 490654408491887712460477)
        ·
          refine ⟨183995403184457892172679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490654408491887712460477 183995403184457892172679)
          ·
            refine ⟨275993104776686838259019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183995403184457892172679 275993104776686838259019)
            ·
              refine ⟨413989657165030257388529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275993104776686838259019 413989657165030257388529)
              ·
                refine ⟨310492242873772693041397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413989657165030257388529 310492242873772693041397)
                ·
                  refine ⟨29108647769416189972631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 310492242873772693041397 29108647769416189972631)
                  ·
                    rfl

theorem cell20_63775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_63775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63775 prefixEnd_63775 := by exact prefixLift 63775
  have htrace : WordTrace (prefixWord ++ tailWord_63775) baseStart_63775 baseEnd_63775 := by
    simpa [prefixWord, tailWord_63775, baseEnd_63775] using wordTrace_append hprefix tailTrace_63775
  have hstable : (prefixWord ++ tailWord_63775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63775).length < 2 ^ (prefixWord ++ tailWord_63775).sum := by decide
  have hdescent : baseEnd_63775 < baseStart_63775 := by decide
  rcases family_descends (prefixWord ++ tailWord_63775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63799 : List Nat := [1, 1, 3, 1, 2, 1, 1, 8, 2]
def baseStart_63799 : Nat := 118140960795 + 63799 * 2 ^ 59
def prefixEnd_63799 : Nat := 4983230072969 + 3 ^ 40 * 63799 * 2
def baseEnd_63799 : Nat := 29119602023378773172533

theorem tailTrace_63799 : CollatzResearch.WordTrace tailWord_63799 prefixEnd_63799 29119602023378773172533 := by
  unfold tailWord_63799
  simp only [CollatzResearch.WordTrace]
  refine ⟨2326940695874593846834451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1551293797249729231222967 2326940695874593846834451)
  ·
    refine ⟨3490411043811890770251677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2326940695874593846834451 3490411043811890770251677)
    ·
      refine ⟨1308904141429459038844379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3490411043811890770251677 1308904141429459038844379)
      ·
        refine ⟨1963356212144188558266569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1308904141429459038844379 1963356212144188558266569)
        ·
          refine ⟨1472517159108141418699927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1963356212144188558266569 1472517159108141418699927)
          ·
            refine ⟨2208775738662212128049891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1472517159108141418699927 2208775738662212128049891)
            ·
              refine ⟨3313163607993318192074837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2208775738662212128049891 3313163607993318192074837)
              ·
                refine ⟨38826136031171697563377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3313163607993318192074837 38826136031171697563377)
                ·
                  refine ⟨29119602023378773172533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38826136031171697563377 29119602023378773172533)
                  ·
                    rfl

theorem cell20_63799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 2].length) (baseStart_63799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63799 prefixEnd_63799 := by exact prefixLift 63799
  have htrace : WordTrace (prefixWord ++ tailWord_63799) baseStart_63799 baseEnd_63799 := by
    simpa [prefixWord, tailWord_63799, baseEnd_63799] using wordTrace_append hprefix tailTrace_63799
  have hstable : (prefixWord ++ tailWord_63799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63799).length < 2 ^ (prefixWord ++ tailWord_63799).sum := by decide
  have hdescent : baseEnd_63799 < baseStart_63799 := by decide
  rcases family_descends (prefixWord ++ tailWord_63799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63806 : List Nat := [4, 2, 1, 2, 1, 2, 1, 7]
def baseStart_63806 : Nat := 118140960795 + 63806 * 2 ^ 59
def prefixEnd_63806 : Nat := 4983230072969 + 3 ^ 40 * 63806 * 2
def baseEnd_63806 : Nat := 9707599004705953313057

theorem tailTrace_63806 : CollatzResearch.WordTrace tailWord_63806 prefixEnd_63806 9707599004705953313057 := by
  unfold tailWord_63806
  simp only [CollatzResearch.WordTrace]
  refine ⟨290899500856154255292409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1551464004566156028226181 290899500856154255292409)
  ·
    refine ⟨218174625642115691469307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290899500856154255292409 218174625642115691469307)
    ·
      refine ⟨327261938463173537203961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218174625642115691469307 327261938463173537203961)
      ·
        refine ⟨245446453847380152902971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327261938463173537203961 245446453847380152902971)
        ·
          refine ⟨368169680771070229354457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245446453847380152902971 368169680771070229354457)
          ·
            refine ⟨276127260578302672015843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368169680771070229354457 276127260578302672015843)
            ·
              refine ⟨414190890867454008023765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276127260578302672015843 414190890867454008023765)
              ·
                refine ⟨9707599004705953313057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 414190890867454008023765 9707599004705953313057)
                ·
                  rfl

theorem cell20_63806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_63806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63806 prefixEnd_63806 := by exact prefixLift 63806
  have htrace : WordTrace (prefixWord ++ tailWord_63806) baseStart_63806 baseEnd_63806 := by
    simpa [prefixWord, tailWord_63806, baseEnd_63806] using wordTrace_append hprefix tailTrace_63806
  have hstable : (prefixWord ++ tailWord_63806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63806).length < 2 ^ (prefixWord ++ tailWord_63806).sum := by decide
  have hdescent : baseEnd_63806 < baseStart_63806 := by decide
  rcases family_descends (prefixWord ++ tailWord_63806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63809 : List Nat := [1, 2, 5, 2, 2, 1, 1, 3, 3]
def baseStart_63809 : Nat := 118140960795 + 63809 * 2 ^ 59
def prefixEnd_63809 : Nat := 4983230072969 + 3 ^ 40 * 63809 * 2
def baseEnd_63809 : Nat := 29124166295863182839159

theorem tailTrace_63809 : CollatzResearch.WordTrace tailWord_63809 prefixEnd_63809 29124166295863182839159 := by
  unfold tailWord_63809
  simp only [CollatzResearch.WordTrace]
  refine ⟨2327305425838365554698481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1551536950558910369798987 2327305425838365554698481)
  ·
    refine ⟨1745479069378774166023861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2327305425838365554698481 1745479069378774166023861)
    ·
      refine ⟨163638662754260078064737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1745479069378774166023861 163638662754260078064737)
      ·
        refine ⟨122728997065695058548553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163638662754260078064737 122728997065695058548553)
        ·
          refine ⟨92046747799271293911415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122728997065695058548553 92046747799271293911415)
          ·
            refine ⟨138070121698906940867123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92046747799271293911415 138070121698906940867123)
            ·
              refine ⟨207105182548360411300685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138070121698906940867123 207105182548360411300685)
              ·
                refine ⟨77664443455635154237757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207105182548360411300685 77664443455635154237757)
                ·
                  refine ⟨29124166295863182839159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77664443455635154237757 29124166295863182839159)
                  ·
                    rfl

theorem cell20_63809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_63809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63809 prefixEnd_63809 := by exact prefixLift 63809
  have htrace : WordTrace (prefixWord ++ tailWord_63809) baseStart_63809 baseEnd_63809 := by
    simpa [prefixWord, tailWord_63809, baseEnd_63809] using wordTrace_append hprefix tailTrace_63809
  have hstable : (prefixWord ++ tailWord_63809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63809).length < 2 ^ (prefixWord ++ tailWord_63809).sum := by decide
  have hdescent : baseEnd_63809 < baseStart_63809 := by decide
  rcases family_descends (prefixWord ++ tailWord_63809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63820 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 6]
def baseStart_63820 : Nat := 118140960795 + 63820 * 2 ^ 59
def prefixEnd_63820 : Nat := 4983230072969 + 3 ^ 40 * 63820 * 2
def baseEnd_63820 : Nat := 29129186995596033472447

theorem tailTrace_63820 : CollatzResearch.WordTrace tailWord_63820 prefixEnd_63820 29129186995596033472447 := by
  unfold tailWord_63820
  simp only [CollatzResearch.WordTrace]
  refine ⟨1163853314399257216674457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1551804419199009622232609 1163853314399257216674457)
  ·
    refine ⟨872889985799442912505843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1163853314399257216674457 872889985799442912505843)
    ·
      refine ⟨1309334978699164368758765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 872889985799442912505843 1309334978699164368758765)
      ·
        refine ⟨491000617012186638284537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1309334978699164368758765 491000617012186638284537)
        ·
          refine ⟨368250462759139978713403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491000617012186638284537 368250462759139978713403)
          ·
            refine ⟨552375694138709968070105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368250462759139978713403 552375694138709968070105)
            ·
              refine ⟨414281770604032476052579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552375694138709968070105 414281770604032476052579)
              ·
                refine ⟨621422655906048714078869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414281770604032476052579 621422655906048714078869)
                ·
                  refine ⟨29129186995596033472447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 621422655906048714078869 29129186995596033472447)
                  ·
                    rfl

theorem cell20_63820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_63820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63820 prefixEnd_63820 := by exact prefixLift 63820
  have htrace : WordTrace (prefixWord ++ tailWord_63820) baseStart_63820 baseEnd_63820 := by
    simpa [prefixWord, tailWord_63820, baseEnd_63820] using wordTrace_append hprefix tailTrace_63820
  have hstable : (prefixWord ++ tailWord_63820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63820).length < 2 ^ (prefixWord ++ tailWord_63820).sum := by decide
  have hdescent : baseEnd_63820 < baseStart_63820 := by decide
  rcases family_descends (prefixWord ++ tailWord_63820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63850 : List Nat := [3, 1, 3, 3, 1, 3, 2, 2, 2]
def baseStart_63850 : Nat := 118140960795 + 63850 * 2 ^ 59
def prefixEnd_63850 : Nat := 4983230072969 + 3 ^ 40 * 63850 * 2
def baseEnd_63850 : Nat := 29142879813049262472325

theorem tailTrace_63850 : CollatzResearch.WordTrace tailWord_63850 prefixEnd_63850 29142879813049262472325 := by
  unfold tailWord_63850
  simp only [CollatzResearch.WordTrace]
  refine ⟨582200204672457389235251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1552533879126553037960669 582200204672457389235251)
  ·
    refine ⟨873300307008686083852877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 582200204672457389235251 873300307008686083852877)
    ·
      refine ⟨327487615128257281444829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 873300307008686083852877 327487615128257281444829)
      ·
        refine ⟨122807855673096480541811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327487615128257281444829 122807855673096480541811)
        ·
          refine ⟨184211783509644720812717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122807855673096480541811 184211783509644720812717)
          ·
            refine ⟨69079418816116770304769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184211783509644720812717 69079418816116770304769)
            ·
              refine ⟨51809564112087577728577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69079418816116770304769 51809564112087577728577)
              ·
                refine ⟨38857173084065683296433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51809564112087577728577 38857173084065683296433)
                ·
                  refine ⟨29142879813049262472325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38857173084065683296433 29142879813049262472325)
                  ·
                    rfl

theorem cell20_63850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_63850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63850 prefixEnd_63850 := by exact prefixLift 63850
  have htrace : WordTrace (prefixWord ++ tailWord_63850) baseStart_63850 baseEnd_63850 := by
    simpa [prefixWord, tailWord_63850, baseEnd_63850] using wordTrace_append hprefix tailTrace_63850
  have hstable : (prefixWord ++ tailWord_63850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63850).length < 2 ^ (prefixWord ++ tailWord_63850).sum := by decide
  have hdescent : baseEnd_63850 < baseStart_63850 := by decide
  rcases family_descends (prefixWord ++ tailWord_63850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63861 : List Nat := [1, 3, 4, 1, 2, 3, 1, 5]
def baseStart_63861 : Nat := 118140960795 + 63861 * 2 ^ 59
def prefixEnd_63861 : Nat := 4983230072969 + 3 ^ 40 * 63861 * 2
def baseEnd_63861 : Nat := 9715966837594037701871

theorem tailTrace_63861 : CollatzResearch.WordTrace tailWord_63861 prefixEnd_63861 9715966837594037701871 := by
  unfold tailWord_63861
  simp only [CollatzResearch.WordTrace]
  refine ⟨2329202021649978435591437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1552801347766652290394291 2329202021649978435591437)
  ·
    refine ⟨873450758118741913346789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2329202021649978435591437 873450758118741913346789)
    ·
      refine ⟨163772017147264108752523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 873450758118741913346789 163772017147264108752523)
      ·
        refine ⟨245658025720896163128785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163772017147264108752523 245658025720896163128785)
        ·
          refine ⟨184243519290672122346589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245658025720896163128785 184243519290672122346589)
          ·
            refine ⟨69091319734002045879971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184243519290672122346589 69091319734002045879971)
            ·
              refine ⟨103636979601003068819957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69091319734002045879971 103636979601003068819957)
              ·
                refine ⟨9715966837594037701871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103636979601003068819957 9715966837594037701871)
                ·
                  rfl

theorem cell20_63861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 5].length) (baseStart_63861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63861 prefixEnd_63861 := by exact prefixLift 63861
  have htrace : WordTrace (prefixWord ++ tailWord_63861) baseStart_63861 baseEnd_63861 := by
    simpa [prefixWord, tailWord_63861, baseEnd_63861] using wordTrace_append hprefix tailTrace_63861
  have hstable : (prefixWord ++ tailWord_63861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63861).length < 2 ^ (prefixWord ++ tailWord_63861).sum := by decide
  have hdescent : baseEnd_63861 < baseStart_63861 := by decide
  rcases family_descends (prefixWord ++ tailWord_63861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63872 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 9]
def baseStart_63872 : Nat := 118140960795 + 63872 * 2 ^ 59
def prefixEnd_63872 : Nat := 4983230072969 + 3 ^ 40 * 63872 * 2
def baseEnd_63872 : Nat := 29152921212514963738901

theorem tailTrace_63872 : CollatzResearch.WordTrace tailWord_63872 prefixEnd_63872 29152921212514963738901 := by
  unfold tailWord_63872
  simp only [CollatzResearch.WordTrace]
  refine ⟨1164801612305063657120935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1553068816406751542827913 1164801612305063657120935)
  ·
    refine ⟨1747202418457595485681403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1164801612305063657120935 1747202418457595485681403)
    ·
      refine ⟨2620803627686393228522105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1747202418457595485681403 2620803627686393228522105)
      ·
        refine ⟨1965602720764794921391579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2620803627686393228522105 1965602720764794921391579)
        ·
          refine ⟨2948404081147192382087369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1965602720764794921391579 2948404081147192382087369)
          ·
            refine ⟨2211303060860394286565527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2948404081147192382087369 2211303060860394286565527)
            ·
              refine ⟨3316954591290591429848291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2211303060860394286565527 3316954591290591429848291)
              ·
                refine ⟨4975431886935887144772437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3316954591290591429848291 4975431886935887144772437)
                ·
                  refine ⟨29152921212514963738901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4975431886935887144772437 29152921212514963738901)
                  ·
                    rfl

theorem cell20_63872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_63872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63872 prefixEnd_63872 := by exact prefixLift 63872
  have htrace : WordTrace (prefixWord ++ tailWord_63872) baseStart_63872 baseEnd_63872 := by
    simpa [prefixWord, tailWord_63872, baseEnd_63872] using wordTrace_append hprefix tailTrace_63872
  have hstable : (prefixWord ++ tailWord_63872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63872).length < 2 ^ (prefixWord ++ tailWord_63872).sum := by decide
  have hdescent : baseEnd_63872 < baseStart_63872 := by decide
  rcases family_descends (prefixWord ++ tailWord_63872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63875 : List Nat := [1, 1, 1, 3, 6, 1, 1, 2, 4]
def baseStart_63875 : Nat := 118140960795 + 63875 * 2 ^ 59
def prefixEnd_63875 : Nat := 4983230072969 + 3 ^ 40 * 63875 * 2
def baseEnd_63875 : Nat := 29154290494260286638889

theorem tailTrace_63875 : CollatzResearch.WordTrace tailWord_63875 prefixEnd_63875 29154290494260286638889 := by
  unfold tailWord_63875
  simp only [CollatzResearch.WordTrace]
  refine ⟨2329712643599258826601079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1553141762399505884400719 2329712643599258826601079)
  ·
    refine ⟨3494568965398888239901619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2329712643599258826601079 3494568965398888239901619)
    ·
      refine ⟨5241853448098332359852429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3494568965398888239901619 5241853448098332359852429)
      ·
        refine ⟨1965695043036874634944661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5241853448098332359852429 1965695043036874634944661)
        ·
          refine ⟨92141955142353498513031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1965695043036874634944661 92141955142353498513031)
          ·
            refine ⟨138212932713530247769547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92141955142353498513031 138212932713530247769547)
            ·
              refine ⟨207319399070295371654321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138212932713530247769547 207319399070295371654321)
              ·
                refine ⟨155489549302721528740741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207319399070295371654321 155489549302721528740741)
                ·
                  refine ⟨29154290494260286638889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155489549302721528740741 29154290494260286638889)
                  ·
                    rfl

theorem cell20_63875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 4].length) (baseStart_63875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63875 prefixEnd_63875 := by exact prefixLift 63875
  have htrace : WordTrace (prefixWord ++ tailWord_63875) baseStart_63875 baseEnd_63875 := by
    simpa [prefixWord, tailWord_63875, baseEnd_63875] using wordTrace_append hprefix tailTrace_63875
  have hstable : (prefixWord ++ tailWord_63875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63875).length < 2 ^ (prefixWord ++ tailWord_63875).sum := by decide
  have hdescent : baseEnd_63875 < baseStart_63875 := by decide
  rcases family_descends (prefixWord ++ tailWord_63875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63902 : List Nat := [4, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_63902 : Nat := 118140960795 + 63902 * 2 ^ 59
def prefixEnd_63902 : Nat := 4983230072969 + 3 ^ 40 * 63902 * 2
def baseEnd_63902 : Nat := 29166614029968192738779

theorem tailTrace_63902 : CollatzResearch.WordTrace tailWord_63902 prefixEnd_63902 29166614029968192738779 := by
  unfold tailWord_63902
  simp only [CollatzResearch.WordTrace]
  refine ⟨291337176812680304729245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1553798276334294958555973 291337176812680304729245)
  ·
    refine ⟨109251441304755114273467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291337176812680304729245 109251441304755114273467)
    ·
      refine ⟨163877161957132671410201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109251441304755114273467 163877161957132671410201)
      ·
        refine ⟨122907871467849503557651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163877161957132671410201 122907871467849503557651)
        ·
          refine ⟨184361807201774255336477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122907871467849503557651 184361807201774255336477)
          ·
            refine ⟨69135677700665345751179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184361807201774255336477 69135677700665345751179)
            ·
              refine ⟨103703516550998018626769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69135677700665345751179 103703516550998018626769)
              ·
                refine ⟨77777637413248513970077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103703516550998018626769 77777637413248513970077)
                ·
                  refine ⟨29166614029968192738779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77777637413248513970077 29166614029968192738779)
                  ·
                    rfl

theorem cell20_63902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_63902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63902 prefixEnd_63902 := by exact prefixLift 63902
  have htrace : WordTrace (prefixWord ++ tailWord_63902) baseStart_63902 baseEnd_63902 := by
    simpa [prefixWord, tailWord_63902, baseEnd_63902] using wordTrace_append hprefix tailTrace_63902
  have hstable : (prefixWord ++ tailWord_63902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63902).length < 2 ^ (prefixWord ++ tailWord_63902).sum := by decide
  have hdescent : baseEnd_63902 < baseStart_63902 := by decide
  rcases family_descends (prefixWord ++ tailWord_63902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63903 : List Nat := [1, 1, 2, 5, 1, 1, 9]
def baseStart_63903 : Nat := 118140960795 + 63903 * 2 ^ 59
def prefixEnd_63903 : Nat := 4983230072969 + 3 ^ 40 * 63903 * 2
def baseEnd_63903 : Nat := 3240785606357403745049

theorem tailTrace_63903 : CollatzResearch.WordTrace tailWord_63903 prefixEnd_63903 3240785606357403745049 := by
  unfold tailWord_63903
  simp only [CollatzResearch.WordTrace]
  refine ⟨2330733887497819608620363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1553822591665213072413575 2330733887497819608620363)
  ·
    refine ⟨3496100831246729412930545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2330733887497819608620363 3496100831246729412930545)
    ·
      refine ⟨2622075623435047059697909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3496100831246729412930545 2622075623435047059697909)
      ·
        refine ⟨245819589697035661846679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2622075623435047059697909 245819589697035661846679)
        ·
          refine ⟨368729384545553492770019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245819589697035661846679 368729384545553492770019)
          ·
            refine ⟨553094076818330239155029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368729384545553492770019 553094076818330239155029)
            ·
              refine ⟨3240785606357403745049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 553094076818330239155029 3240785606357403745049)
              ·
                rfl

theorem cell20_63903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 9].length) (baseStart_63903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63903 prefixEnd_63903 := by exact prefixLift 63903
  have htrace : WordTrace (prefixWord ++ tailWord_63903) baseStart_63903 baseEnd_63903 := by
    simpa [prefixWord, tailWord_63903, baseEnd_63903] using wordTrace_append hprefix tailTrace_63903
  have hstable : (prefixWord ++ tailWord_63903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63903).length < 2 ^ (prefixWord ++ tailWord_63903).sum := by decide
  have hdescent : baseEnd_63903 < baseStart_63903 := by decide
  rcases family_descends (prefixWord ++ tailWord_63903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63954 : List Nat := [3, 2, 2, 4, 2, 1, 6]
def baseStart_63954 : Nat := 118140960795 + 63954 * 2 ^ 59
def prefixEnd_63954 : Nat := 4983230072969 + 3 ^ 40 * 63954 * 2
def baseEnd_63954 : Nat := 3243372027431902556137

theorem tailTrace_63954 : CollatzResearch.WordTrace tailWord_63954 prefixEnd_63954 3243372027431902556137 := by
  unfold tailWord_63954
  simp only [CollatzResearch.WordTrace]
  refine ⟨583148502578263829681729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1555062673542036879151277 583148502578263829681729)
  ·
    refine ⟨437361376933697872261297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 583148502578263829681729 437361376933697872261297)
    ·
      refine ⟨328021032700273404195973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437361376933697872261297 328021032700273404195973)
      ·
        refine ⟨61503943631301263286745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328021032700273404195973 61503943631301263286745)
        ·
          refine ⟨46127957723475947465059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61503943631301263286745 46127957723475947465059)
          ·
            refine ⟨69191936585213921197589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46127957723475947465059 69191936585213921197589)
            ·
              refine ⟨3243372027431902556137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69191936585213921197589 3243372027431902556137)
              ·
                rfl

theorem cell20_63954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 6].length) (baseStart_63954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63954 prefixEnd_63954 := by exact prefixLift 63954
  have htrace : WordTrace (prefixWord ++ tailWord_63954) baseStart_63954 baseEnd_63954 := by
    simpa [prefixWord, tailWord_63954, baseEnd_63954] using wordTrace_append hprefix tailTrace_63954
  have hstable : (prefixWord ++ tailWord_63954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63954).length < 2 ^ (prefixWord ++ tailWord_63954).sum := by decide
  have hdescent : baseEnd_63954 < baseStart_63954 := by decide
  rcases family_descends (prefixWord ++ tailWord_63954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63965 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 5]
def baseStart_63965 : Nat := 118140960795 + 63965 * 2 ^ 59
def prefixEnd_63965 : Nat := 4983230072969 + 3 ^ 40 * 63965 * 2
def baseEnd_63965 : Nat := 29195368946619973638521

theorem tailTrace_63965 : CollatzResearch.WordTrace tailWord_63965 prefixEnd_63965 29195368946619973638521 := by
  unfold tailWord_63965
  simp only [CollatzResearch.WordTrace]
  refine ⟨2332995213273204197377349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1555330142182136131584899 2332995213273204197377349)
  ·
    refine ⟨437436602488725787008253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2332995213273204197377349 437436602488725787008253)
    ·
      refine ⟨164038725933272170128095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437436602488725787008253 164038725933272170128095)
      ·
        refine ⟨246058088899908255192143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164038725933272170128095 246058088899908255192143)
        ·
          refine ⟨369087133349862382788215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246058088899908255192143 369087133349862382788215)
          ·
            refine ⟨553630700024793574182323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369087133349862382788215 553630700024793574182323)
            ·
              refine ⟨830446050037190361273485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553630700024793574182323 830446050037190361273485)
              ·
                refine ⟨311417268763946385477557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 830446050037190361273485 311417268763946385477557)
                ·
                  refine ⟨29195368946619973638521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 311417268763946385477557 29195368946619973638521)
                  ·
                    rfl

theorem cell20_63965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_63965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63965 prefixEnd_63965 := by exact prefixLift 63965
  have htrace : WordTrace (prefixWord ++ tailWord_63965) baseStart_63965 baseEnd_63965 := by
    simpa [prefixWord, tailWord_63965, baseEnd_63965] using wordTrace_append hprefix tailTrace_63965
  have hstable : (prefixWord ++ tailWord_63965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63965).length < 2 ^ (prefixWord ++ tailWord_63965).sum := by decide
  have hdescent : baseEnd_63965 < baseStart_63965 := by decide
  rcases family_descends (prefixWord ++ tailWord_63965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63968 : List Nat := [2, 1, 1, 3, 1, 1, 7, 2, 2]
def baseStart_63968 : Nat := 118140960795 + 63968 * 2 ^ 59
def prefixEnd_63968 : Nat := 4983230072969 + 3 ^ 40 * 63968 * 2
def baseEnd_63968 : Nat := 29196738228365296538509

theorem tailTrace_63968 : CollatzResearch.WordTrace tailWord_63968 prefixEnd_63968 29196738228365296538509 := by
  unfold tailWord_63968
  simp only [CollatzResearch.WordTrace]
  refine ⟨1166552316131167854868279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1555403088174890473157705 1166552316131167854868279)
  ·
    refine ⟨1749828474196751782302419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1166552316131167854868279 1749828474196751782302419)
    ·
      refine ⟨2624742711295127673453629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1749828474196751782302419 2624742711295127673453629)
      ·
        refine ⟨984278516735672877545111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2624742711295127673453629 984278516735672877545111)
        ·
          refine ⟨1476417775103509316317667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984278516735672877545111 1476417775103509316317667)
          ·
            refine ⟨2214626662655263974476501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476417775103509316317667 2214626662655263974476501)
            ·
              refine ⟨51905312405982749401793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2214626662655263974476501 51905312405982749401793)
              ·
                refine ⟨38928984304487062051345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51905312405982749401793 38928984304487062051345)
                ·
                  refine ⟨29196738228365296538509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38928984304487062051345 29196738228365296538509)
                  ·
                    rfl

theorem cell20_63968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 2].length) (baseStart_63968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63968 prefixEnd_63968 := by exact prefixLift 63968
  have htrace : WordTrace (prefixWord ++ tailWord_63968) baseStart_63968 baseEnd_63968 := by
    simpa [prefixWord, tailWord_63968, baseEnd_63968] using wordTrace_append hprefix tailTrace_63968
  have hstable : (prefixWord ++ tailWord_63968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63968).length < 2 ^ (prefixWord ++ tailWord_63968).sum := by decide
  have hdescent : baseEnd_63968 < baseStart_63968 := by decide
  rcases family_descends (prefixWord ++ tailWord_63968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63979 : List Nat := [1, 1, 1, 1, 2, 3, 6, 5]
def baseStart_63979 : Nat := 118140960795 + 63979 * 2 ^ 59
def prefixEnd_63979 : Nat := 4983230072969 + 3 ^ 40 * 63979 * 2
def baseEnd_63979 : Nat := 9733919642699382390599

theorem tailTrace_63979 : CollatzResearch.WordTrace tailWord_63979 prefixEnd_63979 9733919642699382390599 := by
  unfold tailWord_63979
  simp only [CollatzResearch.WordTrace]
  refine ⟨2333505835222484588386991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1555670556814989725591327 2333505835222484588386991)
  ·
    refine ⟨3500258752833726882580487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2333505835222484588386991 3500258752833726882580487)
    ·
      refine ⟨5250388129250590323870731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3500258752833726882580487 5250388129250590323870731)
      ·
        refine ⟨7875582193875885485806097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5250388129250590323870731 7875582193875885485806097)
        ·
          refine ⟨5906686645406914114354573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7875582193875885485806097 5906686645406914114354573)
          ·
            refine ⟨2215007492027592792882965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5906686645406914114354573 2215007492027592792882965)
            ·
              refine ⟨103828476188793412166389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2215007492027592792882965 103828476188793412166389)
              ·
                refine ⟨9733919642699382390599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103828476188793412166389 9733919642699382390599)
                ·
                  rfl

theorem cell20_63979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 5].length) (baseStart_63979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63979 prefixEnd_63979 := by exact prefixLift 63979
  have htrace : WordTrace (prefixWord ++ tailWord_63979) baseStart_63979 baseEnd_63979 := by
    simpa [prefixWord, tailWord_63979, baseEnd_63979] using wordTrace_append hprefix tailTrace_63979
  have hstable : (prefixWord ++ tailWord_63979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63979).length < 2 ^ (prefixWord ++ tailWord_63979).sum := by decide
  have hdescent : baseEnd_63979 < baseStart_63979 := by decide
  rcases family_descends (prefixWord ++ tailWord_63979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63982 : List Nat := [4, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_63982 : Nat := 118140960795 + 63982 * 2 ^ 59
def prefixEnd_63982 : Nat := 4983230072969 + 3 ^ 40 * 63982 * 2
def baseEnd_63982 : Nat := 29203128209843470071785

theorem tailTrace_63982 : CollatzResearch.WordTrace tailWord_63982 prefixEnd_63982 29203128209843470071785 := by
  unfold tailWord_63982
  simp only [CollatzResearch.WordTrace]
  refine ⟨291701906776452012593275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1555743502807744067164133 291701906776452012593275)
  ·
    refine ⟨437552860164678018889913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291701906776452012593275 437552860164678018889913)
    ·
      refine ⟨328164645123508514167435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437552860164678018889913 328164645123508514167435)
      ·
        refine ⟨492246967685262771251153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328164645123508514167435 492246967685262771251153)
        ·
          refine ⟨369185225763947078438365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492246967685262771251153 369185225763947078438365)
          ·
            refine ⟨138444459661480154414387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369185225763947078438365 138444459661480154414387)
            ·
              refine ⟨207666689492220231621581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138444459661480154414387 207666689492220231621581)
              ·
                refine ⟨77875008559582586858093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207666689492220231621581 77875008559582586858093)
                ·
                  refine ⟨29203128209843470071785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77875008559582586858093 29203128209843470071785)
                  ·
                    rfl

theorem cell20_63982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_63982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_63982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_63982 prefixEnd_63982 := by exact prefixLift 63982
  have htrace : WordTrace (prefixWord ++ tailWord_63982) baseStart_63982 baseEnd_63982 := by
    simpa [prefixWord, tailWord_63982, baseEnd_63982] using wordTrace_append hprefix tailTrace_63982
  have hstable : (prefixWord ++ tailWord_63982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63982).length < 2 ^ (prefixWord ++ tailWord_63982).sum := by decide
  have hdescent : baseEnd_63982 < baseStart_63982 := by decide
  rcases family_descends (prefixWord ++ tailWord_63982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64013 : List Nat := [1, 7, 1, 1, 1, 9]
def baseStart_64013 : Nat := 118140960795 + 64013 * 2 ^ 59
def prefixEnd_64013 : Nat := 4983230072969 + 3 ^ 40 * 64013 * 2
def baseEnd_64013 : Nat := 1082121387205375556975

theorem tailTrace_64013 : CollatzResearch.WordTrace tailWord_64013 prefixEnd_64013 1082121387205375556975 := by
  unfold tailWord_64013
  simp only [CollatzResearch.WordTrace]
  refine ⟨2334745917099308395124693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1556497278066205596749795 2334745917099308395124693)
  ·
    refine ⟨54720607432015040510735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 2334745917099308395124693 54720607432015040510735)
    ·
      refine ⟨82080911148022560766103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54720607432015040510735 82080911148022560766103)
      ·
        refine ⟨123121366722033841149155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82080911148022560766103 123121366722033841149155)
        ·
          refine ⟨184682050083050761723733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123121366722033841149155 184682050083050761723733)
          ·
            refine ⟨1082121387205375556975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 184682050083050761723733 1082121387205375556975)
            ·
              rfl

theorem cell20_64013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 9].length) (baseStart_64013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64013 prefixEnd_64013 := by exact prefixLift 64013
  have htrace : WordTrace (prefixWord ++ tailWord_64013) baseStart_64013 baseEnd_64013 := by
    simpa [prefixWord, tailWord_64013, baseEnd_64013] using wordTrace_append hprefix tailTrace_64013
  have hstable : (prefixWord ++ tailWord_64013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64013).length < 2 ^ (prefixWord ++ tailWord_64013).sum := by decide
  have hdescent : baseEnd_64013 < baseStart_64013 := by decide
  rcases family_descends (prefixWord ++ tailWord_64013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64023 : List Nat := [1, 1, 3, 6, 1, 1, 1, 4, 2]
def baseStart_64023 : Nat := 118140960795 + 64023 * 2 ^ 59
def prefixEnd_64023 : Nat := 4983230072969 + 3 ^ 40 * 64023 * 2
def baseEnd_64023 : Nat := 29221841727029549704951

theorem tailTrace_64023 : CollatzResearch.WordTrace tailWord_64023 prefixEnd_64023 29221841727029549704951 := by
  unfold tailWord_64023
  simp only [CollatzResearch.WordTrace]
  refine ⟨2335110647063080102988723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1556740431375386735325815 2335110647063080102988723)
  ·
    refine ⟨3502665970594620154483085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2335110647063080102988723 3502665970594620154483085)
    ·
      refine ⟨1313499738972982557931157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3502665970594620154483085 1313499738972982557931157)
      ·
        refine ⟨61570300264358557403023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1313499738972982557931157 61570300264358557403023)
        ·
          refine ⟨92355450396537836104535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61570300264358557403023 92355450396537836104535)
          ·
            refine ⟨138533175594806754156803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92355450396537836104535 138533175594806754156803)
            ·
              refine ⟨207799763392210131235205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138533175594806754156803 207799763392210131235205)
              ·
                refine ⟨38962455636039399606601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207799763392210131235205 38962455636039399606601)
                ·
                  refine ⟨29221841727029549704951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38962455636039399606601 29221841727029549704951)
                  ·
                    rfl

theorem cell20_64023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 2].length) (baseStart_64023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64023 prefixEnd_64023 := by exact prefixLift 64023
  have htrace : WordTrace (prefixWord ++ tailWord_64023) baseStart_64023 baseEnd_64023 := by
    simpa [prefixWord, tailWord_64023, baseEnd_64023] using wordTrace_append hprefix tailTrace_64023
  have hstable : (prefixWord ++ tailWord_64023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64023).length < 2 ^ (prefixWord ++ tailWord_64023).sum := by decide
  have hdescent : baseEnd_64023 < baseStart_64023 := by decide
  rcases family_descends (prefixWord ++ tailWord_64023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64068 : List Nat := [2, 3, 5, 1, 1, 1, 7]
def baseStart_64068 : Nat := 118140960795 + 64068 * 2 ^ 59
def prefixEnd_64068 : Nat := 4983230072969 + 3 ^ 40 * 64068 * 2
def baseEnd_64068 : Nat := 3249153439245488133863

theorem tailTrace_64068 : CollatzResearch.WordTrace tailWord_64068 prefixEnd_64068 3249153439245488133863 := by
  unfold tailWord_64068
  simp only [CollatzResearch.WordTrace]
  refine ⟨1168375965950026394188429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1557834621266701858917905 1168375965950026394188429)
  ·
    refine ⟨438140987231259897820661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1168375965950026394188429 438140987231259897820661)
    ·
      refine ⟨41075717552930615420687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 438140987231259897820661 41075717552930615420687)
      ·
        refine ⟨61613576329395923131031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41075717552930615420687 61613576329395923131031)
        ·
          refine ⟨92420364494093884696547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61613576329395923131031 92420364494093884696547)
          ·
            refine ⟨138630546741140827044821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92420364494093884696547 138630546741140827044821)
            ·
              refine ⟨3249153439245488133863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 138630546741140827044821 3249153439245488133863)
              ·
                rfl

theorem cell20_64068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 7].length) (baseStart_64068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64068 prefixEnd_64068 := by exact prefixLift 64068
  have htrace : WordTrace (prefixWord ++ tailWord_64068) baseStart_64068 baseEnd_64068 := by
    simpa [prefixWord, tailWord_64068, baseEnd_64068] using wordTrace_append hprefix tailTrace_64068
  have hstable : (prefixWord ++ tailWord_64068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64068).length < 2 ^ (prefixWord ++ tailWord_64068).sum := by decide
  have hdescent : baseEnd_64068 < baseStart_64068 := by decide
  rcases family_descends (prefixWord ++ tailWord_64068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64079 : List Nat := [1, 1, 2, 1, 1, 2, 7, 2, 3]
def baseStart_64079 : Nat := 118140960795 + 64079 * 2 ^ 59
def prefixEnd_64079 : Nat := 4983230072969 + 3 ^ 40 * 64079 * 2
def baseEnd_64079 : Nat := 29247401652942243838055

theorem tailTrace_64079 : CollatzResearch.WordTrace tailWord_64079 prefixEnd_64079 29247401652942243838055 := by
  unfold tailWord_64079
  simp only [CollatzResearch.WordTrace]
  refine ⟨2337153134860201667027291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1558102089906801111351527 2337153134860201667027291)
  ·
    refine ⟨3505729702290302500540937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2337153134860201667027291 3505729702290302500540937)
    ·
      refine ⟨2629297276717726875405703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3505729702290302500540937 2629297276717726875405703)
      ·
        refine ⟨3943945915076590313108555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2629297276717726875405703 3943945915076590313108555)
        ·
          refine ⟨5915918872614885469662833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3943945915076590313108555 5915918872614885469662833)
          ·
            refine ⟨4436939154461164102247125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5915918872614885469662833 4436939154461164102247125)
            ·
              refine ⟨103990761432683533646417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4436939154461164102247125 103990761432683533646417)
              ·
                refine ⟨77993071074512650234813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103990761432683533646417 77993071074512650234813)
                ·
                  refine ⟨29247401652942243838055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77993071074512650234813 29247401652942243838055)
                  ·
                    rfl

theorem cell20_64079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 3].length) (baseStart_64079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64079 prefixEnd_64079 := by exact prefixLift 64079
  have htrace : WordTrace (prefixWord ++ tailWord_64079) baseStart_64079 baseEnd_64079 := by
    simpa [prefixWord, tailWord_64079, baseEnd_64079] using wordTrace_append hprefix tailTrace_64079
  have hstable : (prefixWord ++ tailWord_64079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64079).length < 2 ^ (prefixWord ++ tailWord_64079).sum := by decide
  have hdescent : baseEnd_64079 < baseStart_64079 := by decide
  rcases family_descends (prefixWord ++ tailWord_64079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64107 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 6]
def baseStart_64107 : Nat := 118140960795 + 64107 * 2 ^ 59
def prefixEnd_64107 : Nat := 4983230072969 + 3 ^ 40 * 64107 * 2
def baseEnd_64107 : Nat := 29260181615898590904607

theorem tailTrace_64107 : CollatzResearch.WordTrace tailWord_64107 prefixEnd_64107 29260181615898590904607 := by
  unfold tailWord_64107
  simp only [CollatzResearch.WordTrace]
  refine ⟨2338174378758762449046575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1558782919172508299364383 2338174378758762449046575)
  ·
    refine ⟨3507261568138143673569863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2338174378758762449046575 3507261568138143673569863)
    ·
      refine ⟨5260892352207215510354795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3507261568138143673569863 5260892352207215510354795)
      ·
        refine ⟨7891338528310823265532193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5260892352207215510354795 7891338528310823265532193)
        ·
          refine ⟨5918503896233117449149145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7891338528310823265532193 5918503896233117449149145)
          ·
            refine ⟨4438877922174838086861859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5918503896233117449149145 4438877922174838086861859)
            ·
              refine ⟨6658316883262257130292789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4438877922174838086861859 6658316883262257130292789)
              ·
                refine ⟨624217207805836605964949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6658316883262257130292789 624217207805836605964949)
                ·
                  refine ⟨29260181615898590904607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 624217207805836605964949 29260181615898590904607)
                  ·
                    rfl

theorem cell20_64107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_64107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64107 prefixEnd_64107 := by exact prefixLift 64107
  have htrace : WordTrace (prefixWord ++ tailWord_64107) baseStart_64107 baseEnd_64107 := by
    simpa [prefixWord, tailWord_64107, baseEnd_64107] using wordTrace_append hprefix tailTrace_64107
  have hstable : (prefixWord ++ tailWord_64107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64107).length < 2 ^ (prefixWord ++ tailWord_64107).sum := by decide
  have hdescent : baseEnd_64107 < baseStart_64107 := by decide
  rcases family_descends (prefixWord ++ tailWord_64107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64110 : List Nat := [4, 1, 2, 2, 2, 2, 1, 6]
def baseStart_64110 : Nat := 118140960795 + 64110 * 2 ^ 59
def prefixEnd_64110 : Nat := 4983230072969 + 3 ^ 40 * 64110 * 2
def baseEnd_64110 : Nat := 9753850299214637934865

theorem tailTrace_64110 : CollatzResearch.WordTrace tailWord_64110 prefixEnd_64110 9753850299214637934865 := by
  unfold tailWord_64110
  simp only [CollatzResearch.WordTrace]
  refine ⟨292285474718486745175723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1558855865165262640937189 292285474718486745175723)
  ·
    refine ⟨438428212077730117763585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292285474718486745175723 438428212077730117763585)
    ·
      refine ⟨328821159058297588322689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438428212077730117763585 328821159058297588322689)
      ·
        refine ⟨246615869293723191242017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328821159058297588322689 246615869293723191242017)
        ·
          refine ⟨184961901970292393431513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246615869293723191242017 184961901970292393431513)
          ·
            refine ⟨138721426477719295073635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184961901970292393431513 138721426477719295073635)
            ·
              refine ⟨208082139716578942610453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138721426477719295073635 208082139716578942610453)
              ·
                refine ⟨9753850299214637934865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 208082139716578942610453 9753850299214637934865)
                ·
                  rfl

theorem cell20_64110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_64110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64110 prefixEnd_64110 := by exact prefixLift 64110
  have htrace : WordTrace (prefixWord ++ tailWord_64110) baseStart_64110 baseEnd_64110 := by
    simpa [prefixWord, tailWord_64110, baseEnd_64110] using wordTrace_append hprefix tailTrace_64110
  have hstable : (prefixWord ++ tailWord_64110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64110).length < 2 ^ (prefixWord ++ tailWord_64110).sum := by decide
  have hdescent : baseEnd_64110 < baseStart_64110 := by decide
  rcases family_descends (prefixWord ++ tailWord_64110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64148 : List Nat := [2, 4, 2, 2, 1, 1, 1, 7]
def baseStart_64148 : Nat := 118140960795 + 64148 * 2 ^ 59
def prefixEnd_64148 : Nat := 4983230072969 + 3 ^ 40 * 64148 * 2
def baseEnd_64148 : Nat := 9759631711028223512591

theorem tailTrace_64148 : CollatzResearch.WordTrace tailWord_64148 prefixEnd_64148 9759631711028223512591 := by
  unfold tailWord_64148
  simp only [CollatzResearch.WordTrace]
  refine ⟨1169834885805113225644549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1559779847740150967526065 1169834885805113225644549)
  ·
    refine ⟨219344041088458729808353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1169834885805113225644549 219344041088458729808353)
    ·
      refine ⟨164508030816344047356265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219344041088458729808353 164508030816344047356265)
      ·
        refine ⟨123381023112258035517199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164508030816344047356265 123381023112258035517199)
        ·
          refine ⟨185071534668387053275799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123381023112258035517199 185071534668387053275799)
          ·
            refine ⟨277607302002580579913699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185071534668387053275799 277607302002580579913699)
            ·
              refine ⟨416410953003870869870549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277607302002580579913699 416410953003870869870549)
              ·
                refine ⟨9759631711028223512591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 416410953003870869870549 9759631711028223512591)
                ·
                  rfl

theorem cell20_64148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_64148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64148 prefixEnd_64148 := by exact prefixLift 64148
  have htrace : WordTrace (prefixWord ++ tailWord_64148) baseStart_64148 baseEnd_64148 := by
    simpa [prefixWord, tailWord_64148, baseEnd_64148] using wordTrace_append hprefix tailTrace_64148
  have hstable : (prefixWord ++ tailWord_64148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64148).length < 2 ^ (prefixWord ++ tailWord_64148).sum := by decide
  have hdescent : baseEnd_64148 < baseStart_64148 := by decide
  rcases family_descends (prefixWord ++ tailWord_64148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64196 : List Nat := [2, 3, 3, 1, 1, 3, 1, 4, 2]
def baseStart_64196 : Nat := 118140960795 + 64196 * 2 ^ 59
def prefixEnd_64196 : Nat := 4983230072969 + 3 ^ 40 * 64196 * 2
def baseEnd_64196 : Nat := 29300803641009836937577

theorem tailTrace_64196 : CollatzResearch.WordTrace tailWord_64196 prefixEnd_64196 29300803641009836937577 := by
  unfold tailWord_64196
  simp only [CollatzResearch.WordTrace]
  refine ⟨1170710237718165324518221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1560946983624220432690961 1170710237718165324518221)
  ·
    refine ⟨439016339144311996694333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1170710237718165324518221 439016339144311996694333)
    ·
      refine ⟨164631127179116998760375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439016339144311996694333 164631127179116998760375)
      ·
        refine ⟨246946690768675498140563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164631127179116998760375 246946690768675498140563)
        ·
          refine ⟨370420036153013247210845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246946690768675498140563 370420036153013247210845)
          ·
            refine ⟨138907513557379967704067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370420036153013247210845 138907513557379967704067)
            ·
              refine ⟨208361270336069951556101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138907513557379967704067 208361270336069951556101)
              ·
                refine ⟨39067738188013115916769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208361270336069951556101 39067738188013115916769)
                ·
                  refine ⟨29300803641009836937577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39067738188013115916769 29300803641009836937577)
                  ·
                    rfl

theorem cell20_64196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_64196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64196 prefixEnd_64196 := by exact prefixLift 64196
  have htrace : WordTrace (prefixWord ++ tailWord_64196) baseStart_64196 baseEnd_64196 := by
    simpa [prefixWord, tailWord_64196, baseEnd_64196] using wordTrace_append hprefix tailTrace_64196
  have hstable : (prefixWord ++ tailWord_64196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64196).length < 2 ^ (prefixWord ++ tailWord_64196).sum := by decide
  have hdescent : baseEnd_64196 < baseStart_64196 := by decide
  rcases family_descends (prefixWord ++ tailWord_64196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64279 : List Nat := [1, 1, 3, 4, 3, 2, 2, 4]
def baseStart_64279 : Nat := 118140960795 + 64279 * 2 ^ 59
def prefixEnd_64279 : Nat := 4983230072969 + 3 ^ 40 * 64279 * 2
def baseEnd_64279 : Nat := 9779562367543479056857

theorem tailTrace_64279 : CollatzResearch.WordTrace tailWord_64279 prefixEnd_64279 9779562367543479056857 := by
  unfold tailWord_64279
  simp only [CollatzResearch.WordTrace]
  refine ⟨2344447734135635824307891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1562965156090423882871927 2344447734135635824307891)
  ·
    refine ⟨3516671601203453736461837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2344447734135635824307891 3516671601203453736461837)
    ·
      refine ⟨1318751850451295151173189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3516671601203453736461837 1318751850451295151173189)
      ·
        refine ⟨247265971959617840844973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1318751850451295151173189 247265971959617840844973)
        ·
          refine ⟨92724739484856690316865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247265971959617840844973 92724739484856690316865)
          ·
            refine ⟨69543554613642517737649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92724739484856690316865 69543554613642517737649)
            ·
              refine ⟨52157665960231888303237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69543554613642517737649 52157665960231888303237)
              ·
                refine ⟨9779562367543479056857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52157665960231888303237 9779562367543479056857)
                ·
                  rfl

theorem cell20_64279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 4].length) (baseStart_64279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64279 prefixEnd_64279 := by exact prefixLift 64279
  have htrace : WordTrace (prefixWord ++ tailWord_64279) baseStart_64279 baseEnd_64279 := by
    simpa [prefixWord, tailWord_64279, baseEnd_64279] using wordTrace_append hprefix tailTrace_64279
  have hstable : (prefixWord ++ tailWord_64279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64279).length < 2 ^ (prefixWord ++ tailWord_64279).sum := by decide
  have hdescent : baseEnd_64279 < baseStart_64279 := by decide
  rcases family_descends (prefixWord ++ tailWord_64279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64369 : List Nat := [1, 2, 2, 2, 1, 5, 1, 4, 2]
def baseStart_64369 : Nat := 118140960795 + 64369 * 2 ^ 59
def prefixEnd_64369 : Nat := 4983230072969 + 3 ^ 40 * 64369 * 2
def baseEnd_64369 : Nat := 29379765554990124170203

theorem tailTrace_64369 : CollatzResearch.WordTrace tailWord_64369 prefixEnd_64369 29379765554990124170203 := by
  unfold tailWord_64369
  simp only [CollatzResearch.WordTrace]
  refine ⟨2347730303809581195084161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1565153535873054130056107 2347730303809581195084161)
  ·
    refine ⟨1760797727857185896313121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2347730303809581195084161 1760797727857185896313121)
    ·
      refine ⟨1320598295892889422234841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1760797727857185896313121 1320598295892889422234841)
      ·
        refine ⟨990448721919667066676131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1320598295892889422234841 990448721919667066676131)
        ·
          refine ⟨1485673082879500600014197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990448721919667066676131 1485673082879500600014197)
          ·
            refine ⟨139281851519953181251331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1485673082879500600014197 139281851519953181251331)
            ·
              refine ⟨208922777279929771876997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139281851519953181251331 208922777279929771876997)
              ·
                refine ⟨39173020739986832226937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208922777279929771876997 39173020739986832226937)
                ·
                  refine ⟨29379765554990124170203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39173020739986832226937 29379765554990124170203)
                  ·
                    rfl

theorem cell20_64369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 2].length) (baseStart_64369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64369 prefixEnd_64369 := by exact prefixLift 64369
  have htrace : WordTrace (prefixWord ++ tailWord_64369) baseStart_64369 baseEnd_64369 := by
    simpa [prefixWord, tailWord_64369, baseEnd_64369] using wordTrace_append hprefix tailTrace_64369
  have hstable : (prefixWord ++ tailWord_64369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64369).length < 2 ^ (prefixWord ++ tailWord_64369).sum := by decide
  have hdescent : baseEnd_64369 < baseStart_64369 := by decide
  rcases family_descends (prefixWord ++ tailWord_64369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64407 : List Nat := [1, 1, 3, 3, 1, 2, 4, 3, 2]
def baseStart_64407 : Nat := 118140960795 + 64407 * 2 ^ 59
def prefixEnd_64407 : Nat := 4983230072969 + 3 ^ 40 * 64407 * 2
def baseEnd_64407 : Nat := 29397109790430880903381

theorem tailTrace_64407 : CollatzResearch.WordTrace tailWord_64407 prefixEnd_64407 29397109790430880903381 := by
  unfold tailWord_64407
  simp only [CollatzResearch.WordTrace]
  refine ⟨2349116277671913684967475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1566077518447942456644983 2349116277671913684967475)
  ·
    refine ⟨3523674416507870527451213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2349116277671913684967475 3523674416507870527451213)
    ·
      refine ⟨1321377906190451447794205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3523674416507870527451213 1321377906190451447794205)
      ·
        refine ⟨495516714821419292922827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1321377906190451447794205 495516714821419292922827)
        ·
          refine ⟨743275072232128939384241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495516714821419292922827 743275072232128939384241)
          ·
            refine ⟨557456304174096704538181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743275072232128939384241 557456304174096704538181)
            ·
              refine ⟨104523057032643132100909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 557456304174096704538181 104523057032643132100909)
              ·
                refine ⟨39196146387241174537841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104523057032643132100909 39196146387241174537841)
                ·
                  refine ⟨29397109790430880903381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39196146387241174537841 29397109790430880903381)
                  ·
                    rfl

theorem cell20_64407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 2].length) (baseStart_64407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64407 prefixEnd_64407 := by exact prefixLift 64407
  have htrace : WordTrace (prefixWord ++ tailWord_64407) baseStart_64407 baseEnd_64407 := by
    simpa [prefixWord, tailWord_64407, baseEnd_64407] using wordTrace_append hprefix tailTrace_64407
  have hstable : (prefixWord ++ tailWord_64407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64407).length < 2 ^ (prefixWord ++ tailWord_64407).sum := by decide
  have hdescent : baseEnd_64407 < baseStart_64407 := by decide
  rcases family_descends (prefixWord ++ tailWord_64407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64454 : List Nat := [6, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_64454 : Nat := 118140960795 + 64454 * 2 ^ 59
def prefixEnd_64454 : Nat := 4983230072969 + 3 ^ 40 * 64454 * 2
def baseEnd_64454 : Nat := 29418561871107606336523

theorem tailTrace_64454 : CollatzResearch.WordTrace tailWord_64454 prefixEnd_64454 29418561871107606336523 := by
  unfold tailWord_64454
  simp only [CollatzResearch.WordTrace]
  refine ⟨73463453390676272247763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1567220339001093807952277 73463453390676272247763)
  ·
    refine ⟨110195180086014408371645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73463453390676272247763 110195180086014408371645)
    ·
      refine ⟨41323192532255403139367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110195180086014408371645 41323192532255403139367)
      ·
        refine ⟨61984788798383104709051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41323192532255403139367 61984788798383104709051)
        ·
          refine ⟨92977183197574657063577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61984788798383104709051 92977183197574657063577)
          ·
            refine ⟨69732887398180992797683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92977183197574657063577 69732887398180992797683)
            ·
              refine ⟨104599331097271489196525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69732887398180992797683 104599331097271489196525)
              ·
                refine ⟨39224749161476808448697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104599331097271489196525 39224749161476808448697)
                ·
                  refine ⟨29418561871107606336523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39224749161476808448697 29418561871107606336523)
                  ·
                    rfl

theorem cell20_64454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_64454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64454 prefixEnd_64454 := by exact prefixLift 64454
  have htrace : WordTrace (prefixWord ++ tailWord_64454) baseStart_64454 baseEnd_64454 := by
    simpa [prefixWord, tailWord_64454, baseEnd_64454] using wordTrace_append hprefix tailTrace_64454
  have hstable : (prefixWord ++ tailWord_64454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64454).length < 2 ^ (prefixWord ++ tailWord_64454).sum := by decide
  have hdescent : baseEnd_64454 < baseStart_64454 := by decide
  rcases family_descends (prefixWord ++ tailWord_64454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64462 : List Nat := [4, 1, 1, 1, 2, 5, 1, 3, 2]
def baseStart_64462 : Nat := 118140960795 + 64462 * 2 ^ 59
def prefixEnd_64462 : Nat := 4983230072969 + 3 ^ 40 * 64462 * 2
def baseEnd_64462 : Nat := 29422213289095134069823

theorem tailTrace_64462 : CollatzResearch.WordTrace tailWord_64462 prefixEnd_64462 29422213289095134069823 := by
  unfold tailWord_64462
  simp only [CollatzResearch.WordTrace]
  refine ⟨293890286559082259777455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1567414861648438718813093 293890286559082259777455)
  ·
    refine ⟨440835429838623389666183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293890286559082259777455 440835429838623389666183)
    ·
      refine ⟨661253144757935084499275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440835429838623389666183 661253144757935084499275)
      ·
        refine ⟨991879717136902626748913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661253144757935084499275 991879717136902626748913)
        ·
          refine ⟨743909787852676970061685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 991879717136902626748913 743909787852676970061685)
          ·
            refine ⟨69741542611188465943283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 743909787852676970061685 69741542611188465943283)
            ·
              refine ⟨104612313916782698914925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69741542611188465943283 104612313916782698914925)
              ·
                refine ⟨39229617718793512093097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104612313916782698914925 39229617718793512093097)
                ·
                  refine ⟨29422213289095134069823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39229617718793512093097 29422213289095134069823)
                  ·
                    rfl

theorem cell20_64462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_64462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64462 prefixEnd_64462 := by exact prefixLift 64462
  have htrace : WordTrace (prefixWord ++ tailWord_64462) baseStart_64462 baseEnd_64462 := by
    simpa [prefixWord, tailWord_64462, baseEnd_64462] using wordTrace_append hprefix tailTrace_64462
  have hstable : (prefixWord ++ tailWord_64462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64462).length < 2 ^ (prefixWord ++ tailWord_64462).sum := by decide
  have hdescent : baseEnd_64462 < baseStart_64462 := by decide
  rcases family_descends (prefixWord ++ tailWord_64462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64473 : List Nat := [1, 2, 1, 2, 5, 3, 6]
def baseStart_64473 : Nat := 118140960795 + 64473 * 2 ^ 59
def prefixEnd_64473 : Nat := 4983230072969 + 3 ^ 40 * 64473 * 2
def baseEnd_64473 : Nat := 3269692665425331633679

theorem tailTrace_64473 : CollatzResearch.WordTrace tailWord_64473 prefixEnd_64473 3269692665425331633679 := by
  unfold tailWord_64473
  simp only [CollatzResearch.WordTrace]
  refine ⟨2351523495432806956870073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1567682330288537971246715 2351523495432806956870073)
  ·
    refine ⟨1763642621574605217652555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2351523495432806956870073 1763642621574605217652555)
    ·
      refine ⟨2645463932361907826478833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1763642621574605217652555 2645463932361907826478833)
      ·
        refine ⟨1984097949271430869859125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2645463932361907826478833 1984097949271430869859125)
        ·
          refine ⟨186009182744196644049293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1984097949271430869859125 186009182744196644049293)
          ·
            refine ⟨69753443529073741518485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186009182744196644049293 69753443529073741518485)
            ·
              refine ⟨3269692665425331633679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69753443529073741518485 3269692665425331633679)
              ·
                rfl

theorem cell20_64473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 6].length) (baseStart_64473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64473 prefixEnd_64473 := by exact prefixLift 64473
  have htrace : WordTrace (prefixWord ++ tailWord_64473) baseStart_64473 baseEnd_64473 := by
    simpa [prefixWord, tailWord_64473, baseEnd_64473] using wordTrace_append hprefix tailTrace_64473
  have hstable : (prefixWord ++ tailWord_64473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64473).length < 2 ^ (prefixWord ++ tailWord_64473).sum := by decide
  have hdescent : baseEnd_64473 < baseStart_64473 := by decide
  rcases family_descends (prefixWord ++ tailWord_64473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64497 : List Nat := [1, 2, 2, 2, 4, 2, 1, 3, 3]
def baseStart_64497 : Nat := 118140960795 + 64497 * 2 ^ 59
def prefixEnd_64497 : Nat := 4983230072969 + 3 ^ 40 * 64497 * 2
def baseEnd_64497 : Nat := 29438188242790567903013

theorem tailTrace_64497 : CollatzResearch.WordTrace tailWord_64497 prefixEnd_64497 29438188242790567903013 := by
  unfold tailWord_64497
  simp only [CollatzResearch.WordTrace]
  refine ⟨2352398847345859055743745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1568265898230572703829163 2352398847345859055743745)
  ·
    refine ⟨1764299135509394291807809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2352398847345859055743745 1764299135509394291807809)
    ·
      refine ⟨1323224351632045718855857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1764299135509394291807809 1323224351632045718855857)
      ·
        refine ⟨992418263724034289141893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1323224351632045718855857 992418263724034289141893)
        ·
          refine ⟨186078424448256429214105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 992418263724034289141893 186078424448256429214105)
          ·
            refine ⟨139558818336192321910579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186078424448256429214105 139558818336192321910579)
            ·
              refine ⟨209338227504288482865869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139558818336192321910579 209338227504288482865869)
              ·
                refine ⟨78501835314108181074701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209338227504288482865869 78501835314108181074701)
                ·
                  refine ⟨29438188242790567903013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78501835314108181074701 29438188242790567903013)
                  ·
                    rfl

theorem cell20_64497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_64497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64497 prefixEnd_64497 := by exact prefixLift 64497
  have htrace : WordTrace (prefixWord ++ tailWord_64497) baseStart_64497 baseEnd_64497 := by
    simpa [prefixWord, tailWord_64497, baseEnd_64497] using wordTrace_append hprefix tailTrace_64497
  have hstable : (prefixWord ++ tailWord_64497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64497).length < 2 ^ (prefixWord ++ tailWord_64497).sum := by decide
  have hdescent : baseEnd_64497 < baseStart_64497 := by decide
  rcases family_descends (prefixWord ++ tailWord_64497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64530 : List Nat := [3, 2, 5, 1, 2, 1, 2, 2, 2]
def baseStart_64530 : Nat := 118140960795 + 64530 * 2 ^ 59
def prefixEnd_64530 : Nat := 4983230072969 + 3 ^ 40 * 64530 * 2
def baseEnd_64530 : Nat := 29453250341989119802879

theorem tailTrace_64530 : CollatzResearch.WordTrace tailWord_64530 prefixEnd_64530 29453250341989119802879 := by
  unfold tailWord_64530
  simp only [CollatzResearch.WordTrace]
  refine ⟨588400614056576422923761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1569068304150870461130029 588400614056576422923761)
  ·
    refine ⟨441300460542432317192821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 588400614056576422923761 441300460542432317192821)
    ·
      refine ⟨41371918175853029736827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 441300460542432317192821 41371918175853029736827)
      ·
        refine ⟨62057877263779544605241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41371918175853029736827 62057877263779544605241)
        ·
          refine ⟨46543407947834658453931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62057877263779544605241 46543407947834658453931)
          ·
            refine ⟨69815111921751987680897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46543407947834658453931 69815111921751987680897)
            ·
              refine ⟨52361333941313990760673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69815111921751987680897 52361333941313990760673)
              ·
                refine ⟨39271000455985493070505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52361333941313990760673 39271000455985493070505)
                ·
                  refine ⟨29453250341989119802879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39271000455985493070505 29453250341989119802879)
                  ·
                    rfl

theorem cell20_64530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_64530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64530 prefixEnd_64530 := by exact prefixLift 64530
  have htrace : WordTrace (prefixWord ++ tailWord_64530) baseStart_64530 baseEnd_64530 := by
    simpa [prefixWord, tailWord_64530, baseEnd_64530] using wordTrace_append hprefix tailTrace_64530
  have hstable : (prefixWord ++ tailWord_64530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64530).length < 2 ^ (prefixWord ++ tailWord_64530).sum := by decide
  have hdescent : baseEnd_64530 < baseStart_64530 := by decide
  rcases family_descends (prefixWord ++ tailWord_64530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64535 : List Nat := [1, 1, 3, 5, 1, 1, 1, 4, 3]
def baseStart_64535 : Nat := 118140960795 + 64535 * 2 ^ 59
def prefixEnd_64535 : Nat := 4983230072969 + 3 ^ 40 * 64535 * 2
def baseEnd_64535 : Nat := 29455532478231324636191

theorem tailTrace_64535 : CollatzResearch.WordTrace tailWord_64535 prefixEnd_64535 29455532478231324636191 := by
  unfold tailWord_64535
  simp only [CollatzResearch.WordTrace]
  refine ⟨2353784821208191545627059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1569189880805461030418039 2353784821208191545627059)
  ·
    refine ⟨3530677231812287318440589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2353784821208191545627059 3530677231812287318440589)
    ·
      refine ⟨1324003961929607744415221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3530677231812287318440589 1324003961929607744415221)
      ·
        refine ⟨124125371430900726038927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1324003961929607744415221 124125371430900726038927)
        ·
          refine ⟨186188057146351089058391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124125371430900726038927 186188057146351089058391)
          ·
            refine ⟨279282085719526633587587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186188057146351089058391 279282085719526633587587)
            ·
              refine ⟨418923128579289950381381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279282085719526633587587 418923128579289950381381)
              ·
                refine ⟨78548086608616865696509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 418923128579289950381381 78548086608616865696509)
                ·
                  refine ⟨29455532478231324636191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78548086608616865696509 29455532478231324636191)
                  ·
                    rfl

theorem cell20_64535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 3].length) (baseStart_64535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64535 prefixEnd_64535 := by exact prefixLift 64535
  have htrace : WordTrace (prefixWord ++ tailWord_64535) baseStart_64535 baseEnd_64535 := by
    simpa [prefixWord, tailWord_64535, baseEnd_64535] using wordTrace_append hprefix tailTrace_64535
  have hstable : (prefixWord ++ tailWord_64535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64535).length < 2 ^ (prefixWord ++ tailWord_64535).sum := by decide
  have hdescent : baseEnd_64535 < baseStart_64535 := by decide
  rcases family_descends (prefixWord ++ tailWord_64535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64539 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 9]
def baseStart_64539 : Nat := 118140960795 + 64539 * 2 ^ 59
def prefixEnd_64539 : Nat := 4983230072969 + 3 ^ 40 * 64539 * 2
def baseEnd_64539 : Nat := 29457358187225088502841

theorem tailTrace_64539 : CollatzResearch.WordTrace tailWord_64539 prefixEnd_64539 29457358187225088502841 := by
  unfold tailWord_64539
  simp only [CollatzResearch.WordTrace]
  refine ⟨2353930713193700228772671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1569287142129133485848447 2353930713193700228772671)
  ·
    refine ⟨3530896069790550343159007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2353930713193700228772671 3530896069790550343159007)
    ·
      refine ⟨5296344104685825514738511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3530896069790550343159007 5296344104685825514738511)
      ·
        refine ⟨7944516157028738272107767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5296344104685825514738511 7944516157028738272107767)
        ·
          refine ⟨11916774235543107408161651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7944516157028738272107767 11916774235543107408161651)
          ·
            refine ⟨17875161353314661112242477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11916774235543107408161651 17875161353314661112242477)
            ·
              refine ⟨6703185507492997917090929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17875161353314661112242477 6703185507492997917090929)
              ·
                refine ⟨5027389130619748437818197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6703185507492997917090929 5027389130619748437818197)
                ·
                  refine ⟨29457358187225088502841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5027389130619748437818197 29457358187225088502841)
                  ·
                    rfl

theorem cell20_64539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_64539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64539 prefixEnd_64539 := by exact prefixLift 64539
  have htrace : WordTrace (prefixWord ++ tailWord_64539) baseStart_64539 baseEnd_64539 := by
    simpa [prefixWord, tailWord_64539, baseEnd_64539] using wordTrace_append hprefix tailTrace_64539
  have hstable : (prefixWord ++ tailWord_64539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64539).length < 2 ^ (prefixWord ++ tailWord_64539).sum := by decide
  have hdescent : baseEnd_64539 < baseStart_64539 := by decide
  rcases family_descends (prefixWord ++ tailWord_64539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64556 : List Nat := [2, 2, 1, 1, 1, 2, 3, 5, 3]
def baseStart_64556 : Nat := 118140960795 + 64556 * 2 ^ 59
def prefixEnd_64556 : Nat := 4983230072969 + 3 ^ 40 * 64556 * 2
def baseEnd_64556 : Nat := 29465117450448584936105

theorem tailTrace_64556 : CollatzResearch.WordTrace tailWord_64556 prefixEnd_64556 29465117450448584936105 := by
  unfold tailWord_64556
  simp only [CollatzResearch.WordTrace]
  refine ⟨1177275377066056066070761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1569700502754741421427681 1177275377066056066070761)
  ·
    refine ⟨882956532799542049553071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1177275377066056066070761 882956532799542049553071)
    ·
      refine ⟨1324434799199313074329607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 882956532799542049553071 1324434799199313074329607)
      ·
        refine ⟨1986652198798969611494411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1324434799199313074329607 1986652198798969611494411)
        ·
          refine ⟨2979978298198454417241617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1986652198798969611494411 2979978298198454417241617)
          ·
            refine ⟨2234983723648840812931213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2979978298198454417241617 2234983723648840812931213)
            ·
              refine ⟨838118896368315304849205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2234983723648840812931213 838118896368315304849205)
              ·
                refine ⟨78573646534529559829613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 838118896368315304849205 78573646534529559829613)
                ·
                  refine ⟨29465117450448584936105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78573646534529559829613 29465117450448584936105)
                  ·
                    rfl

theorem cell20_64556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_64556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64556 prefixEnd_64556 := by exact prefixLift 64556
  have htrace : WordTrace (prefixWord ++ tailWord_64556) baseStart_64556 baseEnd_64556 := by
    simpa [prefixWord, tailWord_64556, baseEnd_64556] using wordTrace_append hprefix tailTrace_64556
  have hstable : (prefixWord ++ tailWord_64556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64556).length < 2 ^ (prefixWord ++ tailWord_64556).sum := by decide
  have hdescent : baseEnd_64556 < baseStart_64556 := by decide
  rcases family_descends (prefixWord ++ tailWord_64556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64570 : List Nat := [3, 1, 1, 1, 3, 1, 2, 8]
def baseStart_64570 : Nat := 118140960795 + 64570 * 2 ^ 59
def prefixEnd_64570 : Nat := 4983230072969 + 3 ^ 40 * 64570 * 2
def baseEnd_64570 : Nat := 9823835810642252823127

theorem tailTrace_64570 : CollatzResearch.WordTrace tailWord_64570 prefixEnd_64570 9823835810642252823127 := by
  unfold tailWord_64570
  simp only [CollatzResearch.WordTrace]
  refine ⟨588765344020348130787791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1570040917387595015434109 588765344020348130787791)
  ·
    refine ⟨883148016030522196181687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 588765344020348130787791 883148016030522196181687)
    ·
      refine ⟨1324722024045783294272531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 883148016030522196181687 1324722024045783294272531)
      ·
        refine ⟨1987083036068674941408797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1324722024045783294272531 1987083036068674941408797)
        ·
          refine ⟨745156138525753103028299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1987083036068674941408797 745156138525753103028299)
          ·
            refine ⟨1117734207788629654542449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745156138525753103028299 1117734207788629654542449)
            ·
              refine ⟨838300655841472240906837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1117734207788629654542449 838300655841472240906837)
              ·
                refine ⟨9823835810642252823127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 838300655841472240906837 9823835810642252823127)
                ·
                  rfl

theorem cell20_64570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_64570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64570 prefixEnd_64570 := by exact prefixLift 64570
  have htrace : WordTrace (prefixWord ++ tailWord_64570) baseStart_64570 baseEnd_64570 := by
    simpa [prefixWord, tailWord_64570, baseEnd_64570] using wordTrace_append hprefix tailTrace_64570
  have hstable : (prefixWord ++ tailWord_64570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64570).length < 2 ^ (prefixWord ++ tailWord_64570).sum := by decide
  have hdescent : baseEnd_64570 < baseStart_64570 := by decide
  rcases family_descends (prefixWord ++ tailWord_64570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64608 : List Nat := [2, 1, 1, 3, 2, 2, 2, 7]
def baseStart_64608 : Nat := 118140960795 + 64608 * 2 ^ 59
def prefixEnd_64608 : Nat := 4983230072969 + 3 ^ 40 * 64608 * 2
def baseEnd_64608 : Nat := 9829617222455838400853

theorem tailTrace_64608 : CollatzResearch.WordTrace tailWord_64608 prefixEnd_64608 9829617222455838400853 := by
  unfold tailWord_64608
  simp only [CollatzResearch.WordTrace]
  refine ⟨1178223674971862506517239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1570964899962483342022985 1178223674971862506517239)
  ·
    refine ⟨1767335512457793759775859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1178223674971862506517239 1767335512457793759775859)
    ·
      refine ⟨2651003268686690639663789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1767335512457793759775859 2651003268686690639663789)
      ·
        refine ⟨994126225757508989873921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2651003268686690639663789 994126225757508989873921)
        ·
          refine ⟨745594669318131742405441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 994126225757508989873921 745594669318131742405441)
          ·
            refine ⟨559196001988598806804081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745594669318131742405441 559196001988598806804081)
            ·
              refine ⟨419397001491449105103061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 559196001988598806804081 419397001491449105103061)
              ·
                refine ⟨9829617222455838400853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 419397001491449105103061 9829617222455838400853)
                ·
                  rfl

theorem cell20_64608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_64608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64608 prefixEnd_64608 := by exact prefixLift 64608
  have htrace : WordTrace (prefixWord ++ tailWord_64608) baseStart_64608 baseEnd_64608 := by
    simpa [prefixWord, tailWord_64608, baseEnd_64608] using wordTrace_append hprefix tailTrace_64608
  have hstable : (prefixWord ++ tailWord_64608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64608).length < 2 ^ (prefixWord ++ tailWord_64608).sum := by decide
  have hdescent : baseEnd_64608 < baseStart_64608 := by decide
  rcases family_descends (prefixWord ++ tailWord_64608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64618 : List Nat := [3, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_64618 : Nat := 118140960795 + 64618 * 2 ^ 59
def prefixEnd_64618 : Nat := 4983230072969 + 3 ^ 40 * 64618 * 2
def baseEnd_64618 : Nat := 29493415939851924869185

theorem tailTrace_64618 : CollatzResearch.WordTrace tailWord_64618 prefixEnd_64618 29493415939851924869185 := by
  unfold tailWord_64618
  simp only [CollatzResearch.WordTrace]
  refine ⟨589203019976874180224627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1571208053271664480599005 589203019976874180224627)
  ·
    refine ⟨883804529965311270336941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 589203019976874180224627 883804529965311270336941)
    ·
      refine ⟨331426698736991726376353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 883804529965311270336941 331426698736991726376353)
      ·
        refine ⟨248570024052743794782265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331426698736991726376353 248570024052743794782265)
        ·
          refine ⟨186427518039557846086699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248570024052743794782265 186427518039557846086699)
          ·
            refine ⟨279641277059336769130049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186427518039557846086699 279641277059336769130049)
            ·
              refine ⟨209730957794502576847537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279641277059336769130049 209730957794502576847537)
              ·
                refine ⟨157298218345876932635653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209730957794502576847537 157298218345876932635653)
                ·
                  refine ⟨29493415939851924869185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157298218345876932635653 29493415939851924869185)
                  ·
                    rfl

theorem cell20_64618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_64618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64618 prefixEnd_64618 := by exact prefixLift 64618
  have htrace : WordTrace (prefixWord ++ tailWord_64618) baseStart_64618 baseEnd_64618 := by
    simpa [prefixWord, tailWord_64618, baseEnd_64618] using wordTrace_append hprefix tailTrace_64618
  have hstable : (prefixWord ++ tailWord_64618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64618).length < 2 ^ (prefixWord ++ tailWord_64618).sum := by decide
  have hdescent : baseEnd_64618 < baseStart_64618 := by decide
  rcases family_descends (prefixWord ++ tailWord_64618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64638 : List Nat := [4, 2, 4, 1, 1, 2, 6]
def baseStart_64638 : Nat := 118140960795 + 64638 * 2 ^ 59
def prefixEnd_64638 : Nat := 4983230072969 + 3 ^ 40 * 64638 * 2
def baseEnd_64638 : Nat := 3278060498313416022493

theorem tailTrace_64638 : CollatzResearch.WordTrace tailWord_64638 prefixEnd_64638 3278060498313416022493 := by
  unfold tailWord_64638
  simp only [CollatzResearch.WordTrace]
  refine ⟨294692692479380017078321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1571694359890026757751045 294692692479380017078321)
  ·
    refine ⟨221019519359535012808741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294692692479380017078321 221019519359535012808741)
    ·
      refine ⟨41441159879912814901639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221019519359535012808741 41441159879912814901639)
      ·
        refine ⟨62161739819869222352459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41441159879912814901639 62161739819869222352459)
        ·
          refine ⟨93242609729803833528689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62161739819869222352459 93242609729803833528689)
          ·
            refine ⟨69931957297352875146517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93242609729803833528689 69931957297352875146517)
            ·
              refine ⟨3278060498313416022493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69931957297352875146517 3278060498313416022493)
              ·
                rfl

theorem cell20_64638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 6].length) (baseStart_64638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64638 prefixEnd_64638 := by exact prefixLift 64638
  have htrace : WordTrace (prefixWord ++ tailWord_64638) baseStart_64638 baseEnd_64638 := by
    simpa [prefixWord, tailWord_64638, baseEnd_64638] using wordTrace_append hprefix tailTrace_64638
  have hstable : (prefixWord ++ tailWord_64638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64638).length < 2 ^ (prefixWord ++ tailWord_64638).sum := by decide
  have hdescent : baseEnd_64638 < baseStart_64638 := by decide
  rcases family_descends (prefixWord ++ tailWord_64638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64663 : List Nat := [1, 1, 3, 3, 3, 2, 2, 5]
def baseStart_64663 : Nat := 118140960795 + 64663 * 2 ^ 59
def prefixEnd_64663 : Nat := 4983230072969 + 3 ^ 40 * 64663 * 2
def baseEnd_64663 : Nat := 9837985055343922789667

theorem tailTrace_64663 : CollatzResearch.WordTrace tailWord_64663 prefixEnd_64663 9837985055343922789667 := by
  unfold tailWord_64663
  simp only [CollatzResearch.WordTrace]
  refine ⟨2358453364744469406286643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1572302243162979604191095 2358453364744469406286643)
  ·
    refine ⟨3537680047116704109429965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2358453364744469406286643 3537680047116704109429965)
    ·
      refine ⟨1326630017668764041036237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3537680047116704109429965 1326630017668764041036237)
      ·
        refine ⟨497486256625786515388589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1326630017668764041036237 497486256625786515388589)
        ·
          refine ⟨186557346234669943270721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 497486256625786515388589 186557346234669943270721)
          ·
            refine ⟨139918009676002457453041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186557346234669943270721 139918009676002457453041)
            ·
              refine ⟨104938507257001843089781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139918009676002457453041 104938507257001843089781)
              ·
                refine ⟨9837985055343922789667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104938507257001843089781 9837985055343922789667)
                ·
                  rfl

theorem cell20_64663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 5].length) (baseStart_64663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64663 prefixEnd_64663 := by exact prefixLift 64663
  have htrace : WordTrace (prefixWord ++ tailWord_64663) baseStart_64663 baseEnd_64663 := by
    simpa [prefixWord, tailWord_64663, baseEnd_64663] using wordTrace_append hprefix tailTrace_64663
  have hstable : (prefixWord ++ tailWord_64663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64663).length < 2 ^ (prefixWord ++ tailWord_64663).sum := by decide
  have hdescent : baseEnd_64663 < baseStart_64663 := by decide
  rcases family_descends (prefixWord ++ tailWord_64663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64666 : List Nat := [3, 1, 1, 5, 1, 1, 4, 1, 3]
def baseStart_64666 : Nat := 118140960795 + 64666 * 2 ^ 59
def prefixEnd_64666 : Nat := 4983230072969 + 3 ^ 40 * 64666 * 2
def baseEnd_64666 : Nat := 29515324447777091268989

theorem tailTrace_64666 : CollatzResearch.WordTrace tailWord_64666 prefixEnd_64666 29515324447777091268989 := by
  unfold tailWord_64666
  simp only [CollatzResearch.WordTrace]
  refine ⟨589640695933400229661463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1572375189155733945763901 589640695933400229661463)
  ·
    refine ⟨884461043900100344492195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 589640695933400229661463 884461043900100344492195)
    ·
      refine ⟨1326691565850150516738293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 884461043900100344492195 1326691565850150516738293)
      ·
        refine ⟨124377334298451610944215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1326691565850150516738293 124377334298451610944215)
        ·
          refine ⟨186566001447677416416323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124377334298451610944215 186566001447677416416323)
          ·
            refine ⟨279849002171516124624485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186566001447677416416323 279849002171516124624485)
            ·
              refine ⟨52471687907159273367091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 279849002171516124624485 52471687907159273367091)
              ·
                refine ⟨78707531860738910050637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52471687907159273367091 78707531860738910050637)
                ·
                  refine ⟨29515324447777091268989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78707531860738910050637 29515324447777091268989)
                  ·
                    rfl

theorem cell20_64666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_64666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64666 prefixEnd_64666 := by exact prefixLift 64666
  have htrace : WordTrace (prefixWord ++ tailWord_64666) baseStart_64666 baseEnd_64666 := by
    simpa [prefixWord, tailWord_64666, baseEnd_64666] using wordTrace_append hprefix tailTrace_64666
  have hstable : (prefixWord ++ tailWord_64666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64666).length < 2 ^ (prefixWord ++ tailWord_64666).sum := by decide
  have hdescent : baseEnd_64666 < baseStart_64666 := by decide
  rcases family_descends (prefixWord ++ tailWord_64666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64691 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 7]
def baseStart_64691 : Nat := 118140960795 + 64691 * 2 ^ 59
def prefixEnd_64691 : Nat := 4983230072969 + 3 ^ 40 * 64691 * 2
def baseEnd_64691 : Nat := 29526735128988115435553

theorem tailTrace_64691 : CollatzResearch.WordTrace tailWord_64691 prefixEnd_64691 29526735128988115435553 := by
  unfold tailWord_64691
  simp only [CollatzResearch.WordTrace]
  refine ⟨2359474608643030188305927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1572983072428686792203951 2359474608643030188305927)
  ·
    refine ⟨3539211912964545282458891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2359474608643030188305927 3539211912964545282458891)
    ·
      refine ⟨5308817869446817923688337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3539211912964545282458891 5308817869446817923688337)
      ·
        refine ⟨3981613402085113442766253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5308817869446817923688337 3981613402085113442766253)
        ·
          refine ⟨1493105025781917541037345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3981613402085113442766253 1493105025781917541037345)
          ·
            refine ⟨1119828769336438155778009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1493105025781917541037345 1119828769336438155778009)
            ·
              refine ⟨839871577002328616833507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1119828769336438155778009 839871577002328616833507)
              ·
                refine ⟨1259807365503492925250261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 839871577002328616833507 1259807365503492925250261)
                ·
                  refine ⟨29526735128988115435553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1259807365503492925250261 29526735128988115435553)
                  ·
                    rfl

theorem cell20_64691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_64691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64691 prefixEnd_64691 := by exact prefixLift 64691
  have htrace : WordTrace (prefixWord ++ tailWord_64691) baseStart_64691 baseEnd_64691 := by
    simpa [prefixWord, tailWord_64691, baseEnd_64691] using wordTrace_append hprefix tailTrace_64691
  have hstable : (prefixWord ++ tailWord_64691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64691).length < 2 ^ (prefixWord ++ tailWord_64691).sum := by decide
  have hdescent : baseEnd_64691 < baseStart_64691 := by decide
  rcases family_descends (prefixWord ++ tailWord_64691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64718 : List Nat := [4, 1, 1, 1, 5, 2, 1, 5]
def baseStart_64718 : Nat := 118140960795 + 64718 * 2 ^ 59
def prefixEnd_64718 : Nat := 4983230072969 + 3 ^ 40 * 64718 * 2
def baseEnd_64718 : Nat := 9846352888232007178481

theorem tailTrace_64718 : CollatzResearch.WordTrace tailWord_64718 prefixEnd_64718 9846352888232007178481 := by
  unfold tailWord_64718
  simp only [CollatzResearch.WordTrace]
  refine ⟨295057422443151724942351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1573639586363475866359205 295057422443151724942351)
  ·
    refine ⟨442586133664727587413527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295057422443151724942351 442586133664727587413527)
    ·
      refine ⟨663879200497091381120291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442586133664727587413527 663879200497091381120291)
      ·
        refine ⟨995818800745637071680437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663879200497091381120291 995818800745637071680437)
        ·
          refine ⟨93358012569903475470041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 995818800745637071680437 93358012569903475470041)
          ·
            refine ⟨70018509427427606602531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93358012569903475470041 70018509427427606602531)
            ·
              refine ⟨105027764141141409903797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70018509427427606602531 105027764141141409903797)
              ·
                refine ⟨9846352888232007178481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105027764141141409903797 9846352888232007178481)
                ·
                  rfl

theorem cell20_64718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_64718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64718 prefixEnd_64718 := by exact prefixLift 64718
  have htrace : WordTrace (prefixWord ++ tailWord_64718) baseStart_64718 baseEnd_64718 := by
    simpa [prefixWord, tailWord_64718, baseEnd_64718] using wordTrace_append hprefix tailTrace_64718
  have hstable : (prefixWord ++ tailWord_64718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64718).length < 2 ^ (prefixWord ++ tailWord_64718).sum := by decide
  have hdescent : baseEnd_64718 < baseStart_64718 := by decide
  rcases family_descends (prefixWord ++ tailWord_64718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64725 : List Nat := [1, 3, 2, 4, 1, 1, 2, 3, 3]
def baseStart_64725 : Nat := 118140960795 + 64725 * 2 ^ 59
def prefixEnd_64725 : Nat := 4983230072969 + 3 ^ 40 * 64725 * 2
def baseEnd_64725 : Nat := 29542253655435108302081

theorem tailTrace_64725 : CollatzResearch.WordTrace tailWord_64725 prefixEnd_64725 29542253655435108302081 := by
  unfold tailWord_64725
  simp only [CollatzResearch.WordTrace]
  refine ⟨2360714690519853995043629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1573809793679902663362419 2360714690519853995043629)
  ·
    refine ⟨885268008944945248141361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2360714690519853995043629 885268008944945248141361)
    ·
      refine ⟨663951006708708936106021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 885268008944945248141361 663951006708708936106021)
      ·
        refine ⟨124490813757882925519879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 663951006708708936106021 124490813757882925519879)
        ·
          refine ⟨186736220636824388279819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124490813757882925519879 186736220636824388279819)
          ·
            refine ⟨280104330955236582419729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186736220636824388279819 280104330955236582419729)
            ·
              refine ⟨210078248216427436814797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280104330955236582419729 210078248216427436814797)
              ·
                refine ⟨78779343081160288805549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210078248216427436814797 78779343081160288805549)
                ·
                  refine ⟨29542253655435108302081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78779343081160288805549 29542253655435108302081)
                  ·
                    rfl

theorem cell20_64725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_64725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64725 prefixEnd_64725 := by exact prefixLift 64725
  have htrace : WordTrace (prefixWord ++ tailWord_64725) baseStart_64725 baseEnd_64725 := by
    simpa [prefixWord, tailWord_64725, baseEnd_64725] using wordTrace_append hprefix tailTrace_64725
  have hstable : (prefixWord ++ tailWord_64725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64725).length < 2 ^ (prefixWord ++ tailWord_64725).sum := by decide
  have hdescent : baseEnd_64725 < baseStart_64725 := by decide
  rcases family_descends (prefixWord ++ tailWord_64725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64729 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 7]
def baseStart_64729 : Nat := 118140960795 + 64729 * 2 ^ 59
def prefixEnd_64729 : Nat := 4983230072969 + 3 ^ 40 * 64729 * 2
def baseEnd_64729 : Nat := 29544079364428872168731

theorem tailTrace_64729 : CollatzResearch.WordTrace tailWord_64729 prefixEnd_64729 29544079364428872168731 := by
  unfold tailWord_64729
  simp only [CollatzResearch.WordTrace]
  refine ⟨2360860582505362678189241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1573907055003575118792827 2360860582505362678189241)
  ·
    refine ⟨1770645436879022008641931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2360860582505362678189241 1770645436879022008641931)
    ·
      refine ⟨2655968155318533012962897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1770645436879022008641931 2655968155318533012962897)
      ·
        refine ⟨1991976116488899759722173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2655968155318533012962897 1991976116488899759722173)
        ·
          refine ⟨746991043683337409895815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1991976116488899759722173 746991043683337409895815)
          ·
            refine ⟨1120486565525006114843723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746991043683337409895815 1120486565525006114843723)
            ·
              refine ⟨1680729848287509172265585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120486565525006114843723 1680729848287509172265585)
              ·
                refine ⟨1260547386215631879199189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1680729848287509172265585 1260547386215631879199189)
                ·
                  refine ⟨29544079364428872168731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1260547386215631879199189 29544079364428872168731)
                  ·
                    rfl

theorem cell20_64729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_64729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64729 prefixEnd_64729 := by exact prefixLift 64729
  have htrace : WordTrace (prefixWord ++ tailWord_64729) baseStart_64729 baseEnd_64729 := by
    simpa [prefixWord, tailWord_64729, baseEnd_64729] using wordTrace_append hprefix tailTrace_64729
  have hstable : (prefixWord ++ tailWord_64729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64729).length < 2 ^ (prefixWord ++ tailWord_64729).sum := by decide
  have hdescent : baseEnd_64729 < baseStart_64729 := by decide
  rcases family_descends (prefixWord ++ tailWord_64729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64749 : List Nat := [1, 5, 1, 2, 2, 1, 1, 5, 2]
def baseStart_64749 : Nat := 118140960795 + 64749 * 2 ^ 59
def prefixEnd_64749 : Nat := 4983230072969 + 3 ^ 40 * 64749 * 2
def baseEnd_64749 : Nat := 29553207909397691501983

theorem tailTrace_64749 : CollatzResearch.WordTrace tailWord_64749 prefixEnd_64749 29553207909397691501983 := by
  unfold tailWord_64749
  simp only [CollatzResearch.WordTrace]
  refine ⟨2361590042432906093917301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1574393361621937395944867 2361590042432906093917301)
  ·
    refine ⟨221399066478084946304747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2361590042432906093917301 221399066478084946304747)
    ·
      refine ⟨332098599717127419457121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221399066478084946304747 332098599717127419457121)
      ·
        refine ⟨249073949787845564592841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332098599717127419457121 249073949787845564592841)
        ·
          refine ⟨186805462340884173444631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249073949787845564592841 186805462340884173444631)
          ·
            refine ⟨280208193511326260166947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186805462340884173444631 280208193511326260166947)
            ·
              refine ⟨420312290266989390250421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280208193511326260166947 420312290266989390250421)
              ·
                refine ⟨39404277212530255335977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 420312290266989390250421 39404277212530255335977)
                ·
                  refine ⟨29553207909397691501983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39404277212530255335977 29553207909397691501983)
                  ·
                    rfl

theorem cell20_64749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_64749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64749 prefixEnd_64749 := by exact prefixLift 64749
  have htrace : WordTrace (prefixWord ++ tailWord_64749) baseStart_64749 baseEnd_64749 := by
    simpa [prefixWord, tailWord_64749, baseEnd_64749] using wordTrace_append hprefix tailTrace_64749
  have hstable : (prefixWord ++ tailWord_64749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64749).length < 2 ^ (prefixWord ++ tailWord_64749).sum := by decide
  have hdescent : baseEnd_64749 < baseStart_64749 := by decide
  rcases family_descends (prefixWord ++ tailWord_64749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64791 : List Nat := [1, 1, 3, 4, 1, 1, 1, 4, 4]
def baseStart_64791 : Nat := 118140960795 + 64791 * 2 ^ 59
def prefixEnd_64791 : Nat := 4983230072969 + 3 ^ 40 * 64791 * 2
def baseEnd_64791 : Nat := 29572377853832212101811

theorem tailTrace_64791 : CollatzResearch.WordTrace tailWord_64791 prefixEnd_64791 29572377853832212101811 := by
  unfold tailWord_64791
  simp only [CollatzResearch.WordTrace]
  refine ⟨2363121908280747266946227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1575414605520498177964151 2363121908280747266946227)
  ·
    refine ⟨3544682862421120900419341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2363121908280747266946227 3544682862421120900419341)
    ·
      refine ⟨1329256073407920337657253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3544682862421120900419341 1329256073407920337657253)
      ·
        refine ⟨249235513763985063310735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1329256073407920337657253 249235513763985063310735)
        ·
          refine ⟨373853270645977594966103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249235513763985063310735 373853270645977594966103)
          ·
            refine ⟨560779905968966392449155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373853270645977594966103 560779905968966392449155)
            ·
              refine ⟨841169858953449588673733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560779905968966392449155 841169858953449588673733)
              ·
                refine ⟨157719348553771797876325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 841169858953449588673733 157719348553771797876325)
                ·
                  refine ⟨29572377853832212101811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157719348553771797876325 29572377853832212101811)
                  ·
                    rfl

theorem cell20_64791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_64791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64791 prefixEnd_64791 := by exact prefixLift 64791
  have htrace : WordTrace (prefixWord ++ tailWord_64791) baseStart_64791 baseEnd_64791 := by
    simpa [prefixWord, tailWord_64791, baseEnd_64791] using wordTrace_append hprefix tailTrace_64791
  have hstable : (prefixWord ++ tailWord_64791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64791).length < 2 ^ (prefixWord ++ tailWord_64791).sum := by decide
  have hdescent : baseEnd_64791 < baseStart_64791 := by decide
  rcases family_descends (prefixWord ++ tailWord_64791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64794 : List Nat := [3, 1, 1, 3, 3, 3, 2, 4]
def baseStart_64794 : Nat := 118140960795 + 64794 * 2 ^ 59
def prefixEnd_64794 : Nat := 4983230072969 + 3 ^ 40 * 64794 * 2
def baseEnd_64794 : Nat := 9857915711859178333933

theorem tailTrace_64794 : CollatzResearch.WordTrace tailWord_64794 prefixEnd_64794 9857915711859178333933 := by
  unfold tailWord_64794
  simp only [CollatzResearch.WordTrace]
  refine ⟨590807831817469694826359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1575487551513252519536957 590807831817469694826359)
  ·
    refine ⟨886211747726204542239539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 590807831817469694826359 886211747726204542239539)
    ·
      refine ⟨1329317621589306813359309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 886211747726204542239539 1329317621589306813359309)
      ·
        refine ⟨498494108095990055009741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1329317621589306813359309 498494108095990055009741)
        ·
          refine ⟨186935290535996270628653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498494108095990055009741 186935290535996270628653)
          ·
            refine ⟨70100733950998601485745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186935290535996270628653 70100733950998601485745)
            ·
              refine ⟨52575550463248951114309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70100733950998601485745 52575550463248951114309)
              ·
                refine ⟨9857915711859178333933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52575550463248951114309 9857915711859178333933)
                ·
                  rfl

theorem cell20_64794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_64794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64794 prefixEnd_64794 := by exact prefixLift 64794
  have htrace : WordTrace (prefixWord ++ tailWord_64794) baseStart_64794 baseEnd_64794 := by
    simpa [prefixWord, tailWord_64794, baseEnd_64794] using wordTrace_append hprefix tailTrace_64794
  have hstable : (prefixWord ++ tailWord_64794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64794).length < 2 ^ (prefixWord ++ tailWord_64794).sum := by decide
  have hdescent : baseEnd_64794 < baseStart_64794 := by decide
  rcases family_descends (prefixWord ++ tailWord_64794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64825 : List Nat := [1, 2, 1, 6, 2, 2, 1, 1, 4]
def baseStart_64825 : Nat := 118140960795 + 64825 * 2 ^ 59
def prefixEnd_64825 : Nat := 4983230072969 + 3 ^ 40 * 64825 * 2
def baseEnd_64825 : Nat := 29587896380279204968339

theorem tailTrace_64825 : CollatzResearch.WordTrace tailWord_64825 prefixEnd_64825 29587896380279204968339 := by
  unfold tailWord_64825
  simp only [CollatzResearch.WordTrace]
  refine ⟨2364361990157571073683929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1576241326771714049122619 2364361990157571073683929)
  ·
    refine ⟨1773271492618178305262947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2364361990157571073683929 1773271492618178305262947)
    ·
      refine ⟨2659907238927267457894421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1773271492618178305262947 2659907238927267457894421)
      ·
        refine ⟨124683151824715662088801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2659907238927267457894421 124683151824715662088801)
        ·
          refine ⟨93512363868536746566601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124683151824715662088801 93512363868536746566601)
          ·
            refine ⟨70134272901402559924951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93512363868536746566601 70134272901402559924951)
            ·
              refine ⟨105201409352103839887427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70134272901402559924951 105201409352103839887427)
              ·
                refine ⟨157802114028155759831141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105201409352103839887427 157802114028155759831141)
                ·
                  refine ⟨29587896380279204968339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157802114028155759831141 29587896380279204968339)
                  ·
                    rfl

theorem cell20_64825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 4].length) (baseStart_64825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64825 prefixEnd_64825 := by exact prefixLift 64825
  have htrace : WordTrace (prefixWord ++ tailWord_64825) baseStart_64825 baseEnd_64825 := by
    simpa [prefixWord, tailWord_64825, baseEnd_64825] using wordTrace_append hprefix tailTrace_64825
  have hstable : (prefixWord ++ tailWord_64825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64825).length < 2 ^ (prefixWord ++ tailWord_64825).sum := by decide
  have hdescent : baseEnd_64825 < baseStart_64825 := by decide
  rcases family_descends (prefixWord ++ tailWord_64825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64839 : List Nat := [1, 1, 4, 1, 2, 3, 4, 1, 3]
def baseStart_64839 : Nat := 118140960795 + 64839 * 2 ^ 59
def prefixEnd_64839 : Nat := 4983230072969 + 3 ^ 40 * 64839 * 2
def baseEnd_64839 : Nat := 29594286361757378501615

theorem tailTrace_64839 : CollatzResearch.WordTrace tailWord_64839 prefixEnd_64839 29594286361757378501615 := by
  unfold tailWord_64839
  simp only [CollatzResearch.WordTrace]
  refine ⟨2364872612106851464693571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1576581741404567643129047 2364872612106851464693571)
  ·
    refine ⟨3547308918160277197040357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2364872612106851464693571 3547308918160277197040357)
    ·
      refine ⟨665120422155051974445067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3547308918160277197040357 665120422155051974445067)
      ·
        refine ⟨997680633232577961667601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665120422155051974445067 997680633232577961667601)
        ·
          refine ⟨748260474924433471250701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 997680633232577961667601 748260474924433471250701)
          ·
            refine ⟨280597678096662551719013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 748260474924433471250701 280597678096662551719013)
            ·
              refine ⟨52612064643124228447315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280597678096662551719013 52612064643124228447315)
              ·
                refine ⟨78918096964686342670973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52612064643124228447315 78918096964686342670973)
                ·
                  refine ⟨29594286361757378501615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78918096964686342670973 29594286361757378501615)
                  ·
                    rfl

theorem cell20_64839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 3].length) (baseStart_64839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64839 prefixEnd_64839 := by exact prefixLift 64839
  have htrace : WordTrace (prefixWord ++ tailWord_64839) baseStart_64839 baseEnd_64839 := by
    simpa [prefixWord, tailWord_64839, baseEnd_64839] using wordTrace_append hprefix tailTrace_64839
  have hstable : (prefixWord ++ tailWord_64839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64839).length < 2 ^ (prefixWord ++ tailWord_64839).sum := by decide
  have hdescent : baseEnd_64839 < baseStart_64839 := by decide
  rcases family_descends (prefixWord ++ tailWord_64839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64874 : List Nat := [3, 1, 3, 3, 10]
def baseStart_64874 : Nat := 118140960795 + 64874 * 2 ^ 59
def prefixEnd_64874 : Nat := 4983230072969 + 3 ^ 40 * 64874 * 2
def baseEnd_64874 : Nat := 365558781672256942405

theorem tailTrace_64874 : CollatzResearch.WordTrace tailWord_64874 prefixEnd_64874 365558781672256942405 := by
  unfold tailWord_64874
  simp only [CollatzResearch.WordTrace]
  refine ⟨591537291745013110554419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1577432777986701628145117 591537291745013110554419)
  ·
    refine ⟨887305937617519665831629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 591537291745013110554419 887305937617519665831629)
    ·
      refine ⟨332739726606569874686861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 887305937617519665831629 332739726606569874686861)
      ·
        refine ⟨124777397477463703007573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332739726606569874686861 124777397477463703007573)
        ·
          refine ⟨365558781672256942405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 124777397477463703007573 365558781672256942405)
          ·
            rfl

theorem cell20_64874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 10].length) (baseStart_64874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64874 prefixEnd_64874 := by exact prefixLift 64874
  have htrace : WordTrace (prefixWord ++ tailWord_64874) baseStart_64874 baseEnd_64874 := by
    simpa [prefixWord, tailWord_64874, baseEnd_64874] using wordTrace_append hprefix tailTrace_64874
  have hstable : (prefixWord ++ tailWord_64874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64874).length < 2 ^ (prefixWord ++ tailWord_64874).sum := by decide
  have hdescent : baseEnd_64874 < baseStart_64874 := by decide
  rcases family_descends (prefixWord ++ tailWord_64874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64877 : List Nat := [1, 5, 1, 1, 1, 4, 2, 2, 3]
def baseStart_64877 : Nat := 118140960795 + 64877 * 2 ^ 59
def prefixEnd_64877 : Nat := 4983230072969 + 3 ^ 40 * 64877 * 2
def baseEnd_64877 : Nat := 29611630597198135234793

theorem tailTrace_64877 : CollatzResearch.WordTrace tailWord_64877 prefixEnd_64877 29611630597198135234793 := by
  unfold tailWord_64877
  simp only [CollatzResearch.WordTrace]
  refine ⟨2366258585969183954576885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1577505723979455969717923 2366258585969183954576885)
  ·
    refine ⟨221836742434610995741583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2366258585969183954576885 221836742434610995741583)
    ·
      refine ⟨332755113651916493612375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221836742434610995741583 332755113651916493612375)
      ·
        refine ⟨499132670477874740418563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332755113651916493612375 499132670477874740418563)
        ·
          refine ⟨748699005716812110627845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499132670477874740418563 748699005716812110627845)
          ·
            refine ⟨140381063571902270742721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 748699005716812110627845 140381063571902270742721)
            ·
              refine ⟨105285797678926703057041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140381063571902270742721 105285797678926703057041)
              ·
                refine ⟨78964348259195027292781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105285797678926703057041 78964348259195027292781)
                ·
                  refine ⟨29611630597198135234793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78964348259195027292781 29611630597198135234793)
                  ·
                    rfl

theorem cell20_64877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_64877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64877 prefixEnd_64877 := by exact prefixLift 64877
  have htrace : WordTrace (prefixWord ++ tailWord_64877) baseStart_64877 baseEnd_64877 := by
    simpa [prefixWord, tailWord_64877, baseEnd_64877] using wordTrace_append hprefix tailTrace_64877
  have hstable : (prefixWord ++ tailWord_64877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64877).length < 2 ^ (prefixWord ++ tailWord_64877).sum := by decide
  have hdescent : baseEnd_64877 < baseStart_64877 := by decide
  rcases family_descends (prefixWord ++ tailWord_64877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64881 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 5]
def baseStart_64881 : Nat := 118140960795 + 64881 * 2 ^ 59
def prefixEnd_64881 : Nat := 4983230072969 + 3 ^ 40 * 64881 * 2
def baseEnd_64881 : Nat := 29613456306191899101443

theorem tailTrace_64881 : CollatzResearch.WordTrace tailWord_64881 prefixEnd_64881 29613456306191899101443 := by
  unfold tailWord_64881
  simp only [CollatzResearch.WordTrace]
  refine ⟨2366404477954692637722497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1577602985303128425148331 2366404477954692637722497)
  ·
    refine ⟨1774803358466019478291873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2366404477954692637722497 1774803358466019478291873)
    ·
      refine ⟨1331102518849514608718905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1774803358466019478291873 1331102518849514608718905)
      ·
        refine ⟨998326889137135956539179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1331102518849514608718905 998326889137135956539179)
        ·
          refine ⟨1497490333705703934808769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998326889137135956539179 1497490333705703934808769)
          ·
            refine ⟨1123117750279277951106577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1497490333705703934808769 1123117750279277951106577)
            ·
              refine ⟨842338312709458463329933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123117750279277951106577 842338312709458463329933)
              ·
                refine ⟨315876867266046923748725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 842338312709458463329933 315876867266046923748725)
                ·
                  refine ⟨29613456306191899101443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 315876867266046923748725 29613456306191899101443)
                  ·
                    rfl

theorem cell20_64881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_64881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64881 prefixEnd_64881 := by exact prefixLift 64881
  have htrace : WordTrace (prefixWord ++ tailWord_64881) baseStart_64881 baseEnd_64881 := by
    simpa [prefixWord, tailWord_64881, baseEnd_64881] using wordTrace_append hprefix tailTrace_64881
  have hstable : (prefixWord ++ tailWord_64881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64881).length < 2 ^ (prefixWord ++ tailWord_64881).sum := by decide
  have hdescent : baseEnd_64881 < baseStart_64881 := by decide
  rcases family_descends (prefixWord ++ tailWord_64881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64888 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 10]
def baseStart_64888 : Nat := 118140960795 + 64888 * 2 ^ 59
def prefixEnd_64888 : Nat := 4983230072969 + 3 ^ 40 * 64888 * 2
def baseEnd_64888 : Nat := 29616651296930985868081

theorem tailTrace_64888 : CollatzResearch.WordTrace tailWord_64888 prefixEnd_64888 29616651296930985868081 := by
  unfold tailWord_64888
  simp only [CollatzResearch.WordTrace]
  refine ⟨1183329894464666416613659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1577773192619555222151545 1183329894464666416613659)
  ·
    refine ⟨1774994841696999624920489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1183329894464666416613659 1774994841696999624920489)
    ·
      refine ⟨1331246131272749718690367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1774994841696999624920489 1331246131272749718690367)
      ·
        refine ⟨1996869196909124578035551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1331246131272749718690367 1996869196909124578035551)
        ·
          refine ⟨2995303795363686867053327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1996869196909124578035551 2995303795363686867053327)
          ·
            refine ⟨4492955693045530300579991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2995303795363686867053327 4492955693045530300579991)
            ·
              refine ⟨6739433539568295450869987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4492955693045530300579991 6739433539568295450869987)
              ·
                refine ⟨10109150309352443176304981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6739433539568295450869987 10109150309352443176304981)
                ·
                  refine ⟨29616651296930985868081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 10109150309352443176304981 29616651296930985868081)
                  ·
                    rfl

theorem cell20_64888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_64888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64888 prefixEnd_64888 := by exact prefixLift 64888
  have htrace : WordTrace (prefixWord ++ tailWord_64888) baseStart_64888 baseEnd_64888 := by
    simpa [prefixWord, tailWord_64888, baseEnd_64888] using wordTrace_append hprefix tailTrace_64888
  have hstable : (prefixWord ++ tailWord_64888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64888).length < 2 ^ (prefixWord ++ tailWord_64888).sum := by decide
  have hdescent : baseEnd_64888 < baseStart_64888 := by decide
  rcases family_descends (prefixWord ++ tailWord_64888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64919 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 5]
def baseStart_64919 : Nat := 118140960795 + 64919 * 2 ^ 59
def prefixEnd_64919 : Nat := 4983230072969 + 3 ^ 40 * 64919 * 2
def baseEnd_64919 : Nat := 29630800541632655834621

theorem tailTrace_64919 : CollatzResearch.WordTrace tailWord_64919 prefixEnd_64919 29630800541632655834621 := by
  unfold tailWord_64919
  simp only [CollatzResearch.WordTrace]
  refine ⟨2367790451817025127605811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1578526967878016751737207 2367790451817025127605811)
  ·
    refine ⟨3551685677725537691408717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2367790451817025127605811 3551685677725537691408717)
    ·
      refine ⟨1331882129147076634278269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3551685677725537691408717 1331882129147076634278269)
      ·
        refine ⟨499455798430153737854351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1331882129147076634278269 499455798430153737854351)
        ·
          refine ⟨749183697645230606781527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499455798430153737854351 749183697645230606781527)
          ·
            refine ⟨1123775546467845910172291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749183697645230606781527 1123775546467845910172291)
            ·
              refine ⟨1685663319701768865258437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123775546467845910172291 1685663319701768865258437)
              ·
                refine ⟨316061872444081662235957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1685663319701768865258437 316061872444081662235957)
                ·
                  refine ⟨29630800541632655834621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 316061872444081662235957 29630800541632655834621)
                  ·
                    rfl

theorem cell20_64919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_64919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_64919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_64919 prefixEnd_64919 := by exact prefixLift 64919
  have htrace : WordTrace (prefixWord ++ tailWord_64919) baseStart_64919 baseEnd_64919 := by
    simpa [prefixWord, tailWord_64919, baseEnd_64919] using wordTrace_append hprefix tailTrace_64919
  have hstable : (prefixWord ++ tailWord_64919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64919).length < 2 ^ (prefixWord ++ tailWord_64919).sum := by decide
  have hdescent : baseEnd_64919 < baseStart_64919 := by decide
  rcases family_descends (prefixWord ++ tailWord_64919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65047 : List Nat := [1, 1, 3, 15]
def baseStart_65047 : Nat := 118140960795 + 65047 * 2 ^ 59
def prefixEnd_65047 : Nat := 4983230072969 + 3 ^ 40 * 65047 * 2
def baseEnd_65047 : Nat := 122177873372152673117

theorem tailTrace_65047 : CollatzResearch.WordTrace tailWord_65047 prefixEnd_65047 122177873372152673117 := by
  unfold tailWord_65047
  simp only [CollatzResearch.WordTrace]
  refine ⟨2372458995353302988265395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1581639330235535325510263 2372458995353302988265395)
  ·
    refine ⟨3558688493029954482398093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2372458995353302988265395 3558688493029954482398093)
    ·
      refine ⟨1334508184886232930899285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3558688493029954482398093 1334508184886232930899285)
      ·
        refine ⟨122177873372152673117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 1334508184886232930899285 122177873372152673117)
        ·
          rfl

theorem cell20_65047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 15].length) (baseStart_65047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65047 prefixEnd_65047 := by exact prefixLift 65047
  have htrace : WordTrace (prefixWord ++ tailWord_65047) baseStart_65047 baseEnd_65047 := by
    simpa [prefixWord, tailWord_65047, baseEnd_65047] using wordTrace_append hprefix tailTrace_65047
  have hstable : (prefixWord ++ tailWord_65047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65047).length < 2 ^ (prefixWord ++ tailWord_65047).sum := by decide
  have hdescent : baseEnd_65047 < baseStart_65047 := by decide
  rcases family_descends (prefixWord ++ tailWord_65047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65081 : List Nat := [1, 2, 1, 5, 1, 3, 3, 4]
def baseStart_65081 : Nat := 118140960795 + 65081 * 2 ^ 59
def prefixEnd_65081 : Nat := 4983230072969 + 3 ^ 40 * 65081 * 2
def baseEnd_65081 : Nat := 9901580585293364144653

theorem tailTrace_65081 : CollatzResearch.WordTrace tailWord_65081 prefixEnd_65081 9901580585293364144653 := by
  unfold tailWord_65081
  simp only [CollatzResearch.WordTrace]
  refine ⟨2373699077230126795003097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1582466051486751196668731 2373699077230126795003097)
  ·
    refine ⟨1780274307922595096252323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2373699077230126795003097 1780274307922595096252323)
    ·
      refine ⟨2670411461883892644378485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1780274307922595096252323 2670411461883892644378485)
      ·
        refine ⟨250351074551614935410483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2670411461883892644378485 250351074551614935410483)
        ·
          refine ⟨375526611827422403115725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250351074551614935410483 375526611827422403115725)
          ·
            refine ⟨140822479435283401168397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375526611827422403115725 140822479435283401168397)
            ·
              refine ⟨52808429788231275438149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140822479435283401168397 52808429788231275438149)
              ·
                refine ⟨9901580585293364144653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52808429788231275438149 9901580585293364144653)
                ·
                  rfl

theorem cell20_65081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 4].length) (baseStart_65081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65081 prefixEnd_65081 := by exact prefixLift 65081
  have htrace : WordTrace (prefixWord ++ tailWord_65081) baseStart_65081 baseEnd_65081 := by
    simpa [prefixWord, tailWord_65081, baseEnd_65081] using wordTrace_append hprefix tailTrace_65081
  have hstable : (prefixWord ++ tailWord_65081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65081).length < 2 ^ (prefixWord ++ tailWord_65081).sum := by decide
  have hdescent : baseEnd_65081 < baseStart_65081 := by decide
  rcases family_descends (prefixWord ++ tailWord_65081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65101 : List Nat := [1, 6, 1, 1, 4, 1, 1, 2, 3]
def baseStart_65101 : Nat := 118140960795 + 65101 * 2 ^ 59
def prefixEnd_65101 : Nat := 4983230072969 + 3 ^ 40 * 65101 * 2
def baseEnd_65101 : Nat := 29713870300848911767211

theorem tailTrace_65101 : CollatzResearch.WordTrace tailWord_65101 prefixEnd_65101 29713870300848911767211 := by
  unfold tailWord_65101
  simp only [CollatzResearch.WordTrace]
  refine ⟨2374428537157670210731157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1582952358105113473820771 2374428537157670210731157)
  ·
    refine ⟨111301337679265791128023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2374428537157670210731157 111301337679265791128023)
    ·
      refine ⟨166952006518898686692035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111301337679265791128023 166952006518898686692035)
      ·
        refine ⟨250428009778348030038053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166952006518898686692035 250428009778348030038053)
        ·
          refine ⟨46955251833440255632135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250428009778348030038053 46955251833440255632135)
          ·
            refine ⟨70432877750160383448203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46955251833440255632135 70432877750160383448203)
            ·
              refine ⟨105649316625240575172305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70432877750160383448203 105649316625240575172305)
              ·
                refine ⟨79236987468930431379229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105649316625240575172305 79236987468930431379229)
                ·
                  refine ⟨29713870300848911767211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79236987468930431379229 29713870300848911767211)
                  ·
                    rfl

theorem cell20_65101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_65101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65101 prefixEnd_65101 := by exact prefixLift 65101
  have htrace : WordTrace (prefixWord ++ tailWord_65101) baseStart_65101 baseEnd_65101 := by
    simpa [prefixWord, tailWord_65101, baseEnd_65101] using wordTrace_append hprefix tailTrace_65101
  have hstable : (prefixWord ++ tailWord_65101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65101).length < 2 ^ (prefixWord ++ tailWord_65101).sum := by decide
  have hdescent : baseEnd_65101 < baseStart_65101 := by decide
  rcases family_descends (prefixWord ++ tailWord_65101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65161 : List Nat := [1, 2, 1, 1, 4, 1, 10]
def baseStart_65161 : Nat := 118140960795 + 65161 * 2 ^ 59
def prefixEnd_65161 : Nat := 4983230072969 + 3 ^ 40 * 65161 * 2
def baseEnd_65161 : Nat := 3304583992861707751885

theorem tailTrace_65161 : CollatzResearch.WordTrace tailWord_65161 prefixEnd_65161 3304583992861707751885 := by
  unfold tailWord_65161
  simp only [CollatzResearch.WordTrace]
  refine ⟨2376616916940300457915337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1584411277960200305276891 2376616916940300457915337)
  ·
    refine ⟨1782462687705225343436503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2376616916940300457915337 1782462687705225343436503)
    ·
      refine ⟨2673694031557838015154755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1782462687705225343436503 2673694031557838015154755)
      ·
        refine ⟨4010541047336757022732133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2673694031557838015154755 4010541047336757022732133)
        ·
          refine ⟨751976446375641941762275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4010541047336757022732133 751976446375641941762275)
          ·
            refine ⟨1127964669563462912643413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751976446375641941762275 1127964669563462912643413)
            ·
              refine ⟨3304583992861707751885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1127964669563462912643413 3304583992861707751885)
              ·
                rfl

theorem cell20_65161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 10].length) (baseStart_65161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65161 prefixEnd_65161 := by exact prefixLift 65161
  have htrace : WordTrace (prefixWord ++ tailWord_65161) baseStart_65161 baseEnd_65161 := by
    simpa [prefixWord, tailWord_65161, baseEnd_65161] using wordTrace_append hprefix tailTrace_65161
  have hstable : (prefixWord ++ tailWord_65161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65161).length < 2 ^ (prefixWord ++ tailWord_65161).sum := by decide
  have hdescent : baseEnd_65161 < baseStart_65161 := by decide
  rcases family_descends (prefixWord ++ tailWord_65161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65199 : List Nat := [1, 1, 2, 1, 2, 4, 1, 8]
def baseStart_65199 : Nat := 118140960795 + 65199 * 2 ^ 59
def prefixEnd_65199 : Nat := 4983230072969 + 3 ^ 40 * 65199 * 2
def baseEnd_65199 : Nat := 9919533390398708833381

theorem tailTrace_65199 : CollatzResearch.WordTrace tailWord_65199 prefixEnd_65199 9919533390398708833381 := by
  unfold tailWord_65199
  simp only [CollatzResearch.WordTrace]
  refine ⟨2378002890802632947798651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1585335260535088631865767 2378002890802632947798651)
  ·
    refine ⟨3567004336203949421697977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2378002890802632947798651 3567004336203949421697977)
    ·
      refine ⟨2675253252152962066273483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3567004336203949421697977 2675253252152962066273483)
      ·
        refine ⟨4012879878229443099410225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2675253252152962066273483 4012879878229443099410225)
        ·
          refine ⟨3009659908672082324557669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4012879878229443099410225 3009659908672082324557669)
          ·
            refine ⟨564311232876015435854563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3009659908672082324557669 564311232876015435854563)
            ·
              refine ⟨846466849314023153781845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564311232876015435854563 846466849314023153781845)
              ·
                refine ⟨9919533390398708833381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 846466849314023153781845 9919533390398708833381)
                ·
                  rfl

theorem cell20_65199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 8].length) (baseStart_65199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65199 prefixEnd_65199 := by exact prefixLift 65199
  have htrace : WordTrace (prefixWord ++ tailWord_65199) baseStart_65199 baseEnd_65199 := by
    simpa [prefixWord, tailWord_65199, baseEnd_65199] using wordTrace_append hprefix tailTrace_65199
  have hstable : (prefixWord ++ tailWord_65199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65199).length < 2 ^ (prefixWord ++ tailWord_65199).sum := by decide
  have hdescent : baseEnd_65199 < baseStart_65199 := by decide
  rcases family_descends (prefixWord ++ tailWord_65199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65326 : List Nat := [4, 1, 3, 2, 3, 1, 6]
def baseStart_65326 : Nat := 118140960795 + 65326 * 2 ^ 59
def prefixEnd_65326 : Nat := 4983230072969 + 3 ^ 40 * 65326 * 2
def baseEnd_65326 : Nat := 3312951825749792140699

theorem tailTrace_65326 : CollatzResearch.WordTrace tailWord_65326 prefixEnd_65326 3312951825749792140699 := by
  unfold tailWord_65326
  simp only [CollatzResearch.WordTrace]
  refine ⟨297829370167816704708979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1588423307561689091781221 297829370167816704708979)
  ·
    refine ⟨446744055251725057063469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297829370167816704708979 446744055251725057063469)
    ·
      refine ⟨167529020719396896398801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446744055251725057063469 167529020719396896398801)
      ·
        refine ⟨125646765539547672299101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167529020719396896398801 125646765539547672299101)
        ·
          refine ⟨47117537077330377112163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125646765539547672299101 47117537077330377112163)
          ·
            refine ⟨70676305615995565668245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47117537077330377112163 70676305615995565668245)
            ·
              refine ⟨3312951825749792140699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70676305615995565668245 3312951825749792140699)
              ·
                rfl

theorem cell20_65326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 6].length) (baseStart_65326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65326 prefixEnd_65326 := by exact prefixLift 65326
  have htrace : WordTrace (prefixWord ++ tailWord_65326) baseStart_65326 baseEnd_65326 := by
    simpa [prefixWord, tailWord_65326, baseEnd_65326] using wordTrace_append hprefix tailTrace_65326
  have hstable : (prefixWord ++ tailWord_65326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65326).length < 2 ^ (prefixWord ++ tailWord_65326).sum := by decide
  have hdescent : baseEnd_65326 < baseStart_65326 := by decide
  rcases family_descends (prefixWord ++ tailWord_65326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65330 : List Nat := [3, 2, 1, 1, 3, 4, 6]
def baseStart_65330 : Nat := 118140960795 + 65330 * 2 ^ 59
def prefixEnd_65330 : Nat := 4983230072969 + 3 ^ 40 * 65330 * 2
def baseEnd_65330 : Nat := 3313154682304654792549

theorem tailTrace_65330 : CollatzResearch.WordTrace tailWord_65330 prefixEnd_65330 3313154682304654792549 := by
  unfold tailWord_65330
  simp only [CollatzResearch.WordTrace]
  refine ⟨595695213332010580204361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1588520568885361547211629 595695213332010580204361)
  ·
    refine ⟨446771409999007935153271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 595695213332010580204361 446771409999007935153271)
    ·
      refine ⟨670157114998511902729907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446771409999007935153271 670157114998511902729907)
      ·
        refine ⟨1005235672497767854094861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670157114998511902729907 1005235672497767854094861)
        ·
          refine ⟨376963377186662945285573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1005235672497767854094861 376963377186662945285573)
          ·
            refine ⟨70680633222499302241045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 376963377186662945285573 70680633222499302241045)
            ·
              refine ⟨3313154682304654792549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70680633222499302241045 3313154682304654792549)
              ·
                rfl

theorem cell20_65330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 6].length) (baseStart_65330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65330 prefixEnd_65330 := by exact prefixLift 65330
  have htrace : WordTrace (prefixWord ++ tailWord_65330) baseStart_65330 baseEnd_65330 := by
    simpa [prefixWord, tailWord_65330, baseEnd_65330] using wordTrace_append hprefix tailTrace_65330
  have hstable : (prefixWord ++ tailWord_65330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65330).length < 2 ^ (prefixWord ++ tailWord_65330).sum := by decide
  have hdescent : baseEnd_65330 < baseStart_65330 := by decide
  rcases family_descends (prefixWord ++ tailWord_65330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65350 : List Nat := [6, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_65350 : Nat := 118140960795 + 65350 * 2 ^ 59
def prefixEnd_65350 : Nat := 4983230072969 + 3 ^ 40 * 65350 * 2
def baseEnd_65350 : Nat := 29827520685710712466193

theorem tailTrace_65350 : CollatzResearch.WordTrace tailWord_65350 prefixEnd_65350 29827520685710712466193 := by
  unfold tailWord_65350
  simp only [CollatzResearch.WordTrace]
  refine ⟨74484697289237054267047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1589006875503723824363669 74484697289237054267047)
  ·
    refine ⟨111727045933855581400571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74484697289237054267047 111727045933855581400571)
    ·
      refine ⟨167590568900783372100857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111727045933855581400571 167590568900783372100857)
      ·
        refine ⟨125692926675587529075643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167590568900783372100857 125692926675587529075643)
        ·
          refine ⟨188539390013381293613465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125692926675587529075643 188539390013381293613465)
          ·
            refine ⟨141404542510035970210099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188539390013381293613465 141404542510035970210099)
            ·
              refine ⟨212106813765053955315149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141404542510035970210099 212106813765053955315149)
              ·
                refine ⟨79540055161895233243181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212106813765053955315149 79540055161895233243181)
                ·
                  refine ⟨29827520685710712466193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79540055161895233243181 29827520685710712466193)
                  ·
                    rfl

theorem cell20_65350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_65350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65350 prefixEnd_65350 := by exact prefixLift 65350
  have htrace : WordTrace (prefixWord ++ tailWord_65350) baseStart_65350 baseEnd_65350 := by
    simpa [prefixWord, tailWord_65350, baseEnd_65350] using wordTrace_append hprefix tailTrace_65350
  have hstable : (prefixWord ++ tailWord_65350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65350).length < 2 ^ (prefixWord ++ tailWord_65350).sum := by decide
  have hdescent : baseEnd_65350 < baseStart_65350 := by decide
  rcases family_descends (prefixWord ++ tailWord_65350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65351 : List Nat := [1, 1, 4, 1, 2, 1, 3, 7]
def baseStart_65351 : Nat := 118140960795 + 65351 * 2 ^ 59
def prefixEnd_65351 : Nat := 4983230072969 + 3 ^ 40 * 65351 * 2
def baseEnd_65351 : Nat := 9942659037653051144285

theorem tailTrace_65351 : CollatzResearch.WordTrace tailWord_65351 prefixEnd_65351 9942659037653051144285 := by
  unfold tailWord_65351
  simp only [CollatzResearch.WordTrace]
  refine ⟨2383546786251962907331907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1589031190834641938221271 2383546786251962907331907)
  ·
    refine ⟨3575320179377944360997861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2383546786251962907331907 3575320179377944360997861)
    ·
      refine ⟨670372533633364567687099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3575320179377944360997861 670372533633364567687099)
      ·
        refine ⟨1005558800450046851530649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670372533633364567687099 1005558800450046851530649)
        ·
          refine ⟨754169100337535138647987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1005558800450046851530649 754169100337535138647987)
          ·
            refine ⟨1131253650506302707971981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754169100337535138647987 1131253650506302707971981)
            ·
              refine ⟨424220118939863515489493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1131253650506302707971981 424220118939863515489493)
              ·
                refine ⟨9942659037653051144285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 424220118939863515489493 9942659037653051144285)
                ·
                  rfl

theorem cell20_65351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 7].length) (baseStart_65351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65351 prefixEnd_65351 := by exact prefixLift 65351
  have htrace : WordTrace (prefixWord ++ tailWord_65351) baseStart_65351 baseEnd_65351 := by
    simpa [prefixWord, tailWord_65351, baseEnd_65351] using wordTrace_append hprefix tailTrace_65351
  have hstable : (prefixWord ++ tailWord_65351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65351).length < 2 ^ (prefixWord ++ tailWord_65351).sum := by decide
  have hdescent : baseEnd_65351 < baseStart_65351 := by decide
  rcases family_descends (prefixWord ++ tailWord_65351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65413 : List Nat := [1, 3, 1, 1, 3, 2, 1, 5, 3]
def baseStart_65413 : Nat := 118140960795 + 65413 * 2 ^ 59
def prefixEnd_65413 : Nat := 4983230072969 + 3 ^ 40 * 65413 * 2
def baseEnd_65413 : Nat := 29856275602362493365935

theorem tailTrace_65413 : CollatzResearch.WordTrace tailWord_65413 prefixEnd_65413 29856275602362493365935 := by
  unfold tailWord_65413
  simp only [CollatzResearch.WordTrace]
  refine ⟨2385808112027347496088893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1590538741351564997392595 2385808112027347496088893)
  ·
    refine ⟨894678042010255311033335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2385808112027347496088893 894678042010255311033335)
    ·
      refine ⟨1342017063015382966550003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 894678042010255311033335 1342017063015382966550003)
      ·
        refine ⟨2013025594523074449825005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342017063015382966550003 2013025594523074449825005)
        ·
          refine ⟨754884597946152918684377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2013025594523074449825005 754884597946152918684377)
          ·
            refine ⟨566163448459614689013283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 754884597946152918684377 566163448459614689013283)
            ·
              refine ⟨849245172689422033519925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566163448459614689013283 849245172689422033519925)
              ·
                refine ⟨79616734939633315642493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 849245172689422033519925 79616734939633315642493)
                ·
                  refine ⟨29856275602362493365935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79616734939633315642493 29856275602362493365935)
                  ·
                    rfl

theorem cell20_65413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_65413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65413 prefixEnd_65413 := by exact prefixLift 65413
  have htrace : WordTrace (prefixWord ++ tailWord_65413) baseStart_65413 baseEnd_65413 := by
    simpa [prefixWord, tailWord_65413, baseEnd_65413] using wordTrace_append hprefix tailTrace_65413
  have hstable : (prefixWord ++ tailWord_65413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65413).length < 2 ^ (prefixWord ++ tailWord_65413).sum := by decide
  have hdescent : baseEnd_65413 < baseStart_65413 := by decide
  rcases family_descends (prefixWord ++ tailWord_65413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65447 : List Nat := [1, 1, 6, 1, 2, 3, 1, 2, 3]
def baseStart_65447 : Nat := 118140960795 + 65447 * 2 ^ 59
def prefixEnd_65447 : Nat := 4983230072969 + 3 ^ 40 * 65447 * 2
def baseEnd_65447 : Nat := 29871794128809486232463

theorem tailTrace_65447 : CollatzResearch.WordTrace tailWord_65447 prefixEnd_65447 29871794128809486232463 := by
  unfold tailWord_65447
  simp only [CollatzResearch.WordTrace]
  refine ⟨2387048193904171302826595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1591365462602780868551063 2387048193904171302826595)
  ·
    refine ⟨3580572290856256954239893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2387048193904171302826595 3580572290856256954239893)
    ·
      refine ⟨167839326133887044729995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3580572290856256954239893 167839326133887044729995)
      ·
        refine ⟨251758989200830567094993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167839326133887044729995 251758989200830567094993)
        ·
          refine ⟨188819241900622925321245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251758989200830567094993 188819241900622925321245)
          ·
            refine ⟨70807215712733596995467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188819241900622925321245 70807215712733596995467)
            ·
              refine ⟨106210823569100395493201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70807215712733596995467 106210823569100395493201)
              ·
                refine ⟨79658117676825296619901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106210823569100395493201 79658117676825296619901)
                ·
                  refine ⟨29871794128809486232463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79658117676825296619901 29871794128809486232463)
                  ·
                    rfl

theorem cell20_65447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 3].length) (baseStart_65447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65447 prefixEnd_65447 := by exact prefixLift 65447
  have htrace : WordTrace (prefixWord ++ tailWord_65447) baseStart_65447 baseEnd_65447 := by
    simpa [prefixWord, tailWord_65447, baseEnd_65447] using wordTrace_append hprefix tailTrace_65447
  have hstable : (prefixWord ++ tailWord_65447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65447).length < 2 ^ (prefixWord ++ tailWord_65447).sum := by decide
  have hdescent : baseEnd_65447 < baseStart_65447 := by decide
  rcases family_descends (prefixWord ++ tailWord_65447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65465 : List Nat := [1, 2, 1, 4, 2, 1, 2, 7]
def baseStart_65465 : Nat := 118140960795 + 65465 * 2 ^ 59
def prefixEnd_65465 : Nat := 4983230072969 + 3 ^ 40 * 65465 * 2
def baseEnd_65465 : Nat := 9960003273093807877463

theorem tailTrace_65465 : CollatzResearch.WordTrace tailWord_65465 prefixEnd_65465 9960003273093807877463 := by
  unfold tailWord_65465
  simp only [CollatzResearch.WordTrace]
  refine ⟨2387704707838960376981849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1591803138559306917987899 2387704707838960376981849)
  ·
    refine ⟨1790778530879220282736387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2387704707838960376981849 1790778530879220282736387)
    ·
      refine ⟨2686167796318830424104581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1790778530879220282736387 2686167796318830424104581)
      ·
        refine ⟨503656461809780704519609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2686167796318830424104581 503656461809780704519609)
        ·
          refine ⟨377742346357335528389707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503656461809780704519609 377742346357335528389707)
          ·
            refine ⟨566613519536003292584561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377742346357335528389707 566613519536003292584561)
            ·
              refine ⟨424960139652002469438421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566613519536003292584561 424960139652002469438421)
              ·
                refine ⟨9960003273093807877463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 424960139652002469438421 9960003273093807877463)
                ·
                  rfl

theorem cell20_65465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 7].length) (baseStart_65465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65465 prefixEnd_65465 := by exact prefixLift 65465
  have htrace : WordTrace (prefixWord ++ tailWord_65465) baseStart_65465 baseEnd_65465 := by
    simpa [prefixWord, tailWord_65465, baseEnd_65465] using wordTrace_append hprefix tailTrace_65465
  have hstable : (prefixWord ++ tailWord_65465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65465).length < 2 ^ (prefixWord ++ tailWord_65465).sum := by decide
  have hdescent : baseEnd_65465 < baseStart_65465 := by decide
  rcases family_descends (prefixWord ++ tailWord_65465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65482 : List Nat := [3, 1, 2, 1, 2, 1, 6, 4]
def baseStart_65482 : Nat := 118140960795 + 65482 * 2 ^ 59
def prefixEnd_65482 : Nat := 4983230072969 + 3 ^ 40 * 65482 * 2
def baseEnd_65482 : Nat := 9962589694168306688551

theorem tailTrace_65482 : CollatzResearch.WordTrace tailWord_65482 prefixEnd_65482 9962589694168306688551 := by
  unfold tailWord_65482
  simp only [CollatzResearch.WordTrace]
  refine ⟨597081187194343070087675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1592216499184914853567133 597081187194343070087675)
  ·
    refine ⟨895621780791514605131513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 597081187194343070087675 895621780791514605131513)
    ·
      refine ⟨671716335593635953848635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 895621780791514605131513 671716335593635953848635)
      ·
        refine ⟨1007574503390453930772953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671716335593635953848635 1007574503390453930772953)
        ·
          refine ⟨755680877542840448079715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1007574503390453930772953 755680877542840448079715)
          ·
            refine ⟨1133521316314260672119573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755680877542840448079715 1133521316314260672119573)
            ·
              refine ⟨53133811702230969005605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1133521316314260672119573 53133811702230969005605)
              ·
                refine ⟨9962589694168306688551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53133811702230969005605 9962589694168306688551)
                ·
                  rfl

theorem cell20_65482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_65482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65482 prefixEnd_65482 := by exact prefixLift 65482
  have htrace : WordTrace (prefixWord ++ tailWord_65482) baseStart_65482 baseEnd_65482 := by
    simpa [prefixWord, tailWord_65482, baseEnd_65482] using wordTrace_append hprefix tailTrace_65482
  have hstable : (prefixWord ++ tailWord_65482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65482).length < 2 ^ (prefixWord ++ tailWord_65482).sum := by decide
  have hdescent : baseEnd_65482 < baseStart_65482 := by decide
  rcases family_descends (prefixWord ++ tailWord_65482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65503 : List Nat := [1, 1, 2, 3, 4, 1, 8]
def baseStart_65503 : Nat := 118140960795 + 65503 * 2 ^ 59
def prefixEnd_65503 : Nat := 4983230072969 + 3 ^ 40 * 65503 * 2
def baseEnd_65503 : Nat := 3321928228302464485063

theorem tailTrace_65503 : CollatzResearch.WordTrace tailWord_65503 prefixEnd_65503 3321928228302464485063 := by
  unfold tailWord_65503
  simp only [CollatzResearch.WordTrace]
  refine ⟨2389090681701292866865163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1592727121134195244576775 2389090681701292866865163)
  ·
    refine ⟨3583636022551939300297745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2389090681701292866865163 3583636022551939300297745)
    ·
      refine ⟨2687727016913954475223309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3583636022551939300297745 2687727016913954475223309)
      ·
        refine ⟨1007897631342732928208741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2687727016913954475223309 1007897631342732928208741)
        ·
          refine ⟨188980805876762424039139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1007897631342732928208741 188980805876762424039139)
          ·
            refine ⟨283471208815143636058709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188980805876762424039139 283471208815143636058709)
            ·
              refine ⟨3321928228302464485063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 283471208815143636058709 3321928228302464485063)
              ·
                rfl

theorem cell20_65503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 8].length) (baseStart_65503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65503 prefixEnd_65503 := by exact prefixLift 65503
  have htrace : WordTrace (prefixWord ++ tailWord_65503) baseStart_65503 baseEnd_65503 := by
    simpa [prefixWord, tailWord_65503, baseEnd_65503] using wordTrace_append hprefix tailTrace_65503
  have hstable : (prefixWord ++ tailWord_65503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65503).length < 2 ^ (prefixWord ++ tailWord_65503).sum := by decide
  have hdescent : baseEnd_65503 < baseStart_65503 := by decide
  rcases family_descends (prefixWord ++ tailWord_65503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65541 : List Nat := [1, 3, 1, 1, 2, 4, 2, 6]
def baseStart_65541 : Nat := 118140960795 + 65541 * 2 ^ 59
def prefixEnd_65541 : Nat := 4983230072969 + 3 ^ 40 * 65541 * 2
def baseEnd_65541 : Nat := 9971566096720979032915

theorem tailTrace_65541 : CollatzResearch.WordTrace tailWord_65541 prefixEnd_65541 9971566096720979032915 := by
  unfold tailWord_65541
  simp only [CollatzResearch.WordTrace]
  refine ⟨2390476655563625356748477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1593651103709083571165651 2390476655563625356748477)
  ·
    refine ⟨896428745836359508780679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2390476655563625356748477 896428745836359508780679)
    ·
      refine ⟨1344643118754539263171019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 896428745836359508780679 1344643118754539263171019)
      ·
        refine ⟨2016964678131808894756529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1344643118754539263171019 2016964678131808894756529)
        ·
          refine ⟨1512723508598856671067397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2016964678131808894756529 1512723508598856671067397)
          ·
            refine ⟨283635657862285625825137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1512723508598856671067397 283635657862285625825137)
            ·
              refine ⟨212726743396714219368853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283635657862285625825137 212726743396714219368853)
              ·
                refine ⟨9971566096720979032915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 212726743396714219368853 9971566096720979032915)
                ·
                  rfl

theorem cell20_65541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 6].length) (baseStart_65541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65541 prefixEnd_65541 := by exact prefixLift 65541
  have htrace : WordTrace (prefixWord ++ tailWord_65541) baseStart_65541 baseEnd_65541 := by
    simpa [prefixWord, tailWord_65541, baseEnd_65541] using wordTrace_append hprefix tailTrace_65541
  have hstable : (prefixWord ++ tailWord_65541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65541).length < 2 ^ (prefixWord ++ tailWord_65541).sum := by decide
  have hdescent : baseEnd_65541 < baseStart_65541 := by decide
  rcases family_descends (prefixWord ++ tailWord_65541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65582 : List Nat := [4, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_65582 : Nat := 118140960795 + 65582 * 2 ^ 59
def prefixEnd_65582 : Nat := 4983230072969 + 3 ^ 40 * 65582 * 2
def baseEnd_65582 : Nat := 29933411807349016731911

theorem tailTrace_65582 : CollatzResearch.WordTrace tailWord_65582 prefixEnd_65582 29933411807349016731911 := by
  unfold tailWord_65582
  simp only [CollatzResearch.WordTrace]
  refine ⟨298996506051886169873875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1594648032276726239327333 298996506051886169873875)
  ·
    refine ⟨448494759077829254810813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298996506051886169873875 448494759077829254810813)
    ·
      refine ⟨168185534654185970554055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448494759077829254810813 168185534654185970554055)
      ·
        refine ⟨252278301981278955831083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168185534654185970554055 252278301981278955831083)
        ·
          refine ⟨378417452971918433746625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252278301981278955831083 378417452971918433746625)
          ·
            refine ⟨283813089728938825309969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378417452971918433746625 283813089728938825309969)
            ·
              refine ⟨212859817296704118982477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283813089728938825309969 212859817296704118982477)
              ·
                refine ⟨79822431486264044618429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212859817296704118982477 79822431486264044618429)
                ·
                  refine ⟨29933411807349016731911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79822431486264044618429 29933411807349016731911)
                  ·
                    rfl

theorem cell20_65582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_65582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65582 prefixEnd_65582 := by exact prefixLift 65582
  have htrace : WordTrace (prefixWord ++ tailWord_65582) baseStart_65582 baseEnd_65582 := by
    simpa [prefixWord, tailWord_65582, baseEnd_65582] using wordTrace_append hprefix tailTrace_65582
  have hstable : (prefixWord ++ tailWord_65582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65582).length < 2 ^ (prefixWord ++ tailWord_65582).sum := by decide
  have hdescent : baseEnd_65582 < baseStart_65582 := by decide
  rcases family_descends (prefixWord ++ tailWord_65582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65596 : List Nat := [2, 2, 2, 2, 2, 1, 5, 4]
def baseStart_65596 : Nat := 118140960795 + 65596 * 2 ^ 59
def prefixEnd_65596 : Nat := 4983230072969 + 3 ^ 40 * 65596 * 2
def baseEnd_65596 : Nat := 9979933929609063421729

theorem tailTrace_65596 : CollatzResearch.WordTrace tailWord_65596 prefixEnd_65596 9979933929609063421729 := by
  unfold tailWord_65596
  simp only [CollatzResearch.WordTrace]
  refine ⟨1196241335182184875000321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1594988446909579833333761 1196241335182184875000321)
  ·
    refine ⟨897181001386638656250241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1196241335182184875000321 897181001386638656250241)
    ·
      refine ⟨672885751039978992187681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 897181001386638656250241 672885751039978992187681)
      ·
        refine ⟨504664313279984244140761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672885751039978992187681 504664313279984244140761)
        ·
          refine ⟨378498234959988183105571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504664313279984244140761 378498234959988183105571)
          ·
            refine ⟨567747352439982274658357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378498234959988183105571 567747352439982274658357)
            ·
              refine ⟨53226314291248338249221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 567747352439982274658357 53226314291248338249221)
              ·
                refine ⟨9979933929609063421729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53226314291248338249221 9979933929609063421729)
                ·
                  rfl

theorem cell20_65596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_65596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65596 prefixEnd_65596 := by exact prefixLift 65596
  have htrace : WordTrace (prefixWord ++ tailWord_65596) baseStart_65596 baseEnd_65596 := by
    simpa [prefixWord, tailWord_65596, baseEnd_65596] using wordTrace_append hprefix tailTrace_65596
  have hstable : (prefixWord ++ tailWord_65596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65596).length < 2 ^ (prefixWord ++ tailWord_65596).sum := by decide
  have hdescent : baseEnd_65596 < baseStart_65596 := by decide
  rcases family_descends (prefixWord ++ tailWord_65596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65648 : List Nat := [2, 1, 1, 1, 5, 2, 2, 2, 4]
def baseStart_65648 : Nat := 118140960795 + 65648 * 2 ^ 59
def prefixEnd_65648 : Nat := 4983230072969 + 3 ^ 40 * 65648 * 2
def baseEnd_65648 : Nat := 29963536005746120531641

theorem tailTrace_65648 : CollatzResearch.WordTrace tailWord_65648 prefixEnd_65648 29963536005746120531641 := by
  unfold tailWord_65648
  simp only [CollatzResearch.WordTrace]
  refine ⟨1197189633087991315446799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1596252844117321753929065 1197189633087991315446799)
  ·
    refine ⟨1795784449631986973170199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1197189633087991315446799 1795784449631986973170199)
    ·
      refine ⟨2693676674447980459755299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1795784449631986973170199 2693676674447980459755299)
      ·
        refine ⟨4040515011671970689632949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2693676674447980459755299 4040515011671970689632949)
        ·
          refine ⟨378798282344247252153089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4040515011671970689632949 378798282344247252153089)
          ·
            refine ⟨284098711758185439114817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378798282344247252153089 284098711758185439114817)
            ·
              refine ⟨213074033818639079336113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284098711758185439114817 213074033818639079336113)
              ·
                refine ⟨159805525363979309502085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213074033818639079336113 159805525363979309502085)
                ·
                  refine ⟨29963536005746120531641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159805525363979309502085 29963536005746120531641)
                  ·
                    rfl

theorem cell20_65648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_65648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65648 prefixEnd_65648 := by exact prefixLift 65648
  have htrace : WordTrace (prefixWord ++ tailWord_65648) baseStart_65648 baseEnd_65648 := by
    simpa [prefixWord, tailWord_65648, baseEnd_65648] using wordTrace_append hprefix tailTrace_65648
  have hstable : (prefixWord ++ tailWord_65648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65648).length < 2 ^ (prefixWord ++ tailWord_65648).sum := by decide
  have hdescent : baseEnd_65648 < baseStart_65648 := by decide
  rcases family_descends (prefixWord ++ tailWord_65648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65655 : List Nat := [1, 1, 3, 1, 1, 6, 1, 6]
def baseStart_65655 : Nat := 118140960795 + 65655 * 2 ^ 59
def prefixEnd_65655 : Nat := 4983230072969 + 3 ^ 40 * 65655 * 2
def baseEnd_65655 : Nat := 9988910332161735766093

theorem tailTrace_65655 : CollatzResearch.WordTrace tailWord_65655 prefixEnd_65655 9988910332161735766093 := by
  unfold tailWord_65655
  simp only [CollatzResearch.WordTrace]
  refine ⟨2394634577150622826398419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1596423051433748550932279 2394634577150622826398419)
  ·
    refine ⟨3591951865725934239597629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2394634577150622826398419 3591951865725934239597629)
    ·
      refine ⟨1346981949647225339849111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3591951865725934239597629 1346981949647225339849111)
      ·
        refine ⟨2020472924470838009773667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1346981949647225339849111 2020472924470838009773667)
        ·
          refine ⟨3030709386706257014660501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2020472924470838009773667 3030709386706257014660501)
          ·
            refine ⟨142064502501855797562211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3030709386706257014660501 142064502501855797562211)
            ·
              refine ⟨213096753752783696343317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142064502501855797562211 213096753752783696343317)
              ·
                refine ⟨9988910332161735766093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 213096753752783696343317 9988910332161735766093)
                ·
                  rfl

theorem cell20_65655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 6].length) (baseStart_65655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65655 prefixEnd_65655 := by exact prefixLift 65655
  have htrace : WordTrace (prefixWord ++ tailWord_65655) baseStart_65655 baseEnd_65655 := by
    simpa [prefixWord, tailWord_65655, baseEnd_65655] using wordTrace_append hprefix tailTrace_65655
  have hstable : (prefixWord ++ tailWord_65655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65655).length < 2 ^ (prefixWord ++ tailWord_65655).sum := by decide
  have hdescent : baseEnd_65655 < baseStart_65655 := by decide
  rcases family_descends (prefixWord ++ tailWord_65655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65672 : List Nat := [2, 1, 3, 4, 1, 3, 6]
def baseStart_65672 : Nat := 118140960795 + 65672 * 2 ^ 59
def prefixEnd_65672 : Nat := 4983230072969 + 3 ^ 40 * 65672 * 2
def baseEnd_65672 : Nat := 3330498917745411525727

theorem tailTrace_65672 : CollatzResearch.WordTrace tailWord_65672 prefixEnd_65672 3330498917745411525727 := by
  unfold tailWord_65672
  simp only [CollatzResearch.WordTrace]
  refine ⟨1197627309044517364883635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1596836412059356486511513 1197627309044517364883635)
  ·
    refine ⟨1796440963566776047325453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1197627309044517364883635 1796440963566776047325453)
    ·
      refine ⟨673665361337541017747045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1796440963566776047325453 673665361337541017747045)
      ·
        refine ⟨126312255250788940827571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 673665361337541017747045 126312255250788940827571)
        ·
          refine ⟨189468382876183411241357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126312255250788940827571 189468382876183411241357)
          ·
            refine ⟨71050643578568779215509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189468382876183411241357 71050643578568779215509)
            ·
              refine ⟨3330498917745411525727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71050643578568779215509 3330498917745411525727)
              ·
                rfl

theorem cell20_65672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 6].length) (baseStart_65672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65672 prefixEnd_65672 := by exact prefixLift 65672
  have htrace : WordTrace (prefixWord ++ tailWord_65672) baseStart_65672 baseEnd_65672 := by
    simpa [prefixWord, tailWord_65672, baseEnd_65672] using wordTrace_append hprefix tailTrace_65672
  have hstable : (prefixWord ++ tailWord_65672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65672).length < 2 ^ (prefixWord ++ tailWord_65672).sum := by decide
  have hdescent : baseEnd_65672 < baseStart_65672 := by decide
  rcases family_descends (prefixWord ++ tailWord_65672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65693 : List Nat := [1, 4, 2, 1, 1, 3, 1, 7]
def baseStart_65693 : Nat := 118140960795 + 65693 * 2 ^ 59
def prefixEnd_65693 : Nat := 4983230072969 + 3 ^ 40 * 65693 * 2
def baseEnd_65693 : Nat := 9994691743975321343819

theorem tailTrace_65693 : CollatzResearch.WordTrace tailWord_65693 prefixEnd_65693 9994691743975321343819 := by
  unfold tailWord_65693
  simp only [CollatzResearch.WordTrace]
  refine ⟨2396020551012955316281733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1597347034008636877521155 2396020551012955316281733)
  ·
    refine ⟨449253853314929121802825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2396020551012955316281733 449253853314929121802825)
    ·
      refine ⟨336940389986196841352119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449253853314929121802825 336940389986196841352119)
      ·
        refine ⟨505410584979295262028179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336940389986196841352119 505410584979295262028179)
        ·
          refine ⟨758115877468942893042269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505410584979295262028179 758115877468942893042269)
          ·
            refine ⟨284293454050853584890851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 758115877468942893042269 284293454050853584890851)
            ·
              refine ⟨426440181076280377336277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284293454050853584890851 426440181076280377336277)
              ·
                refine ⟨9994691743975321343819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 426440181076280377336277 9994691743975321343819)
                ·
                  rfl

theorem cell20_65693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 7].length) (baseStart_65693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65693 prefixEnd_65693 := by exact prefixLift 65693
  have htrace : WordTrace (prefixWord ++ tailWord_65693) baseStart_65693 baseEnd_65693 := by
    simpa [prefixWord, tailWord_65693, baseEnd_65693] using wordTrace_append hprefix tailTrace_65693
  have hstable : (prefixWord ++ tailWord_65693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65693).length < 2 ^ (prefixWord ++ tailWord_65693).sum := by decide
  have hdescent : baseEnd_65693 < baseStart_65693 := by decide
  rcases family_descends (prefixWord ++ tailWord_65693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65696 : List Nat := [2, 1, 1, 4, 2, 2, 4, 1, 3]
def baseStart_65696 : Nat := 118140960795 + 65696 * 2 ^ 59
def prefixEnd_65696 : Nat := 4983230072969 + 3 ^ 40 * 65696 * 2
def baseEnd_65696 : Nat := 29985444513671286931445

theorem tailTrace_65696 : CollatzResearch.WordTrace tailWord_65696 prefixEnd_65696 29985444513671286931445 := by
  unfold tailWord_65696
  simp only [CollatzResearch.WordTrace]
  refine ⟨1198064985001043414320471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1597419980001391219093961 1198064985001043414320471)
  ·
    refine ⟨1797097477501565121480707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1198064985001043414320471 1797097477501565121480707)
    ·
      refine ⟨2695646216252347682221061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1797097477501565121480707 2695646216252347682221061)
      ·
        refine ⟨505433665547315190416449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2695646216252347682221061 505433665547315190416449)
        ·
          refine ⟨379075249160486392812337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505433665547315190416449 379075249160486392812337)
          ·
            refine ⟨284306436870364794609253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379075249160486392812337 284306436870364794609253)
            ·
              refine ⟨53307456913193398989235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284306436870364794609253 53307456913193398989235)
              ·
                refine ⟨79961185369790098483853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53307456913193398989235 79961185369790098483853)
                ·
                  refine ⟨29985444513671286931445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79961185369790098483853 29985444513671286931445)
                  ·
                    rfl

theorem cell20_65696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 3].length) (baseStart_65696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65696 prefixEnd_65696 := by exact prefixLift 65696
  have htrace : WordTrace (prefixWord ++ tailWord_65696) baseStart_65696 baseEnd_65696 := by
    simpa [prefixWord, tailWord_65696, baseEnd_65696] using wordTrace_append hprefix tailTrace_65696
  have hstable : (prefixWord ++ tailWord_65696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65696).length < 2 ^ (prefixWord ++ tailWord_65696).sum := by decide
  have hdescent : baseEnd_65696 < baseStart_65696 := by decide
  rcases family_descends (prefixWord ++ tailWord_65696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65730 : List Nat := [3, 5, 1, 1, 1, 2, 2, 2, 3]
def baseStart_65730 : Nat := 118140960795 + 65730 * 2 ^ 59
def prefixEnd_65730 : Nat := 4983230072969 + 3 ^ 40 * 65730 * 2
def baseEnd_65730 : Nat := 30000963040118279797973

theorem tailTrace_65730 : CollatzResearch.WordTrace tailWord_65730 prefixEnd_65730 30000963040118279797973 := by
  unfold tailWord_65730
  simp only [CollatzResearch.WordTrace]
  refine ⟨599342512969727658844661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1598246701252607090252429 599342512969727658844661)
  ·
    refine ⟨56188360590911968016687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 599342512969727658844661 56188360590911968016687)
    ·
      refine ⟨84282540886367952025031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56188360590911968016687 84282540886367952025031)
      ·
        refine ⟨126423811329551928037547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84282540886367952025031 126423811329551928037547)
        ·
          refine ⟨189635716994327892056321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126423811329551928037547 189635716994327892056321)
          ·
            refine ⟨142226787745745919042241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189635716994327892056321 142226787745745919042241)
            ·
              refine ⟨106670090809309439281681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142226787745745919042241 106670090809309439281681)
              ·
                refine ⟨80002568106982079461261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106670090809309439281681 80002568106982079461261)
                ·
                  refine ⟨30000963040118279797973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80002568106982079461261 30000963040118279797973)
                  ·
                    rfl

theorem cell20_65730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_65730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65730 prefixEnd_65730 := by exact prefixLift 65730
  have htrace : WordTrace (prefixWord ++ tailWord_65730) baseStart_65730 baseEnd_65730 := by
    simpa [prefixWord, tailWord_65730, baseEnd_65730] using wordTrace_append hprefix tailTrace_65730
  have hstable : (prefixWord ++ tailWord_65730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65730).length < 2 ^ (prefixWord ++ tailWord_65730).sum := by decide
  have hdescent : baseEnd_65730 < baseStart_65730 := by decide
  rcases family_descends (prefixWord ++ tailWord_65730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65779 : List Nat := [1, 1, 1, 2, 2, 4, 4, 3, 2]
def baseStart_65779 : Nat := 118140960795 + 65779 * 2 ^ 59
def prefixEnd_65779 : Nat := 4983230072969 + 3 ^ 40 * 65779 * 2
def baseEnd_65779 : Nat := 30023327975291887164439

theorem tailTrace_65779 : CollatzResearch.WordTrace tailWord_65779 prefixEnd_65779 30023327975291887164439 := by
  unfold tailWord_65779
  simp only [CollatzResearch.WordTrace]
  refine ⟨2399157228701392003912391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1599438152467594669274927 2399157228701392003912391)
  ·
    refine ⟨3598735843052088005868587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2399157228701392003912391 3598735843052088005868587)
    ·
      refine ⟨5398103764578132008802881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3598735843052088005868587 5398103764578132008802881)
      ·
        refine ⟨4048577823433599006602161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5398103764578132008802881 4048577823433599006602161)
        ·
          refine ⟨3036433367575199254951621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4048577823433599006602161 3036433367575199254951621)
          ·
            refine ⟨569331256420349860303429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3036433367575199254951621 569331256420349860303429)
            ·
              refine ⟨106749610578815598806893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 569331256420349860303429 106749610578815598806893)
              ·
                refine ⟨40031103967055849552585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106749610578815598806893 40031103967055849552585)
                ·
                  refine ⟨30023327975291887164439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40031103967055849552585 30023327975291887164439)
                  ·
                    rfl

theorem cell20_65779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 3, 2].length) (baseStart_65779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65779 prefixEnd_65779 := by exact prefixLift 65779
  have htrace : WordTrace (prefixWord ++ tailWord_65779) baseStart_65779 baseEnd_65779 := by
    simpa [prefixWord, tailWord_65779, baseEnd_65779] using wordTrace_append hprefix tailTrace_65779
  have hstable : (prefixWord ++ tailWord_65779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65779).length < 2 ^ (prefixWord ++ tailWord_65779).sum := by decide
  have hdescent : baseEnd_65779 < baseStart_65779 := by decide
  rcases family_descends (prefixWord ++ tailWord_65779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65800 : List Nat := [2, 1, 3, 2, 3, 1, 1, 3, 4]
def baseStart_65800 : Nat := 118140960795 + 65800 * 2 ^ 59
def prefixEnd_65800 : Nat := 4983230072969 + 3 ^ 40 * 65800 * 2
def baseEnd_65800 : Nat := 30032912947509147464353

theorem tailTrace_65800 : CollatzResearch.WordTrace tailWord_65800 prefixEnd_65800 30032912947509147464353 := by
  unfold tailWord_65800
  simp only [CollatzResearch.WordTrace]
  refine ⟨1199961580812656295213427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1599948774416875060284569 1199961580812656295213427)
  ·
    refine ⟨1799942371218984442820141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1199961580812656295213427 1799942371218984442820141)
    ·
      refine ⟨674978389207119166057553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1799942371218984442820141 674978389207119166057553)
      ·
        refine ⟨506233791905339374543165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 674978389207119166057553 506233791905339374543165)
        ·
          refine ⟨189837671964502265453687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 506233791905339374543165 189837671964502265453687)
          ·
            refine ⟨284756507946753398180531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189837671964502265453687 284756507946753398180531)
            ·
              refine ⟨427134761920130097270797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284756507946753398180531 427134761920130097270797)
              ·
                refine ⟨160175535720048786476549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 427134761920130097270797 160175535720048786476549)
                ·
                  refine ⟨30032912947509147464353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160175535720048786476549 30032912947509147464353)
                  ·
                    rfl

theorem cell20_65800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_65800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65800 prefixEnd_65800 := by exact prefixLift 65800
  have htrace : WordTrace (prefixWord ++ tailWord_65800) baseStart_65800 baseEnd_65800 := by
    simpa [prefixWord, tailWord_65800, baseEnd_65800] using wordTrace_append hprefix tailTrace_65800
  have hstable : (prefixWord ++ tailWord_65800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65800).length < 2 ^ (prefixWord ++ tailWord_65800).sum := by decide
  have hdescent : baseEnd_65800 < baseStart_65800 := by decide
  rcases family_descends (prefixWord ++ tailWord_65800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65824 : List Nat := [2, 1, 1, 5, 2, 1, 4, 4]
def baseStart_65824 : Nat := 118140960795 + 65824 * 2 ^ 59
def prefixEnd_65824 : Nat := 4983230072969 + 3 ^ 40 * 65824 * 2
def baseEnd_65824 : Nat := 10014622400490576888085

theorem tailTrace_65824 : CollatzResearch.WordTrace tailWord_65824 prefixEnd_65824 10014622400490576888085 := by
  unfold tailWord_65824
  simp only [CollatzResearch.WordTrace]
  refine ⟨1200399256769182344650263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1600532342358909792867017 1200399256769182344650263)
  ·
    refine ⟨1800598885153773516975395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1200399256769182344650263 1800598885153773516975395)
    ·
      refine ⟨2700898327730660275463093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1800598885153773516975395 2700898327730660275463093)
      ·
        refine ⟨253209218224749400824665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2700898327730660275463093 253209218224749400824665)
        ·
          refine ⟨189906913668562050618499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253209218224749400824665 189906913668562050618499)
          ·
            refine ⟨284860370502843075927749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189906913668562050618499 284860370502843075927749)
            ·
              refine ⟨53411319469283076736453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284860370502843075927749 53411319469283076736453)
              ·
                refine ⟨10014622400490576888085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53411319469283076736453 10014622400490576888085)
                ·
                  rfl

theorem cell20_65824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_65824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65824 prefixEnd_65824 := by exact prefixLift 65824
  have htrace : WordTrace (prefixWord ++ tailWord_65824) baseStart_65824 baseEnd_65824 := by
    simpa [prefixWord, tailWord_65824, baseEnd_65824] using wordTrace_append hprefix tailTrace_65824
  have hstable : (prefixWord ++ tailWord_65824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65824).length < 2 ^ (prefixWord ++ tailWord_65824).sum := by decide
  have hdescent : baseEnd_65824 < baseStart_65824 := by decide
  rcases family_descends (prefixWord ++ tailWord_65824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65852 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 5]
def baseStart_65852 : Nat := 118140960795 + 65852 * 2 ^ 59
def prefixEnd_65852 : Nat := 4983230072969 + 3 ^ 40 * 65852 * 2
def baseEnd_65852 : Nat := 30056647164428077730807

theorem tailTrace_65852 : CollatzResearch.WordTrace tailWord_65852 prefixEnd_65852 30056647164428077730807 := by
  unfold tailWord_65852
  simp only [CollatzResearch.WordTrace]
  refine ⟨1200909878718462735659905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1601213171624616980879873 1200909878718462735659905)
  ·
    refine ⟨900682409038847051744929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1200909878718462735659905 900682409038847051744929)
    ·
      refine ⟨675511806779135288808697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 900682409038847051744929 675511806779135288808697)
      ·
        refine ⟨506633855084351466606523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675511806779135288808697 506633855084351466606523)
        ·
          refine ⟨759950782626527199909785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506633855084351466606523 759950782626527199909785)
          ·
            refine ⟨569963086969895399932339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 759950782626527199909785 569963086969895399932339)
            ·
              refine ⟨854944630454843099898509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569963086969895399932339 854944630454843099898509)
              ·
                refine ⟨320604236420566162461941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 854944630454843099898509 320604236420566162461941)
                ·
                  refine ⟨30056647164428077730807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 320604236420566162461941 30056647164428077730807)
                  ·
                    rfl

theorem cell20_65852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_65852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65852 prefixEnd_65852 := by exact prefixLift 65852
  have htrace : WordTrace (prefixWord ++ tailWord_65852) baseStart_65852 baseEnd_65852 := by
    simpa [prefixWord, tailWord_65852, baseEnd_65852] using wordTrace_append hprefix tailTrace_65852
  have hstable : (prefixWord ++ tailWord_65852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65852).length < 2 ^ (prefixWord ++ tailWord_65852).sum := by decide
  have hdescent : baseEnd_65852 < baseStart_65852 := by decide
  rcases family_descends (prefixWord ++ tailWord_65852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65904 : List Nat := [2, 1, 1, 1, 4, 11]
def baseStart_65904 : Nat := 118140960795 + 65904 * 2 ^ 59
def prefixEnd_65904 : Nat := 4983230072969 + 3 ^ 40 * 65904 * 2
def baseEnd_65904 : Nat := 1114088199309148444343

theorem tailTrace_65904 : CollatzResearch.WordTrace tailWord_65904 prefixEnd_65904 1114088199309148444343 := by
  unfold tailWord_65904
  simp only [CollatzResearch.WordTrace]
  refine ⟨1201858176624269176106383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1602477568832358901475177 1201858176624269176106383)
  ·
    refine ⟨1802787264936403764159575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1201858176624269176106383 1802787264936403764159575)
    ·
      refine ⟨2704180897404605646239363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1802787264936403764159575 2704180897404605646239363)
      ·
        refine ⟨4056271346106908469359045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2704180897404605646239363 4056271346106908469359045)
        ·
          refine ⟨760550877395045338004821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4056271346106908469359045 760550877395045338004821)
          ·
            refine ⟨1114088199309148444343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 760550877395045338004821 1114088199309148444343)
            ·
              rfl

theorem cell20_65904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 11].length) (baseStart_65904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65904 prefixEnd_65904 := by exact prefixLift 65904
  have htrace : WordTrace (prefixWord ++ tailWord_65904) baseStart_65904 baseEnd_65904 := by
    simpa [prefixWord, tailWord_65904, baseEnd_65904] using wordTrace_append hprefix tailTrace_65904
  have hstable : (prefixWord ++ tailWord_65904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65904).length < 2 ^ (prefixWord ++ tailWord_65904).sum := by decide
  have hdescent : baseEnd_65904 < baseStart_65904 := by decide
  rcases family_descends (prefixWord ++ tailWord_65904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65959 : List Nat := [1, 1, 6, 1, 1, 3, 7]
def baseStart_65959 : Nat := 118140960795 + 65959 * 2 ^ 59
def prefixEnd_65959 : Nat := 4983230072969 + 3 ^ 40 * 65959 * 2
def baseEnd_65959 : Nat := 3345053875556806795967

theorem tailTrace_65959 : CollatzResearch.WordTrace tailWord_65959 prefixEnd_65959 3345053875556806795967 := by
  unfold tailWord_65959
  simp only [CollatzResearch.WordTrace]
  refine ⟨2405722368049282745464931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1603814912032855163643287 2405722368049282745464931)
  ·
    refine ⟨3608583552073924118197397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2405722368049282745464931 3608583552073924118197397)
    ·
      refine ⟨169152354003465193040503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3608583552073924118197397 169152354003465193040503)
      ·
        refine ⟨253728531005197789560755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169152354003465193040503 253728531005197789560755)
        ·
          refine ⟨380592796507796684341133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253728531005197789560755 380592796507796684341133)
          ·
            refine ⟨142722298690423756627925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380592796507796684341133 142722298690423756627925)
            ·
              refine ⟨3345053875556806795967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 142722298690423756627925 3345053875556806795967)
              ·
                rfl

theorem cell20_65959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 7].length) (baseStart_65959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65959 prefixEnd_65959 := by exact prefixLift 65959
  have htrace : WordTrace (prefixWord ++ tailWord_65959) baseStart_65959 baseEnd_65959 := by
    simpa [prefixWord, tailWord_65959, baseEnd_65959] using wordTrace_append hprefix tailTrace_65959
  have hstable : (prefixWord ++ tailWord_65959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65959).length < 2 ^ (prefixWord ++ tailWord_65959).sum := by decide
  have hdescent : baseEnd_65959 < baseStart_65959 := by decide
  rcases family_descends (prefixWord ++ tailWord_65959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65969 : List Nat := [1, 2, 2, 4, 1, 2, 2, 4, 2]
def baseStart_65969 : Nat := 118140960795 + 65969 * 2 ^ 59
def prefixEnd_65969 : Nat := 4983230072969 + 3 ^ 40 * 65969 * 2
def baseEnd_65969 : Nat := 30110049152495670830329

theorem tailTrace_65969 : CollatzResearch.WordTrace tailWord_65969 prefixEnd_65969 30110049152495670830329 := by
  unfold tailWord_65969
  simp only [CollatzResearch.WordTrace]
  refine ⟨2406087098013054453328961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1604058065342036302219307 2406087098013054453328961)
  ·
    refine ⟨1804565323509790839996721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2406087098013054453328961 1804565323509790839996721)
    ·
      refine ⟨1353423992632343129997541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1804565323509790839996721 1353423992632343129997541)
      ·
        refine ⟨253766998618564336874539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1353423992632343129997541 253766998618564336874539)
        ·
          refine ⟨380650497927846505311809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253766998618564336874539 380650497927846505311809)
          ·
            refine ⟨285487873445884878983857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380650497927846505311809 285487873445884878983857)
            ·
              refine ⟨214115905084413659237893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285487873445884878983857 214115905084413659237893)
              ·
                refine ⟨40146732203327561107105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214115905084413659237893 40146732203327561107105)
                ·
                  refine ⟨30110049152495670830329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40146732203327561107105 30110049152495670830329)
                  ·
                    rfl

theorem cell20_65969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 2].length) (baseStart_65969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_65969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_65969 prefixEnd_65969 := by exact prefixLift 65969
  have htrace : WordTrace (prefixWord ++ tailWord_65969) baseStart_65969 baseEnd_65969 := by
    simpa [prefixWord, tailWord_65969, baseEnd_65969] using wordTrace_append hprefix tailTrace_65969
  have hstable : (prefixWord ++ tailWord_65969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65969).length < 2 ^ (prefixWord ++ tailWord_65969).sum := by decide
  have hdescent : baseEnd_65969 < baseStart_65969 := by decide
  rcases family_descends (prefixWord ++ tailWord_65969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66024 : List Nat := [2, 1, 4, 1, 1, 4, 3, 2, 2]
def baseStart_66024 : Nat := 118140960795 + 66024 * 2 ^ 59
def prefixEnd_66024 : Nat := 4983230072969 + 3 ^ 40 * 66024 * 2
def baseEnd_66024 : Nat := 30135152651159923996771

theorem tailTrace_66024 : CollatzResearch.WordTrace tailWord_66024 prefixEnd_66024 30135152651159923996771 := by
  unfold tailWord_66024
  simp only [CollatzResearch.WordTrace]
  refine ⟨1204046556406899423290563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1605395408542532564387417 1204046556406899423290563)
  ·
    refine ⟨1806069834610349134935845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1204046556406899423290563 1806069834610349134935845)
    ·
      refine ⟨338638093989440462800471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1806069834610349134935845 338638093989440462800471)
      ·
        refine ⟨507957140984160694200707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338638093989440462800471 507957140984160694200707)
        ·
          refine ⟨761935711476241041301061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507957140984160694200707 761935711476241041301061)
          ·
            refine ⟨142862945901795195243949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 761935711476241041301061 142862945901795195243949)
            ·
              refine ⟨53573604713173198216481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142862945901795195243949 53573604713173198216481)
              ·
                refine ⟨40180203534879898662361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53573604713173198216481 40180203534879898662361)
                ·
                  refine ⟨30135152651159923996771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40180203534879898662361 30135152651159923996771)
                  ·
                    rfl

theorem cell20_66024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 2].length) (baseStart_66024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66024 prefixEnd_66024 := by exact prefixLift 66024
  have htrace : WordTrace (prefixWord ++ tailWord_66024) baseStart_66024 baseEnd_66024 := by
    simpa [prefixWord, tailWord_66024, baseEnd_66024] using wordTrace_append hprefix tailTrace_66024
  have hstable : (prefixWord ++ tailWord_66024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66024).length < 2 ^ (prefixWord ++ tailWord_66024).sum := by decide
  have hdescent : baseEnd_66024 < baseStart_66024 := by decide
  rcases family_descends (prefixWord ++ tailWord_66024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66034 : List Nat := [3, 2, 1, 4, 3, 1, 2, 1, 3]
def baseStart_66034 : Nat := 118140960795 + 66034 * 2 ^ 59
def prefixEnd_66034 : Nat := 4983230072969 + 3 ^ 40 * 66034 * 2
def baseEnd_66034 : Nat := 30139716923644333663397

theorem tailTrace_66034 : CollatzResearch.WordTrace tailWord_66034 prefixEnd_66034 30139716923644333663397 := by
  unfold tailWord_66034
  simp only [CollatzResearch.WordTrace]
  refine ⟨602114460694392638611289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1605638561851713702963437 602114460694392638611289)
  ·
    refine ⟨451585845520794478958467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 602114460694392638611289 451585845520794478958467)
    ·
      refine ⟨677378768281191718437701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451585845520794478958467 677378768281191718437701)
      ·
        refine ⟨127008519052723447207069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 677378768281191718437701 127008519052723447207069)
        ·
          refine ⟨47628194644771292702651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127008519052723447207069 47628194644771292702651)
          ·
            refine ⟨71442291967156939053977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47628194644771292702651 71442291967156939053977)
            ·
              refine ⟨53581718975367704290483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71442291967156939053977 53581718975367704290483)
              ·
                refine ⟨80372578463051556435725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53581718975367704290483 80372578463051556435725)
                ·
                  refine ⟨30139716923644333663397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80372578463051556435725 30139716923644333663397)
                  ·
                    rfl

theorem cell20_66034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_66034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66034 prefixEnd_66034 := by exact prefixLift 66034
  have htrace : WordTrace (prefixWord ++ tailWord_66034) baseStart_66034 baseEnd_66034 := by
    simpa [prefixWord, tailWord_66034, baseEnd_66034] using wordTrace_append hprefix tailTrace_66034
  have hstable : (prefixWord ++ tailWord_66034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66034).length < 2 ^ (prefixWord ++ tailWord_66034).sum := by decide
  have hdescent : baseEnd_66034 < baseStart_66034 := by decide
  rcases family_descends (prefixWord ++ tailWord_66034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66083 : List Nat := [1, 1, 1, 4, 4, 2, 1, 4, 2]
def baseStart_66083 : Nat := 118140960795 + 66083 * 2 ^ 59
def prefixEnd_66083 : Nat := 4983230072969 + 3 ^ 40 * 66083 * 2
def baseEnd_66083 : Nat := 30162081858817941029863

theorem tailTrace_66083 : CollatzResearch.WordTrace tailWord_66083 prefixEnd_66083 30162081858817941029863 := by
  unfold tailWord_66083
  simp only [CollatzResearch.WordTrace]
  refine ⟨2410245019600051922978903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1606830013066701281985935 2410245019600051922978903)
  ·
    refine ⟨3615367529400077884468355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2410245019600051922978903 3615367529400077884468355)
    ·
      refine ⟨5423051294100116826702533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3615367529400077884468355 5423051294100116826702533)
      ·
        refine ⟨1016822117643771905006725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5423051294100116826702533 1016822117643771905006725)
        ·
          refine ⟨190654147058207232188761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1016822117643771905006725 190654147058207232188761)
          ·
            refine ⟨142990610293655424141571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190654147058207232188761 142990610293655424141571)
            ·
              refine ⟨214485915440483136212357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142990610293655424141571 214485915440483136212357)
              ·
                refine ⟨40216109145090588039817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214485915440483136212357 40216109145090588039817)
                ·
                  refine ⟨30162081858817941029863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40216109145090588039817 30162081858817941029863)
                  ·
                    rfl

theorem cell20_66083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 2].length) (baseStart_66083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66083 prefixEnd_66083 := by exact prefixLift 66083
  have htrace : WordTrace (prefixWord ++ tailWord_66083) baseStart_66083 baseEnd_66083 := by
    simpa [prefixWord, tailWord_66083, baseEnd_66083] using wordTrace_append hprefix tailTrace_66083
  have hstable : (prefixWord ++ tailWord_66083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66083).length < 2 ^ (prefixWord ++ tailWord_66083).sum := by decide
  have hdescent : baseEnd_66083 < baseStart_66083 := by decide
  rcases family_descends (prefixWord ++ tailWord_66083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66090 : List Nat := [3, 1, 4, 1, 1, 4, 1, 5]
def baseStart_66090 : Nat := 118140960795 + 66090 * 2 ^ 59
def prefixEnd_66090 : Nat := 4983230072969 + 3 ^ 40 * 66090 * 2
def baseEnd_66090 : Nat := 10055092283185675932167

theorem tailTrace_66090 : CollatzResearch.WordTrace tailWord_66090 prefixEnd_66090 10055092283185675932167 := by
  unfold tailWord_66090
  simp only [CollatzResearch.WordTrace]
  refine ⟨602625082643673029620931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1607000220383128078989149 602625082643673029620931)
  ·
    refine ⟨903937623965509544431397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 602625082643673029620931 903937623965509544431397)
    ·
      refine ⟨169488304493533039580887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 903937623965509544431397 169488304493533039580887)
      ·
        refine ⟨254232456740299559371331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169488304493533039580887 254232456740299559371331)
        ·
          refine ⟨381348685110449339056997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254232456740299559371331 381348685110449339056997)
          ·
            refine ⟨71502878458209251073187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 381348685110449339056997 71502878458209251073187)
            ·
              refine ⟨107254317687313876609781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71502878458209251073187 107254317687313876609781)
              ·
                refine ⟨10055092283185675932167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107254317687313876609781 10055092283185675932167)
                ·
                  rfl

theorem cell20_66090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_66090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66090 prefixEnd_66090 := by exact prefixLift 66090
  have htrace : WordTrace (prefixWord ++ tailWord_66090) baseStart_66090 baseEnd_66090 := by
    simpa [prefixWord, tailWord_66090, baseEnd_66090] using wordTrace_append hprefix tailTrace_66090
  have hstable : (prefixWord ++ tailWord_66090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66090).length < 2 ^ (prefixWord ++ tailWord_66090).sum := by decide
  have hdescent : baseEnd_66090 < baseStart_66090 := by decide
  rcases family_descends (prefixWord ++ tailWord_66090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66100 : List Nat := [2, 5, 1, 3, 1, 1, 1, 2, 4]
def baseStart_66100 : Nat := 118140960795 + 66100 * 2 ^ 59
def prefixEnd_66100 : Nat := 4983230072969 + 3 ^ 40 * 66100 * 2
def baseEnd_66100 : Nat := 30169841122041437463127

theorem tailTrace_66100 : CollatzResearch.WordTrace tailWord_66100 prefixEnd_66100 30169841122041437463127 := by
  unfold tailWord_66100
  simp only [CollatzResearch.WordTrace]
  refine ⟨1205432530269231913173877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1607243373692309217565169 1205432530269231913173877)
  ·
    refine ⟨113009299712740491860051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1205432530269231913173877 113009299712740491860051)
    ·
      refine ⟨169513949569110737790077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113009299712740491860051 169513949569110737790077)
      ·
        refine ⟨63567731088416526671279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169513949569110737790077 63567731088416526671279)
        ·
          refine ⟨95351596632624790006919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63567731088416526671279 95351596632624790006919)
          ·
            refine ⟨143027394948937185010379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95351596632624790006919 143027394948937185010379)
            ·
              refine ⟨214541092423405777515569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143027394948937185010379 214541092423405777515569)
              ·
                refine ⟨160905819317554333136677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214541092423405777515569 160905819317554333136677)
                ·
                  refine ⟨30169841122041437463127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160905819317554333136677 30169841122041437463127)
                  ·
                    rfl

theorem cell20_66100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_66100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66100 prefixEnd_66100 := by exact prefixLift 66100
  have htrace : WordTrace (prefixWord ++ tailWord_66100) baseStart_66100 baseEnd_66100 := by
    simpa [prefixWord, tailWord_66100, baseEnd_66100] using wordTrace_append hprefix tailTrace_66100
  have hstable : (prefixWord ++ tailWord_66100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66100).length < 2 ^ (prefixWord ++ tailWord_66100).sum := by decide
  have hdescent : baseEnd_66100 < baseStart_66100 := by decide
  rcases family_descends (prefixWord ++ tailWord_66100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66111 : List Nat := [1, 1, 2, 2, 3, 2, 5, 4]
def baseStart_66111 : Nat := 118140960795 + 66111 * 2 ^ 59
def prefixEnd_66111 : Nat := 4983230072969 + 3 ^ 40 * 66111 * 2
def baseEnd_66111 : Nat := 10058287273924762698805

theorem tailTrace_66111 : CollatzResearch.WordTrace tailWord_66111 prefixEnd_66111 10058287273924762698805 := by
  unfold tailWord_66111
  simp only [CollatzResearch.WordTrace]
  refine ⟨2411266263498612704998187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1607510842332408469998791 2411266263498612704998187)
  ·
    refine ⟨3616899395247919057497281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2411266263498612704998187 3616899395247919057497281)
    ·
      refine ⟨2712674546435939293122961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3616899395247919057497281 2712674546435939293122961)
      ·
        refine ⟨2034505909826954469842221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2712674546435939293122961 2034505909826954469842221)
        ·
          refine ⟨762939716185107926190833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2034505909826954469842221 762939716185107926190833)
          ·
            refine ⟨572204787138830944643125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 762939716185107926190833 572204787138830944643125)
            ·
              refine ⟨53644198794265401060293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 572204787138830944643125 53644198794265401060293)
              ·
                refine ⟨10058287273924762698805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53644198794265401060293 10058287273924762698805)
                ·
                  rfl

theorem cell20_66111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 4].length) (baseStart_66111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66111 prefixEnd_66111 := by exact prefixLift 66111
  have htrace : WordTrace (prefixWord ++ tailWord_66111) baseStart_66111 baseEnd_66111 := by
    simpa [prefixWord, tailWord_66111, baseEnd_66111] using wordTrace_append hprefix tailTrace_66111
  have hstable : (prefixWord ++ tailWord_66111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66111).length < 2 ^ (prefixWord ++ tailWord_66111).sum := by decide
  have hdescent : baseEnd_66111 < baseStart_66111 := by decide
  rcases family_descends (prefixWord ++ tailWord_66111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66156 : List Nat := [2, 2, 1, 1, 3, 1, 2, 5, 3]
def baseStart_66156 : Nat := 118140960795 + 66156 * 2 ^ 59
def prefixEnd_66156 : Nat := 4983230072969 + 3 ^ 40 * 66156 * 2
def baseEnd_66156 : Nat := 30195401047954131596231

theorem tailTrace_66156 : CollatzResearch.WordTrace tailWord_66156 prefixEnd_66156 30195401047954131596231 := by
  unfold tailWord_66156
  simp only [CollatzResearch.WordTrace]
  refine ⟨1206453774167792695193161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1608605032223723593590881 1206453774167792695193161)
  ·
    refine ⟨904840330625844521394871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1206453774167792695193161 904840330625844521394871)
    ·
      refine ⟨1357260495938766782092307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 904840330625844521394871 1357260495938766782092307)
      ·
        refine ⟨2035890743908150173138461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1357260495938766782092307 2035890743908150173138461)
        ·
          refine ⟨763459028965556314926923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2035890743908150173138461 763459028965556314926923)
          ·
            refine ⟨1145188543448334472390385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763459028965556314926923 1145188543448334472390385)
            ·
              refine ⟨858891407586250854292789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1145188543448334472390385 858891407586250854292789)
              ·
                refine ⟨80521069461211017589949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 858891407586250854292789 80521069461211017589949)
                ·
                  refine ⟨30195401047954131596231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80521069461211017589949 30195401047954131596231)
                  ·
                    rfl

theorem cell20_66156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_66156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66156 prefixEnd_66156 := by exact prefixLift 66156
  have htrace : WordTrace (prefixWord ++ tailWord_66156) baseStart_66156 baseEnd_66156 := by
    simpa [prefixWord, tailWord_66156, baseEnd_66156] using wordTrace_append hprefix tailTrace_66156
  have hstable : (prefixWord ++ tailWord_66156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66156).length < 2 ^ (prefixWord ++ tailWord_66156).sum := by decide
  have hdescent : baseEnd_66156 < baseStart_66156 := by decide
  rcases family_descends (prefixWord ++ tailWord_66156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66166 : List Nat := [5, 1, 1, 2, 3, 1, 1, 6]
def baseStart_66166 : Nat := 118140960795 + 66166 * 2 ^ 59
def prefixEnd_66166 : Nat := 4983230072969 + 3 ^ 40 * 66166 * 2
def baseEnd_66166 : Nat := 10066655106812847087619

theorem tailTrace_66166 : CollatzResearch.WordTrace tailWord_66166 prefixEnd_66166 10066655106812847087619 := by
  unfold tailWord_66166
  simp only [CollatzResearch.WordTrace]
  refine ⟨150829517393709818640647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1608848185532904732166901 150829517393709818640647)
  ·
    refine ⟨226244276090564727960971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150829517393709818640647 226244276090564727960971)
    ·
      refine ⟨339366414135847091941457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226244276090564727960971 339366414135847091941457)
      ·
        refine ⟨254524810601885318956093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339366414135847091941457 254524810601885318956093)
        ·
          refine ⟨95446803975706994608535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254524810601885318956093 95446803975706994608535)
          ·
            refine ⟨143170205963560491912803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95446803975706994608535 143170205963560491912803)
            ·
              refine ⟨214755308945340737869205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143170205963560491912803 214755308945340737869205)
              ·
                refine ⟨10066655106812847087619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 214755308945340737869205 10066655106812847087619)
                ·
                  rfl

theorem cell20_66166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_66166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66166 prefixEnd_66166 := by exact prefixLift 66166
  have htrace : WordTrace (prefixWord ++ tailWord_66166) baseStart_66166 baseEnd_66166 := by
    simpa [prefixWord, tailWord_66166, baseEnd_66166] using wordTrace_append hprefix tailTrace_66166
  have hstable : (prefixWord ++ tailWord_66166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66166).length < 2 ^ (prefixWord ++ tailWord_66166).sum := by decide
  have hdescent : baseEnd_66166 < baseStart_66166 := by decide
  rcases family_descends (prefixWord ++ tailWord_66166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66252 : List Nat := [2, 2, 1, 5, 1, 1, 4, 2, 2]
def baseStart_66252 : Nat := 118140960795 + 66252 * 2 ^ 59
def prefixEnd_66252 : Nat := 4983230072969 + 3 ^ 40 * 66252 * 2
def baseEnd_66252 : Nat := 30239218063804464395839

theorem tailTrace_66252 : CollatzResearch.WordTrace tailWord_66252 prefixEnd_66252 30239218063804464395839 := by
  unfold tailWord_66252
  simp only [CollatzResearch.WordTrace]
  refine ⟨1208204477993896892940505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1610939303991862523920673 1208204477993896892940505)
  ·
    refine ⟨906153358495422669705379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1208204477993896892940505 906153358495422669705379)
    ·
      refine ⟨1359230037743134004558069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 906153358495422669705379 1359230037743134004558069)
      ·
        refine ⟨127427816038418812927319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1359230037743134004558069 127427816038418812927319)
        ·
          refine ⟨191141724057628219390979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127427816038418812927319 191141724057628219390979)
          ·
            refine ⟨286712586086442329086469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191141724057628219390979 286712586086442329086469)
            ·
              refine ⟨53758609891207936703713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286712586086442329086469 53758609891207936703713)
              ·
                refine ⟨40318957418405952527785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53758609891207936703713 40318957418405952527785)
                ·
                  refine ⟨30239218063804464395839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40318957418405952527785 30239218063804464395839)
                  ·
                    rfl

theorem cell20_66252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_66252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66252 prefixEnd_66252 := by exact prefixLift 66252
  have htrace : WordTrace (prefixWord ++ tailWord_66252) baseStart_66252 baseEnd_66252 := by
    simpa [prefixWord, tailWord_66252, baseEnd_66252] using wordTrace_append hprefix tailTrace_66252
  have hstable : (prefixWord ++ tailWord_66252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66252).length < 2 ^ (prefixWord ++ tailWord_66252).sum := by decide
  have hdescent : baseEnd_66252 < baseStart_66252 := by decide
  rcases family_descends (prefixWord ++ tailWord_66252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66263 : List Nat := [1, 1, 3, 2, 1, 6, 1, 5]
def baseStart_66263 : Nat := 118140960795 + 66263 * 2 ^ 59
def prefixEnd_66263 : Nat := 4983230072969 + 3 ^ 40 * 66263 * 2
def baseEnd_66263 : Nat := 10081412921179105009709

theorem tailTrace_66263 : CollatzResearch.WordTrace tailWord_66263 prefixEnd_66263 10081412921179105009709 := by
  unfold tailWord_66263
  simp only [CollatzResearch.WordTrace]
  refine ⟨2416810158947942664531443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1611206772631961776354295 2416810158947942664531443)
  ·
    refine ⟨3625215238421913996797165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2416810158947942664531443 3625215238421913996797165)
    ·
      refine ⟨1359455714408217748798937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3625215238421913996797165 1359455714408217748798937)
      ·
        refine ⟨1019591785806163311599203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1359455714408217748798937 1019591785806163311599203)
        ·
          refine ⟨1529387678709244967398805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019591785806163311599203 1529387678709244967398805)
          ·
            refine ⟨71690047439495857846819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1529387678709244967398805 71690047439495857846819)
            ·
              refine ⟨107535071159243786770229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71690047439495857846819 107535071159243786770229)
              ·
                refine ⟨10081412921179105009709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107535071159243786770229 10081412921179105009709)
                ·
                  rfl

theorem cell20_66263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 5].length) (baseStart_66263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66263 prefixEnd_66263 := by exact prefixLift 66263
  have htrace : WordTrace (prefixWord ++ tailWord_66263) baseStart_66263 baseEnd_66263 := by
    simpa [prefixWord, tailWord_66263, baseEnd_66263] using wordTrace_append hprefix tailTrace_66263
  have hstable : (prefixWord ++ tailWord_66263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66263).length < 2 ^ (prefixWord ++ tailWord_66263).sum := by decide
  have hdescent : baseEnd_66263 < baseStart_66263 := by decide
  rcases family_descends (prefixWord ++ tailWord_66263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66277 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 6]
def baseStart_66277 : Nat := 118140960795 + 66277 * 2 ^ 59
def prefixEnd_66277 : Nat := 4983230072969 + 3 ^ 40 * 66277 * 2
def baseEnd_66277 : Nat := 30250628745015488562403

theorem tailTrace_66277 : CollatzResearch.WordTrace tailWord_66277 prefixEnd_66277 30250628745015488562403 := by
  unfold tailWord_66277
  simp only [CollatzResearch.WordTrace]
  refine ⟨2417320780897223055541085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1611547187264815370360723 2417320780897223055541085)
  ·
    refine ⟨906495292836458645827907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2417320780897223055541085 906495292836458645827907)
    ·
      refine ⟨1359742939254687968741861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 906495292836458645827907 1359742939254687968741861)
      ·
        refine ⟨254951801110253994139099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1359742939254687968741861 254951801110253994139099)
        ·
          refine ⟨382427701665380991208649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254951801110253994139099 382427701665380991208649)
          ·
            refine ⟨286820776249035743406487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382427701665380991208649 286820776249035743406487)
            ·
              refine ⟨430231164373553615109731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286820776249035743406487 430231164373553615109731)
              ·
                refine ⟨645346746560330422664597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430231164373553615109731 645346746560330422664597)
                ·
                  refine ⟨30250628745015488562403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 645346746560330422664597 30250628745015488562403)
                  ·
                    rfl

theorem cell20_66277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_66277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66277 prefixEnd_66277 := by exact prefixLift 66277
  have htrace : WordTrace (prefixWord ++ tailWord_66277) baseStart_66277 baseEnd_66277 := by
    simpa [prefixWord, tailWord_66277, baseEnd_66277] using wordTrace_append hprefix tailTrace_66277
  have hstable : (prefixWord ++ tailWord_66277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66277).length < 2 ^ (prefixWord ++ tailWord_66277).sum := by decide
  have hdescent : baseEnd_66277 < baseStart_66277 := by decide
  rcases family_descends (prefixWord ++ tailWord_66277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66280 : List Nat := [2, 1, 4, 1, 4, 1, 3, 4]
def baseStart_66280 : Nat := 118140960795 + 66280 * 2 ^ 59
def prefixEnd_66280 : Nat := 4983230072969 + 3 ^ 40 * 66280 * 2
def baseEnd_66280 : Nat := 10083999342253603820797

theorem tailTrace_66280 : CollatzResearch.WordTrace tailWord_66280 prefixEnd_66280 10083999342253603820797 := by
  unfold tailWord_66280
  simp only [CollatzResearch.WordTrace]
  refine ⟨1208715099943177283950147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1611620133257569711933529 1208715099943177283950147)
  ·
    refine ⟨1813072649914765925925221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1208715099943177283950147 1813072649914765925925221)
    ·
      refine ⟨339951121859018611110979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1813072649914765925925221 339951121859018611110979)
      ·
        refine ⟨509926682788527916666469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339951121859018611110979 509926682788527916666469)
        ·
          refine ⟨95611253022848984374963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 509926682788527916666469 95611253022848984374963)
          ·
            refine ⟨143416879534273476562445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95611253022848984374963 143416879534273476562445)
            ·
              refine ⟨53781329825352553710917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143416879534273476562445 53781329825352553710917)
              ·
                refine ⟨10083999342253603820797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53781329825352553710917 10083999342253603820797)
                ·
                  rfl

theorem cell20_66280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_66280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66280 prefixEnd_66280 := by exact prefixLift 66280
  have htrace : WordTrace (prefixWord ++ tailWord_66280) baseStart_66280 baseEnd_66280 := by
    simpa [prefixWord, tailWord_66280, baseEnd_66280] using wordTrace_append hprefix tailTrace_66280
  have hstable : (prefixWord ++ tailWord_66280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66280).length < 2 ^ (prefixWord ++ tailWord_66280).sum := by decide
  have hdescent : baseEnd_66280 < baseStart_66280 := by decide
  rcases family_descends (prefixWord ++ tailWord_66280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66291 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 5]
def baseStart_66291 : Nat := 118140960795 + 66291 * 2 ^ 59
def prefixEnd_66291 : Nat := 4983230072969 + 3 ^ 40 * 66291 * 2
def baseEnd_66291 : Nat := 30257018726493662095679

theorem tailTrace_66291 : CollatzResearch.WordTrace tailWord_66291 prefixEnd_66291 30257018726493662095679 := by
  unfold tailWord_66291
  simp only [CollatzResearch.WordTrace]
  refine ⟨2417831402846503446550727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1611887601897668964367151 2417831402846503446550727)
  ·
    refine ⟨3626747104269755169826091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2417831402846503446550727 3626747104269755169826091)
    ·
      refine ⟨5440120656404632754739137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3626747104269755169826091 5440120656404632754739137)
      ·
        refine ⟨4080090492303474566054353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5440120656404632754739137 4080090492303474566054353)
        ·
          refine ⟨3060067869227605924540765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4080090492303474566054353 3060067869227605924540765)
          ·
            refine ⟨1147525450960352221702787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3060067869227605924540765 1147525450960352221702787)
            ·
              refine ⟨1721288176440528332554181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147525450960352221702787 1721288176440528332554181)
              ·
                refine ⟨322741533082599062353909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1721288176440528332554181 322741533082599062353909)
                ·
                  refine ⟨30257018726493662095679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 322741533082599062353909 30257018726493662095679)
                  ·
                    rfl

theorem cell20_66291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_66291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66291 prefixEnd_66291 := by exact prefixLift 66291
  have htrace : WordTrace (prefixWord ++ tailWord_66291) baseStart_66291 baseEnd_66291 := by
    simpa [prefixWord, tailWord_66291, baseEnd_66291] using wordTrace_append hprefix tailTrace_66291
  have hstable : (prefixWord ++ tailWord_66291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66291).length < 2 ^ (prefixWord ++ tailWord_66291).sum := by decide
  have hdescent : baseEnd_66291 < baseStart_66291 := by decide
  rcases family_descends (prefixWord ++ tailWord_66291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66308 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 5]
def baseStart_66308 : Nat := 118140960795 + 66308 * 2 ^ 59
def prefixEnd_66308 : Nat := 4983230072969 + 3 ^ 40 * 66308 * 2
def baseEnd_66308 : Nat := 30264777989717158528943

theorem tailTrace_66308 : CollatzResearch.WordTrace tailWord_66308 prefixEnd_66308 30264777989717158528943 := by
  unfold tailWord_66308
  simp only [CollatzResearch.WordTrace]
  refine ⟨1209225721892457674959789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1612300962523276899946385 1209225721892457674959789)
  ·
    refine ⟨453459645709671628109921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1209225721892457674959789 453459645709671628109921)
    ·
      refine ⟨340094734282253721082441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453459645709671628109921 340094734282253721082441)
      ·
        refine ⟨255071050711690290811831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340094734282253721082441 255071050711690290811831)
        ·
          refine ⟨382606576067535436217747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255071050711690290811831 382606576067535436217747)
          ·
            refine ⟨573909864101303154326621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382606576067535436217747 573909864101303154326621)
            ·
              refine ⟨215216199037988682872483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 573909864101303154326621 215216199037988682872483)
              ·
                refine ⟨322824298556983024308725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215216199037988682872483 322824298556983024308725)
                ·
                  refine ⟨30264777989717158528943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 322824298556983024308725 30264777989717158528943)
                  ·
                    rfl

theorem cell20_66308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_66308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66308 prefixEnd_66308 := by exact prefixLift 66308
  have htrace : WordTrace (prefixWord ++ tailWord_66308) baseStart_66308 baseEnd_66308 := by
    simpa [prefixWord, tailWord_66308, baseEnd_66308] using wordTrace_append hprefix tailTrace_66308
  have hstable : (prefixWord ++ tailWord_66308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66308).length < 2 ^ (prefixWord ++ tailWord_66308).sum := by decide
  have hdescent : baseEnd_66308 < baseStart_66308 := by decide
  rcases family_descends (prefixWord ++ tailWord_66308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66311 : List Nat := [1, 1, 4, 4, 1, 1, 2, 4, 2]
def baseStart_66311 : Nat := 118140960795 + 66311 * 2 ^ 59
def prefixEnd_66311 : Nat := 4983230072969 + 3 ^ 40 * 66311 * 2
def baseEnd_66311 : Nat := 30266147271462481428931

theorem tailTrace_66311 : CollatzResearch.WordTrace tailWord_66311 prefixEnd_66311 30266147271462481428931 := by
  unfold tailWord_66311
  simp only [CollatzResearch.WordTrace]
  refine ⟨2418560862774046862278787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1612373908516031241519191 2418560862774046862278787)
  ·
    refine ⟨3627841294161070293418181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2418560862774046862278787 3627841294161070293418181)
    ·
      refine ⟨680220242655200680015909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3627841294161070293418181 680220242655200680015909)
      ·
        refine ⟨127541295497850127502983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 680220242655200680015909 127541295497850127502983)
        ·
          refine ⟨191311943246775191254475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127541295497850127502983 191311943246775191254475)
          ·
            refine ⟨286967914870162786881713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191311943246775191254475 286967914870162786881713)
            ·
              refine ⟨215225936152622090161285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286967914870162786881713 215225936152622090161285)
              ·
                refine ⟨40354863028616641905241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215225936152622090161285 40354863028616641905241)
                ·
                  refine ⟨30266147271462481428931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40354863028616641905241 30266147271462481428931)
                  ·
                    rfl

theorem cell20_66311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 2].length) (baseStart_66311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66311 prefixEnd_66311 := by exact prefixLift 66311
  have htrace : WordTrace (prefixWord ++ tailWord_66311) baseStart_66311 baseEnd_66311 := by
    simpa [prefixWord, tailWord_66311, baseEnd_66311] using wordTrace_append hprefix tailTrace_66311
  have hstable : (prefixWord ++ tailWord_66311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66311).length < 2 ^ (prefixWord ++ tailWord_66311).sum := by decide
  have hdescent : baseEnd_66311 < baseStart_66311 := by decide
  rcases family_descends (prefixWord ++ tailWord_66311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66325 : List Nat := [1, 3, 2, 1, 2, 2, 5, 1, 3]
def baseStart_66325 : Nat := 118140960795 + 66325 * 2 ^ 59
def prefixEnd_66325 : Nat := 4983230072969 + 3 ^ 40 * 66325 * 2
def baseEnd_66325 : Nat := 30272537252940654962207

theorem tailTrace_66325 : CollatzResearch.WordTrace tailWord_66325 prefixEnd_66325 30272537252940654962207 := by
  unfold tailWord_66325
  simp only [CollatzResearch.WordTrace]
  refine ⟨2419071484723327253288429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1612714323148884835525619 2419071484723327253288429)
  ·
    refine ⟨907151806771247719983161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2419071484723327253288429 907151806771247719983161)
    ·
      refine ⟨680363855078435789987371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 907151806771247719983161 680363855078435789987371)
      ·
        refine ⟨1020545782617653684981057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680363855078435789987371 1020545782617653684981057)
        ·
          refine ⟨765409336963240263735793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1020545782617653684981057 765409336963240263735793)
          ·
            refine ⟨574057002722430197801845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765409336963240263735793 574057002722430197801845)
            ·
              refine ⟨53817844005227831043923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 574057002722430197801845 53817844005227831043923)
              ·
                refine ⟨80726766007841746565885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53817844005227831043923 80726766007841746565885)
                ·
                  refine ⟨30272537252940654962207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80726766007841746565885 30272537252940654962207)
                  ·
                    rfl

theorem cell20_66325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_66325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66325 prefixEnd_66325 := by exact prefixLift 66325
  have htrace : WordTrace (prefixWord ++ tailWord_66325) baseStart_66325 baseEnd_66325 := by
    simpa [prefixWord, tailWord_66325, baseEnd_66325] using wordTrace_append hprefix tailTrace_66325
  have hstable : (prefixWord ++ tailWord_66325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66325).length < 2 ^ (prefixWord ++ tailWord_66325).sum := by decide
  have hdescent : baseEnd_66325 < baseStart_66325 := by decide
  rcases family_descends (prefixWord ++ tailWord_66325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66356 : List Nat := [2, 5, 1, 1, 3, 2, 6]
def baseStart_66356 : Nat := 118140960795 + 66356 * 2 ^ 59
def prefixEnd_66356 : Nat := 4983230072969 + 3 ^ 40 * 66356 * 2
def baseEnd_66356 : Nat := 3365187388626924992083

theorem tailTrace_66356 : CollatzResearch.WordTrace tailWord_66356 prefixEnd_66356 3365187388626924992083 := by
  unfold tailWord_66356
  simp only [CollatzResearch.WordTrace]
  refine ⟨1210101073805509773833461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1613468098407346365111281 1210101073805509773833461)
  ·
    refine ⟨113446975669266541296887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1210101073805509773833461 113446975669266541296887)
    ·
      refine ⟨170170463503899811945331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113446975669266541296887 170170463503899811945331)
      ·
        refine ⟨255255695255849717917997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170170463503899811945331 255255695255849717917997)
        ·
          refine ⟨95720885720943644219249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255255695255849717917997 95720885720943644219249)
          ·
            refine ⟨71790664290707733164437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95720885720943644219249 71790664290707733164437)
            ·
              refine ⟨3365187388626924992083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71790664290707733164437 3365187388626924992083)
              ·
                rfl

theorem cell20_66356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 6].length) (baseStart_66356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66356 prefixEnd_66356 := by exact prefixLift 66356
  have htrace : WordTrace (prefixWord ++ tailWord_66356) baseStart_66356 baseEnd_66356 := by
    simpa [prefixWord, tailWord_66356, baseEnd_66356] using wordTrace_append hprefix tailTrace_66356
  have hstable : (prefixWord ++ tailWord_66356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66356).length < 2 ^ (prefixWord ++ tailWord_66356).sum := by decide
  have hdescent : baseEnd_66356 < baseStart_66356 := by decide
  rcases family_descends (prefixWord ++ tailWord_66356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66366 : List Nat := [4, 2, 1, 2, 4, 1, 1, 1, 4]
def baseStart_66366 : Nat := 118140960795 + 66366 * 2 ^ 59
def prefixEnd_66366 : Nat := 4983230072969 + 3 ^ 40 * 66366 * 2
def baseEnd_66366 : Nat := 30291250770126734595373

theorem tailTrace_66366 : CollatzResearch.WordTrace tailWord_66366 prefixEnd_66366 30291250770126734595373 := by
  unfold tailWord_66366
  simp only [CollatzResearch.WordTrace]
  refine ⟨302570859696848906941369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1613711251716527503687301 302570859696848906941369)
  ·
    refine ⟨226928144772636680206027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302570859696848906941369 226928144772636680206027)
    ·
      refine ⟨340392217158955020309041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226928144772636680206027 340392217158955020309041)
      ·
        refine ⟨255294162869216265231781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340392217158955020309041 255294162869216265231781)
        ·
          refine ⟨47867655537978049730959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255294162869216265231781 47867655537978049730959)
          ·
            refine ⟨71801483306967074596439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47867655537978049730959 71801483306967074596439)
            ·
              refine ⟨107702224960450611894659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71801483306967074596439 107702224960450611894659)
              ·
                refine ⟨161553337440675917841989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107702224960450611894659 161553337440675917841989)
                ·
                  refine ⟨30291250770126734595373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161553337440675917841989 30291250770126734595373)
                  ·
                    rfl

theorem cell20_66366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_66366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66366 prefixEnd_66366 := by exact prefixLift 66366
  have htrace : WordTrace (prefixWord ++ tailWord_66366) baseStart_66366 baseEnd_66366 := by
    simpa [prefixWord, tailWord_66366, baseEnd_66366] using wordTrace_append hprefix tailTrace_66366
  have hstable : (prefixWord ++ tailWord_66366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66366).length < 2 ^ (prefixWord ++ tailWord_66366).sum := by decide
  have hdescent : baseEnd_66366 < baseStart_66366 := by decide
  rcases family_descends (prefixWord ++ tailWord_66366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66380 : List Nat := [2, 2, 1, 3, 3, 3, 2, 1, 3]
def baseStart_66380 : Nat := 118140960795 + 66380 * 2 ^ 59
def prefixEnd_66380 : Nat := 4983230072969 + 3 ^ 40 * 66380 * 2
def baseEnd_66380 : Nat := 30297640751604908128649

theorem tailTrace_66380 : CollatzResearch.WordTrace tailWord_66380 prefixEnd_66380 30297640751604908128649 := by
  unfold tailWord_66380
  simp only [CollatzResearch.WordTrace]
  refine ⟨1210538749762035823270297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1614051666349381097693729 1210538749762035823270297)
  ·
    refine ⟨907904062321526867452723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1210538749762035823270297 907904062321526867452723)
    ·
      refine ⟨1361856093482290301179085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 907904062321526867452723 1361856093482290301179085)
      ·
        refine ⟨510696035055858862942157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1361856093482290301179085 510696035055858862942157)
        ·
          refine ⟨191511013145947073603309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 510696035055858862942157 191511013145947073603309)
          ·
            refine ⟨71816629929730152601241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191511013145947073603309 71816629929730152601241)
            ·
              refine ⟨53862472447297614450931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71816629929730152601241 53862472447297614450931)
              ·
                refine ⟨80793708670946421676397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53862472447297614450931 80793708670946421676397)
                ·
                  refine ⟨30297640751604908128649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80793708670946421676397 30297640751604908128649)
                  ·
                    rfl

theorem cell20_66380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_66380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66380 prefixEnd_66380 := by exact prefixLift 66380
  have htrace : WordTrace (prefixWord ++ tailWord_66380) baseStart_66380 baseEnd_66380 := by
    simpa [prefixWord, tailWord_66380, baseEnd_66380] using wordTrace_append hprefix tailTrace_66380
  have hstable : (prefixWord ++ tailWord_66380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66380).length < 2 ^ (prefixWord ++ tailWord_66380).sum := by decide
  have hdescent : baseEnd_66380 < baseStart_66380 := by decide
  rcases family_descends (prefixWord ++ tailWord_66380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66405 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 7]
def baseStart_66405 : Nat := 118140960795 + 66405 * 2 ^ 59
def prefixEnd_66405 : Nat := 4983230072969 + 3 ^ 40 * 66405 * 2
def baseEnd_66405 : Nat := 30309051432815932295213

theorem tailTrace_66405 : CollatzResearch.WordTrace tailWord_66405 prefixEnd_66405 30309051432815932295213 := by
  unfold tailWord_66405
  simp only [CollatzResearch.WordTrace]
  refine ⟨2421989324433500916200669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1614659549622333944133779 2421989324433500916200669)
  ·
    refine ⟨908245996662562843575251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2421989324433500916200669 908245996662562843575251)
    ·
      refine ⟨1362368994993844265362877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 908245996662562843575251 1362368994993844265362877)
      ·
        refine ⟨510888373122691599511079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1362368994993844265362877 510888373122691599511079)
        ·
          refine ⟨766332559684037399266619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510888373122691599511079 766332559684037399266619)
          ·
            refine ⟨1149498839526056098899929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766332559684037399266619 1149498839526056098899929)
            ·
              refine ⟨862124129644542074174947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1149498839526056098899929 862124129644542074174947)
              ·
                refine ⟨1293186194466813111262421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862124129644542074174947 1293186194466813111262421)
                ·
                  refine ⟨30309051432815932295213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1293186194466813111262421 30309051432815932295213)
                  ·
                    rfl

theorem cell20_66405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_66405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66405 prefixEnd_66405 := by exact prefixLift 66405
  have htrace : WordTrace (prefixWord ++ tailWord_66405) baseStart_66405 baseEnd_66405 := by
    simpa [prefixWord, tailWord_66405, baseEnd_66405] using wordTrace_append hprefix tailTrace_66405
  have hstable : (prefixWord ++ tailWord_66405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66405).length < 2 ^ (prefixWord ++ tailWord_66405).sum := by decide
  have hdescent : baseEnd_66405 < baseStart_66405 := by decide
  rcases family_descends (prefixWord ++ tailWord_66405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66425 : List Nat := [1, 2, 1, 3, 2, 3, 4, 2, 2]
def baseStart_66425 : Nat := 118140960795 + 66425 * 2 ^ 59
def prefixEnd_66425 : Nat := 4983230072969 + 3 ^ 40 * 66425 * 2
def baseEnd_66425 : Nat := 30318179977784751628465

theorem tailTrace_66425 : CollatzResearch.WordTrace tailWord_66425 prefixEnd_66425 30318179977784751628465 := by
  unfold tailWord_66425
  simp only [CollatzResearch.WordTrace]
  refine ⟨2422718784361044331928729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1615145856240696221285819 2422718784361044331928729)
  ·
    refine ⟨1817039088270783248946547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2422718784361044331928729 1817039088270783248946547)
    ·
      refine ⟨2725558632406174873419821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1817039088270783248946547 2725558632406174873419821)
      ·
        refine ⟨1022084487152315577532433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2725558632406174873419821 1022084487152315577532433)
        ·
          refine ⟨766563365364236683149325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1022084487152315577532433 766563365364236683149325)
          ·
            refine ⟨287461262011588756180997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 766563365364236683149325 287461262011588756180997)
            ·
              refine ⟨53898986627172891783937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287461262011588756180997 53898986627172891783937)
              ·
                refine ⟨40424239970379668837953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53898986627172891783937 40424239970379668837953)
                ·
                  refine ⟨30318179977784751628465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40424239970379668837953 30318179977784751628465)
                  ·
                    rfl

theorem cell20_66425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 2].length) (baseStart_66425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66425 prefixEnd_66425 := by exact prefixLift 66425
  have htrace : WordTrace (prefixWord ++ tailWord_66425) baseStart_66425 baseEnd_66425 := by
    simpa [prefixWord, tailWord_66425, baseEnd_66425] using wordTrace_append hprefix tailTrace_66425
  have hstable : (prefixWord ++ tailWord_66425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66425).length < 2 ^ (prefixWord ++ tailWord_66425).sum := by decide
  have hdescent : baseEnd_66425 < baseStart_66425 := by decide
  rcases family_descends (prefixWord ++ tailWord_66425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66453 : List Nat := [1, 3, 2, 1, 1, 5, 3, 4]
def baseStart_66453 : Nat := 118140960795 + 66453 * 2 ^ 59
def prefixEnd_66453 : Nat := 4983230072969 + 3 ^ 40 * 66453 * 2
def baseEnd_66453 : Nat := 10110319980247032898339

theorem tailTrace_66453 : CollatzResearch.WordTrace tailWord_66453 prefixEnd_66453 10110319980247032898339 := by
  unfold tailWord_66453
  simp only [CollatzResearch.WordTrace]
  refine ⟨2423740028259605113948013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1615826685506403409298675 2423740028259605113948013)
  ·
    refine ⟨908902510597351917730505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2423740028259605113948013 908902510597351917730505)
    ·
      refine ⟨681676882948013938297879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 908902510597351917730505 681676882948013938297879)
      ·
        refine ⟨1022515324422020907446819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681676882948013938297879 1022515324422020907446819)
        ·
          refine ⟨1533772986633031361170229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022515324422020907446819 1533772986633031361170229)
          ·
            refine ⟨143791217496846690109709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1533772986633031361170229 143791217496846690109709)
            ·
              refine ⟨53921706561317508791141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143791217496846690109709 53921706561317508791141)
              ·
                refine ⟨10110319980247032898339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53921706561317508791141 10110319980247032898339)
                ·
                  rfl

theorem cell20_66453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 4].length) (baseStart_66453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66453 prefixEnd_66453 := by exact prefixLift 66453
  have htrace : WordTrace (prefixWord ++ tailWord_66453) baseStart_66453 baseEnd_66453 := by
    simpa [prefixWord, tailWord_66453, baseEnd_66453] using wordTrace_append hprefix tailTrace_66453
  have hstable : (prefixWord ++ tailWord_66453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66453).length < 2 ^ (prefixWord ++ tailWord_66453).sum := by decide
  have hdescent : baseEnd_66453 < baseStart_66453 := by decide
  rcases family_descends (prefixWord ++ tailWord_66453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66463 : List Nat := [1, 1, 2, 5, 2, 2, 2, 3, 2]
def baseStart_66463 : Nat := 118140960795 + 66463 * 2 ^ 59
def prefixEnd_66463 : Nat := 4983230072969 + 3 ^ 40 * 66463 * 2
def baseEnd_66463 : Nat := 30335524213225508361643

theorem tailTrace_66463 : CollatzResearch.WordTrace tailWord_66463 prefixEnd_66463 30335524213225508361643 := by
  unfold tailWord_66463
  simp only [CollatzResearch.WordTrace]
  refine ⟨2424104758223376821812043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1616069838815584547874695 2424104758223376821812043)
  ·
    refine ⟨3636157137335065232718065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2424104758223376821812043 3636157137335065232718065)
    ·
      refine ⟨2727117853001298924538549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3636157137335065232718065 2727117853001298924538549)
      ·
        refine ⟨255667298718871774175489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2727117853001298924538549 255667298718871774175489)
        ·
          refine ⟨191750474039153830631617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255667298718871774175489 191750474039153830631617)
          ·
            refine ⟨143812855529365372973713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191750474039153830631617 143812855529365372973713)
            ·
              refine ⟨107859641647024029730285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143812855529365372973713 107859641647024029730285)
              ·
                refine ⟨40447365617634011148857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107859641647024029730285 40447365617634011148857)
                ·
                  refine ⟨30335524213225508361643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40447365617634011148857 30335524213225508361643)
                  ·
                    rfl

theorem cell20_66463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 2].length) (baseStart_66463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66463 prefixEnd_66463 := by exact prefixLift 66463
  have htrace : WordTrace (prefixWord ++ tailWord_66463) baseStart_66463 baseEnd_66463 := by
    simpa [prefixWord, tailWord_66463, baseEnd_66463] using wordTrace_append hprefix tailTrace_66463
  have hstable : (prefixWord ++ tailWord_66463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66463).length < 2 ^ (prefixWord ++ tailWord_66463).sum := by decide
  have hdescent : baseEnd_66463 < baseStart_66463 := by decide
  rcases family_descends (prefixWord ++ tailWord_66463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66518 : List Nat := [5, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_66518 : Nat := 118140960795 + 66518 * 2 ^ 59
def prefixEnd_66518 : Nat := 4983230072969 + 3 ^ 40 * 66518 * 2
def baseEnd_66518 : Nat := 30360627711889761528085

theorem tailTrace_66518 : CollatzResearch.WordTrace tailWord_66518 prefixEnd_66518 30360627711889761528085 := by
  unfold tailWord_66518
  simp only [CollatzResearch.WordTrace]
  refine ⟨151631923314007575941513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1617407182016080810042805 151631923314007575941513)
  ·
    refine ⟨113723942485505681956135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151631923314007575941513 113723942485505681956135)
    ·
      refine ⟨170585913728258522934203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113723942485505681956135 170585913728258522934203)
      ·
        refine ⟨255878870592387784401305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170585913728258522934203 255878870592387784401305)
        ·
          refine ⟨191909152944290838300979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255878870592387784401305 191909152944290838300979)
          ·
            refine ⟨287863729416436257451469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191909152944290838300979 287863729416436257451469)
            ·
              refine ⟨107948898531163596544301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287863729416436257451469 107948898531163596544301)
              ·
                refine ⟨40480836949186348704113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107948898531163596544301 40480836949186348704113)
                ·
                  refine ⟨30360627711889761528085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40480836949186348704113 30360627711889761528085)
                  ·
                    rfl

theorem cell20_66518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_66518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66518 prefixEnd_66518 := by exact prefixLift 66518
  have htrace : WordTrace (prefixWord ++ tailWord_66518) baseStart_66518 baseEnd_66518 := by
    simpa [prefixWord, tailWord_66518, baseEnd_66518] using wordTrace_append hprefix tailTrace_66518
  have hstable : (prefixWord ++ tailWord_66518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66518).length < 2 ^ (prefixWord ++ tailWord_66518).sum := by decide
  have hdescent : baseEnd_66518 < baseStart_66518 := by decide
  rcases family_descends (prefixWord ++ tailWord_66518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66543 : List Nat := [1, 1, 2, 1, 4, 3, 3, 1, 4]
def baseStart_66543 : Nat := 118140960795 + 66543 * 2 ^ 59
def prefixEnd_66543 : Nat := 4983230072969 + 3 ^ 40 * 66543 * 2
def baseEnd_66543 : Nat := 30372038393100785694649

theorem tailTrace_66543 : CollatzResearch.WordTrace tailWord_66543 prefixEnd_66543 30372038393100785694649 := by
  unfold tailWord_66543
  simp only [CollatzResearch.WordTrace]
  refine ⟨2427022597933550484724283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1618015065289033656482855 2427022597933550484724283)
  ·
    refine ⟨3640533896900325727086425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2427022597933550484724283 3640533896900325727086425)
    ·
      refine ⟨2730400422675244295314819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3640533896900325727086425 2730400422675244295314819)
      ·
        refine ⟨4095600634012866442972229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2730400422675244295314819 4095600634012866442972229)
        ·
          refine ⟨767925118877412458057293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4095600634012866442972229 767925118877412458057293)
          ·
            refine ⟨287971919579029671771485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 767925118877412458057293 287971919579029671771485)
            ·
              refine ⟨107989469842136126914307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287971919579029671771485 107989469842136126914307)
              ·
                refine ⟨161984204763204190371461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107989469842136126914307 161984204763204190371461)
                ·
                  refine ⟨30372038393100785694649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161984204763204190371461 30372038393100785694649)
                  ·
                    rfl

theorem cell20_66543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 4].length) (baseStart_66543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66543 prefixEnd_66543 := by exact prefixLift 66543
  have htrace : WordTrace (prefixWord ++ tailWord_66543) baseStart_66543 baseEnd_66543 := by
    simpa [prefixWord, tailWord_66543, baseEnd_66543] using wordTrace_append hprefix tailTrace_66543
  have hstable : (prefixWord ++ tailWord_66543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66543).length < 2 ^ (prefixWord ++ tailWord_66543).sum := by decide
  have hdescent : baseEnd_66543 < baseStart_66543 := by decide
  rcases family_descends (prefixWord ++ tailWord_66543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66546 : List Nat := [3, 2, 1, 5, 1, 1, 2, 5]
def baseStart_66546 : Nat := 118140960795 + 66546 * 2 ^ 59
def prefixEnd_66546 : Nat := 4983230072969 + 3 ^ 40 * 66546 * 2
def baseEnd_66546 : Nat := 10124469224948702864879

theorem tailTrace_66546 : CollatzResearch.WordTrace tailWord_66546 prefixEnd_66546 10124469224948702864879 := by
  unfold tailWord_66546
  simp only [CollatzResearch.WordTrace]
  refine ⟨606783004230670499270873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1618088011281787998055661 606783004230670499270873)
  ·
    refine ⟨455087253173002874453155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 606783004230670499270873 455087253173002874453155)
    ·
      refine ⟨682630879759504311679733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455087253173002874453155 682630879759504311679733)
      ·
        refine ⟨63996644977453529219975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 682630879759504311679733 63996644977453529219975)
        ·
          refine ⟨95994967466180293829963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63996644977453529219975 95994967466180293829963)
          ·
            refine ⟨143992451199270440744945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95994967466180293829963 143992451199270440744945)
            ·
              refine ⟨107994338399452830558709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143992451199270440744945 107994338399452830558709)
              ·
                refine ⟨10124469224948702864879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107994338399452830558709 10124469224948702864879)
                ·
                  rfl

theorem cell20_66546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_66546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66546 prefixEnd_66546 := by exact prefixLift 66546
  have htrace : WordTrace (prefixWord ++ tailWord_66546) baseStart_66546 baseEnd_66546 := by
    simpa [prefixWord, tailWord_66546, baseEnd_66546] using wordTrace_append hprefix tailTrace_66546
  have hstable : (prefixWord ++ tailWord_66546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66546).length < 2 ^ (prefixWord ++ tailWord_66546).sum := by decide
  have hdescent : baseEnd_66546 < baseStart_66546 := by decide
  rcases family_descends (prefixWord ++ tailWord_66546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66588 : List Nat := [2, 2, 3, 1, 4, 8]
def baseStart_66588 : Nat := 118140960795 + 66588 * 2 ^ 59
def prefixEnd_66588 : Nat := 4983230072969 + 3 ^ 40 * 66588 * 2
def baseEnd_66588 : Nat := 1125651022936319599795

theorem tailTrace_66588 : CollatzResearch.WordTrace tailWord_66588 prefixEnd_66588 1125651022936319599795 := by
  unfold tailWord_66588
  simp only [CollatzResearch.WordTrace]
  refine ⟨1214331941385261585056209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1619109255180348780074945 1214331941385261585056209)
  ·
    refine ⟨910748956038946188792157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1214331941385261585056209 910748956038946188792157)
    ·
      refine ⟨341530858514604820797059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 910748956038946188792157 341530858514604820797059)
      ·
        refine ⟨512296287771907231195589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341530858514604820797059 512296287771907231195589)
        ·
          refine ⟨96055553957232605849173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 512296287771907231195589 96055553957232605849173)
          ·
            refine ⟨1125651022936319599795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 96055553957232605849173 1125651022936319599795)
            ·
              rfl

theorem cell20_66588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 8].length) (baseStart_66588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66588 prefixEnd_66588 := by exact prefixLift 66588
  have htrace : WordTrace (prefixWord ++ tailWord_66588) baseStart_66588 baseEnd_66588 := by
    simpa [prefixWord, tailWord_66588, baseEnd_66588] using wordTrace_append hprefix tailTrace_66588
  have hstable : (prefixWord ++ tailWord_66588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66588).length < 2 ^ (prefixWord ++ tailWord_66588).sum := by decide
  have hdescent : baseEnd_66588 < baseStart_66588 := by decide
  rcases family_descends (prefixWord ++ tailWord_66588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66594 : List Nat := [3, 3, 1, 1, 1, 5, 2, 2, 2]
def baseStart_66594 : Nat := 118140960795 + 66594 * 2 ^ 59
def prefixEnd_66594 : Nat := 4983230072969 + 3 ^ 40 * 66594 * 2
def baseEnd_66594 : Nat := 30395316182771274994441

theorem tailTrace_66594 : CollatzResearch.WordTrace tailWord_66594 prefixEnd_66594 30395316182771274994441 := by
  unfold tailWord_66594
  simp only [CollatzResearch.WordTrace]
  refine ⟨607220680187196548707709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1619255147165857463220557 607220680187196548707709)
  ·
    refine ⟨227707755070198705765391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 607220680187196548707709 227707755070198705765391)
    ·
      refine ⟨341561632605298058648087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227707755070198705765391 341561632605298058648087)
      ·
        refine ⟨512342448907947087972131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341561632605298058648087 512342448907947087972131)
        ·
          refine ⟨768513673361920631958197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512342448907947087972131 768513673361920631958197)
          ·
            refine ⟨72048156877680059246081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 768513673361920631958197 72048156877680059246081)
            ·
              refine ⟨54036117658260044434561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72048156877680059246081 54036117658260044434561)
              ·
                refine ⟨40527088243695033325921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54036117658260044434561 40527088243695033325921)
                ·
                  refine ⟨30395316182771274994441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40527088243695033325921 30395316182771274994441)
                  ·
                    rfl

theorem cell20_66594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_66594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66594 prefixEnd_66594 := by exact prefixLift 66594
  have htrace : WordTrace (prefixWord ++ tailWord_66594) baseStart_66594 baseEnd_66594 := by
    simpa [prefixWord, tailWord_66594, baseEnd_66594] using wordTrace_append hprefix tailTrace_66594
  have hstable : (prefixWord ++ tailWord_66594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66594).length < 2 ^ (prefixWord ++ tailWord_66594).sum := by decide
  have hdescent : baseEnd_66594 < baseStart_66594 := by decide
  rcases family_descends (prefixWord ++ tailWord_66594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66622 : List Nat := [4, 2, 1, 3, 1, 2, 3, 4]
def baseStart_66622 : Nat := 118140960795 + 66622 * 2 ^ 59
def prefixEnd_66622 : Nat := 4983230072969 + 3 ^ 40 * 66622 * 2
def baseEnd_66622 : Nat := 10136032048575874020331

theorem tailTrace_66622 : CollatzResearch.WordTrace tailWord_66622 prefixEnd_66622 10136032048575874020331 := by
  unfold tailWord_66622
  simp only [CollatzResearch.WordTrace]
  refine ⟨303737995580918372106265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1619935976431564651233413 303737995580918372106265)
  ·
    refine ⟨227803496685688779079699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303737995580918372106265 227803496685688779079699)
    ·
      refine ⟨341705245028533168619549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227803496685688779079699 341705245028533168619549)
      ·
        refine ⟨128139466885699938232331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341705245028533168619549 128139466885699938232331)
        ·
          refine ⟨192209200328549907348497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128139466885699938232331 192209200328549907348497)
          ·
            refine ⟨144156900246412430511373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192209200328549907348497 144156900246412430511373)
            ·
              refine ⟨54058837592404661441765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144156900246412430511373 54058837592404661441765)
              ·
                refine ⟨10136032048575874020331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54058837592404661441765 10136032048575874020331)
                ·
                  rfl

theorem cell20_66622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_66622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66622 prefixEnd_66622 := by exact prefixLift 66622
  have htrace : WordTrace (prefixWord ++ tailWord_66622) baseStart_66622 baseEnd_66622 := by
    simpa [prefixWord, tailWord_66622, baseEnd_66622] using wordTrace_append hprefix tailTrace_66622
  have hstable : (prefixWord ++ tailWord_66622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66622).length < 2 ^ (prefixWord ++ tailWord_66622).sum := by decide
  have hdescent : baseEnd_66622 < baseStart_66622 := by decide
  rcases family_descends (prefixWord ++ tailWord_66622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66646 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_66646 : Nat := 118140960795 + 66646 * 2 ^ 59
def prefixEnd_66646 : Nat := 4983230072969 + 3 ^ 40 * 66646 * 2
def baseEnd_66646 : Nat := 30419050399690205260895

theorem tailTrace_66646 : CollatzResearch.WordTrace tailWord_66646 prefixEnd_66646 30419050399690205260895 := by
  unfold tailWord_66646
  simp only [CollatzResearch.WordTrace]
  refine ⟨151923707285024942232737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1620519544373599383815861 151923707285024942232737)
  ·
    refine ⟨113942780463768706674553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151923707285024942232737 113942780463768706674553)
    ·
      refine ⟨85457085347826530005915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113942780463768706674553 85457085347826530005915)
      ·
        refine ⟨128185628021739795008873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85457085347826530005915 128185628021739795008873)
        ·
          refine ⟨96139221016304846256655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128185628021739795008873 96139221016304846256655)
          ·
            refine ⟨144208831524457269384983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96139221016304846256655 144208831524457269384983)
            ·
              refine ⟨216313247286685904077475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144208831524457269384983 216313247286685904077475)
              ·
                refine ⟨324469870930028856116213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216313247286685904077475 324469870930028856116213)
                ·
                  refine ⟨30419050399690205260895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 324469870930028856116213 30419050399690205260895)
                  ·
                    rfl

theorem cell20_66646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_66646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66646 prefixEnd_66646 := by exact prefixLift 66646
  have htrace : WordTrace (prefixWord ++ tailWord_66646) baseStart_66646 baseEnd_66646 := by
    simpa [prefixWord, tailWord_66646, baseEnd_66646] using wordTrace_append hprefix tailTrace_66646
  have hstable : (prefixWord ++ tailWord_66646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66646).length < 2 ^ (prefixWord ++ tailWord_66646).sum := by decide
  have hdescent : baseEnd_66646 < baseStart_66646 := by decide
  rcases family_descends (prefixWord ++ tailWord_66646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66653 : List Nat := [1, 4, 4, 1, 2, 1, 2, 1, 4]
def baseStart_66653 : Nat := 118140960795 + 66653 * 2 ^ 59
def prefixEnd_66653 : Nat := 4983230072969 + 3 ^ 40 * 66653 * 2
def baseEnd_66653 : Nat := 30422245390429292027533

theorem tailTrace_66653 : CollatzResearch.WordTrace tailWord_66653 prefixEnd_66653 30422245390429292027533 := by
  unfold tailWord_66653
  simp only [CollatzResearch.WordTrace]
  refine ⟨2431034627535039271228613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1620689751690026180819075 2431034627535039271228613)
  ·
    refine ⟨455818992662819863355365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2431034627535039271228613 455818992662819863355365)
    ·
      refine ⟨85466061124278724379131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 455818992662819863355365 85466061124278724379131)
      ·
        refine ⟨128199091686418086568697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85466061124278724379131 128199091686418086568697)
        ·
          refine ⟨96149318764813564926523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128199091686418086568697 96149318764813564926523)
          ·
            refine ⟨144223978147220347389785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96149318764813564926523 144223978147220347389785)
            ·
              refine ⟨108167983610415260542339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144223978147220347389785 108167983610415260542339)
              ·
                refine ⟨162251975415622890813509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108167983610415260542339 162251975415622890813509)
                ·
                  refine ⟨30422245390429292027533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162251975415622890813509 30422245390429292027533)
                  ·
                    rfl

theorem cell20_66653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_66653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66653 prefixEnd_66653 := by exact prefixLift 66653
  have htrace : WordTrace (prefixWord ++ tailWord_66653) baseStart_66653 baseEnd_66653 := by
    simpa [prefixWord, tailWord_66653, baseEnd_66653] using wordTrace_append hprefix tailTrace_66653
  have hstable : (prefixWord ++ tailWord_66653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66653).length < 2 ^ (prefixWord ++ tailWord_66653).sum := by decide
  have hdescent : baseEnd_66653 < baseStart_66653 := by decide
  rcases family_descends (prefixWord ++ tailWord_66653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66677 : List Nat := [1, 3, 4, 3, 1, 2, 2, 4]
def baseStart_66677 : Nat := 118140960795 + 66677 * 2 ^ 59
def prefixEnd_66677 : Nat := 4983230072969 + 3 ^ 40 * 66677 * 2
def baseEnd_66677 : Nat := 10144399881463958409145

theorem tailTrace_66677 : CollatzResearch.WordTrace tailWord_66677 prefixEnd_66677 10144399881463958409145 := by
  unfold tailWord_66677
  simp only [CollatzResearch.WordTrace]
  refine ⟨2431909979448091370102285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1621273319632060913401523 2431909979448091370102285)
  ·
    refine ⟨911966242293034263788357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2431909979448091370102285 911966242293034263788357)
    ·
      refine ⟨170993670429943924460317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 911966242293034263788357 170993670429943924460317)
      ·
        refine ⟨64122626411228971672619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170993670429943924460317 64122626411228971672619)
        ·
          refine ⟨96183939616843457508929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64122626411228971672619 96183939616843457508929)
          ·
            refine ⟨72137954712632593131697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96183939616843457508929 72137954712632593131697)
            ·
              refine ⟨54103466034474444848773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72137954712632593131697 54103466034474444848773)
              ·
                refine ⟨10144399881463958409145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54103466034474444848773 10144399881463958409145)
                ·
                  rfl

theorem cell20_66677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 4].length) (baseStart_66677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66677 prefixEnd_66677 := by exact prefixLift 66677
  have htrace : WordTrace (prefixWord ++ tailWord_66677) baseStart_66677 baseEnd_66677 := by
    simpa [prefixWord, tailWord_66677, baseEnd_66677] using wordTrace_append hprefix tailTrace_66677
  have hstable : (prefixWord ++ tailWord_66677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66677).length < 2 ^ (prefixWord ++ tailWord_66677).sum := by decide
  have hdescent : baseEnd_66677 < baseStart_66677 := by decide
  rcases family_descends (prefixWord ++ tailWord_66677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66702 : List Nat := [4, 1, 1, 3, 2, 1, 8]
def baseStart_66702 : Nat := 118140960795 + 66702 * 2 ^ 59
def prefixEnd_66702 : Nat := 4983230072969 + 3 ^ 40 * 66702 * 2
def baseEnd_66702 : Nat := 3382734480622544377111

theorem tailTrace_66702 : CollatzResearch.WordTrace tailWord_66702 prefixEnd_66702 3382734480622544377111 := by
  unfold tailWord_66702
  simp only [CollatzResearch.WordTrace]
  refine ⟨304102725544690079970295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1621881202905013759841573 304102725544690079970295)
  ·
    refine ⟨456154088317035119955443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304102725544690079970295 456154088317035119955443)
    ·
      refine ⟨684231132475552679933165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456154088317035119955443 684231132475552679933165)
      ·
        refine ⟨256586674678332254974937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 684231132475552679933165 256586674678332254974937)
        ·
          refine ⟨192440006008749191231203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256586674678332254974937 192440006008749191231203)
          ·
            refine ⟨288660009013123786846805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192440006008749191231203 288660009013123786846805)
            ·
              refine ⟨3382734480622544377111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 288660009013123786846805 3382734480622544377111)
              ·
                rfl

theorem cell20_66702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 8].length) (baseStart_66702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66702 prefixEnd_66702 := by exact prefixLift 66702
  have htrace : WordTrace (prefixWord ++ tailWord_66702) baseStart_66702 baseEnd_66702 := by
    simpa [prefixWord, tailWord_66702, baseEnd_66702] using wordTrace_append hprefix tailTrace_66702
  have hstable : (prefixWord ++ tailWord_66702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66702).length < 2 ^ (prefixWord ++ tailWord_66702).sum := by decide
  have hdescent : baseEnd_66702 < baseStart_66702 := by decide
  rcases family_descends (prefixWord ++ tailWord_66702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66712 : List Nat := [2, 1, 2, 4, 2, 3, 1, 1, 4]
def baseStart_66712 : Nat := 118140960795 + 66712 * 2 ^ 59
def prefixEnd_66712 : Nat := 4983230072969 + 3 ^ 40 * 66712 * 2
def baseEnd_66712 : Nat := 30449174598087309060625

theorem tailTrace_66712 : CollatzResearch.WordTrace tailWord_66712 prefixEnd_66712 30449174598087309060625 := by
  unfold tailWord_66712
  simp only [CollatzResearch.WordTrace]
  refine ⟨1216593267160646173813195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1622124356214194898417593 1216593267160646173813195)
  ·
    refine ⟨1824889900740969260719793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1216593267160646173813195 1824889900740969260719793)
    ·
      refine ⟨1368667425555726945539845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1824889900740969260719793 1368667425555726945539845)
      ·
        refine ⟨256625142291698802288721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1368667425555726945539845 256625142291698802288721)
        ·
          refine ⟨192468856718774101716541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256625142291698802288721 192468856718774101716541)
          ·
            refine ⟨72175821269540288143703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192468856718774101716541 72175821269540288143703)
            ·
              refine ⟨108263731904310432215555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72175821269540288143703 108263731904310432215555)
              ·
                refine ⟨162395597856465648323333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108263731904310432215555 162395597856465648323333)
                ·
                  refine ⟨30449174598087309060625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162395597856465648323333 30449174598087309060625)
                  ·
                    rfl

theorem cell20_66712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 4].length) (baseStart_66712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66712 prefixEnd_66712 := by exact prefixLift 66712
  have htrace : WordTrace (prefixWord ++ tailWord_66712) baseStart_66712 baseEnd_66712 := by
    simpa [prefixWord, tailWord_66712, baseEnd_66712] using wordTrace_append hprefix tailTrace_66712
  have hstable : (prefixWord ++ tailWord_66712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66712).length < 2 ^ (prefixWord ++ tailWord_66712).sum := by decide
  have hdescent : baseEnd_66712 < baseStart_66712 := by decide
  rcases family_descends (prefixWord ++ tailWord_66712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66719 : List Nat := [1, 1, 2, 6, 2, 1, 2, 5]
def baseStart_66719 : Nat := 118140960795 + 66719 * 2 ^ 59
def prefixEnd_66719 : Nat := 4983230072969 + 3 ^ 40 * 66719 * 2
def baseEnd_66719 : Nat := 10150789862942131942421

theorem tailTrace_66719 : CollatzResearch.WordTrace tailWord_66719 prefixEnd_66719 10150789862942131942421 := by
  unfold tailWord_66719
  simp only [CollatzResearch.WordTrace]
  refine ⟨2433441845295932543131211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1622294563530621695420807 2433441845295932543131211)
  ·
    refine ⟨3650162767943898814696817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2433441845295932543131211 3650162767943898814696817)
    ·
      refine ⟨2737622075957924111022613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3650162767943898814696817 2737622075957924111022613)
      ·
        refine ⟨128326034810527692704185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2737622075957924111022613 128326034810527692704185)
        ·
          refine ⟨96244526107895769528139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128326034810527692704185 96244526107895769528139)
          ·
            refine ⟨144366789161843654292209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96244526107895769528139 144366789161843654292209)
            ·
              refine ⟨108275091871382740719157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144366789161843654292209 108275091871382740719157)
              ·
                refine ⟨10150789862942131942421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108275091871382740719157 10150789862942131942421)
                ·
                  rfl

theorem cell20_66719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 5].length) (baseStart_66719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66719 prefixEnd_66719 := by exact prefixLift 66719
  have htrace : WordTrace (prefixWord ++ tailWord_66719) baseStart_66719 baseEnd_66719 := by
    simpa [prefixWord, tailWord_66719, baseEnd_66719] using wordTrace_append hprefix tailTrace_66719
  have hstable : (prefixWord ++ tailWord_66719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66719).length < 2 ^ (prefixWord ++ tailWord_66719).sum := by decide
  have hdescent : baseEnd_66719 < baseStart_66719 := by decide
  rcases family_descends (prefixWord ++ tailWord_66719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66771 : List Nat := [1, 1, 1, 2, 1, 1, 1, 10, 2]
def baseStart_66771 : Nat := 118140960795 + 66771 * 2 ^ 59
def prefixEnd_66771 : Nat := 4983230072969 + 3 ^ 40 * 66771 * 2
def baseEnd_66771 : Nat := 30476103805745326093717

theorem tailTrace_66771 : CollatzResearch.WordTrace tailWord_66771 prefixEnd_66771 30476103805745326093717 := by
  unfold tailWord_66771
  simp only [CollatzResearch.WordTrace]
  refine ⟨2435338441107545424024167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1623558960738363616016111 2435338441107545424024167)
  ·
    refine ⟨3653007661661318136036251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2435338441107545424024167 3653007661661318136036251)
    ·
      refine ⟨5479511492491977204054377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3653007661661318136036251 5479511492491977204054377)
      ·
        refine ⟨4109633619368982903040783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5479511492491977204054377 4109633619368982903040783)
        ·
          refine ⟨6164450429053474354561175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4109633619368982903040783 6164450429053474354561175)
          ·
            refine ⟨9246675643580211531841763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6164450429053474354561175 9246675643580211531841763)
            ·
              refine ⟨13870013465370317297762645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9246675643580211531841763 13870013465370317297762645)
              ·
                refine ⟨40634805074327101458289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13870013465370317297762645 40634805074327101458289)
                ·
                  refine ⟨30476103805745326093717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40634805074327101458289 30476103805745326093717)
                  ·
                    rfl

theorem cell20_66771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 2].length) (baseStart_66771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66771 prefixEnd_66771 := by exact prefixLift 66771
  have htrace : WordTrace (prefixWord ++ tailWord_66771) baseStart_66771 baseEnd_66771 := by
    simpa [prefixWord, tailWord_66771, baseEnd_66771] using wordTrace_append hprefix tailTrace_66771
  have hstable : (prefixWord ++ tailWord_66771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66771).length < 2 ^ (prefixWord ++ tailWord_66771).sum := by decide
  have hdescent : baseEnd_66771 < baseStart_66771 := by decide
  rcases family_descends (prefixWord ++ tailWord_66771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66837 : List Nat := [1, 3, 2, 1, 2, 1, 1, 9]
def baseStart_66837 : Nat := 118140960795 + 66837 * 2 ^ 59
def prefixEnd_66837 : Nat := 4983230072969 + 3 ^ 40 * 66837 * 2
def baseEnd_66837 : Nat := 10168742668047476631149

theorem tailTrace_66837 : CollatzResearch.WordTrace tailWord_66837 prefixEnd_66837 10168742668047476631149 := by
  unfold tailWord_66837
  simp only [CollatzResearch.WordTrace]
  refine ⟨2437745658868438695926765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1625163772578959130617843 2437745658868438695926765)
  ·
    refine ⟨914154622075664510972537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2437745658868438695926765 914154622075664510972537)
    ·
      refine ⟨685615966556748383229403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 914154622075664510972537 685615966556748383229403)
      ·
        refine ⟨1028423949835122574844105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685615966556748383229403 1028423949835122574844105)
        ·
          refine ⟨771317962376341931133079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1028423949835122574844105 771317962376341931133079)
          ·
            refine ⟨1156976943564512896699619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771317962376341931133079 1156976943564512896699619)
            ·
              refine ⟨1735465415346769345049429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1156976943564512896699619 1735465415346769345049429)
              ·
                refine ⟨10168742668047476631149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1735465415346769345049429 10168742668047476631149)
                ·
                  rfl

theorem cell20_66837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 9].length) (baseStart_66837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66837 prefixEnd_66837 := by exact prefixLift 66837
  have htrace : WordTrace (prefixWord ++ tailWord_66837) baseStart_66837 baseEnd_66837 := by
    simpa [prefixWord, tailWord_66837, baseEnd_66837] using wordTrace_append hprefix tailTrace_66837
  have hstable : (prefixWord ++ tailWord_66837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66837).length < 2 ^ (prefixWord ++ tailWord_66837).sum := by decide
  have hdescent : baseEnd_66837 < baseStart_66837 := by decide
  rcases family_descends (prefixWord ++ tailWord_66837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66846 : List Nat := [4, 3, 2, 1, 3, 1, 2, 4]
def baseStart_66846 : Nat := 118140960795 + 66846 * 2 ^ 59
def prefixEnd_66846 : Nat := 4983230072969 + 3 ^ 40 * 66846 * 2
def baseEnd_66846 : Nat := 10170111949792799531137

theorem tailTrace_66846 : CollatzResearch.WordTrace tailWord_66846 prefixEnd_66846 10170111949792799531137 := by
  unfold tailWord_66846
  simp only [CollatzResearch.WordTrace]
  refine ⟨304759239479479154125549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1625382610557222155336261 304759239479479154125549)
  ·
    refine ⟨114284714804804682797081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304759239479479154125549 114284714804804682797081)
    ·
      refine ⟨85713536103603512097811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114284714804804682797081 85713536103603512097811)
      ·
        refine ⟨128570304155405268146717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85713536103603512097811 128570304155405268146717)
        ·
          refine ⟨48213864058276975555019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128570304155405268146717 48213864058276975555019)
          ·
            refine ⟨72320796087415463332529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48213864058276975555019 72320796087415463332529)
            ·
              refine ⟨54240597065561597499397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72320796087415463332529 54240597065561597499397)
              ·
                refine ⟨10170111949792799531137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54240597065561597499397 10170111949792799531137)
                ·
                  rfl

theorem cell20_66846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_66846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66846 prefixEnd_66846 := by exact prefixLift 66846
  have htrace : WordTrace (prefixWord ++ tailWord_66846) baseStart_66846 baseEnd_66846 := by
    simpa [prefixWord, tailWord_66846, baseEnd_66846] using wordTrace_append hprefix tailTrace_66846
  have hstable : (prefixWord ++ tailWord_66846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66846).length < 2 ^ (prefixWord ++ tailWord_66846).sum := by decide
  have hdescent : baseEnd_66846 < baseStart_66846 := by decide
  rcases family_descends (prefixWord ++ tailWord_66846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66850 : List Nat := [3, 3, 1, 1, 4, 2, 2, 4]
def baseStart_66850 : Nat := 118140960795 + 66850 * 2 ^ 59
def prefixEnd_66850 : Nat := 4983230072969 + 3 ^ 40 * 66850 * 2
def baseEnd_66850 : Nat := 10170720519457387486687

theorem tailTrace_66850 : CollatzResearch.WordTrace tailWord_66850 prefixEnd_66850 10170720519457387486687 := by
  unfold tailWord_66850
  simp only [CollatzResearch.WordTrace]
  refine ⟨609554951955335479037501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1625479871880894610766669 609554951955335479037501)
  ·
    refine ⟨228583106983250804639063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 609554951955335479037501 228583106983250804639063)
    ·
      refine ⟨342874660474876206958595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228583106983250804639063 342874660474876206958595)
      ·
        refine ⟨514311990712314310437893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342874660474876206958595 514311990712314310437893)
        ·
          refine ⟨96433498258558933207105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 514311990712314310437893 96433498258558933207105)
          ·
            refine ⟨72325123693919199905329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96433498258558933207105 72325123693919199905329)
            ·
              refine ⟨54243842770439399928997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72325123693919199905329 54243842770439399928997)
              ·
                refine ⟨10170720519457387486687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54243842770439399928997 10170720519457387486687)
                ·
                  rfl

theorem cell20_66850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_66850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66850 prefixEnd_66850 := by exact prefixLift 66850
  have htrace : WordTrace (prefixWord ++ tailWord_66850) baseStart_66850 baseEnd_66850 := by
    simpa [prefixWord, tailWord_66850, baseEnd_66850] using wordTrace_append hprefix tailTrace_66850
  have hstable : (prefixWord ++ tailWord_66850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66850).length < 2 ^ (prefixWord ++ tailWord_66850).sum := by decide
  have hdescent : baseEnd_66850 < baseStart_66850 := by decide
  rcases family_descends (prefixWord ++ tailWord_66850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66878 : List Nat := [4, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_66878 : Nat := 118140960795 + 66878 * 2 ^ 59
def prefixEnd_66878 : Nat := 4983230072969 + 3 ^ 40 * 66878 * 2
def baseEnd_66878 : Nat := 30524941521328509526613

theorem tailTrace_66878 : CollatzResearch.WordTrace tailWord_66878 prefixEnd_66878 30524941521328509526613 := by
  unfold tailWord_66878
  simp only [CollatzResearch.WordTrace]
  refine ⟨304905131464987837271161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1626160701146601798779525 304905131464987837271161)
  ·
    refine ⟨228678848598740877953371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 304905131464987837271161 228678848598740877953371)
    ·
      refine ⟨343018272898111316930057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228678848598740877953371 343018272898111316930057)
      ·
        refine ⟨257263704673583487697543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343018272898111316930057 257263704673583487697543)
        ·
          refine ⟨385895557010375231546315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257263704673583487697543 385895557010375231546315)
          ·
            refine ⟨578843335515562847319473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385895557010375231546315 578843335515562847319473)
            ·
              refine ⟨434132501636672135489605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 578843335515562847319473 434132501636672135489605)
              ·
                refine ⟨81399844056876025404301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 434132501636672135489605 81399844056876025404301)
                ·
                  refine ⟨30524941521328509526613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81399844056876025404301 30524941521328509526613)
                  ·
                    rfl

theorem cell20_66878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_66878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66878 prefixEnd_66878 := by exact prefixLift 66878
  have htrace : WordTrace (prefixWord ++ tailWord_66878) baseStart_66878 baseEnd_66878 := by
    simpa [prefixWord, tailWord_66878, baseEnd_66878] using wordTrace_append hprefix tailTrace_66878
  have hstable : (prefixWord ++ tailWord_66878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66878).length < 2 ^ (prefixWord ++ tailWord_66878).sum := by decide
  have hdescent : baseEnd_66878 < baseStart_66878 := by decide
  rcases family_descends (prefixWord ++ tailWord_66878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66885 : List Nat := [1, 3, 1, 1, 1, 2, 1, 8, 2]
def baseStart_66885 : Nat := 118140960795 + 66885 * 2 ^ 59
def prefixEnd_66885 : Nat := 4983230072969 + 3 ^ 40 * 66885 * 2
def baseEnd_66885 : Nat := 30528136512067596293251

theorem tailTrace_66885 : CollatzResearch.WordTrace tailWord_66885 prefixEnd_66885 30528136512067596293251 := by
  unfold tailWord_66885
  simp only [CollatzResearch.WordTrace]
  refine ⟨2439496362694542893674109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1626330908463028595782739 2439496362694542893674109)
  ·
    refine ⟨914811136010453585127791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2439496362694542893674109 914811136010453585127791)
    ·
      refine ⟨1372216704015680377691687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 914811136010453585127791 1372216704015680377691687)
      ·
        refine ⟨2058325056023520566537531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1372216704015680377691687 2058325056023520566537531)
        ·
          refine ⟨3087487584035280849806297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058325056023520566537531 3087487584035280849806297)
          ·
            refine ⟨2315615688026460637354723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3087487584035280849806297 2315615688026460637354723)
            ·
              refine ⟨3473423532039690956032085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2315615688026460637354723 3473423532039690956032085)
              ·
                refine ⟨40704182016090128391001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3473423532039690956032085 40704182016090128391001)
                ·
                  refine ⟨30528136512067596293251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40704182016090128391001 30528136512067596293251)
                  ·
                    rfl

theorem cell20_66885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_66885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66885 prefixEnd_66885 := by exact prefixLift 66885
  have htrace : WordTrace (prefixWord ++ tailWord_66885) baseStart_66885 baseEnd_66885 := by
    simpa [prefixWord, tailWord_66885, baseEnd_66885] using wordTrace_append hprefix tailTrace_66885
  have hstable : (prefixWord ++ tailWord_66885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66885).length < 2 ^ (prefixWord ++ tailWord_66885).sum := by decide
  have hdescent : baseEnd_66885 < baseStart_66885 := by decide
  rcases family_descends (prefixWord ++ tailWord_66885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66892 : List Nat := [2, 2, 1, 3, 2, 3, 2, 5]
def baseStart_66892 : Nat := 118140960795 + 66892 * 2 ^ 59
def prefixEnd_66892 : Nat := 4983230072969 + 3 ^ 40 * 66892 * 2
def baseEnd_66892 : Nat := 10177110500935561019963

theorem tailTrace_66892 : CollatzResearch.WordTrace tailWord_66892 prefixEnd_66892 10177110500935561019963 := by
  unfold tailWord_66892
  simp only [CollatzResearch.WordTrace]
  refine ⟨1219875836834591544589465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1626501115779455392785953 1219875836834591544589465)
  ·
    refine ⟨914906877625943658442099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1219875836834591544589465 914906877625943658442099)
    ·
      refine ⟨1372360316438915487663149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 914906877625943658442099 1372360316438915487663149)
      ·
        refine ⟨514635118664593307873681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1372360316438915487663149 514635118664593307873681)
        ·
          refine ⟨385976338998444980905261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514635118664593307873681 385976338998444980905261)
          ·
            refine ⟨144741127124416867839473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 385976338998444980905261 144741127124416867839473)
            ·
              refine ⟨108555845343312650879605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144741127124416867839473 108555845343312650879605)
              ·
                refine ⟨10177110500935561019963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108555845343312650879605 10177110500935561019963)
                ·
                  rfl

theorem cell20_66892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_66892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66892 prefixEnd_66892 := by exact prefixLift 66892
  have htrace : WordTrace (prefixWord ++ tailWord_66892) baseStart_66892 baseEnd_66892 := by
    simpa [prefixWord, tailWord_66892, baseEnd_66892] using wordTrace_append hprefix tailTrace_66892
  have hstable : (prefixWord ++ tailWord_66892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66892).length < 2 ^ (prefixWord ++ tailWord_66892).sum := by decide
  have hdescent : baseEnd_66892 < baseStart_66892 := by decide
  rcases family_descends (prefixWord ++ tailWord_66892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66899 : List Nat := [1, 1, 1, 2, 1, 1, 7, 3, 3]
def baseStart_66899 : Nat := 118140960795 + 66899 * 2 ^ 59
def prefixEnd_66899 : Nat := 4983230072969 + 3 ^ 40 * 66899 * 2
def baseEnd_66899 : Nat := 30534526493545769826527

theorem tailTrace_66899 : CollatzResearch.WordTrace tailWord_66899 prefixEnd_66899 30534526493545769826527 := by
  unfold tailWord_66899
  simp only [CollatzResearch.WordTrace]
  refine ⟨2440006984643823284683751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1626671323095882189789167 2440006984643823284683751)
  ·
    refine ⟨3660010476965734927025627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2440006984643823284683751 3660010476965734927025627)
    ·
      refine ⟨5490015715448602390538441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3660010476965734927025627 5490015715448602390538441)
      ·
        refine ⟨4117511786586451792903831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5490015715448602390538441 4117511786586451792903831)
        ·
          refine ⟨6176267679879677689355747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4117511786586451792903831 6176267679879677689355747)
          ·
            refine ⟨9264401519819516534033621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6176267679879677689355747 9264401519819516534033621)
            ·
              refine ⟨217134410620769918766413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9264401519819516534033621 217134410620769918766413)
              ·
                refine ⟨81425403982788719537405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217134410620769918766413 81425403982788719537405)
                ·
                  refine ⟨30534526493545769826527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81425403982788719537405 30534526493545769826527)
                  ·
                    rfl

theorem cell20_66899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 3].length) (baseStart_66899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66899 prefixEnd_66899 := by exact prefixLift 66899
  have htrace : WordTrace (prefixWord ++ tailWord_66899) baseStart_66899 baseEnd_66899 := by
    simpa [prefixWord, tailWord_66899, baseEnd_66899] using wordTrace_append hprefix tailTrace_66899
  have hstable : (prefixWord ++ tailWord_66899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66899).length < 2 ^ (prefixWord ++ tailWord_66899).sum := by decide
  have hdescent : baseEnd_66899 < baseStart_66899 := by decide
  rcases family_descends (prefixWord ++ tailWord_66899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66906 : List Nat := [3, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_66906 : Nat := 118140960795 + 66906 * 2 ^ 59
def prefixEnd_66906 : Nat := 4983230072969 + 3 ^ 40 * 66906 * 2
def baseEnd_66906 : Nat := 30537721484284856593165

theorem tailTrace_66906 : CollatzResearch.WordTrace tailWord_66906 prefixEnd_66906 30537721484284856593165 := by
  unfold tailWord_66906
  simp only [CollatzResearch.WordTrace]
  refine ⟨610065573904615870047143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1626841530412308986792381 610065573904615870047143)
  ·
    refine ⟨915098360856923805070715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 610065573904615870047143 915098360856923805070715)
    ·
      refine ⟨1372647541285385707606073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 915098360856923805070715 1372647541285385707606073)
      ·
        refine ⟨1029485655964039280704555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1372647541285385707606073 1029485655964039280704555)
        ·
          refine ⟨1544228483946058921056833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029485655964039280704555 1544228483946058921056833)
          ·
            refine ⟨1158171362959544190792625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1544228483946058921056833 1158171362959544190792625)
            ·
              refine ⟨868628522219658143094469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1158171362959544190792625 868628522219658143094469)
              ·
                refine ⟨162867847916185901830213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 868628522219658143094469 162867847916185901830213)
                ·
                  refine ⟨30537721484284856593165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162867847916185901830213 30537721484284856593165)
                  ·
                    rfl

theorem cell20_66906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_66906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66906 prefixEnd_66906 := by exact prefixLift 66906
  have htrace : WordTrace (prefixWord ++ tailWord_66906) baseStart_66906 baseEnd_66906 := by
    simpa [prefixWord, tailWord_66906, baseEnd_66906] using wordTrace_append hprefix tailTrace_66906
  have hstable : (prefixWord ++ tailWord_66906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66906).length < 2 ^ (prefixWord ++ tailWord_66906).sum := by decide
  have hdescent : baseEnd_66906 < baseStart_66906 := by decide
  rcases family_descends (prefixWord ++ tailWord_66906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66933 : List Nat := [1, 3, 4, 1, 3, 1, 2, 2, 3]
def baseStart_66933 : Nat := 118140960795 + 66933 * 2 ^ 59
def prefixEnd_66933 : Nat := 4983230072969 + 3 ^ 40 * 66933 * 2
def baseEnd_66933 : Nat := 30550045019992762693055

theorem tailTrace_66933 : CollatzResearch.WordTrace tailWord_66933 prefixEnd_66933 30550045019992762693055 := by
  unfold tailWord_66933
  simp only [CollatzResearch.WordTrace]
  refine ⟨2441247066520647091421453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1627498044347098060947635 2441247066520647091421453)
  ·
    refine ⟨915467649945242659283045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2441247066520647091421453 915467649945242659283045)
    ·
      refine ⟨171650184364732998615571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 915467649945242659283045 171650184364732998615571)
      ·
        refine ⟨257475276547099497923357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171650184364732998615571 257475276547099497923357)
        ·
          refine ⟨96553228705162311721259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257475276547099497923357 96553228705162311721259)
          ·
            refine ⟨144829843057743467581889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96553228705162311721259 144829843057743467581889)
            ·
              refine ⟨108622382293307600686417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144829843057743467581889 108622382293307600686417)
              ·
                refine ⟨81466786719980700514813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108622382293307600686417 81466786719980700514813)
                ·
                  refine ⟨30550045019992762693055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81466786719980700514813 30550045019992762693055)
                  ·
                    rfl

theorem cell20_66933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_66933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66933 prefixEnd_66933 := by exact prefixLift 66933
  have htrace : WordTrace (prefixWord ++ tailWord_66933) baseStart_66933 baseEnd_66933 := by
    simpa [prefixWord, tailWord_66933, baseEnd_66933] using wordTrace_append hprefix tailTrace_66933
  have hstable : (prefixWord ++ tailWord_66933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66933).length < 2 ^ (prefixWord ++ tailWord_66933).sum := by decide
  have hdescent : baseEnd_66933 < baseStart_66933 := by decide
  rcases family_descends (prefixWord ++ tailWord_66933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66937 : List Nat := [1, 2, 1, 3, 2, 1, 3, 4, 3]
def baseStart_66937 : Nat := 118140960795 + 66937 * 2 ^ 59
def prefixEnd_66937 : Nat := 4983230072969 + 3 ^ 40 * 66937 * 2
def baseEnd_66937 : Nat := 30551870728986526559705

theorem tailTrace_66937 : CollatzResearch.WordTrace tailWord_66937 prefixEnd_66937 30551870728986526559705 := by
  unfold tailWord_66937
  simp only [CollatzResearch.WordTrace]
  refine ⟨2441392958506155774567065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1627595305670770516378043 2441392958506155774567065)
  ·
    refine ⟨1831044718879616830925299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2441392958506155774567065 1831044718879616830925299)
    ·
      refine ⟨2746567078319425246387949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1831044718879616830925299 2746567078319425246387949)
      ·
        refine ⟨1029962654369784467395481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2746567078319425246387949 1029962654369784467395481)
        ·
          refine ⟨772471990777338350546611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1029962654369784467395481 772471990777338350546611)
          ·
            refine ⟨1158707986166007525819917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772471990777338350546611 1158707986166007525819917)
            ·
              refine ⟨434515494812252822182469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1158707986166007525819917 434515494812252822182469)
              ·
                refine ⟨81471655277297404159213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 434515494812252822182469 81471655277297404159213)
                ·
                  refine ⟨30551870728986526559705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81471655277297404159213 30551870728986526559705)
                  ·
                    rfl

theorem cell20_66937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_66937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66937 prefixEnd_66937 := by exact prefixLift 66937
  have htrace : WordTrace (prefixWord ++ tailWord_66937) baseStart_66937 baseEnd_66937 := by
    simpa [prefixWord, tailWord_66937, baseEnd_66937] using wordTrace_append hprefix tailTrace_66937
  have hstable : (prefixWord ++ tailWord_66937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66937).length < 2 ^ (prefixWord ++ tailWord_66937).sum := by decide
  have hdescent : baseEnd_66937 < baseStart_66937 := by decide
  rcases family_descends (prefixWord ++ tailWord_66937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66974 : List Nat := [4, 3, 1, 2, 2, 1, 2, 3, 2]
def baseStart_66974 : Nat := 118140960795 + 66974 * 2 ^ 59
def prefixEnd_66974 : Nat := 4983230072969 + 3 ^ 40 * 66974 * 2
def baseEnd_66974 : Nat := 30568758537178842326221

theorem tailTrace_66974 : CollatzResearch.WordTrace tailWord_66974 prefixEnd_66974 30568758537178842326221 := by
  unfold tailWord_66974
  simp only [CollatzResearch.WordTrace]
  refine ⟨305342807421513886707997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1628494972914740729109317 305342807421513886707997)
  ·
    refine ⟨114503552783067707515499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305342807421513886707997 114503552783067707515499)
    ·
      refine ⟨171755329174601561273249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114503552783067707515499 171755329174601561273249)
      ·
        refine ⟨128816496880951170954937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171755329174601561273249 128816496880951170954937)
        ·
          refine ⟨96612372660713378216203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128816496880951170954937 96612372660713378216203)
          ·
            refine ⟨144918558991070067324305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96612372660713378216203 144918558991070067324305)
            ·
              refine ⟨108688919243302550493229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144918558991070067324305 108688919243302550493229)
              ·
                refine ⟨40758344716238456434961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108688919243302550493229 40758344716238456434961)
                ·
                  refine ⟨30568758537178842326221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40758344716238456434961 30568758537178842326221)
                  ·
                    rfl

theorem cell20_66974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_66974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66974 prefixEnd_66974 := by exact prefixLift 66974
  have htrace : WordTrace (prefixWord ++ tailWord_66974) baseStart_66974 baseEnd_66974 := by
    simpa [prefixWord, tailWord_66974, baseEnd_66974] using wordTrace_append hprefix tailTrace_66974
  have hstable : (prefixWord ++ tailWord_66974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66974).length < 2 ^ (prefixWord ++ tailWord_66974).sum := by decide
  have hdescent : baseEnd_66974 < baseStart_66974 := by decide
  rcases family_descends (prefixWord ++ tailWord_66974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66978 : List Nat := [3, 3, 1, 2, 1, 2, 1, 5, 2]
def baseStart_66978 : Nat := 118140960795 + 66978 * 2 ^ 59
def prefixEnd_66978 : Nat := 4983230072969 + 3 ^ 40 * 66978 * 2
def baseEnd_66978 : Nat := 30570584246172606192871

theorem tailTrace_66978 : CollatzResearch.WordTrace tailWord_66978 prefixEnd_66978 30570584246172606192871 := by
  unfold tailWord_66978
  simp only [CollatzResearch.WordTrace]
  refine ⟨610722087839404944202397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1628592234238413184539725 610722087839404944202397)
  ·
    refine ⟨229020782939776854075899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 610722087839404944202397 229020782939776854075899)
    ·
      refine ⟨343531174409665281113849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229020782939776854075899 343531174409665281113849)
      ·
        refine ⟨257648380807248960835387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343531174409665281113849 257648380807248960835387)
        ·
          refine ⟨386472571210873441253081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257648380807248960835387 386472571210873441253081)
          ·
            refine ⟨289854428408155080939811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386472571210873441253081 289854428408155080939811)
            ·
              refine ⟨434781642612232621409717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289854428408155080939811 434781642612232621409717)
              ·
                refine ⟨40760778994896808257161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 434781642612232621409717 40760778994896808257161)
                ·
                  refine ⟨30570584246172606192871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40760778994896808257161 30570584246172606192871)
                  ·
                    rfl

theorem cell20_66978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_66978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66978 prefixEnd_66978 := by exact prefixLift 66978
  have htrace : WordTrace (prefixWord ++ tailWord_66978) baseStart_66978 baseEnd_66978 := by
    simpa [prefixWord, tailWord_66978, baseEnd_66978] using wordTrace_append hprefix tailTrace_66978
  have hstable : (prefixWord ++ tailWord_66978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66978).length < 2 ^ (prefixWord ++ tailWord_66978).sum := by decide
  have hdescent : baseEnd_66978 < baseStart_66978 := by decide
  rcases family_descends (prefixWord ++ tailWord_66978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66999 : List Nat := [1, 1, 3, 1, 3, 2, 1, 6, 2]
def baseStart_66999 : Nat := 118140960795 + 66999 * 2 ^ 59
def prefixEnd_66999 : Nat := 4983230072969 + 3 ^ 40 * 66999 * 2
def baseEnd_66999 : Nat := 30580169218389866492785

theorem tailTrace_66999 : CollatzResearch.WordTrace tailWord_66999 prefixEnd_66999 30580169218389866492785 := by
  unfold tailWord_66999
  simp only [CollatzResearch.WordTrace]
  refine ⟨2443654284281540363324051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1629102856187693575549367 2443654284281540363324051)
  ·
    refine ⟨3665481426422310544986077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2443654284281540363324051 3665481426422310544986077)
    ·
      refine ⟨1374555534908366454369779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3665481426422310544986077 1374555534908366454369779)
      ·
        refine ⟨2061833302362549681554669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1374555534908366454369779 2061833302362549681554669)
        ·
          refine ⟨773187488385956130583001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2061833302362549681554669 773187488385956130583001)
          ·
            refine ⟨579890616289467097937251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 773187488385956130583001 579890616289467097937251)
            ·
              refine ⟨869835924434200646905877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579890616289467097937251 869835924434200646905877)
              ·
                refine ⟨40773558957853155323713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 869835924434200646905877 40773558957853155323713)
                ·
                  refine ⟨30580169218389866492785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40773558957853155323713 30580169218389866492785)
                  ·
                    rfl

theorem cell20_66999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 2].length) (baseStart_66999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_66999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_66999 prefixEnd_66999 := by exact prefixLift 66999
  have htrace : WordTrace (prefixWord ++ tailWord_66999) baseStart_66999 baseEnd_66999 := by
    simpa [prefixWord, tailWord_66999, baseEnd_66999] using wordTrace_append hprefix tailTrace_66999
  have hstable : (prefixWord ++ tailWord_66999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66999).length < 2 ^ (prefixWord ++ tailWord_66999).sum := by decide
  have hdescent : baseEnd_66999 < baseStart_66999 := by decide
  rcases family_descends (prefixWord ++ tailWord_66999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67030 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_67030 : Nat := 118140960795 + 67030 * 2 ^ 59
def prefixEnd_67030 : Nat := 4983230072969 + 3 ^ 40 * 67030 * 2
def baseEnd_67030 : Nat := 30594318463091536459325

theorem tailTrace_67030 : CollatzResearch.WordTrace tailWord_67030 prefixEnd_67030 30594318463091536459325 := by
  unfold tailWord_67030
  simp only [CollatzResearch.WordTrace]
  refine ⟨152799059198077041106409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1629856631446155105135029 152799059198077041106409)
  ·
    refine ⟨114599294398557780829807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152799059198077041106409 114599294398557780829807)
    ·
      refine ⟨171898941597836671244711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114599294398557780829807 171898941597836671244711)
      ·
        refine ⟨257848412396755006867067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171898941597836671244711 257848412396755006867067)
        ·
          refine ⟨386772618595132510300601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257848412396755006867067 386772618595132510300601)
          ·
            refine ⟨290079463946349382725451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386772618595132510300601 290079463946349382725451)
            ·
              refine ⟨435119195919524074088177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290079463946349382725451 435119195919524074088177)
              ·
                refine ⟨326339396939643055566133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 435119195919524074088177 326339396939643055566133)
                ·
                  refine ⟨30594318463091536459325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 326339396939643055566133 30594318463091536459325)
                  ·
                    rfl

theorem cell20_67030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_67030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67030 prefixEnd_67030 := by exact prefixLift 67030
  have htrace : WordTrace (prefixWord ++ tailWord_67030) baseStart_67030 baseEnd_67030 := by
    simpa [prefixWord, tailWord_67030, baseEnd_67030] using wordTrace_append hprefix tailTrace_67030
  have hstable : (prefixWord ++ tailWord_67030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67030).length < 2 ^ (prefixWord ++ tailWord_67030).sum := by decide
  have hdescent : baseEnd_67030 < baseStart_67030 := by decide
  rcases family_descends (prefixWord ++ tailWord_67030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67061 : List Nat := [1, 3, 5, 1, 1, 2, 2, 5]
def baseStart_67061 : Nat := 118140960795 + 67061 * 2 ^ 59
def prefixEnd_67061 : Nat := 4983230072969 + 3 ^ 40 * 67061 * 2
def baseEnd_67061 : Nat := 10202822569264402141955

theorem tailTrace_67061 : CollatzResearch.WordTrace tailWord_67061 prefixEnd_67061 10202822569264402141955 := by
  unfold tailWord_67061
  simp only [CollatzResearch.WordTrace]
  refine ⟨2445915610056924952081037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1630610406704616634720691 2445915610056924952081037)
  ·
    refine ⟨917218353771346857030389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2445915610056924952081037 917218353771346857030389)
    ·
      refine ⟨85989220666063767846599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 917218353771346857030389 85989220666063767846599)
      ·
        refine ⟨128983830999095651769899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85989220666063767846599 128983830999095651769899)
        ·
          refine ⟨193475746498643477654849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128983830999095651769899 193475746498643477654849)
          ·
            refine ⟨145106809873982608241137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193475746498643477654849 145106809873982608241137)
            ·
              refine ⟨108830107405486956180853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145106809873982608241137 108830107405486956180853)
              ·
                refine ⟨10202822569264402141955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108830107405486956180853 10202822569264402141955)
                ·
                  rfl

theorem cell20_67061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 5].length) (baseStart_67061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67061 prefixEnd_67061 := by exact prefixLift 67061
  have htrace : WordTrace (prefixWord ++ tailWord_67061) baseStart_67061 baseEnd_67061 := by
    simpa [prefixWord, tailWord_67061, baseEnd_67061] using wordTrace_append hprefix tailTrace_67061
  have hstable : (prefixWord ++ tailWord_67061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67061).length < 2 ^ (prefixWord ++ tailWord_67061).sum := by decide
  have hdescent : baseEnd_67061 < baseStart_67061 := by decide
  rcases family_descends (prefixWord ++ tailWord_67061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67068 : List Nat := [2, 2, 2, 1, 2, 1, 6, 1, 3]
def baseStart_67068 : Nat := 118140960795 + 67068 * 2 ^ 59
def prefixEnd_67068 : Nat := 4983230072969 + 3 ^ 40 * 67068 * 2
def baseEnd_67068 : Nat := 30611662698532293192503

theorem tailTrace_67068 : CollatzResearch.WordTrace tailWord_67068 prefixEnd_67068 30611662698532293192503 := by
  unfold tailWord_67068
  simp only [CollatzResearch.WordTrace]
  refine ⟨1223085460515782573792929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1630780614021043431723905 1223085460515782573792929)
  ·
    refine ⟨917314095386836930344697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1223085460515782573792929 917314095386836930344697)
    ·
      refine ⟨687985571540127697758523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 917314095386836930344697 687985571540127697758523)
      ·
        refine ⟨1031978357310191546637785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687985571540127697758523 1031978357310191546637785)
        ·
          refine ⟨773983767982643659978339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1031978357310191546637785 773983767982643659978339)
          ·
            refine ⟨1160975651973965489967509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773983767982643659978339 1160975651973965489967509)
            ·
              refine ⟨54420733686279632342227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1160975651973965489967509 54420733686279632342227)
              ·
                refine ⟨81631100529419448513341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54420733686279632342227 81631100529419448513341)
                ·
                  refine ⟨30611662698532293192503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81631100529419448513341 30611662698532293192503)
                  ·
                    rfl

theorem cell20_67068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_67068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67068 prefixEnd_67068 := by exact prefixLift 67068
  have htrace : WordTrace (prefixWord ++ tailWord_67068) baseStart_67068 baseEnd_67068 := by
    simpa [prefixWord, tailWord_67068, baseEnd_67068] using wordTrace_append hprefix tailTrace_67068
  have hstable : (prefixWord ++ tailWord_67068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67068).length < 2 ^ (prefixWord ++ tailWord_67068).sum := by decide
  have hdescent : baseEnd_67068 < baseStart_67068 := by decide
  rcases family_descends (prefixWord ++ tailWord_67068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67127 : List Nat := [1, 1, 3, 1, 2, 4, 2, 3, 3]
def baseStart_67127 : Nat := 118140960795 + 67127 * 2 ^ 59
def prefixEnd_67127 : Nat := 4983230072969 + 3 ^ 40 * 67127 * 2
def baseEnd_67127 : Nat := 30638591906190310225595

theorem tailTrace_67127 : CollatzResearch.WordTrace tailWord_67127 prefixEnd_67127 30638591906190310225595 := by
  unfold tailWord_67127
  simp only [CollatzResearch.WordTrace]
  refine ⟨2448322827817818223983635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1632215218545212149322423 2448322827817818223983635)
  ·
    refine ⟨3672484241726727335975453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2448322827817818223983635 3672484241726727335975453)
    ·
      refine ⟨1377181590647522750990795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3672484241726727335975453 1377181590647522750990795)
      ·
        refine ⟨2065772385971284126486193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1377181590647522750990795 2065772385971284126486193)
        ·
          refine ⟨1549329289478463094864645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2065772385971284126486193 1549329289478463094864645)
          ·
            refine ⟨290499241777211830287121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1549329289478463094864645 290499241777211830287121)
            ·
              refine ⟨217874431332908872715341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290499241777211830287121 217874431332908872715341)
              ·
                refine ⟨81702911749840827268253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217874431332908872715341 81702911749840827268253)
                ·
                  refine ⟨30638591906190310225595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81702911749840827268253 30638591906190310225595)
                  ·
                    rfl

theorem cell20_67127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 3].length) (baseStart_67127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67127 prefixEnd_67127 := by exact prefixLift 67127
  have htrace : WordTrace (prefixWord ++ tailWord_67127) baseStart_67127 baseEnd_67127 := by
    simpa [prefixWord, tailWord_67127, baseEnd_67127] using wordTrace_append hprefix tailTrace_67127
  have hstable : (prefixWord ++ tailWord_67127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67127).length < 2 ^ (prefixWord ++ tailWord_67127).sum := by decide
  have hdescent : baseEnd_67127 < baseStart_67127 := by decide
  rcases family_descends (prefixWord ++ tailWord_67127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67172 : List Nat := [2, 3, 1, 1, 2, 3, 1, 3, 4]
def baseStart_67172 : Nat := 118140960795 + 67172 * 2 ^ 59
def prefixEnd_67172 : Nat := 4983230072969 + 3 ^ 40 * 67172 * 2
def baseEnd_67172 : Nat := 30659131132370153725411

theorem tailTrace_67172 : CollatzResearch.WordTrace tailWord_67172 prefixEnd_67172 30659131132370153725411 := by
  unfold tailWord_67172
  simp only [CollatzResearch.WordTrace]
  refine ⟨1224982056327395454685885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1633309408436527272914513 1224982056327395454685885)
  ·
    refine ⟨459368271122773295507207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1224982056327395454685885 459368271122773295507207)
    ·
      refine ⟨689052406684159943260811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 459368271122773295507207 689052406684159943260811)
      ·
        refine ⟨1033578610026239914891217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 689052406684159943260811 1033578610026239914891217)
        ·
          refine ⟨775183957519679936168413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1033578610026239914891217 775183957519679936168413)
          ·
            refine ⟨290693984069879976063155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 775183957519679936168413 290693984069879976063155)
            ·
              refine ⟨436040976104819964094733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290693984069879976063155 436040976104819964094733)
              ·
                refine ⟨163515366039307486535525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 436040976104819964094733 163515366039307486535525)
                ·
                  refine ⟨30659131132370153725411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163515366039307486535525 30659131132370153725411)
                  ·
                    rfl

theorem cell20_67172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_67172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67172 prefixEnd_67172 := by exact prefixLift 67172
  have htrace : WordTrace (prefixWord ++ tailWord_67172) baseStart_67172 baseEnd_67172 := by
    simpa [prefixWord, tailWord_67172, baseEnd_67172] using wordTrace_append hprefix tailTrace_67172
  have hstable : (prefixWord ++ tailWord_67172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67172).length < 2 ^ (prefixWord ++ tailWord_67172).sum := by decide
  have hdescent : baseEnd_67172 < baseStart_67172 := by decide
  rcases family_descends (prefixWord ++ tailWord_67172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67189 : List Nat := [1, 3, 4, 2, 1, 1, 2, 2, 4]
def baseStart_67189 : Nat := 118140960795 + 67189 * 2 ^ 59
def prefixEnd_67189 : Nat := 4983230072969 + 3 ^ 40 * 67189 * 2
def baseEnd_67189 : Nat := 30666890395593650158675

theorem tailTrace_67189 : CollatzResearch.WordTrace tailWord_67189 prefixEnd_67189 30666890395593650158675 := by
  unfold tailWord_67189
  simp only [CollatzResearch.WordTrace]
  refine ⟨2450584153593202812740621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1633722769062135208493747 2450584153593202812740621)
  ·
    refine ⟨918969057597451054777733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2450584153593202812740621 918969057597451054777733)
    ·
      refine ⟨172306698299522072770825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 918969057597451054777733 172306698299522072770825)
      ·
        refine ⟨129230023724641554578119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172306698299522072770825 129230023724641554578119)
        ·
          refine ⟨193845035586962331867179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129230023724641554578119 193845035586962331867179)
          ·
            refine ⟨290767553380443497800769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193845035586962331867179 290767553380443497800769)
            ·
              refine ⟨218075665035332623350577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290767553380443497800769 218075665035332623350577)
              ·
                refine ⟨163556748776499467512933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218075665035332623350577 163556748776499467512933)
                ·
                  refine ⟨30666890395593650158675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163556748776499467512933 30666890395593650158675)
                  ·
                    rfl

theorem cell20_67189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_67189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67189 prefixEnd_67189 := by exact prefixLift 67189
  have htrace : WordTrace (prefixWord ++ tailWord_67189) baseStart_67189 baseEnd_67189 := by
    simpa [prefixWord, tailWord_67189, baseEnd_67189] using wordTrace_append hprefix tailTrace_67189
  have hstable : (prefixWord ++ tailWord_67189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67189).length < 2 ^ (prefixWord ++ tailWord_67189).sum := by decide
  have hdescent : baseEnd_67189 < baseStart_67189 := by decide
  rcases family_descends (prefixWord ++ tailWord_67189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67255 : List Nat := [1, 1, 3, 1, 5, 1, 2, 6]
def baseStart_67255 : Nat := 118140960795 + 67255 * 2 ^ 59
def prefixEnd_67255 : Nat := 4983230072969 + 3 ^ 40 * 67255 * 2
def baseEnd_67255 : Nat := 10232338197996917986135

theorem tailTrace_67255 : CollatzResearch.WordTrace tailWord_67255 prefixEnd_67255 10232338197996917986135 := by
  unfold tailWord_67255
  simp only [CollatzResearch.WordTrace]
  refine ⟨2452991371354096084643219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1635327580902730723095479 2452991371354096084643219)
  ·
    refine ⟨3679487057031144126964829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2452991371354096084643219 3679487057031144126964829)
    ·
      refine ⟨1379807646386679047611811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3679487057031144126964829 1379807646386679047611811)
      ·
        refine ⟨2069711469580018571417717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1379807646386679047611811 2069711469580018571417717)
        ·
          refine ⟨194035450273126741070411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2069711469580018571417717 194035450273126741070411)
          ·
            refine ⟨291053175409690111605617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194035450273126741070411 291053175409690111605617)
            ·
              refine ⟨218289881557267583704213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291053175409690111605617 218289881557267583704213)
              ·
                refine ⟨10232338197996917986135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 218289881557267583704213 10232338197996917986135)
                ·
                  rfl

theorem cell20_67255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 6].length) (baseStart_67255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67255 prefixEnd_67255 := by exact prefixLift 67255
  have htrace : WordTrace (prefixWord ++ tailWord_67255) baseStart_67255 baseEnd_67255 := by
    simpa [prefixWord, tailWord_67255, baseEnd_67255] using wordTrace_append hprefix tailTrace_67255
  have hstable : (prefixWord ++ tailWord_67255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67255).length < 2 ^ (prefixWord ++ tailWord_67255).sum := by decide
  have hdescent : baseEnd_67255 < baseStart_67255 := by decide
  rcases family_descends (prefixWord ++ tailWord_67255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67269 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 6]
def baseStart_67269 : Nat := 118140960795 + 67269 * 2 ^ 59
def prefixEnd_67269 : Nat := 4983230072969 + 3 ^ 40 * 67269 * 2
def baseEnd_67269 : Nat := 30703404575468927491681

theorem tailTrace_67269 : CollatzResearch.WordTrace tailWord_67269 prefixEnd_67269 30703404575468927491681 := by
  unfold tailWord_67269
  simp only [CollatzResearch.WordTrace]
  refine ⟨2453501993303376475652861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1635667995535584317101907 2453501993303376475652861)
  ·
    refine ⟨920063247488766178369823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2453501993303376475652861 920063247488766178369823)
    ·
      refine ⟨1380094871233149267554735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 920063247488766178369823 1380094871233149267554735)
      ·
        refine ⟨2070142306849723901332103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1380094871233149267554735 2070142306849723901332103)
        ·
          refine ⟨3105213460274585851998155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2070142306849723901332103 3105213460274585851998155)
          ·
            refine ⟨4657820190411878777997233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3105213460274585851998155 4657820190411878777997233)
            ·
              refine ⟨3493365142808909083497925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4657820190411878777997233 3493365142808909083497925)
              ·
                refine ⟨655005964276670453155861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3493365142808909083497925 655005964276670453155861)
                ·
                  refine ⟨30703404575468927491681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 655005964276670453155861 30703404575468927491681)
                  ·
                    rfl

theorem cell20_67269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_67269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67269 prefixEnd_67269 := by exact prefixLift 67269
  have htrace : WordTrace (prefixWord ++ tailWord_67269) baseStart_67269 baseEnd_67269 := by
    simpa [prefixWord, tailWord_67269, baseEnd_67269] using wordTrace_append hprefix tailTrace_67269
  have hstable : (prefixWord ++ tailWord_67269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67269).length < 2 ^ (prefixWord ++ tailWord_67269).sum := by decide
  have hdescent : baseEnd_67269 < baseStart_67269 := by decide
  rcases family_descends (prefixWord ++ tailWord_67269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67282 : List Nat := [3, 2, 2, 2, 2, 2, 1, 4, 2]
def baseStart_67282 : Nat := 118140960795 + 67282 * 2 ^ 59
def prefixEnd_67282 : Nat := 4983230072969 + 3 ^ 40 * 67282 * 2
def baseEnd_67282 : Nat := 30709338129698660058295

theorem tailTrace_67282 : CollatzResearch.WordTrace tailWord_67282 prefixEnd_67282 30709338129698660058295 := by
  unfold tailWord_67282
  simp only [CollatzResearch.WordTrace]
  refine ⟨613494035564069923969025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1635984094837519797250733 613494035564069923969025)
  ·
    refine ⟨460120526673052442976769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 613494035564069923969025 460120526673052442976769)
    ·
      refine ⟨345090395004789332232577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 460120526673052442976769 345090395004789332232577)
      ·
        refine ⟨258817796253591999174433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345090395004789332232577 258817796253591999174433)
        ·
          refine ⟨194113347190193999380825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258817796253591999174433 194113347190193999380825)
          ·
            refine ⟨145585010392645499535619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194113347190193999380825 145585010392645499535619)
            ·
              refine ⟨218377515588968249303429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145585010392645499535619 218377515588968249303429)
              ·
                refine ⟨40945784172931546744393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218377515588968249303429 40945784172931546744393)
                ·
                  refine ⟨30709338129698660058295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40945784172931546744393 30709338129698660058295)
                  ·
                    rfl

theorem cell20_67282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_67282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67282 prefixEnd_67282 := by exact prefixLift 67282
  have htrace : WordTrace (prefixWord ++ tailWord_67282) baseStart_67282 baseEnd_67282 := by
    simpa [prefixWord, tailWord_67282, baseEnd_67282] using wordTrace_append hprefix tailTrace_67282
  have hstable : (prefixWord ++ tailWord_67282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67282).length < 2 ^ (prefixWord ++ tailWord_67282).sum := by decide
  have hdescent : baseEnd_67282 < baseStart_67282 := by decide
  rcases family_descends (prefixWord ++ tailWord_67282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67307 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 6]
def baseStart_67307 : Nat := 118140960795 + 67307 * 2 ^ 59
def prefixEnd_67307 : Nat := 4983230072969 + 3 ^ 40 * 67307 * 2
def baseEnd_67307 : Nat := 30720748810909684224859

theorem tailTrace_67307 : CollatzResearch.WordTrace tailWord_67307 prefixEnd_67307 30720748810909684224859 := by
  unfold tailWord_67307
  simp only [CollatzResearch.WordTrace]
  refine ⟨2454887967165708965536175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1636591978110472643690783 2454887967165708965536175)
  ·
    refine ⟨3682331950748563448304263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2454887967165708965536175 3682331950748563448304263)
    ·
      refine ⟨5523497926122845172456395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3682331950748563448304263 5523497926122845172456395)
      ·
        refine ⟨8285246889184267758684593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5523497926122845172456395 8285246889184267758684593)
        ·
          refine ⟨6213935166888200819013445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8285246889184267758684593 6213935166888200819013445)
          ·
            refine ⟨1165112843791537653565021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6213935166888200819013445 1165112843791537653565021)
            ·
              refine ⟨436917316421826620086883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1165112843791537653565021 436917316421826620086883)
              ·
                refine ⟨655375974632739930130325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436917316421826620086883 655375974632739930130325)
                ·
                  refine ⟨30720748810909684224859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 655375974632739930130325 30720748810909684224859)
                  ·
                    rfl

theorem cell20_67307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_67307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67307 prefixEnd_67307 := by exact prefixLift 67307
  have htrace : WordTrace (prefixWord ++ tailWord_67307) baseStart_67307 baseEnd_67307 := by
    simpa [prefixWord, tailWord_67307, baseEnd_67307] using wordTrace_append hprefix tailTrace_67307
  have hstable : (prefixWord ++ tailWord_67307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67307).length < 2 ^ (prefixWord ++ tailWord_67307).sum := by decide
  have hdescent : baseEnd_67307 < baseStart_67307 := by decide
  rcases family_descends (prefixWord ++ tailWord_67307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67310 : List Nat := [4, 1, 2, 1, 1, 2, 5, 4]
def baseStart_67310 : Nat := 118140960795 + 67310 * 2 ^ 59
def prefixEnd_67310 : Nat := 4983230072969 + 3 ^ 40 * 67310 * 2
def baseEnd_67310 : Nat := 10240706030885002374949

theorem tailTrace_67310 : CollatzResearch.WordTrace tailWord_67310 prefixEnd_67310 10240706030885002374949 := by
  unfold tailWord_67310
  simp only [CollatzResearch.WordTrace]
  refine ⟨306874673269355059736923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1636664924103226985263589 306874673269355059736923)
  ·
    refine ⟨460312009904032589605385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 306874673269355059736923 460312009904032589605385)
    ·
      refine ⟨345234007428024442204039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 460312009904032589605385 345234007428024442204039)
      ·
        refine ⟨517851011142036663306059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345234007428024442204039 517851011142036663306059)
        ·
          refine ⟨776776516713054994959089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517851011142036663306059 776776516713054994959089)
          ·
            refine ⟨582582387534791246219317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 776776516713054994959089 582582387534791246219317)
            ·
              refine ⟨54617098831386679333061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 582582387534791246219317 54617098831386679333061)
              ·
                refine ⟨10240706030885002374949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54617098831386679333061 10240706030885002374949)
                ·
                  rfl

theorem cell20_67310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_67310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67310 prefixEnd_67310 := by exact prefixLift 67310
  have htrace : WordTrace (prefixWord ++ tailWord_67310) baseStart_67310 baseEnd_67310 := by
    simpa [prefixWord, tailWord_67310, baseEnd_67310] using wordTrace_append hprefix tailTrace_67310
  have hstable : (prefixWord ++ tailWord_67310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67310).length < 2 ^ (prefixWord ++ tailWord_67310).sum := by decide
  have hdescent : baseEnd_67310 < baseStart_67310 := by decide
  rcases family_descends (prefixWord ++ tailWord_67310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67316 : List Nat := [2, 6, 1, 1, 1, 2, 2, 3, 2]
def baseStart_67316 : Nat := 118140960795 + 67316 * 2 ^ 59
def prefixEnd_67316 : Nat := 4983230072969 + 3 ^ 40 * 67316 * 2
def baseEnd_67316 : Nat := 30724856656145652924823

theorem tailTrace_67316 : CollatzResearch.WordTrace tailWord_67316 prefixEnd_67316 30724856656145652924823 := by
  unfold tailWord_67316
  simp only [CollatzResearch.WordTrace]
  refine ⟨1227608112066551751306901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1636810816088735668409201 1227608112066551751306901)
  ·
    refine ⟨57544130253119613342511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1227608112066551751306901 57544130253119613342511)
    ·
      refine ⟨86316195379679420013767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57544130253119613342511 86316195379679420013767)
      ·
        refine ⟨129474293069519130020651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86316195379679420013767 129474293069519130020651)
        ·
          refine ⟨194211439604278695030977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129474293069519130020651 194211439604278695030977)
          ·
            refine ⟨145658579703209021273233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194211439604278695030977 145658579703209021273233)
            ·
              refine ⟨109243934777406765954925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145658579703209021273233 109243934777406765954925)
              ·
                refine ⟨40966475541527537233097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109243934777406765954925 40966475541527537233097)
                ·
                  refine ⟨30724856656145652924823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40966475541527537233097 30724856656145652924823)
                  ·
                    rfl

theorem cell20_67316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_67316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67316 prefixEnd_67316 := by exact prefixLift 67316
  have htrace : WordTrace (prefixWord ++ tailWord_67316) baseStart_67316 baseEnd_67316 := by
    simpa [prefixWord, tailWord_67316, baseEnd_67316] using wordTrace_append hprefix tailTrace_67316
  have hstable : (prefixWord ++ tailWord_67316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67316).length < 2 ^ (prefixWord ++ tailWord_67316).sum := by decide
  have hdescent : baseEnd_67316 < baseStart_67316 := by decide
  rcases family_descends (prefixWord ++ tailWord_67316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67362 : List Nat := [3, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_67362 : Nat := 118140960795 + 67362 * 2 ^ 59
def prefixEnd_67362 : Nat := 4983230072969 + 3 ^ 40 * 67362 * 2
def baseEnd_67362 : Nat := 30745852309573937391301

theorem tailTrace_67362 : CollatzResearch.WordTrace tailWord_67362 prefixEnd_67362 30745852309573937391301 := by
  unfold tailWord_67362
  simp only [CollatzResearch.WordTrace]
  refine ⟨614223495491613339697085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1637929321310968905858893 614223495491613339697085)
  ·
    refine ⟨230333810809355002386407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 614223495491613339697085 230333810809355002386407)
    ·
      refine ⟨345500716214032503579611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230333810809355002386407 345500716214032503579611)
      ·
        refine ⟨518251074321048755369417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345500716214032503579611 518251074321048755369417)
        ·
          refine ⟨388688305740786566527063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 518251074321048755369417 388688305740786566527063)
          ·
            refine ⟨583032458611179849790595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388688305740786566527063 583032458611179849790595)
            ·
              refine ⟨874548687916769774685893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 583032458611179849790595 874548687916769774685893)
              ·
                refine ⟨163977878984394332753605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 874548687916769774685893 163977878984394332753605)
                ·
                  refine ⟨30745852309573937391301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163977878984394332753605 30745852309573937391301)
                  ·
                    rfl

theorem cell20_67362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_67362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67362 prefixEnd_67362 := by exact prefixLift 67362
  have htrace : WordTrace (prefixWord ++ tailWord_67362) baseStart_67362 baseEnd_67362 := by
    simpa [prefixWord, tailWord_67362, baseEnd_67362] using wordTrace_append hprefix tailTrace_67362
  have hstable : (prefixWord ++ tailWord_67362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67362).length < 2 ^ (prefixWord ++ tailWord_67362).sum := by decide
  have hdescent : baseEnd_67362 < baseStart_67362 := by decide
  rcases family_descends (prefixWord ++ tailWord_67362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67400 : List Nat := [2, 1, 3, 1, 1, 4, 3, 1, 4]
def baseStart_67400 : Nat := 118140960795 + 67400 * 2 ^ 59
def prefixEnd_67400 : Nat := 4983230072969 + 3 ^ 40 * 67400 * 2
def baseEnd_67400 : Nat := 30763196545014694124479

theorem tailTrace_67400 : CollatzResearch.WordTrace tailWord_67400 prefixEnd_67400 30763196545014694124479 := by
  unfold tailWord_67400
  simp only [CollatzResearch.WordTrace]
  refine ⟨1229139977914392924335827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1638853303885857232447769 1229139977914392924335827)
  ·
    refine ⟨1843709966871589386503741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1229139977914392924335827 1843709966871589386503741)
    ·
      refine ⟨691391237576846019938903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1843709966871589386503741 691391237576846019938903)
      ·
        refine ⟨1037086856365269029908355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 691391237576846019938903 1037086856365269029908355)
        ·
          refine ⟨1555630284547903544862533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1037086856365269029908355 1555630284547903544862533)
          ·
            refine ⟨291680678352731914661725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1555630284547903544862533 291680678352731914661725)
            ·
              refine ⟨109380254382274467998147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 291680678352731914661725 109380254382274467998147)
              ·
                refine ⟨164070381573411701997221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109380254382274467998147 164070381573411701997221)
                ·
                  refine ⟨30763196545014694124479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164070381573411701997221 30763196545014694124479)
                  ·
                    rfl

theorem cell20_67400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_67400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67400 prefixEnd_67400 := by exact prefixLift 67400
  have htrace : WordTrace (prefixWord ++ tailWord_67400) baseStart_67400 baseEnd_67400 := by
    simpa [prefixWord, tailWord_67400, baseEnd_67400] using wordTrace_append hprefix tailTrace_67400
  have hstable : (prefixWord ++ tailWord_67400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67400).length < 2 ^ (prefixWord ++ tailWord_67400).sum := by decide
  have hdescent : baseEnd_67400 < baseStart_67400 := by decide
  rcases family_descends (prefixWord ++ tailWord_67400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67410 : List Nat := [3, 2, 2, 1, 1, 3, 4, 1, 3]
def baseStart_67410 : Nat := 118140960795 + 67410 * 2 ^ 59
def prefixEnd_67410 : Nat := 4983230072969 + 3 ^ 40 * 67410 * 2
def baseEnd_67410 : Nat := 30767760817499103791105

theorem tailTrace_67410 : CollatzResearch.WordTrace tailWord_67410 prefixEnd_67410 30767760817499103791105 := by
  unfold tailWord_67410
  simp only [CollatzResearch.WordTrace]
  refine ⟨614661171448139389133921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1639096457195038371023789 614661171448139389133921)
  ·
    refine ⟨460995878586104541850441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 614661171448139389133921 460995878586104541850441)
    ·
      refine ⟨345746908939578406387831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 460995878586104541850441 345746908939578406387831)
      ·
        refine ⟨518620363409367609581747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345746908939578406387831 518620363409367609581747)
        ·
          refine ⟨777930545114051414372621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518620363409367609581747 777930545114051414372621)
          ·
            refine ⟨291723954417769280389733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 777930545114051414372621 291723954417769280389733)
            ·
              refine ⟨54698241453331740073075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 291723954417769280389733 54698241453331740073075)
              ·
                refine ⟨82047362179997610109613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54698241453331740073075 82047362179997610109613)
                ·
                  refine ⟨30767760817499103791105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82047362179997610109613 30767760817499103791105)
                  ·
                    rfl

theorem cell20_67410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_67410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67410 prefixEnd_67410 := by exact prefixLift 67410
  have htrace : WordTrace (prefixWord ++ tailWord_67410) baseStart_67410 baseEnd_67410 := by
    simpa [prefixWord, tailWord_67410, baseEnd_67410] using wordTrace_append hprefix tailTrace_67410
  have hstable : (prefixWord ++ tailWord_67410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67410).length < 2 ^ (prefixWord ++ tailWord_67410).sum := by decide
  have hdescent : baseEnd_67410 < baseStart_67410 := by decide
  rcases family_descends (prefixWord ++ tailWord_67410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67476 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 6]
def baseStart_67476 : Nat := 118140960795 + 67476 * 2 ^ 59
def prefixEnd_67476 : Nat := 4983230072969 + 3 ^ 40 * 67476 * 2
def baseEnd_67476 : Nat := 30797885015896207590835

theorem tailTrace_67476 : CollatzResearch.WordTrace tailWord_67476 prefixEnd_67476 30797885015896207590835 := by
  unfold tailWord_67476
  simp only [CollatzResearch.WordTrace]
  refine ⟨1230525951776725414219141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1640701269035633885625521 1230525951776725414219141)
  ·
    refine ⟨230723615958136015166089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1230525951776725414219141 230723615958136015166089)
    ·
      refine ⟨173042711968602011374567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230723615958136015166089 173042711968602011374567)
      ·
        refine ⟨259564067952903017061851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173042711968602011374567 259564067952903017061851)
        ·
          refine ⟨389346101929354525592777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259564067952903017061851 389346101929354525592777)
          ·
            refine ⟨292009576447015894194583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 389346101929354525592777 292009576447015894194583)
            ·
              refine ⟨438014364670523841291875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292009576447015894194583 438014364670523841291875)
              ·
                refine ⟨657021547005785761937813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438014364670523841291875 657021547005785761937813)
                ·
                  refine ⟨30797885015896207590835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 657021547005785761937813 30797885015896207590835)
                  ·
                    rfl

theorem cell20_67476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_67476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67476 prefixEnd_67476 := by exact prefixLift 67476
  have htrace : WordTrace (prefixWord ++ tailWord_67476) baseStart_67476 baseEnd_67476 := by
    simpa [prefixWord, tailWord_67476, baseEnd_67476] using wordTrace_append hprefix tailTrace_67476
  have hstable : (prefixWord ++ tailWord_67476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67476).length < 2 ^ (prefixWord ++ tailWord_67476).sum := by decide
  have hdescent : baseEnd_67476 < baseStart_67476 := by decide
  rcases family_descends (prefixWord ++ tailWord_67476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67535 : List Nat := [1, 1, 2, 1, 1, 5, 1, 4, 4]
def baseStart_67535 : Nat := 118140960795 + 67535 * 2 ^ 59
def prefixEnd_67535 : Nat := 4983230072969 + 3 ^ 40 * 67535 * 2
def baseEnd_67535 : Nat := 30824814223554224623927

theorem tailTrace_67535 : CollatzResearch.WordTrace tailWord_67535 prefixEnd_67535 30824814223554224623927 := by
  unfold tailWord_67535
  simp only [CollatzResearch.WordTrace]
  refine ⟨2463203810339703904836059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1642135873559802603224039 2463203810339703904836059)
  ·
    refine ⟨3694805715509555857254089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2463203810339703904836059 3694805715509555857254089)
    ·
      refine ⟨2771104286632166892940567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3694805715509555857254089 2771104286632166892940567)
      ·
        refine ⟨4156656429948250339410851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2771104286632166892940567 4156656429948250339410851)
        ·
          refine ⟨6234984644922375509116277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4156656429948250339410851 6234984644922375509116277)
          ·
            refine ⟨584529810461472703979651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6234984644922375509116277 584529810461472703979651)
            ·
              refine ⟨876794715692209055969477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584529810461472703979651 876794715692209055969477)
              ·
                refine ⟨164399009192289197994277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 876794715692209055969477 164399009192289197994277)
                ·
                  refine ⟨30824814223554224623927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164399009192289197994277 30824814223554224623927)
                  ·
                    rfl

theorem cell20_67535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_67535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67535 prefixEnd_67535 := by exact prefixLift 67535
  have htrace : WordTrace (prefixWord ++ tailWord_67535) baseStart_67535 baseEnd_67535 := by
    simpa [prefixWord, tailWord_67535, baseEnd_67535] using wordTrace_append hprefix tailTrace_67535
  have hstable : (prefixWord ++ tailWord_67535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67535).length < 2 ^ (prefixWord ++ tailWord_67535).sum := by decide
  have hdescent : baseEnd_67535 < baseStart_67535 := by decide
  rcases family_descends (prefixWord ++ tailWord_67535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67538 : List Nat := [3, 2, 2, 3, 2, 1, 1, 6]
def baseStart_67538 : Nat := 118140960795 + 67538 * 2 ^ 59
def prefixEnd_67538 : Nat := 4983230072969 + 3 ^ 40 * 67538 * 2
def baseEnd_67538 : Nat := 10275394501766515841305

theorem tailTrace_67538 : CollatzResearch.WordTrace tailWord_67538 prefixEnd_67538 10275394501766515841305 := by
  unfold tailWord_67538
  simp only [CollatzResearch.WordTrace]
  refine ⟨615828307332208854298817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1642208819552556944796845 615828307332208854298817)
  ·
    refine ⟨461871230499156640724113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 615828307332208854298817 461871230499156640724113)
    ·
      refine ⟨346403422874367480543085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 461871230499156640724113 346403422874367480543085)
      ·
        refine ⟨129901283577887805203657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 346403422874367480543085 129901283577887805203657)
        ·
          refine ⟨97425962683415853902743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129901283577887805203657 97425962683415853902743)
          ·
            refine ⟨146138944025123780854115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97425962683415853902743 146138944025123780854115)
            ·
              refine ⟨219208416037685671281173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146138944025123780854115 219208416037685671281173)
              ·
                refine ⟨10275394501766515841305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 219208416037685671281173 10275394501766515841305)
                ·
                  rfl

theorem cell20_67538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_67538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_67538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_67538 prefixEnd_67538 := by exact prefixLift 67538
  have htrace : WordTrace (prefixWord ++ tailWord_67538) baseStart_67538 baseEnd_67538 := by
    simpa [prefixWord, tailWord_67538, baseEnd_67538] using wordTrace_append hprefix tailTrace_67538
  have hstable : (prefixWord ++ tailWord_67538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67538).length < 2 ^ (prefixWord ++ tailWord_67538).sum := by decide
  have hdescent : baseEnd_67538 < baseStart_67538 := by decide
  rcases family_descends (prefixWord ++ tailWord_67538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
