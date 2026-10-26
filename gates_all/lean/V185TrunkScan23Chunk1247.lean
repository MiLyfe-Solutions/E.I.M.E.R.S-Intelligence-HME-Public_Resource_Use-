import V185TrunkScan23Chunk1246

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7386493 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 3, 4, 2]
def baseStart_7386493 : Nat := 118140960795 + 7386493 * 2 ^ 59
def prefixEnd_7386493 : Nat := 4983230072969 + 3 ^ 40 * 7386493 * 2
def baseEnd_7386493 : Nat := 3792821260070874045867643

theorem tailTrace_7386493 : CollatzResearch.WordTrace tailWord_7386493 prefixEnd_7386493 3792821260070874045867643 := by
  unfold tailWord_7386493
  simp only [CollatzResearch.WordTrace]
  refine ⟨269407532429004848415364133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179605021619336565610242755 269407532429004848415364133)
  ·
    refine ⟨50513912330438409077880775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269407532429004848415364133 50513912330438409077880775)
    ·
      refine ⟨75770868495657613616821163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50513912330438409077880775 75770868495657613616821163)
      ·
        refine ⟨113656302743486420425231745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75770868495657613616821163 113656302743486420425231745)
        ·
          refine ⟨85242227057614815318923809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113656302743486420425231745 85242227057614815318923809)
          ·
            refine ⟨63931670293211111489192857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85242227057614815318923809 63931670293211111489192857)
            ·
              refine ⟨47948752719908333616894643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63931670293211111489192857 47948752719908333616894643)
              ·
                refine ⟨71923129079862500425341965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47948752719908333616894643 71923129079862500425341965)
                ·
                  refine ⟨26971173404948437659503237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71923129079862500425341965 26971173404948437659503237)
                  ·
                    refine ⟨5057095013427832061156857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26971173404948437659503237 5057095013427832061156857)
                    ·
                      refine ⟨3792821260070874045867643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5057095013427832061156857 3792821260070874045867643)
                      ·
                        rfl

theorem cell23_7386493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_7386493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386493 prefixEnd_7386493 := by exact prefixLift 7386493
  have htrace : WordTrace (prefixWord ++ tailWord_7386493) baseStart_7386493 baseEnd_7386493 := by
    simpa [prefixWord, tailWord_7386493, baseEnd_7386493] using wordTrace_append hprefix tailTrace_7386493
  have hstable : (prefixWord ++ tailWord_7386493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386493).length < 2 ^ (prefixWord ++ tailWord_7386493).sum := by decide
  have hdescent : baseEnd_7386493 < baseStart_7386493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386527 : List Nat := [1, 1, 2, 5, 1, 3, 1, 3, 2, 2, 2]
def baseStart_7386527 : Nat := 118140960795 + 7386527 * 2 ^ 59
def prefixEnd_7386527 : Nat := 4983230072969 + 3 ^ 40 * 7386527 * 2
def baseEnd_7386527 : Nat := 3792838718413126912842487

theorem tailTrace_7386527 : CollatzResearch.WordTrace tailWord_7386527 prefixEnd_7386527 3792838718413126912842487 := by
  unfold tailWord_7386527
  simp only [CollatzResearch.WordTrace]
  refine ⟨269408772510881672222101835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179605848340587781481401223 269408772510881672222101835)
  ·
    refine ⟨404113158766322508333152753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269408772510881672222101835 404113158766322508333152753)
    ·
      refine ⟨303084869074741881249864565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404113158766322508333152753 303084869074741881249864565)
      ·
        refine ⟨28414206475757051367174803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 303084869074741881249864565 28414206475757051367174803)
        ·
          refine ⟨42621309713635577050762205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28414206475757051367174803 42621309713635577050762205)
          ·
            refine ⟨15982991142613341394035827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42621309713635577050762205 15982991142613341394035827)
            ·
              refine ⟨23974486713920012091053741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15982991142613341394035827 23974486713920012091053741)
              ·
                refine ⟨8990432517720004534145153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23974486713920012091053741 8990432517720004534145153)
                ·
                  refine ⟨6742824388290003400608865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8990432517720004534145153 6742824388290003400608865)
                  ·
                    refine ⟨5057118291217502550456649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6742824388290003400608865 5057118291217502550456649)
                    ·
                      refine ⟨3792838718413126912842487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5057118291217502550456649 3792838718413126912842487)
                      ·
                        rfl

theorem cell23_7386527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_7386527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386527 prefixEnd_7386527 := by exact prefixLift 7386527
  have htrace : WordTrace (prefixWord ++ tailWord_7386527) baseStart_7386527 baseEnd_7386527 := by
    simpa [prefixWord, tailWord_7386527, baseEnd_7386527] using wordTrace_append hprefix tailTrace_7386527
  have hstable : (prefixWord ++ tailWord_7386527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386527).length < 2 ^ (prefixWord ++ tailWord_7386527).sum := by decide
  have hdescent : baseEnd_7386527 < baseStart_7386527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386593 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 5, 4]
def baseStart_7386593 : Nat := 118140960795 + 7386593 * 2 ^ 59
def prefixEnd_7386593 : Nat := 4983230072969 + 3 ^ 40 * 7386593 * 2
def baseEnd_7386593 : Nat := 1264290869378774551539061

theorem tailTrace_7386593 : CollatzResearch.WordTrace tailWord_7386593 prefixEnd_7386593 1264290869378774551539061 := by
  unfold tailWord_7386593
  simp only [CollatzResearch.WordTrace]
  refine ⟨269411179728642565494004433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179607453152428376996002955 269411179728642565494004433)
  ·
    refine ⟨202058384796481924120503325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269411179728642565494004433 202058384796481924120503325)
    ·
      refine ⟨75771894298680721545188747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202058384796481924120503325 75771894298680721545188747)
      ·
        refine ⟨113657841448021082317783121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75771894298680721545188747 113657841448021082317783121)
        ·
          refine ⟨85243381086015811738337341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113657841448021082317783121 85243381086015811738337341)
          ·
            refine ⟨31966267907255929401876503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85243381086015811738337341 31966267907255929401876503)
            ·
              refine ⟨47949401860883894102814755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31966267907255929401876503 47949401860883894102814755)
              ·
                refine ⟨71924102791325841154222133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47949401860883894102814755 71924102791325841154222133)
                ·
                  refine ⟨6742884636686797608208325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71924102791325841154222133 6742884636686797608208325)
                  ·
                    refine ⟨1264290869378774551539061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6742884636686797608208325 1264290869378774551539061)
                    ·
                      rfl

theorem cell23_7386593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_7386593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386593 prefixEnd_7386593 := by exact prefixLift 7386593
  have htrace : WordTrace (prefixWord ++ tailWord_7386593) baseStart_7386593 baseEnd_7386593 := by
    simpa [prefixWord, tailWord_7386593, baseEnd_7386593] using wordTrace_append hprefix tailTrace_7386593
  have hstable : (prefixWord ++ tailWord_7386593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386593).length < 2 ^ (prefixWord ++ tailWord_7386593).sum := by decide
  have hdescent : baseEnd_7386593 < baseStart_7386593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386596 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_7386596 : Nat := 118140960795 + 7386596 * 2 ^ 59
def prefixEnd_7386596 : Nat := 4983230072969 + 3 ^ 40 * 7386596 * 2
def baseEnd_7386596 : Nat := 3792874148578287142879669

theorem tailTrace_7386596 : CollatzResearch.WordTrace tailWord_7386596 prefixEnd_7386596 3792874148578287142879669 := by
  unfold tailWord_7386596
  simp only [CollatzResearch.WordTrace]
  refine ⟨134705644573815848503181821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179607526098421131337575761 134705644573815848503181821)
  ·
    refine ⟨50514616715180943188693183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134705644573815848503181821 50514616715180943188693183)
    ·
      refine ⟨75771925072771414783039775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50514616715180943188693183 75771925072771414783039775)
      ·
        refine ⟨113657887609157122174559663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75771925072771414783039775 113657887609157122174559663)
        ·
          refine ⟨170486831413735683261839495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113657887609157122174559663 170486831413735683261839495)
          ·
            refine ⟨255730247120603524892759243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170486831413735683261839495 255730247120603524892759243)
            ·
              refine ⟨383595370680905287339138865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255730247120603524892759243 383595370680905287339138865)
              ·
                refine ⟨287696528010678965504354149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383595370680905287339138865 287696528010678965504354149)
                ·
                  refine ⟨53943099002002306032066403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 287696528010678965504354149 53943099002002306032066403)
                  ·
                    refine ⟨80914648503003459048099605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53943099002002306032066403 80914648503003459048099605)
                    ·
                      refine ⟨3792874148578287142879669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80914648503003459048099605 3792874148578287142879669)
                      ·
                        rfl

theorem cell23_7386596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_7386596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386596 prefixEnd_7386596 := by exact prefixLift 7386596
  have htrace : WordTrace (prefixWord ++ tailWord_7386596) baseStart_7386596 baseEnd_7386596 := by
    simpa [prefixWord, tailWord_7386596, baseEnd_7386596] using wordTrace_append hprefix tailTrace_7386596
  have hstable : (prefixWord ++ tailWord_7386596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386596).length < 2 ^ (prefixWord ++ tailWord_7386596).sum := by decide
  have hdescent : baseEnd_7386596 < baseStart_7386596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386603 : List Nat := [1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 3]
def baseStart_7386603 : Nat := 118140960795 + 7386603 * 2 ^ 59
def prefixEnd_7386603 : Nat := 4983230072969 + 3 ^ 40 * 7386603 * 2
def baseEnd_7386603 : Nat := 3792877742942868615492137

theorem tailTrace_7386603 : CollatzResearch.WordTrace tailWord_7386603 prefixEnd_7386603 3792877742942868615492137 := by
  unfold tailWord_7386603
  simp only [CollatzResearch.WordTrace]
  refine ⟨269411544458606337201868463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179607696305737558134578975 269411544458606337201868463)
  ·
    refine ⟨404117316687909505802802695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269411544458606337201868463 404117316687909505802802695)
    ·
      refine ⟨606175975031864258704204043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404117316687909505802802695 606175975031864258704204043)
      ·
        refine ⟨909263962547796388056306065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606175975031864258704204043 909263962547796388056306065)
        ·
          refine ⟨681947971910847291042229549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 909263962547796388056306065 681947971910847291042229549)
          ·
            refine ⟨255730489466567734140836081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 681947971910847291042229549 255730489466567734140836081)
            ·
              refine ⟨191797867099925800605627061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255730489466567734140836081 191797867099925800605627061)
              ·
                refine ⟨17981050040618043806777537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191797867099925800605627061 17981050040618043806777537)
                ·
                  refine ⟨13485787530463532855083153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17981050040618043806777537 13485787530463532855083153)
                  ·
                    refine ⟨10114340647847649641312365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13485787530463532855083153 10114340647847649641312365)
                    ·
                      refine ⟨3792877742942868615492137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10114340647847649641312365 3792877742942868615492137)
                      ·
                        rfl

theorem cell23_7386603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 3].length) (baseStart_7386603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386603 prefixEnd_7386603 := by exact prefixLift 7386603
  have htrace : WordTrace (prefixWord ++ tailWord_7386603) baseStart_7386603 baseEnd_7386603 := by
    simpa [prefixWord, tailWord_7386603, baseEnd_7386603] using wordTrace_append hprefix tailTrace_7386603
  have hstable : (prefixWord ++ tailWord_7386603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386603).length < 2 ^ (prefixWord ++ tailWord_7386603).sum := by decide
  have hdescent : baseEnd_7386603 < baseStart_7386603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386673 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 5, 1, 4]
def baseStart_7386673 : Nat := 118140960795 + 7386673 * 2 ^ 59
def prefixEnd_7386673 : Nat := 4983230072969 + 3 ^ 40 * 7386673 * 2
def baseEnd_7386673 : Nat := 3792913686588683341616815

theorem tailTrace_7386673 : CollatzResearch.WordTrace tailWord_7386673 prefixEnd_7386673 3792913686588683341616815 := by
  unfold tailWord_7386673
  simp only [CollatzResearch.WordTrace]
  refine ⟨269414097568352739156916673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179609398378901826104611115 269414097568352739156916673)
  ·
    refine ⟨202060573176264554367687505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269414097568352739156916673 202060573176264554367687505)
    ·
      refine ⟨151545429882198415775765629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202060573176264554367687505 151545429882198415775765629)
      ·
        refine ⟨56829536205824405915912111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151545429882198415775765629 56829536205824405915912111)
        ·
          refine ⟨85244304308736608873868167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56829536205824405915912111 85244304308736608873868167)
          ·
            refine ⟨127866456463104913310802251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85244304308736608873868167 127866456463104913310802251)
            ·
              refine ⟨191799684694657369966203377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127866456463104913310802251 191799684694657369966203377)
              ·
                refine ⟨143849763520993027474652533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191799684694657369966203377 143849763520993027474652533)
                ·
                  refine ⟨13485915330093096325748675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143849763520993027474652533 13485915330093096325748675)
                  ·
                    refine ⟨20228872995139644488623013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13485915330093096325748675 20228872995139644488623013)
                    ·
                      refine ⟨3792913686588683341616815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20228872995139644488623013 3792913686588683341616815)
                      ·
                        rfl

theorem cell23_7386673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_7386673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386673 prefixEnd_7386673 := by exact prefixLift 7386673
  have htrace : WordTrace (prefixWord ++ tailWord_7386673) baseStart_7386673 baseEnd_7386673 := by
    simpa [prefixWord, tailWord_7386673, baseEnd_7386673] using wordTrace_append hprefix tailTrace_7386673
  have hstable : (prefixWord ++ tailWord_7386673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386673).length < 2 ^ (prefixWord ++ tailWord_7386673).sum := by decide
  have hdescent : baseEnd_7386673 < baseStart_7386673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386677 : List Nat := [1, 3, 3, 1, 1, 4, 1, 2, 2, 3, 2]
def baseStart_7386677 : Nat := 118140960795 + 7386677 * 2 ^ 59
def prefixEnd_7386677 : Nat := 4983230072969 + 3 ^ 40 * 7386677 * 2
def baseEnd_7386677 : Nat := 3792915740511301325966797

theorem tailTrace_7386677 : CollatzResearch.WordTrace tailWord_7386677 prefixEnd_7386677 3792915740511301325966797 := by
  unfold tailWord_7386677
  simp only [CollatzResearch.WordTrace]
  refine ⟨269414243460338247840062285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179609495640225498560041523 269414243460338247840062285)
  ·
    refine ⟨101030341297626842940023357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269414243460338247840062285 101030341297626842940023357)
    ·
      refine ⟨37886377986610066102508759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101030341297626842940023357 37886377986610066102508759)
      ·
        refine ⟨56829566979915099153763139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37886377986610066102508759 56829566979915099153763139)
        ·
          refine ⟨85244350469872648730644709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56829566979915099153763139 85244350469872648730644709)
          ·
            refine ⟨15983315713101121636995883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85244350469872648730644709 15983315713101121636995883)
            ·
              refine ⟨23974973569651682455493825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15983315713101121636995883 23974973569651682455493825)
              ·
                refine ⟨17981230177238761841620369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23974973569651682455493825 17981230177238761841620369)
                ·
                  refine ⟨13485922632929071381215277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17981230177238761841620369 13485922632929071381215277)
                  ·
                    refine ⟨5057220987348401767955729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13485922632929071381215277 5057220987348401767955729)
                    ·
                      refine ⟨3792915740511301325966797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5057220987348401767955729 3792915740511301325966797)
                      ·
                        rfl

theorem cell23_7386677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_7386677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386677 prefixEnd_7386677 := by exact prefixLift 7386677
  have htrace : WordTrace (prefixWord ++ tailWord_7386677) baseStart_7386677 baseEnd_7386677 := by
    simpa [prefixWord, tailWord_7386677, baseEnd_7386677] using wordTrace_append hprefix tailTrace_7386677
  have hstable : (prefixWord ++ tailWord_7386677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386677).length < 2 ^ (prefixWord ++ tailWord_7386677).sum := by decide
  have hdescent : baseEnd_7386677 < baseStart_7386677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386684 : List Nat := [2, 2, 2, 2, 4, 2, 1, 1, 3, 1, 3]
def baseStart_7386684 : Nat := 118140960795 + 7386684 * 2 ^ 59
def prefixEnd_7386684 : Nat := 4983230072969 + 3 ^ 40 * 7386684 * 2
def baseEnd_7386684 : Nat := 3792919334875882798579265

theorem tailTrace_7386684 : CollatzResearch.WordTrace tailWord_7386684 prefixEnd_7386684 3792919334875882798579265 := by
  unfold tailWord_7386684
  simp only [CollatzResearch.WordTrace]
  refine ⟨134707249385656444017783553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179609665847541925357044737 134707249385656444017783553)
  ·
    refine ⟨101030437039242333013337665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134707249385656444017783553 101030437039242333013337665)
    ·
      refine ⟨75772827779431749760003249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101030437039242333013337665 75772827779431749760003249)
      ·
        refine ⟨56829620834573812320002437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75772827779431749760003249 56829620834573812320002437)
        ·
          refine ⟨10655553906482589810000457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56829620834573812320002437 10655553906482589810000457)
          ·
            refine ⟨7991665429861942357500343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10655553906482589810000457 7991665429861942357500343)
            ·
              refine ⟨11987498144792913536250515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7991665429861942357500343 11987498144792913536250515)
              ·
                refine ⟨17981247217189370304375773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11987498144792913536250515 17981247217189370304375773)
                ·
                  refine ⟨6742967706446013864140915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17981247217189370304375773 6742967706446013864140915)
                  ·
                    refine ⟨10114451559669020796211373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6742967706446013864140915 10114451559669020796211373)
                    ·
                      refine ⟨3792919334875882798579265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10114451559669020796211373 3792919334875882798579265)
                      ·
                        rfl

theorem cell23_7386684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_7386684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386684 prefixEnd_7386684 := by exact prefixLift 7386684
  have htrace : WordTrace (prefixWord ++ tailWord_7386684) baseStart_7386684 baseEnd_7386684 := by
    simpa [prefixWord, tailWord_7386684, baseEnd_7386684] using wordTrace_append hprefix tailTrace_7386684
  have hstable : (prefixWord ++ tailWord_7386684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386684).length < 2 ^ (prefixWord ++ tailWord_7386684).sum := by decide
  have hdescent : baseEnd_7386684 < baseStart_7386684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386693 : List Nat := [1, 3, 1, 1, 1, 4, 1, 4, 1, 1, 5]
def baseStart_7386693 : Nat := 118140960795 + 7386693 * 2 ^ 59
def prefixEnd_7386693 : Nat := 4983230072969 + 3 ^ 40 * 7386693 * 2
def baseEnd_7386693 : Nat := 3792923956201773263366723

theorem tailTrace_7386693 : CollatzResearch.WordTrace tailWord_7386693 prefixEnd_7386693 3792923956201773263366723 := by
  unfold tailWord_7386693
  simp only [CollatzResearch.WordTrace]
  refine ⟨269414827028280282572644733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179609884685520188381763155 269414827028280282572644733)
  ·
    refine ⟨101030560135605105964741775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269414827028280282572644733 101030560135605105964741775)
    ·
      refine ⟨151545840203407658947112663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101030560135605105964741775 151545840203407658947112663)
      ·
        refine ⟨227318760305111488420668995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151545840203407658947112663 227318760305111488420668995)
        ·
          refine ⟨340978140457667232631003493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227318760305111488420668995 340978140457667232631003493)
          ·
            refine ⟨63933401335812606118313155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340978140457667232631003493 63933401335812606118313155)
            ·
              refine ⟨95900102003718909177469733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63933401335812606118313155 95900102003718909177469733)
              ·
                refine ⟨17981269125697295470775575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95900102003718909177469733 17981269125697295470775575)
                ·
                  refine ⟨26971903688545943206163363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17981269125697295470775575 26971903688545943206163363)
                  ·
                    refine ⟨40457855532818914809245045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26971903688545943206163363 40457855532818914809245045)
                    ·
                      refine ⟨3792923956201773263366723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40457855532818914809245045 3792923956201773263366723)
                      ·
                        rfl

theorem cell23_7386693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_7386693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386693 prefixEnd_7386693 := by exact prefixLift 7386693
  have htrace : WordTrace (prefixWord ++ tailWord_7386693) baseStart_7386693 baseEnd_7386693 := by
    simpa [prefixWord, tailWord_7386693, baseEnd_7386693] using wordTrace_append hprefix tailTrace_7386693
  have hstable : (prefixWord ++ tailWord_7386693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386693).length < 2 ^ (prefixWord ++ tailWord_7386693).sum := by decide
  have hdescent : baseEnd_7386693 < baseStart_7386693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386703 : List Nat := [1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 4]
def baseStart_7386703 : Nat := 118140960795 + 7386703 * 2 ^ 59
def prefixEnd_7386703 : Nat := 4983230072969 + 3 ^ 40 * 7386703 * 2
def baseEnd_7386703 : Nat := 3792929091008318224241677

theorem tailTrace_7386703 : CollatzResearch.WordTrace tailWord_7386703 prefixEnd_7386703 3792929091008318224241677 := by
  unfold tailWord_7386703
  simp only [CollatzResearch.WordTrace]
  refine ⟨269415191758244054280508763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179610127838829369520339175 269415191758244054280508763)
  ·
    refine ⟨404122787637366081420763145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269415191758244054280508763 404122787637366081420763145)
    ·
      refine ⟨303092090728024561065572359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404122787637366081420763145 303092090728024561065572359)
      ·
        refine ⟨454638136092036841598358539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303092090728024561065572359 454638136092036841598358539)
        ·
          refine ⟨681957204138055262397537809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454638136092036841598358539 681957204138055262397537809)
          ·
            refine ⟨511467903103541446798153357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 681957204138055262397537809 511467903103541446798153357)
            ·
              refine ⟨191800463663828042549307509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 511467903103541446798153357 191800463663828042549307509)
              ·
                refine ⟨17981293468483878988997579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191800463663828042549307509 17981293468483878988997579)
                ·
                  refine ⟨26971940202725818483496369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17981293468483878988997579 26971940202725818483496369)
                  ·
                    refine ⟨20228955152044363862622277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26971940202725818483496369 20228955152044363862622277)
                    ·
                      refine ⟨3792929091008318224241677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20228955152044363862622277 3792929091008318224241677)
                      ·
                        rfl

theorem cell23_7386703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 4].length) (baseStart_7386703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386703 prefixEnd_7386703 := by exact prefixLift 7386703
  have htrace : WordTrace (prefixWord ++ tailWord_7386703) baseStart_7386703 baseEnd_7386703 := by
    simpa [prefixWord, tailWord_7386703, baseEnd_7386703] using wordTrace_append hprefix tailTrace_7386703
  have hstable : (prefixWord ++ tailWord_7386703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386703).length < 2 ^ (prefixWord ++ tailWord_7386703).sum := by decide
  have hdescent : baseEnd_7386703 < baseStart_7386703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386734 : List Nat := [4, 1, 2, 2, 3, 1, 2, 2, 2, 4]
def baseStart_7386734 : Nat := 118140960795 + 7386734 * 2 ^ 59
def prefixEnd_7386734 : Nat := 4983230072969 + 3 ^ 40 * 7386734 * 2
def baseEnd_7386734 : Nat := 1264315002969535867651345

theorem tailTrace_7386734 : CollatzResearch.WordTrace tailWord_7386734 prefixEnd_7386734 1264315002969535867651345 := by
  unfold tailWord_7386734
  simp only [CollatzResearch.WordTrace]
  refine ⟨33677040302641468321860907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179610881614087831049924837 33677040302641468321860907)
  ·
    refine ⟨50515560453962202482791361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33677040302641468321860907 50515560453962202482791361)
    ·
      refine ⟨37886670340471651862093521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50515560453962202482791361 37886670340471651862093521)
      ·
        refine ⟨28415002755353738896570141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37886670340471651862093521 28415002755353738896570141)
        ·
          refine ⟨10655626033257652086213803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28415002755353738896570141 10655626033257652086213803)
          ·
            refine ⟨15983439049886478129320705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10655626033257652086213803 15983439049886478129320705)
            ·
              refine ⟨11987579287414858596990529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15983439049886478129320705 11987579287414858596990529)
              ·
                refine ⟨8990684465561143947742897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11987579287414858596990529 8990684465561143947742897)
                ·
                  refine ⟨6743013349170857960807173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8990684465561143947742897 6743013349170857960807173)
                  ·
                    refine ⟨1264315002969535867651345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6743013349170857960807173 1264315002969535867651345)
                    ·
                      rfl

theorem cell23_7386734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_7386734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386734 prefixEnd_7386734 := by exact prefixLift 7386734
  have htrace : WordTrace (prefixWord ++ tailWord_7386734) baseStart_7386734 baseEnd_7386734 := by
    simpa [prefixWord, tailWord_7386734, baseEnd_7386734] using wordTrace_append hprefix tailTrace_7386734
  have hstable : (prefixWord ++ tailWord_7386734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386734).length < 2 ^ (prefixWord ++ tailWord_7386734).sum := by decide
  have hdescent : baseEnd_7386734 < baseStart_7386734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386757 : List Nat := [1, 3, 1, 1, 4, 1, 1, 5, 2, 1, 3]
def baseStart_7386757 : Nat := 118140960795 + 7386757 * 2 ^ 59
def prefixEnd_7386757 : Nat := 4983230072969 + 3 ^ 40 * 7386757 * 2
def baseEnd_7386757 : Nat := 3792956818963661012966429

theorem tailTrace_7386757 : CollatzResearch.WordTrace tailWord_7386757 prefixEnd_7386757 3792956818963661012966429 := by
  unfold tailWord_7386757
  simp only [CollatzResearch.WordTrace]
  refine ⟨269417161300048421502974525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179611440866698947668649683 269417161300048421502974525)
  ·
    refine ⟨101031435487518158063615447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269417161300048421502974525 101031435487518158063615447)
    ·
      refine ⟨151547153231277237095423171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101031435487518158063615447 151547153231277237095423171)
      ·
        refine ⟨227320729846915855643134757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151547153231277237095423171 227320729846915855643134757)
        ·
          refine ⟨42622636846296722933087767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227320729846915855643134757 42622636846296722933087767)
          ·
            refine ⟨63933955269445084399631651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42622636846296722933087767 63933955269445084399631651)
            ·
              refine ⟨95900932904167626599447477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63933955269445084399631651 95900932904167626599447477)
              ·
                refine ⟨8990712459765714993698201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95900932904167626599447477 8990712459765714993698201)
                ·
                  refine ⟨6743034344824286245273651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8990712459765714993698201 6743034344824286245273651)
                  ·
                    refine ⟨10114551517236429367910477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6743034344824286245273651 10114551517236429367910477)
                    ·
                      refine ⟨3792956818963661012966429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10114551517236429367910477 3792956818963661012966429)
                      ·
                        rfl

theorem cell23_7386757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 1, 3].length) (baseStart_7386757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386757 prefixEnd_7386757 := by exact prefixLift 7386757
  have htrace : WordTrace (prefixWord ++ tailWord_7386757) baseStart_7386757 baseEnd_7386757 := by
    simpa [prefixWord, tailWord_7386757, baseEnd_7386757] using wordTrace_append hprefix tailTrace_7386757
  have hstable : (prefixWord ++ tailWord_7386757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386757).length < 2 ^ (prefixWord ++ tailWord_7386757).sum := by decide
  have hdescent : baseEnd_7386757 < baseStart_7386757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386763 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 4]
def baseStart_7386763 : Nat := 118140960795 + 7386763 * 2 ^ 59
def prefixEnd_7386763 : Nat := 4983230072969 + 3 ^ 40 * 7386763 * 2
def baseEnd_7386763 : Nat := 3792959899847587989491401

theorem tailTrace_7386763 : CollatzResearch.WordTrace tailWord_7386763 prefixEnd_7386763 3792959899847587989491401 := by
  unfold tailWord_7386763
  simp only [CollatzResearch.WordTrace]
  refine ⟨269417380138026684527692943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179611586758684456351795295 269417380138026684527692943)
  ·
    refine ⟨404126070207040026791539415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269417380138026684527692943 404126070207040026791539415)
    ·
      refine ⟨606189105310560040187309123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404126070207040026791539415 606189105310560040187309123)
      ·
        refine ⟨909283657965840060280963685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606189105310560040187309123 909283657965840060280963685)
        ·
          refine ⟨170490685868595011302680691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 909283657965840060280963685 170490685868595011302680691)
          ·
            refine ⟨255736028802892516954021037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170490685868595011302680691 255736028802892516954021037)
            ·
              refine ⟨95901010801084693857757889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255736028802892516954021037 95901010801084693857757889)
              ·
                refine ⟨71925758100813520393318417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95901010801084693857757889 71925758100813520393318417)
                ·
                  refine ⟨53944318575610140294988813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71925758100813520393318417 53944318575610140294988813)
                  ·
                    refine ⟨20229119465853802610620805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53944318575610140294988813 20229119465853802610620805)
                    ·
                      refine ⟨3792959899847587989491401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20229119465853802610620805 3792959899847587989491401)
                      ·
                        rfl

theorem cell23_7386763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 4].length) (baseStart_7386763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386763 prefixEnd_7386763 := by exact prefixLift 7386763
  have htrace : WordTrace (prefixWord ++ tailWord_7386763) baseStart_7386763 baseEnd_7386763 := by
    simpa [prefixWord, tailWord_7386763, baseEnd_7386763] using wordTrace_append hprefix tailTrace_7386763
  have hstable : (prefixWord ++ tailWord_7386763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386763).length < 2 ^ (prefixWord ++ tailWord_7386763).sum := by decide
  have hdescent : baseEnd_7386763 < baseStart_7386763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386784 : List Nat := [2, 1, 1, 4, 3, 2, 1, 3, 1, 3, 2]
def baseStart_7386784 : Nat := 118140960795 + 7386784 * 2 ^ 59
def prefixEnd_7386784 : Nat := 4983230072969 + 3 ^ 40 * 7386784 * 2
def baseEnd_7386784 : Nat := 3792970682941332407328805

theorem tailTrace_7386784 : CollatzResearch.WordTrace tailWord_7386784 prefixEnd_7386784 3792970682941332407328805 := by
  unfold tailWord_7386784
  simp only [CollatzResearch.WordTrace]
  refine ⟨134709073035475302557103703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179612097380633736742804937 134709073035475302557103703)
  ·
    refine ⟨202063609553212953835655555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134709073035475302557103703 202063609553212953835655555)
    ·
      refine ⟨303095414329819430753483333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202063609553212953835655555 303095414329819430753483333)
      ·
        refine ⟨56830390186841143266278125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303095414329819430753483333 56830390186841143266278125)
        ·
          refine ⟨21311396320065428724854297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56830390186841143266278125 21311396320065428724854297)
          ·
            refine ⟨15983547240049071543640723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21311396320065428724854297 15983547240049071543640723)
            ·
              refine ⟨23975320860073607315461085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15983547240049071543640723 23975320860073607315461085)
              ·
                refine ⟨8990745322527602743297907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23975320860073607315461085 8990745322527602743297907)
                ·
                  refine ⟨13486117983791404114946861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8990745322527602743297907 13486117983791404114946861)
                  ·
                    refine ⟨5057294243921776543105073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13486117983791404114946861 5057294243921776543105073)
                    ·
                      refine ⟨3792970682941332407328805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5057294243921776543105073 3792970682941332407328805)
                      ·
                        rfl

theorem cell23_7386784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_7386784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386784 prefixEnd_7386784 := by exact prefixLift 7386784
  have htrace : WordTrace (prefixWord ++ tailWord_7386784) baseStart_7386784 baseEnd_7386784 := by
    simpa [prefixWord, tailWord_7386784, baseEnd_7386784] using wordTrace_append hprefix tailTrace_7386784
  have hstable : (prefixWord ++ tailWord_7386784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386784).length < 2 ^ (prefixWord ++ tailWord_7386784).sum := by decide
  have hdescent : baseEnd_7386784 < baseStart_7386784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386810 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4]
def baseStart_7386810 : Nat := 118140960795 + 7386810 * 2 ^ 59
def prefixEnd_7386810 : Nat := 4983230072969 + 3 ^ 40 * 7386810 * 2
def baseEnd_7386810 : Nat := 3792984033438349305603685

theorem tailTrace_7386810 : CollatzResearch.WordTrace tailWord_7386810 prefixEnd_7386810 3792984033438349305603685 := by
  unfold tailWord_7386810
  simp only [CollatzResearch.WordTrace]
  refine ⟨67354773592214102888663471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179612729579237607703102589 67354773592214102888663471)
  ·
    refine ⟨101032160388321154332995207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67354773592214102888663471 101032160388321154332995207)
    ·
      refine ⟨151548240582481731499492811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101032160388321154332995207 151548240582481731499492811)
      ·
        refine ⟨227322360873722597249239217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151548240582481731499492811 227322360873722597249239217)
        ·
          refine ⟨170491770655291947936929413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227322360873722597249239217 170491770655291947936929413)
          ·
            refine ⟨31967206997867240238174265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170491770655291947936929413 31967206997867240238174265)
            ·
              refine ⟨23975405248400430178630699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31967206997867240238174265 23975405248400430178630699)
              ·
                refine ⟨35963107872600645267946049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23975405248400430178630699 35963107872600645267946049)
                ·
                  refine ⟨26972330904450483950959537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35963107872600645267946049 26972330904450483950959537)
                  ·
                    refine ⟨20229248178337862963219653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26972330904450483950959537 20229248178337862963219653)
                    ·
                      refine ⟨3792984033438349305603685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20229248178337862963219653 3792984033438349305603685)
                      ·
                        rfl

theorem cell23_7386810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_7386810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386810 prefixEnd_7386810 := by exact prefixLift 7386810
  have htrace : WordTrace (prefixWord ++ tailWord_7386810) baseStart_7386810 baseEnd_7386810 := by
    simpa [prefixWord, tailWord_7386810, baseEnd_7386810] using wordTrace_append hprefix tailTrace_7386810
  have hstable : (prefixWord ++ tailWord_7386810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386810).length < 2 ^ (prefixWord ++ tailWord_7386810).sum := by decide
  have hdescent : baseEnd_7386810 < baseStart_7386810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386814 : List Nat := [4, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2]
def baseStart_7386814 : Nat := 118140960795 + 7386814 * 2 ^ 59
def prefixEnd_7386814 : Nat := 4983230072969 + 3 ^ 40 * 7386814 * 2
def baseEnd_7386814 : Nat := 3792986087360967289953667

theorem tailTrace_7386814 : CollatzResearch.WordTrace tailWord_7386814 prefixEnd_7386814 3792986087360967289953667 := by
  unfold tailWord_7386814
  simp only [CollatzResearch.WordTrace]
  refine ⟨33677405032605240029724937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179612826840561280158532997 33677405032605240029724937)
  ·
    refine ⟨25258053774453930022293703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33677405032605240029724937 25258053774453930022293703)
    ·
      refine ⟨37887080661680895033440555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25258053774453930022293703 37887080661680895033440555)
      ·
        refine ⟨56830620992521342550160833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37887080661680895033440555 56830620992521342550160833)
        ·
          refine ⟨42622965744391006912620625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56830620992521342550160833 42622965744391006912620625)
          ·
            refine ⟨31967224308293255184465469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42622965744391006912620625 31967224308293255184465469)
            ·
              refine ⟨11987709115609970694174551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31967224308293255184465469 11987709115609970694174551)
              ·
                refine ⟨17981563673414956041261827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11987709115609970694174551 17981563673414956041261827)
                ·
                  refine ⟨26972345510122434061892741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17981563673414956041261827 26972345510122434061892741)
                  ·
                    refine ⟨5057314783147956386604889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26972345510122434061892741 5057314783147956386604889)
                    ·
                      refine ⟨3792986087360967289953667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5057314783147956386604889 3792986087360967289953667)
                      ·
                        rfl

theorem cell23_7386814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_7386814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386814 prefixEnd_7386814 := by exact prefixLift 7386814
  have htrace : WordTrace (prefixWord ++ tailWord_7386814) baseStart_7386814 baseEnd_7386814 := by
    simpa [prefixWord, tailWord_7386814, baseEnd_7386814] using wordTrace_append hprefix tailTrace_7386814
  have hstable : (prefixWord ++ tailWord_7386814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386814).length < 2 ^ (prefixWord ++ tailWord_7386814).sum := by decide
  have hdescent : baseEnd_7386814 < baseStart_7386814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386820 : List Nat := [2, 3, 3, 1, 1, 1, 1, 4, 7]
def baseStart_7386820 : Nat := 118140960795 + 7386820 * 2 ^ 59
def prefixEnd_7386820 : Nat := 4983230072969 + 3 ^ 40 * 7386820 * 2
def baseEnd_7386820 : Nat := 421443240916099362942071

theorem tailTrace_7386820 : CollatzResearch.WordTrace tailWord_7386820 prefixEnd_7386820 421443240916099362942071 := by
  unfold tailWord_7386820
  simp only [CollatzResearch.WordTrace]
  refine ⟨134709729549410091631258957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179612972732546788841678609 134709729549410091631258957)
  ·
    refine ⟨50516148581028784361722109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134709729549410091631258957 50516148581028784361722109)
    ·
      refine ⟨18943555717885794135645791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50516148581028784361722109 18943555717885794135645791)
      ·
        refine ⟨28415333576828691203468687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18943555717885794135645791 28415333576828691203468687)
        ·
          refine ⟨42623000365243036805203031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28415333576828691203468687 42623000365243036805203031)
          ·
            refine ⟨63934500547864555207804547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42623000365243036805203031 63934500547864555207804547)
            ·
              refine ⟨95901750821796832811706821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63934500547864555207804547 95901750821796832811706821)
              ·
                refine ⟨17981578279086906152195029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95901750821796832811706821 17981578279086906152195029)
                ·
                  refine ⟨421443240916099362942071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17981578279086906152195029 421443240916099362942071)
                  ·
                    rfl

theorem cell23_7386820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_7386820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386820 prefixEnd_7386820 := by exact prefixLift 7386820
  have htrace : WordTrace (prefixWord ++ tailWord_7386820) baseStart_7386820 baseEnd_7386820 := by
    simpa [prefixWord, tailWord_7386820, baseEnd_7386820] using wordTrace_append hprefix tailTrace_7386820
  have hstable : (prefixWord ++ tailWord_7386820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386820).length < 2 ^ (prefixWord ++ tailWord_7386820).sum := by decide
  have hdescent : baseEnd_7386820 < baseStart_7386820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386941 : List Nat := [1, 4, 1, 4, 1, 3, 1, 1, 2, 2, 3]
def baseStart_7386941 : Nat := 118140960795 + 7386941 * 2 ^ 59
def prefixEnd_7386941 : Nat := 4983230072969 + 3 ^ 40 * 7386941 * 2
def baseEnd_7386941 : Nat := 3793051299404088293065583

theorem tailTrace_7386941 : CollatzResearch.WordTrace tailWord_7386941 prefixEnd_7386941 3793051299404088293065583 := by
  unfold tailWord_7386941
  simp only [CollatzResearch.WordTrace]
  refine ⟨269423872331381820927672677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179615914887587880618448451 269423872331381820927672677)
  ·
    refine ⟨50516976062134091423938627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269423872331381820927672677 50516976062134091423938627)
    ·
      refine ⟨75775464093201137135907941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50516976062134091423938627 75775464093201137135907941)
      ·
        refine ⟨14207899517475213212982739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75775464093201137135907941 14207899517475213212982739)
        ·
          refine ⟨21311849276212819819474109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14207899517475213212982739 21311849276212819819474109)
          ·
            refine ⟨7991943478579807432302791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21311849276212819819474109 7991943478579807432302791)
            ·
              refine ⟨11987915217869711148454187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7991943478579807432302791 11987915217869711148454187)
              ·
                refine ⟨17981872826804566722681281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11987915217869711148454187 17981872826804566722681281)
                ·
                  refine ⟨13486404620103425042010961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17981872826804566722681281 13486404620103425042010961)
                  ·
                    refine ⟨10114803465077568781508221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13486404620103425042010961 10114803465077568781508221)
                    ·
                      refine ⟨3793051299404088293065583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10114803465077568781508221 3793051299404088293065583)
                      ·
                        rfl

theorem cell23_7386941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_7386941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386941 prefixEnd_7386941 := by exact prefixLift 7386941
  have htrace : WordTrace (prefixWord ++ tailWord_7386941) baseStart_7386941 baseEnd_7386941 := by
    simpa [prefixWord, tailWord_7386941, baseEnd_7386941] using wordTrace_append hprefix tailTrace_7386941
  have hstable : (prefixWord ++ tailWord_7386941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386941).length < 2 ^ (prefixWord ++ tailWord_7386941).sum := by decide
  have hdescent : baseEnd_7386941 < baseStart_7386941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7386997 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_7386997 : Nat := 118140960795 + 7386997 * 2 ^ 59
def prefixEnd_7386997 : Nat := 4983230072969 + 3 ^ 40 * 7386997 * 2
def baseEnd_7386997 : Nat := 3793080054320740073965325

theorem tailTrace_7386997 : CollatzResearch.WordTrace tailWord_7386997 prefixEnd_7386997 3793080054320740073965325 := by
  unfold tailWord_7386997
  simp only [CollatzResearch.WordTrace]
  refine ⟨269425914819178942491711245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179617276546119294994474163 269425914819178942491711245)
  ·
    refine ⟨101034718057192103434391717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269425914819178942491711245 101034718057192103434391717)
    ·
      refine ⟨18944009635723519393948447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101034718057192103434391717 18944009635723519393948447)
      ·
        refine ⟨28416014453585279090922671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18944009635723519393948447 28416014453585279090922671)
        ·
          refine ⟨42624021680377918636384007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28416014453585279090922671 42624021680377918636384007)
          ·
            refine ⟨63936032520566877954576011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42624021680377918636384007 63936032520566877954576011)
            ·
              refine ⟨95904048780850316931864017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63936032520566877954576011 95904048780850316931864017)
              ·
                refine ⟨71928036585637737698898013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95904048780850316931864017 71928036585637737698898013)
                ·
                  refine ⟨26973013719614151637086755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71928036585637737698898013 26973013719614151637086755)
                  ·
                    refine ⟨40459520579421227455630133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26973013719614151637086755 40459520579421227455630133)
                    ·
                      refine ⟨3793080054320740073965325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40459520579421227455630133 3793080054320740073965325)
                      ·
                        rfl

theorem cell23_7386997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_7386997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7386997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7386997 prefixEnd_7386997 := by exact prefixLift 7386997
  have htrace : WordTrace (prefixWord ++ tailWord_7386997) baseStart_7386997 baseEnd_7386997 := by
    simpa [prefixWord, tailWord_7386997, baseEnd_7386997] using wordTrace_append hprefix tailTrace_7386997
  have hstable : (prefixWord ++ tailWord_7386997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7386997).length < 2 ^ (prefixWord ++ tailWord_7386997).sum := by decide
  have hdescent : baseEnd_7386997 < baseStart_7386997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7386997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387022 : List Nat := [4, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3]
def baseStart_7387022 : Nat := 118140960795 + 7387022 * 2 ^ 59
def prefixEnd_7387022 : Nat := 4983230072969 + 3 ^ 40 * 7387022 * 2
def baseEnd_7387022 : Nat := 3793092891337102476152711

theorem tailTrace_7387022 : CollatzResearch.WordTrace tailWord_7387022 prefixEnd_7387022 3793092891337102476152711 := by
  unfold tailWord_7387022
  simp only [CollatzResearch.WordTrace]
  refine ⟨33678353330511046470171415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179617884429392247840914213 33678353330511046470171415)
  ·
    refine ⟨50517529995766569705257123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33678353330511046470171415 50517529995766569705257123)
    ·
      refine ⟨75776294993649854557885685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50517529995766569705257123 75776294993649854557885685)
      ·
        refine ⟨7104027655654673864801783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75776294993649854557885685 7104027655654673864801783)
        ·
          refine ⟨10656041483482010797202675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7104027655654673864801783 10656041483482010797202675)
          ·
            refine ⟨15984062225223016195804013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10656041483482010797202675 15984062225223016195804013)
            ·
              refine ⟨5994023334458631073426505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15984062225223016195804013 5994023334458631073426505)
              ·
                refine ⟨4495517500843973305069879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5994023334458631073426505 4495517500843973305069879)
                ·
                  refine ⟨6743276251265959957604819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4495517500843973305069879 6743276251265959957604819)
                  ·
                    refine ⟨10114914376898939936407229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6743276251265959957604819 10114914376898939936407229)
                    ·
                      refine ⟨3793092891337102476152711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10114914376898939936407229 3793092891337102476152711)
                      ·
                        rfl

theorem cell23_7387022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_7387022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387022 prefixEnd_7387022 := by exact prefixLift 7387022
  have htrace : WordTrace (prefixWord ++ tailWord_7387022) baseStart_7387022 baseEnd_7387022 := by
    simpa [prefixWord, tailWord_7387022, baseEnd_7387022] using wordTrace_append hprefix tailTrace_7387022
  have hstable : (prefixWord ++ tailWord_7387022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387022).length < 2 ^ (prefixWord ++ tailWord_7387022).sum := by decide
  have hdescent : baseEnd_7387022 < baseStart_7387022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387028 : List Nat := [2, 4, 2, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_7387028 : Nat := 118140960795 + 7387028 * 2 ^ 59
def prefixEnd_7387028 : Nat := 4983230072969 + 3 ^ 40 * 7387028 * 2
def baseEnd_7387028 : Nat := 3793095972221029452677683

theorem tailTrace_7387028 : CollatzResearch.WordTrace tailWord_7387028 prefixEnd_7387028 3793095972221029452677683 := by
  unfold tailWord_7387028
  simp only [CollatzResearch.WordTrace]
  refine ⟨134713522741033317393044869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179618030321377756524059825 134713522741033317393044869)
  ·
    refine ⟨25258785513943747011195913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134713522741033317393044869 25258785513943747011195913)
    ·
      refine ⟨18944089135457810258396935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25258785513943747011195913 18944089135457810258396935)
      ·
        refine ⟨28416133703186715387595403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18944089135457810258396935 28416133703186715387595403)
        ·
          refine ⟨42624200554780073081393105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28416133703186715387595403 42624200554780073081393105)
          ·
            refine ⟨31968150416085054811044829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42624200554780073081393105 31968150416085054811044829)
            ·
              refine ⟨11988056406031895554141811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31968150416085054811044829 11988056406031895554141811)
              ·
                refine ⟨17982084609047843331212717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11988056406031895554141811 17982084609047843331212717)
                ·
                  refine ⟨6743281728392941249204769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17982084609047843331212717 6743281728392941249204769)
                  ·
                    refine ⟨5057461296294705936903577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6743281728392941249204769 5057461296294705936903577)
                    ·
                      refine ⟨3793095972221029452677683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5057461296294705936903577 3793095972221029452677683)
                      ·
                        rfl

theorem cell23_7387028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_7387028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387028 prefixEnd_7387028 := by exact prefixLift 7387028
  have htrace : WordTrace (prefixWord ++ tailWord_7387028) baseStart_7387028 baseEnd_7387028 := by
    simpa [prefixWord, tailWord_7387028, baseEnd_7387028] using wordTrace_append hprefix tailTrace_7387028
  have hstable : (prefixWord ++ tailWord_7387028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387028).length < 2 ^ (prefixWord ++ tailWord_7387028).sum := by decide
  have hdescent : baseEnd_7387028 < baseStart_7387028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387048 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_7387048 : Nat := 118140960795 + 7387048 * 2 ^ 59
def prefixEnd_7387048 : Nat := 4983230072969 + 3 ^ 40 * 7387048 * 2
def baseEnd_7387048 : Nat := 3793106241834119374427591

theorem tailTrace_7387048 : CollatzResearch.WordTrace tailWord_7387048 prefixEnd_7387048 3793106241834119374427591 := by
  unfold tailWord_7387048
  simp only [CollatzResearch.WordTrace]
  refine ⟨134713887470997089100908899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179618516627996118801211865 134713887470997089100908899)
  ·
    refine ⟨202070831206495633651363349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134713887470997089100908899 202070831206495633651363349)
    ·
      refine ⟨9472070212804482827407657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 202070831206495633651363349 9472070212804482827407657)
      ·
        refine ⟨7104052659603362120555743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9472070212804482827407657 7104052659603362120555743)
        ·
          refine ⟨10656078989405043180833615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7104052659603362120555743 10656078989405043180833615)
          ·
            refine ⟨15984118484107564771250423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10656078989405043180833615 15984118484107564771250423)
            ·
              refine ⟨23976177726161347156875635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15984118484107564771250423 23976177726161347156875635)
              ·
                refine ⟨35964266589242020735313453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23976177726161347156875635 35964266589242020735313453)
                ·
                  refine ⟨13486599970965757775742545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35964266589242020735313453 13486599970965757775742545)
                  ·
                    refine ⟨10114949978224318331806909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13486599970965757775742545 10114949978224318331806909)
                    ·
                      refine ⟨3793106241834119374427591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10114949978224318331806909 3793106241834119374427591)
                      ·
                        rfl

theorem cell23_7387048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_7387048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387048 prefixEnd_7387048 := by exact prefixLift 7387048
  have htrace : WordTrace (prefixWord ++ tailWord_7387048) baseStart_7387048 baseEnd_7387048 := by
    simpa [prefixWord, tailWord_7387048, baseEnd_7387048] using wordTrace_append hprefix tailTrace_7387048
  have hstable : (prefixWord ++ tailWord_7387048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387048).length < 2 ^ (prefixWord ++ tailWord_7387048).sum := by decide
  have hdescent : baseEnd_7387048 < baseStart_7387048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387087 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 3]
def baseStart_7387087 : Nat := 118140960795 + 7387087 * 2 ^ 59
def prefixEnd_7387087 : Nat := 4983230072969 + 3 ^ 40 * 7387087 * 2
def baseEnd_7387087 : Nat := 3793126267579644721839911

theorem tailTrace_7387087 : CollatzResearch.WordTrace tailWord_7387087 prefixEnd_7387087 3793126267579644721839911 := by
  unfold tailWord_7387087
  simp only [CollatzResearch.WordTrace]
  refine ⟨269429197388852887862487515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179619464925901925241658343 269429197388852887862487515)
  ·
    refine ⟨404143796083279331793731273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269429197388852887862487515 404143796083279331793731273)
    ·
      refine ⟨303107847062459498845298455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404143796083279331793731273 303107847062459498845298455)
      ·
        refine ⟨454661770593689248267947683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303107847062459498845298455 454661770593689248267947683)
        ·
          refine ⟨681992655890533872401921525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454661770593689248267947683 681992655890533872401921525)
          ·
            refine ⟨63936811489737550537680143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 681992655890533872401921525 63936811489737550537680143)
            ·
              refine ⟨95905217234606325806520215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63936811489737550537680143 95905217234606325806520215)
              ·
                refine ⟨143857825851909488709780323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95905217234606325806520215 143857825851909488709780323)
                ·
                  refine ⟨215786738777864233064670485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143857825851909488709780323 215786738777864233064670485)
                  ·
                    refine ⟨10115003380212385924906429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 215786738777864233064670485 10115003380212385924906429)
                    ·
                      refine ⟨3793126267579644721839911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10115003380212385924906429 3793126267579644721839911)
                      ·
                        rfl

theorem cell23_7387087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 3].length) (baseStart_7387087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387087 prefixEnd_7387087 := by exact prefixLift 7387087
  have htrace : WordTrace (prefixWord ++ tailWord_7387087) baseStart_7387087 baseEnd_7387087 := by
    simpa [prefixWord, tailWord_7387087, baseEnd_7387087] using wordTrace_append hprefix tailTrace_7387087
  have hstable : (prefixWord ++ tailWord_7387087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387087).length < 2 ^ (prefixWord ++ tailWord_7387087).sum := by decide
  have hdescent : baseEnd_7387087 < baseStart_7387087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387107 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 9]
def baseStart_7387107 : Nat := 118140960795 + 7387107 * 2 ^ 59
def prefixEnd_7387107 : Nat := 4983230072969 + 3 ^ 40 * 7387107 * 2
def baseEnd_7387107 : Nat := 421459615243637182621091

theorem tailTrace_7387107 : CollatzResearch.WordTrace tailWord_7387107 prefixEnd_7387107 421459615243637182621091 := by
  unfold tailWord_7387107
  simp only [CollatzResearch.WordTrace]
  refine ⟨269429926848780431278215575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179619951232520287518810383 269429926848780431278215575)
  ·
    refine ⟨404144890273170646917323363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269429926848780431278215575 404144890273170646917323363)
    ·
      refine ⟨606217335409755970375985045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404144890273170646917323363 606217335409755970375985045)
      ·
        refine ⟨28416437597332311111374299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 606217335409755970375985045 28416437597332311111374299)
        ·
          refine ⟨42624656395998466667061449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28416437597332311111374299 42624656395998466667061449)
          ·
            refine ⟨31968492296998850000296087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42624656395998466667061449 31968492296998850000296087)
            ·
              refine ⟨47952738445498275000444131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31968492296998850000296087 47952738445498275000444131)
              ·
                refine ⟨71929107668247412500666197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47952738445498275000444131 71929107668247412500666197)
                ·
                  refine ⟨421459615243637182621091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71929107668247412500666197 421459615243637182621091)
                  ·
                    rfl

theorem cell23_7387107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 9].length) (baseStart_7387107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387107 prefixEnd_7387107 := by exact prefixLift 7387107
  have htrace : WordTrace (prefixWord ++ tailWord_7387107) baseStart_7387107 baseEnd_7387107 := by
    simpa [prefixWord, tailWord_7387107, baseEnd_7387107] using wordTrace_append hprefix tailTrace_7387107
  have hstable : (prefixWord ++ tailWord_7387107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387107).length < 2 ^ (prefixWord ++ tailWord_7387107).sum := by decide
  have hdescent : baseEnd_7387107 < baseStart_7387107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387147 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 7]
def baseStart_7387147 : Nat := 118140960795 + 7387147 * 2 ^ 59
def prefixEnd_7387147 : Nat := 4983230072969 + 3 ^ 40 * 7387147 * 2
def baseEnd_7387147 : Nat := 3793157076418914487089635

theorem tailTrace_7387147 : CollatzResearch.WordTrace tailWord_7387147 prefixEnd_7387147 3793157076418914487089635 := by
  unfold tailWord_7387147
  simp only [CollatzResearch.WordTrace]
  refine ⟨269431385768635518109671695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179620923845757012073114463 269431385768635518109671695)
  ·
    refine ⟨404147078652953277164507543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269431385768635518109671695 404147078652953277164507543)
    ·
      refine ⟨606220617979429915746761315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404147078652953277164507543 606220617979429915746761315)
      ·
        refine ⟨909330926969144873620141973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606220617979429915746761315 909330926969144873620141973)
        ·
          refine ⟨42624887201678665950944155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 909330926969144873620141973 42624887201678665950944155)
          ·
            refine ⟨63937330802517998926416233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42624887201678665950944155 63937330802517998926416233)
            ·
              refine ⟨47952998101888499194812175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63937330802517998926416233 47952998101888499194812175)
              ·
                refine ⟨71929497152832748792218263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47952998101888499194812175 71929497152832748792218263)
                ·
                  refine ⟨107894245729249123188327395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71929497152832748792218263 107894245729249123188327395)
                  ·
                    refine ⟨161841368593873684782491093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107894245729249123188327395 161841368593873684782491093)
                    ·
                      refine ⟨3793157076418914487089635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161841368593873684782491093 3793157076418914487089635)
                      ·
                        rfl

theorem cell23_7387147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 7].length) (baseStart_7387147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387147 prefixEnd_7387147 := by exact prefixLift 7387147
  have htrace : WordTrace (prefixWord ++ tailWord_7387147) baseStart_7387147 baseEnd_7387147 := by
    simpa [prefixWord, tailWord_7387147, baseEnd_7387147] using wordTrace_append hprefix tailTrace_7387147
  have hstable : (prefixWord ++ tailWord_7387147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387147).length < 2 ^ (prefixWord ++ tailWord_7387147).sum := by decide
  have hdescent : baseEnd_7387147 < baseStart_7387147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387167 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 2, 8]
def baseStart_7387167 : Nat := 118140960795 + 7387167 * 2 ^ 59
def prefixEnd_7387167 : Nat := 4983230072969 + 3 ^ 40 * 7387167 * 2
def baseEnd_7387167 : Nat := 1264389115344001469613181

theorem tailTrace_7387167 : CollatzResearch.WordTrace tailWord_7387167 prefixEnd_7387167 1264389115344001469613181 := by
  unfold tailWord_7387167
  simp only [CollatzResearch.WordTrace]
  refine ⟨269432115228563061525399755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179621410152375374350266503 269432115228563061525399755)
  ·
    refine ⟨404148172842844592288099633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269432115228563061525399755 404148172842844592288099633)
    ·
      refine ⟨303111129632133444216074725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404148172842844592288099633 303111129632133444216074725)
      ·
        refine ⟨56833336806025020790514011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303111129632133444216074725 56833336806025020790514011)
        ·
          refine ⟨85250005209037531185771017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56833336806025020790514011 85250005209037531185771017)
          ·
            refine ⟨63937503906778148389328263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85250005209037531185771017 63937503906778148389328263)
            ·
              refine ⟨95906255860167222583992395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63937503906778148389328263 95906255860167222583992395)
              ·
                refine ⟨143859383790250833875988593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95906255860167222583992395 143859383790250833875988593)
                ·
                  refine ⟨107894537842688125406991445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143859383790250833875988593 107894537842688125406991445)
                  ·
                    refine ⟨1264389115344001469613181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107894537842688125406991445 1264389115344001469613181)
                    ·
                      rfl

theorem cell23_7387167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 8].length) (baseStart_7387167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387167 prefixEnd_7387167 := by exact prefixLift 7387167
  have htrace : WordTrace (prefixWord ++ tailWord_7387167) baseStart_7387167 baseEnd_7387167 := by
    simpa [prefixWord, tailWord_7387167, baseEnd_7387167] using wordTrace_append hprefix tailTrace_7387167
  have hstable : (prefixWord ++ tailWord_7387167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387167).length < 2 ^ (prefixWord ++ tailWord_7387167).sum := by decide
  have hdescent : baseEnd_7387167 < baseStart_7387167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387175 : List Nat := [1, 1, 7, 1, 2, 2, 1, 3, 5]
def baseStart_7387175 : Nat := 118140960795 + 7387175 * 2 ^ 59
def prefixEnd_7387175 : Nat := 4983230072969 + 3 ^ 40 * 7387175 * 2
def baseEnd_7387175 : Nat := 421463494875248930837723

theorem tailTrace_7387175 : CollatzResearch.WordTrace tailWord_7387175 prefixEnd_7387175 421463494875248930837723 := by
  unfold tailWord_7387175
  simp only [CollatzResearch.WordTrace]
  refine ⟨269432407012534078891690979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179621604675022719261127319 269432407012534078891690979)
  ·
    refine ⟨404148610518801118337536469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269432407012534078891690979 404148610518801118337536469)
    ·
      refine ⟨9472233059034401211036011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 404148610518801118337536469 9472233059034401211036011)
      ·
        refine ⟨14208349588551601816554017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9472233059034401211036011 14208349588551601816554017)
        ·
          refine ⟨10656262191413701362415513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14208349588551601816554017 10656262191413701362415513)
          ·
            refine ⟨7992196643560276021811635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10656262191413701362415513 7992196643560276021811635)
            ·
              refine ⟨11988294965340414032717453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7992196643560276021811635 11988294965340414032717453)
              ·
                refine ⟨4495610612002655262269045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11988294965340414032717453 4495610612002655262269045)
                ·
                  refine ⟨421463494875248930837723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4495610612002655262269045 421463494875248930837723)
                  ·
                    rfl

theorem cell23_7387175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 5].length) (baseStart_7387175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387175 prefixEnd_7387175 := by exact prefixLift 7387175
  have htrace : WordTrace (prefixWord ++ tailWord_7387175) baseStart_7387175 baseEnd_7387175 := by
    simpa [prefixWord, tailWord_7387175, baseEnd_7387175] using wordTrace_append hprefix tailTrace_7387175
  have hstable : (prefixWord ++ tailWord_7387175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387175).length < 2 ^ (prefixWord ++ tailWord_7387175).sum := by decide
  have hdescent : baseEnd_7387175 < baseStart_7387175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387187 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 6]
def baseStart_7387187 : Nat := 118140960795 + 7387187 * 2 ^ 59
def prefixEnd_7387187 : Nat := 4983230072969 + 3 ^ 40 * 7387187 * 2
def baseEnd_7387187 : Nat := 3793177615645094330589451

theorem tailTrace_7387187 : CollatzResearch.WordTrace tailWord_7387187 prefixEnd_7387187 3793177615645094330589451 := by
  unfold tailWord_7387187
  simp only [CollatzResearch.WordTrace]
  refine ⟨269432844688490604941127815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179621896458993736627418543 269432844688490604941127815)
  ·
    refine ⟨404149267032735907411691723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269432844688490604941127815 404149267032735907411691723)
    ·
      refine ⟨606223900549103861117537585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404149267032735907411691723 606223900549103861117537585)
      ·
        refine ⟨454667925411827895838153189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 606223900549103861117537585 454667925411827895838153189)
        ·
          refine ⟨85250236014717730469653723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 454667925411827895838153189 85250236014717730469653723)
          ·
            refine ⟨127875354022076595704480585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85250236014717730469653723 127875354022076595704480585)
            ·
              refine ⟨95906515516557446778360439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127875354022076595704480585 95906515516557446778360439)
              ·
                refine ⟨143859773274836170167540659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95906515516557446778360439 143859773274836170167540659)
                ·
                  refine ⟨215789659912254255251310989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143859773274836170167540659 215789659912254255251310989)
                  ·
                    refine ⟨80921122467095345719241621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 215789659912254255251310989 80921122467095345719241621)
                    ·
                      refine ⟨3793177615645094330589451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80921122467095345719241621 3793177615645094330589451)
                      ·
                        rfl

theorem cell23_7387187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_7387187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387187 prefixEnd_7387187 := by exact prefixLift 7387187
  have htrace : WordTrace (prefixWord ++ tailWord_7387187) baseStart_7387187 baseEnd_7387187 := by
    simpa [prefixWord, tailWord_7387187, baseEnd_7387187] using wordTrace_append hprefix tailTrace_7387187
  have hstable : (prefixWord ++ tailWord_7387187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387187).length < 2 ^ (prefixWord ++ tailWord_7387187).sum := by decide
  have hdescent : baseEnd_7387187 < baseStart_7387187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387188 : List Nat := [2, 5, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_7387188 : Nat := 118140960795 + 7387188 * 2 ^ 59
def prefixEnd_7387188 : Nat := 4983230072969 + 3 ^ 40 * 7387188 * 2
def baseEnd_7387188 : Nat := 1264392709708582942225649

theorem tailTrace_7387188 : CollatzResearch.WordTrace tailWord_7387188 prefixEnd_7387188 1264392709708582942225649 := by
  unfold tailWord_7387188
  simp only [CollatzResearch.WordTrace]
  refine ⟨134716440580743491055957109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179621920774324654741276145 134716440580743491055957109)
  ·
    refine ⟨12629666304444702286495979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134716440580743491055957109 12629666304444702286495979)
    ·
      refine ⟨18944499456667053429743969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12629666304444702286495979 18944499456667053429743969)
      ·
        refine ⟨14208374592500290072307977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18944499456667053429743969 14208374592500290072307977)
        ·
          refine ⟨10656280944375217554230983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14208374592500290072307977 10656280944375217554230983)
          ·
            refine ⟨15984421416562826331346475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10656280944375217554230983 15984421416562826331346475)
            ·
              refine ⟨23976632124844239497019713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15984421416562826331346475 23976632124844239497019713)
              ·
                refine ⟨17982474093633179622764785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23976632124844239497019713 17982474093633179622764785)
                ·
                  refine ⟨13486855570224884717073589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17982474093633179622764785 13486855570224884717073589)
                  ·
                    refine ⟨1264392709708582942225649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13486855570224884717073589 1264392709708582942225649)
                    ·
                      rfl

theorem cell23_7387188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_7387188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387188 prefixEnd_7387188 := by exact prefixLift 7387188
  have htrace : WordTrace (prefixWord ++ tailWord_7387188) baseStart_7387188 baseEnd_7387188 := by
    simpa [prefixWord, tailWord_7387188, baseEnd_7387188] using wordTrace_append hprefix tailTrace_7387188
  have hstable : (prefixWord ++ tailWord_7387188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387188).length < 2 ^ (prefixWord ++ tailWord_7387188).sum := by decide
  have hdescent : baseEnd_7387188 < baseStart_7387188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387228 : List Nat := [2, 2, 4, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_7387228 : Nat := 118140960795 + 7387228 * 2 ^ 59
def prefixEnd_7387228 : Nat := 4983230072969 + 3 ^ 40 * 7387228 * 2
def baseEnd_7387228 : Nat := 3793198668351928670176763

theorem tailTrace_7387228 : CollatzResearch.WordTrace tailWord_7387228 prefixEnd_7387228 3793198668351928670176763 := by
  unfold tailWord_7387228
  simp only [CollatzResearch.WordTrace]
  refine ⟨134717170040671034471685169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179622893387561379295580225 134717170040671034471685169)
  ·
    refine ⟨101037877530503275853763877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134717170040671034471685169 101037877530503275853763877)
    ·
      refine ⟨18944602036969364222580727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101037877530503275853763877 18944602036969364222580727)
      ·
        refine ⟨28416903055454046333871091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18944602036969364222580727 28416903055454046333871091)
        ·
          refine ⟨42625354583181069500806637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28416903055454046333871091 42625354583181069500806637)
          ·
            refine ⟨15984507968692901062802489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42625354583181069500806637 15984507968692901062802489)
            ·
              refine ⟨11988380976519675797101867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15984507968692901062802489 11988380976519675797101867)
              ·
                refine ⟨17982571464779513695652801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11988380976519675797101867 17982571464779513695652801)
                ·
                  refine ⟨13486928598584635271739601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17982571464779513695652801 13486928598584635271739601)
                  ·
                    refine ⟨10115196448938476453804701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13486928598584635271739601 10115196448938476453804701)
                    ·
                      refine ⟨3793198668351928670176763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10115196448938476453804701 3793198668351928670176763)
                      ·
                        rfl

theorem cell23_7387228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_7387228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387228 prefixEnd_7387228 := by exact prefixLift 7387228
  have htrace : WordTrace (prefixWord ++ tailWord_7387228) baseStart_7387228 baseEnd_7387228 := by
    simpa [prefixWord, tailWord_7387228, baseEnd_7387228] using wordTrace_append hprefix tailTrace_7387228
  have hstable : (prefixWord ++ tailWord_7387228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387228).length < 2 ^ (prefixWord ++ tailWord_7387228).sum := by decide
  have hdescent : baseEnd_7387228 < baseStart_7387228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387295 : List Nat := [1, 1, 2, 6, 1, 3, 2, 1, 1, 5]
def baseStart_7387295 : Nat := 118140960795 + 7387295 * 2 ^ 59
def prefixEnd_7387295 : Nat := 4983230072969 + 3 ^ 40 * 7387295 * 2
def baseEnd_7387295 : Nat := 1264411023851926636012985

theorem tailTrace_7387295 : CollatzResearch.WordTrace tailWord_7387295 prefixEnd_7387295 1264411023851926636012985 := by
  unfold tailWord_7387295
  simp only [CollatzResearch.WordTrace]
  refine ⟨269436783772099339386059339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179624522514732892924039559 269436783772099339386059339)
  ·
    refine ⟨404155175658149009079089009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269436783772099339386059339 404155175658149009079089009)
    ·
      refine ⟨303116381743611756809316757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404155175658149009079089009 303116381743611756809316757)
      ·
        refine ⟨14208580394231801100436723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 303116381743611756809316757 14208580394231801100436723)
        ·
          refine ⟨21312870591347701650655085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14208580394231801100436723 21312870591347701650655085)
          ·
            refine ⟨7992326471755388118995657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21312870591347701650655085 7992326471755388118995657)
            ·
              refine ⟨5994244853816541089246743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7992326471755388118995657 5994244853816541089246743)
              ·
                refine ⟨8991367280724811633870115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5994244853816541089246743 8991367280724811633870115)
                ·
                  refine ⟨13487050921087217450805173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8991367280724811633870115 13487050921087217450805173)
                  ·
                    refine ⟨1264411023851926636012985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13487050921087217450805173 1264411023851926636012985)
                    ·
                      rfl

theorem cell23_7387295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 1, 5].length) (baseStart_7387295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387295 prefixEnd_7387295 := by exact prefixLift 7387295
  have htrace : WordTrace (prefixWord ++ tailWord_7387295) baseStart_7387295 baseEnd_7387295 := by
    simpa [prefixWord, tailWord_7387295, baseEnd_7387295] using wordTrace_append hprefix tailTrace_7387295
  have hstable : (prefixWord ++ tailWord_7387295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387295).length < 2 ^ (prefixWord ++ tailWord_7387295).sum := by decide
  have hdescent : baseEnd_7387295 < baseStart_7387295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387328 : List Nat := [2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 4]
def baseStart_7387328 : Nat := 118140960795 + 7387328 * 2 ^ 59
def prefixEnd_7387328 : Nat := 4983230072969 + 3 ^ 40 * 7387328 * 2
def baseEnd_7387328 : Nat := 3793250016417378278926303

theorem tailTrace_7387328 : CollatzResearch.WordTrace tailWord_7387328 prefixEnd_7387328 3793250016417378278926303 := by
  unfold tailWord_7387328
  simp only [CollatzResearch.WordTrace]
  refine ⟨134718993690489893011005319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179625324920653190681340425 134718993690489893011005319)
  ·
    refine ⟨202078490535734839516507979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134718993690489893011005319 202078490535734839516507979)
    ·
      refine ⟨303117735803602259274761969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202078490535734839516507979 303117735803602259274761969)
      ·
        refine ⟨227338301852701694456071477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303117735803602259274761969 227338301852701694456071477)
        ·
          refine ⟨21312965798690783855256701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 227338301852701694456071477 21312965798690783855256701)
          ·
            refine ⟨7992362174509043945721263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21312965798690783855256701 7992362174509043945721263)
            ·
              refine ⟨11988543261763565918581895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7992362174509043945721263 11988543261763565918581895)
              ·
                refine ⟨17982814892645348877872843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11988543261763565918581895 17982814892645348877872843)
                ·
                  refine ⟨26974222338968023316809265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17982814892645348877872843 26974222338968023316809265)
                  ·
                    refine ⟨20230666754226017487606949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26974222338968023316809265 20230666754226017487606949)
                    ·
                      refine ⟨3793250016417378278926303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20230666754226017487606949 3793250016417378278926303)
                      ·
                        rfl

theorem cell23_7387328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 4].length) (baseStart_7387328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387328 prefixEnd_7387328 := by exact prefixLift 7387328
  have htrace : WordTrace (prefixWord ++ tailWord_7387328) baseStart_7387328 baseEnd_7387328 := by
    simpa [prefixWord, tailWord_7387328, baseEnd_7387328] using wordTrace_append hprefix tailTrace_7387328
  have hstable : (prefixWord ++ tailWord_7387328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387328).length < 2 ^ (prefixWord ++ tailWord_7387328).sum := by decide
  have hdescent : baseEnd_7387328 < baseStart_7387328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387382 : List Nat := [5, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3]
def baseStart_7387382 : Nat := 118140960795 + 7387382 * 2 ^ 59
def prefixEnd_7387382 : Nat := 4983230072969 + 3 ^ 40 * 7387382 * 2
def baseEnd_7387382 : Nat := 3793277744372721067651055

theorem tailTrace_7387382 : CollatzResearch.WordTrace tailWord_7387382 prefixEnd_7387382 3793277744372721067651055 := by
  unfold tailWord_7387382
  simp only [CollatzResearch.WordTrace]
  refine ⟨16839997307674009577779775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179626637948522768829650933 16839997307674009577779775)
  ·
    refine ⟨25259995961511014366669663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16839997307674009577779775 25259995961511014366669663)
    ·
      refine ⟨37889993942266521550004495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25259995961511014366669663 37889993942266521550004495)
      ·
        refine ⟨56834990913399782325006743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37889993942266521550004495 56834990913399782325006743)
        ·
          refine ⟨85252486370099673487510115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56834990913399782325006743 85252486370099673487510115)
          ·
            refine ⟨127878729555149510231265173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85252486370099673487510115 127878729555149510231265173)
            ·
              refine ⟨5994315447897633292090555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127878729555149510231265173 5994315447897633292090555)
              ·
                refine ⟨8991473171846449938135833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5994315447897633292090555 8991473171846449938135833)
                ·
                  refine ⟨6743604878884837453601875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8991473171846449938135833 6743604878884837453601875)
                  ·
                    refine ⟨10115407318327256180402813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6743604878884837453601875 10115407318327256180402813)
                    ·
                      refine ⟨3793277744372721067651055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10115407318327256180402813 3793277744372721067651055)
                      ·
                        rfl

theorem cell23_7387382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_7387382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387382 prefixEnd_7387382 := by exact prefixLift 7387382
  have htrace : WordTrace (prefixWord ++ tailWord_7387382) baseStart_7387382 baseEnd_7387382 := by
    simpa [prefixWord, tailWord_7387382, baseEnd_7387382] using wordTrace_append hprefix tailTrace_7387382
  have hstable : (prefixWord ++ tailWord_7387382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387382).length < 2 ^ (prefixWord ++ tailWord_7387382).sum := by decide
  have hdescent : baseEnd_7387382 < baseStart_7387382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387384 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 2, 3, 6]
def baseStart_7387384 : Nat := 118140960795 + 7387384 * 2 ^ 59
def prefixEnd_7387384 : Nat := 4983230072969 + 3 ^ 40 * 7387384 * 2
def baseEnd_7387384 : Nat := 3793278771334030059826045

theorem tailTrace_7387384 : CollatzResearch.WordTrace tailWord_7387384 prefixEnd_7387384 3793278771334030059826045 := by
  unfold tailWord_7387384
  simp only [CollatzResearch.WordTrace]
  refine ⟨134720014934388453793024603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179626686579184605057366137 134720014934388453793024603)
  ·
    refine ⟨202080022401582680689536905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134720014934388453793024603 202080022401582680689536905)
    ·
      refine ⟨151560016801187010517152679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202080022401582680689536905 151560016801187010517152679)
      ·
        refine ⟨227340025201780515775729019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151560016801187010517152679 227340025201780515775729019)
        ·
          refine ⟨341010037802670773663593529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227340025201780515775729019 341010037802670773663593529)
          ·
            refine ⟨255757528352003080247695147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341010037802670773663593529 255757528352003080247695147)
            ·
              refine ⟨383636292528004620371542721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255757528352003080247695147 383636292528004620371542721)
              ·
                refine ⟨287727219396003465278657041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383636292528004620371542721 287727219396003465278657041)
                ·
                  refine ⟨215795414547002598958992781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287727219396003465278657041 215795414547002598958992781)
                  ·
                    refine ⟨80923280455125974609622293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 215795414547002598958992781 80923280455125974609622293)
                    ·
                      refine ⟨3793278771334030059826045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80923280455125974609622293 3793278771334030059826045)
                      ·
                        rfl

theorem cell23_7387384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_7387384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387384 prefixEnd_7387384 := by exact prefixLift 7387384
  have htrace : WordTrace (prefixWord ++ tailWord_7387384) baseStart_7387384 baseEnd_7387384 := by
    simpa [prefixWord, tailWord_7387384, baseEnd_7387384] using wordTrace_append hprefix tailTrace_7387384
  have hstable : (prefixWord ++ tailWord_7387384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387384).length < 2 ^ (prefixWord ++ tailWord_7387384).sum := by decide
  have hdescent : baseEnd_7387384 < baseStart_7387384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387491 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 6]
def baseStart_7387491 : Nat := 118140960795 + 7387491 * 2 ^ 59
def prefixEnd_7387491 : Nat := 4983230072969 + 3 ^ 40 * 7387491 * 2
def baseEnd_7387491 : Nat := 3793333713764061141188053

theorem tailTrace_7387491 : CollatzResearch.WordTrace tailWord_7387491 prefixEnd_7387491 3793333713764061141188053 := by
  unfold tailWord_7387491
  simp only [CollatzResearch.WordTrace]
  refine ⟨269443932479389264860194327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179629288319592843240129551 269443932479389264860194327)
  ·
    refine ⟨404165898719083897290291491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269443932479389264860194327 404165898719083897290291491)
    ·
      refine ⟨606248848078625845935437237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404165898719083897290291491 606248848078625845935437237)
      ·
        refine ⟨56835829507371173056447241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 606248848078625845935437237 56835829507371173056447241)
        ·
          refine ⟨42626872130528379792335431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56835829507371173056447241 42626872130528379792335431)
          ·
            refine ⟨63940308195792569688503147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42626872130528379792335431 63940308195792569688503147)
            ·
              refine ⟨95910462293688854532754721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63940308195792569688503147 95910462293688854532754721)
              ·
                refine ⟨71932846720266640899566041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95910462293688854532754721 71932846720266640899566041)
                ·
                  refine ⟨53949635040199980674674531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71932846720266640899566041 53949635040199980674674531)
                  ·
                    refine ⟨80924452560299971012011797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53949635040199980674674531 80924452560299971012011797)
                    ·
                      refine ⟨3793333713764061141188053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80924452560299971012011797 3793333713764061141188053)
                      ·
                        rfl

theorem cell23_7387491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_7387491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387491 prefixEnd_7387491 := by exact prefixLift 7387491
  have htrace : WordTrace (prefixWord ++ tailWord_7387491) baseStart_7387491 baseEnd_7387491 := by
    simpa [prefixWord, tailWord_7387491, baseEnd_7387491] using wordTrace_append hprefix tailTrace_7387491
  have hstable : (prefixWord ++ tailWord_7387491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387491).length < 2 ^ (prefixWord ++ tailWord_7387491).sum := by decide
  have hdescent : baseEnd_7387491 < baseStart_7387491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387495 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 2, 4, 2]
def baseStart_7387495 : Nat := 118140960795 + 7387495 * 2 ^ 59
def prefixEnd_7387495 : Nat := 4983230072969 + 3 ^ 40 * 7387495 * 2
def baseEnd_7387495 : Nat := 3793335767686679125538035

theorem tailTrace_7387495 : CollatzResearch.WordTrace tailWord_7387495 prefixEnd_7387495 3793335767686679125538035 := by
  unfold tailWord_7387495
  simp only [CollatzResearch.WordTrace]
  refine ⟨269444078371374773543339939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179629385580916515695559959 269444078371374773543339939)
  ·
    refine ⟨404166117557062160315009909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269444078371374773543339939 404166117557062160315009909)
    ·
      refine ⟨37890573520974577529532179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 404166117557062160315009909 37890573520974577529532179)
      ·
        refine ⟨56835860281461866294298269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37890573520974577529532179 56835860281461866294298269)
        ·
          refine ⟨21313447605548199860361851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56835860281461866294298269 21313447605548199860361851)
          ·
            refine ⟨31970171408322299790542777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21313447605548199860361851 31970171408322299790542777)
            ·
              refine ⟨23977628556241724842907083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31970171408322299790542777 23977628556241724842907083)
              ·
                refine ⟨35966442834362587264360625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23977628556241724842907083 35966442834362587264360625)
                ·
                  refine ⟨26974832125771940448270469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35966442834362587264360625 26974832125771940448270469)
                  ·
                    refine ⟨5057781023582238834050713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26974832125771940448270469 5057781023582238834050713)
                    ·
                      refine ⟨3793335767686679125538035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5057781023582238834050713 3793335767686679125538035)
                      ·
                        rfl

theorem cell23_7387495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_7387495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387495 prefixEnd_7387495 := by exact prefixLift 7387495
  have htrace : WordTrace (prefixWord ++ tailWord_7387495) baseStart_7387495 baseEnd_7387495 := by
    simpa [prefixWord, tailWord_7387495, baseEnd_7387495] using wordTrace_append hprefix tailTrace_7387495
  have hstable : (prefixWord ++ tailWord_7387495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387495).length < 2 ^ (prefixWord ++ tailWord_7387495).sum := by decide
  have hdescent : baseEnd_7387495 < baseStart_7387495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387541 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_7387541 : Nat := 118140960795 + 7387541 * 2 ^ 59
def prefixEnd_7387541 : Nat := 4983230072969 + 3 ^ 40 * 7387541 * 2
def baseEnd_7387541 : Nat := 3793359387796785945562823

theorem tailTrace_7387541 : CollatzResearch.WordTrace tailWord_7387541 prefixEnd_7387541 3793359387796785945562823 := by
  unfold tailWord_7387541
  simp only [CollatzResearch.WordTrace]
  refine ⟨269445756129208123399514477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179630504086138748933009651 269445756129208123399514477)
  ·
    refine ⟨101042158548453046274817929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269445756129208123399514477 101042158548453046274817929)
    ·
      refine ⟨75781618911339784706113447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101042158548453046274817929 75781618911339784706113447)
      ·
        refine ⟨113672428367009677059170171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75781618911339784706113447 113672428367009677059170171)
        ·
          refine ⟨170508642550514515588755257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113672428367009677059170171 170508642550514515588755257)
          ·
            refine ⟨127881481912885886691566443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170508642550514515588755257 127881481912885886691566443)
            ·
              refine ⟨191822222869328830037349665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127881481912885886691566443 191822222869328830037349665)
              ·
                refine ⟨143866667151996622528012249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191822222869328830037349665 143866667151996622528012249)
                ·
                  refine ⟨107900000363997466896009187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143866667151996622528012249 107900000363997466896009187)
                  ·
                    refine ⟨161850000545996200344013781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107900000363997466896009187 161850000545996200344013781)
                    ·
                      refine ⟨3793359387796785945562823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161850000545996200344013781 3793359387796785945562823)
                      ·
                        rfl

theorem cell23_7387541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_7387541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387541 prefixEnd_7387541 := by exact prefixLift 7387541
  have htrace : WordTrace (prefixWord ++ tailWord_7387541) baseStart_7387541 baseEnd_7387541 := by
    simpa [prefixWord, tailWord_7387541, baseEnd_7387541] using wordTrace_append hprefix tailTrace_7387541
  have hstable : (prefixWord ++ tailWord_7387541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387541).length < 2 ^ (prefixWord ++ tailWord_7387541).sum := by decide
  have hdescent : baseEnd_7387541 < baseStart_7387541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387561 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 5, 6]
def baseStart_7387561 : Nat := 118140960795 + 7387561 * 2 ^ 59
def prefixEnd_7387561 : Nat := 4983230072969 + 3 ^ 40 * 7387561 * 2
def baseEnd_7387561 : Nat := 1264456552469958622437577

theorem tailTrace_7387561 : CollatzResearch.WordTrace tailWord_7387561 prefixEnd_7387561 1264456552469958622437577 := by
  unfold tailWord_7387561
  simp only [CollatzResearch.WordTrace]
  refine ⟨269446485589135666815242537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179630990392757111210161691 269446485589135666815242537)
  ·
    refine ⟨202084864191851750111431903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269446485589135666815242537 202084864191851750111431903)
    ·
      refine ⟨303127296287777625167147855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202084864191851750111431903 303127296287777625167147855)
      ·
        refine ⟨454690944431666437750721783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303127296287777625167147855 454690944431666437750721783)
        ·
          refine ⟨682036416647499656626082675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454690944431666437750721783 682036416647499656626082675)
          ·
            refine ⟨1023054624971249484939124013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682036416647499656626082675 1023054624971249484939124013)
            ·
              refine ⟨383645484364218556852171505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1023054624971249484939124013 383645484364218556852171505)
              ·
                refine ⟨287734113273163917639128629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383645484364218556852171505 287734113273163917639128629)
                ·
                  refine ⟨26975073119359117278668309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 287734113273163917639128629 26975073119359117278668309)
                  ·
                    refine ⟨1264456552469958622437577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26975073119359117278668309 1264456552469958622437577)
                    ·
                      rfl

theorem cell23_7387561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 6].length) (baseStart_7387561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387561 prefixEnd_7387561 := by exact prefixLift 7387561
  have htrace : WordTrace (prefixWord ++ tailWord_7387561) baseStart_7387561 baseEnd_7387561 := by
    simpa [prefixWord, tailWord_7387561, baseEnd_7387561] using wordTrace_append hprefix tailTrace_7387561
  have hstable : (prefixWord ++ tailWord_7387561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387561).length < 2 ^ (prefixWord ++ tailWord_7387561).sum := by decide
  have hdescent : baseEnd_7387561 < baseStart_7387561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387571 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 5]
def baseStart_7387571 : Nat := 118140960795 + 7387571 * 2 ^ 59
def prefixEnd_7387571 : Nat := 4983230072969 + 3 ^ 40 * 7387571 * 2
def baseEnd_7387571 : Nat := 3793374792216420828187685

theorem tailTrace_7387571 : CollatzResearch.WordTrace tailWord_7387571 prefixEnd_7387571 3793374792216420828187685 := by
  unfold tailWord_7387571
  simp only [CollatzResearch.WordTrace]
  refine ⟨269446850319099438523106567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179631233546066292348737711 269446850319099438523106567)
  ·
    refine ⟨404170275478649157784659851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269446850319099438523106567 404170275478649157784659851)
    ·
      refine ⟨606255413217973736676989777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404170275478649157784659851 606255413217973736676989777)
      ·
        refine ⟨454691559913480302507742333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 606255413217973736676989777 454691559913480302507742333)
        ·
          refine ⟨170509334967555113440403375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454691559913480302507742333 170509334967555113440403375)
          ·
            refine ⟨255764002451332670160605063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170509334967555113440403375 255764002451332670160605063)
            ·
              refine ⟨383646003676999005240907595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255764002451332670160605063 383646003676999005240907595)
              ·
                refine ⟨575469005515498507861361393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383646003676999005240907595 575469005515498507861361393)
                ·
                  refine ⟨431601754136623880896021045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575469005515498507861361393 431601754136623880896021045)
                  ·
                    refine ⟨40462664450308488834001973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 431601754136623880896021045 40462664450308488834001973)
                    ·
                      refine ⟨3793374792216420828187685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40462664450308488834001973 3793374792216420828187685)
                      ·
                        rfl

theorem cell23_7387571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_7387571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387571 prefixEnd_7387571 := by exact prefixLift 7387571
  have htrace : WordTrace (prefixWord ++ tailWord_7387571) baseStart_7387571 baseEnd_7387571 := by
    simpa [prefixWord, tailWord_7387571, baseEnd_7387571] using wordTrace_append hprefix tailTrace_7387571
  have hstable : (prefixWord ++ tailWord_7387571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387571).length < 2 ^ (prefixWord ++ tailWord_7387571).sum := by decide
  have hdescent : baseEnd_7387571 < baseStart_7387571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387578 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 6, 4]
def baseStart_7387578 : Nat := 118140960795 + 7387578 * 2 ^ 59
def prefixEnd_7387578 : Nat := 4983230072969 + 3 ^ 40 * 7387578 * 2
def baseEnd_7387578 : Nat := 1264459462193667433600051

theorem tailTrace_7387578 : CollatzResearch.WordTrace tailWord_7387578 prefixEnd_7387578 1264459462193667433600051 := by
  unfold tailWord_7387578
  simp only [CollatzResearch.WordTrace]
  refine ⟨67361776407518519679652847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179631403753382719145740925 67361776407518519679652847)
  ·
    refine ⟨101042664611277779519479271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67361776407518519679652847 101042664611277779519479271)
    ·
      refine ⟨151563996916916669279218907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101042664611277779519479271 151563996916916669279218907)
      ·
        refine ⟨227345995375375003918828361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151563996916916669279218907 227345995375375003918828361)
        ·
          refine ⟨170509496531531252939121271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227345995375375003918828361 170509496531531252939121271)
          ·
            refine ⟨255764244797296879408681907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170509496531531252939121271 255764244797296879408681907)
            ·
              refine ⟨383646367195945319113022861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255764244797296879408681907 383646367195945319113022861)
              ·
                refine ⟨143867387698479494667383573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383646367195945319113022861 143867387698479494667383573)
                ·
                  refine ⟨6743783798366226312533605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143867387698479494667383573 6743783798366226312533605)
                  ·
                    refine ⟨1264459462193667433600051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6743783798366226312533605 1264459462193667433600051)
                    ·
                      rfl

theorem cell23_7387578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_7387578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387578 prefixEnd_7387578 := by exact prefixLift 7387578
  have htrace : WordTrace (prefixWord ++ tailWord_7387578) baseStart_7387578 baseEnd_7387578 := by
    simpa [prefixWord, tailWord_7387578, baseEnd_7387578] using wordTrace_append hprefix tailTrace_7387578
  have hstable : (prefixWord ++ tailWord_7387578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387578).length < 2 ^ (prefixWord ++ tailWord_7387578).sum := by decide
  have hdescent : baseEnd_7387578 < baseStart_7387578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387591 : List Nat := [1, 1, 4, 1, 1, 15]
def baseStart_7387591 : Nat := 118140960795 + 7387591 * 2 ^ 59
def prefixEnd_7387591 : Nat := 4983230072969 + 3 ^ 40 * 7387591 * 2
def baseEnd_7387591 : Nat := 15610638114524735596451

theorem tailTrace_7387591 : CollatzResearch.WordTrace tailWord_7387591 prefixEnd_7387591 15610638114524735596451 := by
  unfold tailWord_7387591
  simp only [CollatzResearch.WordTrace]
  refine ⟨269447579779026981938834627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179631719852684654625889751 269447579779026981938834627)
  ·
    refine ⟨404171369668540472908251941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269447579779026981938834627 404171369668540472908251941)
    ·
      refine ⟨75782131812851338670297239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404171369668540472908251941 75782131812851338670297239)
      ·
        refine ⟨113673197719277008005445859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75782131812851338670297239 113673197719277008005445859)
        ·
          refine ⟨170509796578915512008168789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113673197719277008005445859 170509796578915512008168789)
          ·
            refine ⟨15610638114524735596451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 170509796578915512008168789 15610638114524735596451)
            ·
              rfl

theorem cell23_7387591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 15].length) (baseStart_7387591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387591 prefixEnd_7387591 := by exact prefixLift 7387591
  have htrace : WordTrace (prefixWord ++ tailWord_7387591) baseStart_7387591 baseEnd_7387591 := by
    simpa [prefixWord, tailWord_7387591, baseEnd_7387591] using wordTrace_append hprefix tailTrace_7387591
  have hstable : (prefixWord ++ tailWord_7387591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387591).length < 2 ^ (prefixWord ++ tailWord_7387591).sum := by decide
  have hdescent : baseEnd_7387591 < baseStart_7387591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387598 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_7387598 : Nat := 118140960795 + 7387598 * 2 ^ 59
def prefixEnd_7387598 : Nat := 4983230072969 + 3 ^ 40 * 7387598 * 2
def baseEnd_7387598 : Nat := 3793388656194092222550061

theorem tailTrace_7387598 : CollatzResearch.WordTrace tailWord_7387598 prefixEnd_7387598 3793388656194092222550061 := by
  unfold tailWord_7387598
  simp only [CollatzResearch.WordTrace]
  refine ⟨33680979386250202766792431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179631890060001081422892965 33680979386250202766792431)
  ·
    refine ⟨50521469079375304150188647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33680979386250202766792431 50521469079375304150188647)
    ·
      refine ⟨75782203619062956225282971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50521469079375304150188647 75782203619062956225282971)
      ·
        refine ⟨113673305428594434337924457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75782203619062956225282971 113673305428594434337924457)
        ·
          refine ⟨85254979071445825753443343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113673305428594434337924457 85254979071445825753443343)
          ·
            refine ⟨127882468607168738630165015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85254979071445825753443343 127882468607168738630165015)
            ·
              refine ⟨191823702910753107945247523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127882468607168738630165015 191823702910753107945247523)
              ·
                refine ⟨287735554366129661917871285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191823702910753107945247523 287735554366129661917871285)
                ·
                  refine ⟨26975208221824655804800433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 287735554366129661917871285 26975208221824655804800433)
                  ·
                    refine ⟨20231406166368491853600325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26975208221824655804800433 20231406166368491853600325)
                    ·
                      refine ⟨3793388656194092222550061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20231406166368491853600325 3793388656194092222550061)
                      ·
                        rfl

theorem cell23_7387598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_7387598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387598 prefixEnd_7387598 := by exact prefixLift 7387598
  have htrace : WordTrace (prefixWord ++ tailWord_7387598) baseStart_7387598 baseEnd_7387598 := by
    simpa [prefixWord, tailWord_7387598, baseEnd_7387598] using wordTrace_append hprefix tailTrace_7387598
  have hstable : (prefixWord ++ tailWord_7387598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387598).length < 2 ^ (prefixWord ++ tailWord_7387598).sum := by decide
  have hdescent : baseEnd_7387598 < baseStart_7387598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387605 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 3, 2, 3]
def baseStart_7387605 : Nat := 118140960795 + 7387605 * 2 ^ 59
def prefixEnd_7387605 : Nat := 4983230072969 + 3 ^ 40 * 7387605 * 2
def baseEnd_7387605 : Nat := 3793392250558673695162529

theorem tailTrace_7387605 : CollatzResearch.WordTrace tailWord_7387605 prefixEnd_7387605 3793392250558673695162529 := by
  unfold tailWord_7387605
  simp only [CollatzResearch.WordTrace]
  refine ⟨269448090400976262329844269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179632060267317508219896179 269448090400976262329844269)
  ·
    refine ⟨101043033900366098373691601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269448090400976262329844269 101043033900366098373691601)
    ·
      refine ⟨75782275425274573780268701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101043033900366098373691601 75782275425274573780268701)
      ·
        refine ⟨28418353284477965167600763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75782275425274573780268701 28418353284477965167600763)
        ·
          refine ⟨42627529926716947751401145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28418353284477965167600763 42627529926716947751401145)
          ·
            refine ⟨31970647445037710813550859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42627529926716947751401145 31970647445037710813550859)
            ·
              refine ⟨47955971167556566220326289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31970647445037710813550859 47955971167556566220326289)
              ·
                refine ⟨35966978375667424665244717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47955971167556566220326289 35966978375667424665244717)
                ·
                  refine ⟨13487616890875284249466769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35966978375667424665244717 13487616890875284249466769)
                  ·
                    refine ⟨10115712668156463187100077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13487616890875284249466769 10115712668156463187100077)
                    ·
                      refine ⟨3793392250558673695162529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10115712668156463187100077 3793392250558673695162529)
                      ·
                        rfl

theorem cell23_7387605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_7387605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387605 prefixEnd_7387605 := by exact prefixLift 7387605
  have htrace : WordTrace (prefixWord ++ tailWord_7387605) baseStart_7387605 baseEnd_7387605 := by
    simpa [prefixWord, tailWord_7387605, baseEnd_7387605] using wordTrace_append hprefix tailTrace_7387605
  have hstable : (prefixWord ++ tailWord_7387605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387605).length < 2 ^ (prefixWord ++ tailWord_7387605).sum := by decide
  have hdescent : baseEnd_7387605 < baseStart_7387605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387615 : List Nat := [1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 4]
def baseStart_7387615 : Nat := 118140960795 + 7387615 * 2 ^ 59
def prefixEnd_7387615 : Nat := 4983230072969 + 3 ^ 40 * 7387615 * 2
def baseEnd_7387615 : Nat := 3793397385365218656037483

theorem tailTrace_7387615 : CollatzResearch.WordTrace tailWord_7387615 prefixEnd_7387615 3793397385365218656037483 := by
  unfold tailWord_7387615
  simp only [CollatzResearch.WordTrace]
  refine ⟨269448455130940034037708299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179632303420626689358472199 269448455130940034037708299)
  ·
    refine ⟨404172682696410051056562449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269448455130940034037708299 404172682696410051056562449)
    ·
      refine ⟨303129512022307538292421837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404172682696410051056562449 303129512022307538292421837)
      ·
        refine ⟨113673567008365326859658189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303129512022307538292421837 113673567008365326859658189)
        ·
          refine ⟨42627587628136997572371821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113673567008365326859658189 42627587628136997572371821)
          ·
            refine ⟨15985345360551374089639433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42627587628136997572371821 15985345360551374089639433)
            ·
              refine ⟨11989009020413530567229575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15985345360551374089639433 11989009020413530567229575)
              ·
                refine ⟨17983513530620295850844363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11989009020413530567229575 17983513530620295850844363)
                ·
                  refine ⟨26975270295930443776266545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17983513530620295850844363 26975270295930443776266545)
                  ·
                    refine ⟨20231452721947832832199909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26975270295930443776266545 20231452721947832832199909)
                    ·
                      refine ⟨3793397385365218656037483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20231452721947832832199909 3793397385365218656037483)
                      ·
                        rfl

theorem cell23_7387615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_7387615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387615 prefixEnd_7387615 := by exact prefixLift 7387615
  have htrace : WordTrace (prefixWord ++ tailWord_7387615) baseStart_7387615 baseEnd_7387615 := by
    simpa [prefixWord, tailWord_7387615, baseEnd_7387615] using wordTrace_append hprefix tailTrace_7387615
  have hstable : (prefixWord ++ tailWord_7387615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387615).length < 2 ^ (prefixWord ++ tailWord_7387615).sum := by decide
  have hdescent : baseEnd_7387615 < baseStart_7387615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387619 : List Nat := [1, 1, 1, 6, 3, 1, 1, 2, 3, 2, 2]
def baseStart_7387619 : Nat := 118140960795 + 7387619 * 2 ^ 59
def prefixEnd_7387619 : Nat := 4983230072969 + 3 ^ 40 * 7387619 * 2
def baseEnd_7387619 : Nat := 3793399439287836640387465

theorem tailTrace_7387619 : CollatzResearch.WordTrace tailWord_7387619 prefixEnd_7387619 3793399439287836640387465 := by
  unfold tailWord_7387619
  simp only [CollatzResearch.WordTrace]
  refine ⟨269448601022925542720853911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179632400681950361813902607 269448601022925542720853911)
  ·
    refine ⟨404172901534388314081280867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269448601022925542720853911 404172901534388314081280867)
    ·
      refine ⟨606259352301582471121921301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404172901534388314081280867 606259352301582471121921301)
      ·
        refine ⟨28418407139136678333840061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 606259352301582471121921301 28418407139136678333840061)
        ·
          refine ⟨10656902677176254375190023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28418407139136678333840061 10656902677176254375190023)
          ·
            refine ⟨15985354015764381562785035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10656902677176254375190023 15985354015764381562785035)
            ·
              refine ⟨23978031023646572344177553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15985354015764381562785035 23978031023646572344177553)
              ·
                refine ⟨17983523267734929258133165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23978031023646572344177553 17983523267734929258133165)
                ·
                  refine ⟨6743821225400598471799937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17983523267734929258133165 6743821225400598471799937)
                  ·
                    refine ⟨5057865919050448853849953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6743821225400598471799937 5057865919050448853849953)
                    ·
                      refine ⟨3793399439287836640387465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5057865919050448853849953 3793399439287836640387465)
                      ·
                        rfl

theorem cell23_7387619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_7387619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387619 prefixEnd_7387619 := by exact prefixLift 7387619
  have htrace : WordTrace (prefixWord ++ tailWord_7387619) baseStart_7387619 baseEnd_7387619 := by
    simpa [prefixWord, tailWord_7387619, baseEnd_7387619] using wordTrace_append hprefix tailTrace_7387619
  have hstable : (prefixWord ++ tailWord_7387619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387619).length < 2 ^ (prefixWord ++ tailWord_7387619).sum := by decide
  have hdescent : baseEnd_7387619 < baseStart_7387619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387635 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 4, 1, 3]
def baseStart_7387635 : Nat := 118140960795 + 7387635 * 2 ^ 59
def prefixEnd_7387635 : Nat := 4983230072969 + 3 ^ 40 * 7387635 * 2
def baseEnd_7387635 : Nat := 3793407654978308577787391

theorem tailTrace_7387635 : CollatzResearch.WordTrace tailWord_7387635 prefixEnd_7387635 3793407654978308577787391 := by
  unfold tailWord_7387635
  simp only [CollatzResearch.WordTrace]
  refine ⟨269449184590867577453436359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179632789727245051635624239 269449184590867577453436359)
  ·
    refine ⟨404173776886301366180154539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269449184590867577453436359 404173776886301366180154539)
    ·
      refine ⟨606260665329452049270231809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404173776886301366180154539 606260665329452049270231809)
      ·
        refine ⟨454695498997089036952673857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 606260665329452049270231809 454695498997089036952673857)
        ·
          refine ⟨341021624247816777714505393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454695498997089036952673857 341021624247816777714505393)
          ·
            refine ⟨255766218185862583285879045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341021624247816777714505393 255766218185862583285879045)
            ·
              refine ⟨47956165909849234366102321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255766218185862583285879045 47956165909849234366102321)
              ·
                refine ⟨35967124432386925774576741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47956165909849234366102321 35967124432386925774576741)
                ·
                  refine ⟨6743835831072548582733139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35967124432386925774576741 6743835831072548582733139)
                  ·
                    refine ⟨10115753746608822874099709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6743835831072548582733139 10115753746608822874099709)
                    ·
                      refine ⟨3793407654978308577787391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10115753746608822874099709 3793407654978308577787391)
                      ·
                        rfl

theorem cell23_7387635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 1, 3].length) (baseStart_7387635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387635 prefixEnd_7387635 := by exact prefixLift 7387635
  have htrace : WordTrace (prefixWord ++ tailWord_7387635) baseStart_7387635 baseEnd_7387635 := by
    simpa [prefixWord, tailWord_7387635, baseEnd_7387635] using wordTrace_append hprefix tailTrace_7387635
  have hstable : (prefixWord ++ tailWord_7387635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387635).length < 2 ^ (prefixWord ++ tailWord_7387635).sum := by decide
  have hdescent : baseEnd_7387635 < baseStart_7387635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387669 : List Nat := [1, 3, 2, 1, 3, 1, 5, 1, 2, 1, 3]
def baseStart_7387669 : Nat := 118140960795 + 7387669 * 2 ^ 59
def prefixEnd_7387669 : Nat := 4983230072969 + 3 ^ 40 * 7387669 * 2
def baseEnd_7387669 : Nat := 3793425113320561444762235

theorem tailTrace_7387669 : CollatzResearch.WordTrace tailWord_7387669 prefixEnd_7387669 3793425113320561444762235 := by
  unfold tailWord_7387669
  simp only [CollatzResearch.WordTrace]
  refine ⟨269450424672744401260174061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179633616448496267506782707 269450424672744401260174061)
  ·
    refine ⟨101043909252279150472565273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269450424672744401260174061 101043909252279150472565273)
    ·
      refine ⟨75782931939209362854423955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101043909252279150472565273 75782931939209362854423955)
      ·
        refine ⟨113674397908814044281635933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75782931939209362854423955 113674397908814044281635933)
        ·
          refine ⟨42627899215805266605613475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113674397908814044281635933 42627899215805266605613475)
          ·
            refine ⟨63941848823707899908420213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42627899215805266605613475 63941848823707899908420213)
            ·
              refine ⟨5994548327222615616414395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63941848823707899908420213 5994548327222615616414395)
              ·
                refine ⟨8991822490833923424621593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5994548327222615616414395 8991822490833923424621593)
                ·
                  refine ⟨6743866868125442568466195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8991822490833923424621593 6743866868125442568466195)
                  ·
                    refine ⟨10115800302188163852699293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6743866868125442568466195 10115800302188163852699293)
                    ·
                      refine ⟨3793425113320561444762235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10115800302188163852699293 3793425113320561444762235)
                      ·
                        rfl

theorem cell23_7387669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_7387669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387669 prefixEnd_7387669 := by exact prefixLift 7387669
  have htrace : WordTrace (prefixWord ++ tailWord_7387669) baseStart_7387669 baseEnd_7387669 := by
    simpa [prefixWord, tailWord_7387669, baseEnd_7387669] using wordTrace_append hprefix tailTrace_7387669
  have hstable : (prefixWord ++ tailWord_7387669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387669).length < 2 ^ (prefixWord ++ tailWord_7387669).sum := by decide
  have hdescent : baseEnd_7387669 < baseStart_7387669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387687 : List Nat := [1, 1, 7, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_7387687 : Nat := 118140960795 + 7387687 * 2 ^ 59
def prefixEnd_7387687 : Nat := 4983230072969 + 3 ^ 40 * 7387687 * 2
def baseEnd_7387687 : Nat := 3793434355972342374337153

theorem tailTrace_7387687 : CollatzResearch.WordTrace tailWord_7387687 prefixEnd_7387687 3793434355972342374337153 := by
  unfold tailWord_7387687
  simp only [CollatzResearch.WordTrace]
  refine ⟨269451081186679190334329315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179634054124452793556219543 269451081186679190334329315)
  ·
    refine ⟨404176621780018785501493973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269451081186679190334329315 404176621780018785501493973)
    ·
      refine ⟨9472889572969190285191265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 404176621780018785501493973 9472889572969190285191265)
      ·
        refine ⟨7104667179726892713893449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9472889572969190285191265 7104667179726892713893449)
        ·
          refine ⟨5328500384795169535420087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7104667179726892713893449 5328500384795169535420087)
          ·
            refine ⟨7992750577192754303130131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5328500384795169535420087 7992750577192754303130131)
            ·
              refine ⟨11989125865789131454695197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7992750577192754303130131 11989125865789131454695197)
              ·
                refine ⟨4495922199670924295510699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11989125865789131454695197 4495922199670924295510699)
                ·
                  refine ⟨6743883299506386443266049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4495922199670924295510699 6743883299506386443266049)
                  ·
                    refine ⟨5057912474629789832449537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6743883299506386443266049 5057912474629789832449537)
                    ·
                      refine ⟨3793434355972342374337153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5057912474629789832449537 3793434355972342374337153)
                      ·
                        rfl

theorem cell23_7387687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_7387687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387687 prefixEnd_7387687 := by exact prefixLift 7387687
  have htrace : WordTrace (prefixWord ++ tailWord_7387687) baseStart_7387687 baseEnd_7387687 := by
    simpa [prefixWord, tailWord_7387687, baseEnd_7387687] using wordTrace_append hprefix tailTrace_7387687
  have hstable : (prefixWord ++ tailWord_7387687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387687).length < 2 ^ (prefixWord ++ tailWord_7387687).sum := by decide
  have hdescent : baseEnd_7387687 < baseStart_7387687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387698 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 9]
def baseStart_7387698 : Nat := 118140960795 + 7387698 * 2 ^ 59
def prefixEnd_7387698 : Nat := 4983230072969 + 3 ^ 40 * 7387698 * 2
def baseEnd_7387698 : Nat := 421493333806615759033289

theorem tailTrace_7387698 : CollatzResearch.WordTrace tailWord_7387698 prefixEnd_7387698 421493333806615759033289 := by
  unfold tailWord_7387698
  simp only [CollatzResearch.WordTrace]
  refine ⟨67362870597409834803244937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179634321593092892808653165 67362870597409834803244937)
  ·
    refine ⟨50522152948057376102433703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67362870597409834803244937 50522152948057376102433703)
    ·
      refine ⟨75783229422086064153650555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50522152948057376102433703 75783229422086064153650555)
      ·
        refine ⟨113674844133129096230475833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75783229422086064153650555 113674844133129096230475833)
        ·
          refine ⟨85256133099846822172856875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113674844133129096230475833 85256133099846822172856875)
          ·
            refine ⟨127884199649770233259285313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85256133099846822172856875 127884199649770233259285313)
            ·
              refine ⟨95913149737327674944463985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127884199649770233259285313 95913149737327674944463985)
              ·
                refine ⟨71934862302995756208347989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95913149737327674944463985 71934862302995756208347989)
                ·
                  refine ⟨421493333806615759033289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71934862302995756208347989 421493333806615759033289)
                  ·
                    rfl

theorem cell23_7387698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_7387698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387698 prefixEnd_7387698 := by exact prefixLift 7387698
  have htrace : WordTrace (prefixWord ++ tailWord_7387698) baseStart_7387698 baseEnd_7387698 := by
    simpa [prefixWord, tailWord_7387698, baseEnd_7387698] using wordTrace_append hprefix tailTrace_7387698
  have hstable : (prefixWord ++ tailWord_7387698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387698).length < 2 ^ (prefixWord ++ tailWord_7387698).sum := by decide
  have hdescent : baseEnd_7387698 < baseStart_7387698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387709 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 4, 2, 2]
def baseStart_7387709 : Nat := 118140960795 + 7387709 * 2 ^ 59
def prefixEnd_7387709 : Nat := 4983230072969 + 3 ^ 40 * 7387709 * 2
def baseEnd_7387709 : Nat := 3793445652546741288262051

theorem tailTrace_7387709 : CollatzResearch.WordTrace tailWord_7387709 prefixEnd_7387709 3793445652546741288262051 := by
  unfold tailWord_7387709
  simp only [CollatzResearch.WordTrace]
  refine ⟨269451883592599488091630181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179634589061732992061086787 269451883592599488091630181)
  ·
    refine ⟨50522228173612404017180659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269451883592599488091630181 50522228173612404017180659)
    ·
      refine ⟨75783342260418606025770989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50522228173612404017180659 75783342260418606025770989)
      ·
        refine ⟨28418753347656977259664121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75783342260418606025770989 28418753347656977259664121)
        ·
          refine ⟨21314065010742732944748091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28418753347656977259664121 21314065010742732944748091)
          ·
            refine ⟨31971097516114099417122137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21314065010742732944748091 31971097516114099417122137)
            ·
              refine ⟨23978323137085574562841603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31971097516114099417122137 23978323137085574562841603)
              ·
                refine ⟨35967484705628361844262405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23978323137085574562841603 35967484705628361844262405)
                ·
                  refine ⟨6743903382305317845799201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35967484705628361844262405 6743903382305317845799201)
                  ·
                    refine ⟨5057927536728988384349401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6743903382305317845799201 5057927536728988384349401)
                    ·
                      refine ⟨3793445652546741288262051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5057927536728988384349401 3793445652546741288262051)
                      ·
                        rfl

theorem cell23_7387709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_7387709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387709 prefixEnd_7387709 := by exact prefixLift 7387709
  have htrace : WordTrace (prefixWord ++ tailWord_7387709) baseStart_7387709 baseEnd_7387709 := by
    simpa [prefixWord, tailWord_7387709, baseEnd_7387709] using wordTrace_append hprefix tailTrace_7387709
  have hstable : (prefixWord ++ tailWord_7387709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387709).length < 2 ^ (prefixWord ++ tailWord_7387709).sum := by decide
  have hdescent : baseEnd_7387709 < baseStart_7387709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387715 : List Nat := [1, 1, 1, 3, 1, 2, 1, 8, 5]
def baseStart_7387715 : Nat := 118140960795 + 7387715 * 2 ^ 59
def prefixEnd_7387715 : Nat := 4983230072969 + 3 ^ 40 * 7387715 * 2
def baseEnd_7387715 : Nat := 421494303714518696087447

theorem tailTrace_7387715 : CollatzResearch.WordTrace tailWord_7387715 prefixEnd_7387715 421494303714518696087447 := by
  unfold tailWord_7387715
  simp only [CollatzResearch.WordTrace]
  refine ⟨269452102430577751116348599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179634734953718500744232399 269452102430577751116348599)
  ·
    refine ⟨404178153645866626674522899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269452102430577751116348599 404178153645866626674522899)
    ·
      refine ⟨606267230468799940011784349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404178153645866626674522899 606267230468799940011784349)
      ·
        refine ⟨227350211425799977504419131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 606267230468799940011784349 227350211425799977504419131)
        ·
          refine ⟨341025317138699966256628697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227350211425799977504419131 341025317138699966256628697)
          ·
            refine ⟨255768987854024974692471523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341025317138699966256628697 255768987854024974692471523)
            ·
              refine ⟨383653481781037462038707285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255768987854024974692471523 383653481781037462038707285)
              ·
                refine ⟨4495939239621532758266101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 383653481781037462038707285 4495939239621532758266101)
                ·
                  refine ⟨421494303714518696087447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4495939239621532758266101 421494303714518696087447)
                  ·
                    rfl

theorem cell23_7387715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 5].length) (baseStart_7387715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387715 prefixEnd_7387715 := by exact prefixLift 7387715
  have htrace : WordTrace (prefixWord ++ tailWord_7387715) baseStart_7387715 baseEnd_7387715 := by
    simpa [prefixWord, tailWord_7387715, baseEnd_7387715] using wordTrace_append hprefix tailTrace_7387715
  have hstable : (prefixWord ++ tailWord_7387715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387715).length < 2 ^ (prefixWord ++ tailWord_7387715).sum := by decide
  have hdescent : baseEnd_7387715 < baseStart_7387715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387726 : List Nat := [4, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2]
def baseStart_7387726 : Nat := 118140960795 + 7387726 * 2 ^ 59
def prefixEnd_7387726 : Nat := 4983230072969 + 3 ^ 40 * 7387726 * 2
def baseEnd_7387726 : Nat := 3793454381717867721749473

theorem tailTrace_7387726 : CollatzResearch.WordTrace tailWord_7387726 prefixEnd_7387726 3793454381717867721749473 := by
  unfold tailWord_7387726
  simp only [CollatzResearch.WordTrace]
  refine ⟨33681562954192237499374879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179635002422358599996666021 33681562954192237499374879)
  ·
    refine ⟨50522344431288356249062319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33681562954192237499374879 50522344431288356249062319)
    ·
      refine ⟨75783516646932534373593479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50522344431288356249062319 75783516646932534373593479)
      ·
        refine ⟨113675274970398801560390219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75783516646932534373593479 113675274970398801560390219)
        ·
          refine ⟨170512912455598202340585329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113675274970398801560390219 170512912455598202340585329)
          ·
            refine ⟨127884684341698651755438997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170512912455598202340585329 127884684341698651755438997)
            ·
              refine ⟨5994594578517124301036203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127884684341698651755438997 5994594578517124301036203)
              ·
                refine ⟨8991891867775686451554305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5994594578517124301036203 8991891867775686451554305)
                ·
                  refine ⟨6743918900831764838665729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8991891867775686451554305 6743918900831764838665729)
                  ·
                    refine ⟨5057939175623823628999297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6743918900831764838665729 5057939175623823628999297)
                    ·
                      refine ⟨3793454381717867721749473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5057939175623823628999297 3793454381717867721749473)
                      ·
                        rfl

theorem cell23_7387726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_7387726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387726 prefixEnd_7387726 := by exact prefixLift 7387726
  have htrace : WordTrace (prefixWord ++ tailWord_7387726) baseStart_7387726 baseEnd_7387726 := by
    simpa [prefixWord, tailWord_7387726, baseEnd_7387726] using wordTrace_append hprefix tailTrace_7387726
  have hstable : (prefixWord ++ tailWord_7387726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387726).length < 2 ^ (prefixWord ++ tailWord_7387726).sum := by decide
  have hdescent : baseEnd_7387726 < baseStart_7387726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387728 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 1, 7]
def baseStart_7387728 : Nat := 118140960795 + 7387728 * 2 ^ 59
def prefixEnd_7387728 : Nat := 4983230072969 + 3 ^ 40 * 7387728 * 2
def baseEnd_7387728 : Nat := 1264485136226392237974821

theorem tailTrace_7387728 : CollatzResearch.WordTrace tailWord_7387728 prefixEnd_7387728 1264485136226392237974821 := by
  unfold tailWord_7387728
  simp only [CollatzResearch.WordTrace]
  refine ⟨134726288289765327168285919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179635051053020436224381225 134726288289765327168285919)
  ·
    refine ⟨202089432434647990752428879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134726288289765327168285919 202089432434647990752428879)
    ·
      refine ⟨303134148651971986128643319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202089432434647990752428879 303134148651971986128643319)
      ·
        refine ⟨454701222977957979192964979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303134148651971986128643319 454701222977957979192964979)
        ·
          refine ⟨682051834466936968789447469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454701222977957979192964979 682051834466936968789447469)
          ·
            refine ⟨255769437925101363296042801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 682051834466936968789447469 255769437925101363296042801)
            ·
              refine ⟨191827078443826022472032101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255769437925101363296042801 191827078443826022472032101)
              ·
                refine ⟨35967577208217379213506019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191827078443826022472032101 35967577208217379213506019)
                ·
                  refine ⟨53951365812326068820259029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35967577208217379213506019 53951365812326068820259029)
                  ·
                    refine ⟨1264485136226392237974821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53951365812326068820259029 1264485136226392237974821)
                    ·
                      rfl

theorem cell23_7387728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 1, 7].length) (baseStart_7387728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387728 prefixEnd_7387728 := by exact prefixLift 7387728
  have htrace : WordTrace (prefixWord ++ tailWord_7387728) baseStart_7387728 baseEnd_7387728 := by
    simpa [prefixWord, tailWord_7387728, baseEnd_7387728] using wordTrace_append hprefix tailTrace_7387728
  have hstable : (prefixWord ++ tailWord_7387728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387728).length < 2 ^ (prefixWord ++ tailWord_7387728).sum := by decide
  have hdescent : baseEnd_7387728 < baseStart_7387728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387745 : List Nat := [1, 2, 3, 1, 1, 4, 1, 3, 2, 5]
def baseStart_7387745 : Nat := 118140960795 + 7387745 * 2 ^ 59
def prefixEnd_7387745 : Nat := 4983230072969 + 3 ^ 40 * 7387745 * 2
def baseEnd_7387745 : Nat := 1264488045950101049137295

theorem tailTrace_7387745 : CollatzResearch.WordTrace tailWord_7387745 prefixEnd_7387745 1264488045950101049137295 := by
  unfold tailWord_7387745
  simp only [CollatzResearch.WordTrace]
  refine ⟨269453196620469066239940689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179635464413646044159960459 269453196620469066239940689)
  ·
    refine ⟨202089897465351799679955517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269453196620469066239940689 202089897465351799679955517)
    ·
      refine ⟨75783711549506924879983319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202089897465351799679955517 75783711549506924879983319)
      ·
        refine ⟨113675567324260387319974979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75783711549506924879983319 113675567324260387319974979)
        ·
          refine ⟨170513350986390580979962469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113675567324260387319974979 170513350986390580979962469)
          ·
            refine ⟨31971253309948233933742963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170513350986390580979962469 31971253309948233933742963)
            ·
              refine ⟨47956879964922350900614445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31971253309948233933742963 47956879964922350900614445)
              ·
                refine ⟨17983829986845881587730417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47956879964922350900614445 17983829986845881587730417)
                ·
                  refine ⟨13487872490134411190797813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17983829986845881587730417 13487872490134411190797813)
                  ·
                    refine ⟨1264488045950101049137295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13487872490134411190797813 1264488045950101049137295)
                    ·
                      rfl

theorem cell23_7387745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_7387745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387745 prefixEnd_7387745 := by exact prefixLift 7387745
  have htrace : WordTrace (prefixWord ++ tailWord_7387745) baseStart_7387745 baseEnd_7387745 := by
    simpa [prefixWord, tailWord_7387745, baseEnd_7387745] using wordTrace_append hprefix tailTrace_7387745
  have hstable : (prefixWord ++ tailWord_7387745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387745).length < 2 ^ (prefixWord ++ tailWord_7387745).sum := by decide
  have hdescent : baseEnd_7387745 < baseStart_7387745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387785 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 1, 4, 3]
def baseStart_7387785 : Nat := 118140960795 + 7387785 * 2 ^ 59
def prefixEnd_7387785 : Nat := 4983230072969 + 3 ^ 40 * 7387785 * 2
def baseEnd_7387785 : Nat := 3793484677076482990911701

theorem tailTrace_7387785 : CollatzResearch.WordTrace tailWord_7387785 prefixEnd_7387785 3793484677076482990911701 := by
  unfold tailWord_7387785
  simp only [CollatzResearch.WordTrace]
  refine ⟨269454655540324153071396809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179636437026882768714264539 269454655540324153071396809)
  ·
    refine ⟨202090991655243114803547607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269454655540324153071396809 202090991655243114803547607)
    ·
      refine ⟨303136487482864672205321411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202090991655243114803547607 303136487482864672205321411)
      ·
        refine ⟨454704731224297008307982117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303136487482864672205321411 454704731224297008307982117)
        ·
          refine ⟨85257137104555689057746647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 454704731224297008307982117 85257137104555689057746647)
          ·
            refine ⟨127885705656833533586619971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85257137104555689057746647 127885705656833533586619971)
            ·
              refine ⟨191828558485250300379929957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127885705656833533586619971 191828558485250300379929957)
              ·
                refine ⟨35967854715984431321236867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191828558485250300379929957 35967854715984431321236867)
                ·
                  refine ⟨53951782073976646981855301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35967854715984431321236867 53951782073976646981855301)
                  ·
                    refine ⟨10115959138870621309097869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53951782073976646981855301 10115959138870621309097869)
                    ·
                      refine ⟨3793484677076482990911701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10115959138870621309097869 3793484677076482990911701)
                      ·
                        rfl

theorem cell23_7387785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 4, 3].length) (baseStart_7387785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387785 prefixEnd_7387785 := by exact prefixLift 7387785
  have htrace : WordTrace (prefixWord ++ tailWord_7387785) baseStart_7387785 baseEnd_7387785 := by
    simpa [prefixWord, tailWord_7387785, baseEnd_7387785] using wordTrace_append hprefix tailTrace_7387785
  have hstable : (prefixWord ++ tailWord_7387785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387785).length < 2 ^ (prefixWord ++ tailWord_7387785).sum := by decide
  have hdescent : baseEnd_7387785 < baseStart_7387785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387860 : List Nat := [2, 4, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_7387860 : Nat := 118140960795 + 7387860 * 2 ^ 59
def prefixEnd_7387860 : Nat := 4983230072969 + 3 ^ 40 * 7387860 * 2
def baseEnd_7387860 : Nat := 1264507729375190065824619

theorem tailTrace_7387860 : CollatzResearch.WordTrace tailWord_7387860 prefixEnd_7387860 1264507729375190065824619 := by
  unfold tailWord_7387860
  simp only [CollatzResearch.WordTrace]
  refine ⟨134728695507526220440188517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179638260676701627253584689 134728695507526220440188517)
  ·
    refine ⟨25261630407661166332535347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134728695507526220440188517 25261630407661166332535347)
    ·
      refine ⟨37892445611491749498803021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25261630407661166332535347 37892445611491749498803021)
      ·
        refine ⟨14209667104309406062051133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37892445611491749498803021 14209667104309406062051133)
        ·
          refine ⟨5328625164116027273269175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14209667104309406062051133 5328625164116027273269175)
          ·
            refine ⟨7992937746174040909903763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5328625164116027273269175 7992937746174040909903763)
            ·
              refine ⟨11989406619261061364855645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7992937746174040909903763 11989406619261061364855645)
              ·
                refine ⟨4496027482222898011820867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11989406619261061364855645 4496027482222898011820867)
                ·
                  refine ⟨6744041223334347017731301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4496027482222898011820867 6744041223334347017731301)
                  ·
                    refine ⟨1264507729375190065824619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6744041223334347017731301 1264507729375190065824619)
                    ·
                      rfl

theorem cell23_7387860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_7387860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387860 prefixEnd_7387860 := by exact prefixLift 7387860
  have htrace : WordTrace (prefixWord ++ tailWord_7387860) baseStart_7387860 baseEnd_7387860 := by
    simpa [prefixWord, tailWord_7387860, baseEnd_7387860] using wordTrace_append hprefix tailTrace_7387860
  have hstable : (prefixWord ++ tailWord_7387860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387860).length < 2 ^ (prefixWord ++ tailWord_7387860).sum := by decide
  have hdescent : baseEnd_7387860 < baseStart_7387860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387865 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 3, 6]
def baseStart_7387865 : Nat := 118140960795 + 7387865 * 2 ^ 59
def prefixEnd_7387865 : Nat := 4983230072969 + 3 ^ 40 * 7387865 * 2
def baseEnd_7387865 : Nat := 1264508585176280892637111

theorem tailTrace_7387865 : CollatzResearch.WordTrace tailWord_7387865 prefixEnd_7387865 1264508585176280892637111 := by
  unfold tailWord_7387865
  simp only [CollatzResearch.WordTrace]
  refine ⟨269457573380034326734309049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179638382253356217822872699 269457573380034326734309049)
  ·
    refine ⟨202093180035025745050731787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269457573380034326734309049 202093180035025745050731787)
    ·
      refine ⟨303139770052538617576097681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202093180035025745050731787 303139770052538617576097681)
      ·
        refine ⟨227354827539403963182073261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303139770052538617576097681 227354827539403963182073261)
        ·
          refine ⟨85258060327276486193277473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227354827539403963182073261 85258060327276486193277473)
          ·
            refine ⟨63943545245457364644958105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85258060327276486193277473 63943545245457364644958105)
            ·
              refine ⟨47957658934093023483718579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63943545245457364644958105 47957658934093023483718579)
              ·
                refine ⟨71936488401139535225577869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47957658934093023483718579 71936488401139535225577869)
                ·
                  refine ⟨26976183150427325709591701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71936488401139535225577869 26976183150427325709591701)
                  ·
                    refine ⟨1264508585176280892637111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26976183150427325709591701 1264508585176280892637111)
                    ·
                      rfl

theorem cell23_7387865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 6].length) (baseStart_7387865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387865 prefixEnd_7387865 := by exact prefixLift 7387865
  have htrace : WordTrace (prefixWord ++ tailWord_7387865) baseStart_7387865 baseEnd_7387865 := by
    simpa [prefixWord, tailWord_7387865, baseEnd_7387865] using wordTrace_append hprefix tailTrace_7387865
  have hstable : (prefixWord ++ tailWord_7387865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387865).length < 2 ^ (prefixWord ++ tailWord_7387865).sum := by decide
  have hdescent : baseEnd_7387865 < baseStart_7387865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387906 : List Nat := [3, 4, 1, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_7387906 : Nat := 118140960795 + 7387906 * 2 ^ 59
def prefixEnd_7387906 : Nat := 4983230072969 + 3 ^ 40 * 7387906 * 2
def baseEnd_7387906 : Nat := 3793546808235677017498645

theorem tailTrace_7387906 : CollatzResearch.WordTrace tailWord_7387906 prefixEnd_7387906 3793546808235677017498645 := by
  unfold tailWord_7387906
  simp only [CollatzResearch.WordTrace]
  refine ⟨67364767193221447684137893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179639379181923860491034381 67364767193221447684137893)
  ·
    refine ⟨12630893848729021440775855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67364767193221447684137893 12630893848729021440775855)
    ·
      refine ⟨18946340773093532161163783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12630893848729021440775855 18946340773093532161163783)
      ·
        refine ⟨28419511159640298241745675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18946340773093532161163783 28419511159640298241745675)
        ·
          refine ⟨42629266739460447362618513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28419511159640298241745675 42629266739460447362618513)
          ·
            refine ⟨31971950054595335521963885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42629266739460447362618513 31971950054595335521963885)
            ·
              refine ⟨11989481270473250820736457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31971950054595335521963885 11989481270473250820736457)
              ·
                refine ⟨8992110952854938115552343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11989481270473250820736457 8992110952854938115552343)
                ·
                  refine ⟨13488166429282407173328515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8992110952854938115552343 13488166429282407173328515)
                  ·
                    refine ⟨20232249643923610759992773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13488166429282407173328515 20232249643923610759992773)
                    ·
                      refine ⟨3793546808235677017498645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20232249643923610759992773 3793546808235677017498645)
                      ·
                        rfl

theorem cell23_7387906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_7387906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387906 prefixEnd_7387906 := by exact prefixLift 7387906
  have htrace : WordTrace (prefixWord ++ tailWord_7387906) baseStart_7387906 baseEnd_7387906 := by
    simpa [prefixWord, tailWord_7387906, baseEnd_7387906] using wordTrace_append hprefix tailTrace_7387906
  have hstable : (prefixWord ++ tailWord_7387906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387906).length < 2 ^ (prefixWord ++ tailWord_7387906).sum := by decide
  have hdescent : baseEnd_7387906 < baseStart_7387906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387933 : List Nat := [1, 4, 2, 4, 1, 1, 2, 2, 2, 4]
def baseStart_7387933 : Nat := 118140960795 + 7387933 * 2 ^ 59
def prefixEnd_7387933 : Nat := 4983230072969 + 3 ^ 40 * 7387933 * 2
def baseEnd_7387933 : Nat := 1264520224071116137287007

theorem tailTrace_7387933 : CollatzResearch.WordTrace tailWord_7387933 prefixEnd_7387933 1264520224071116137287007 := by
  unfold tailWord_7387933
  simp only [CollatzResearch.WordTrace]
  refine ⟨269460053543787974347784453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179640035695858649565189635 269460053543787974347784453)
  ·
    refine ⟨50523760039460245190209585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269460053543787974347784453 50523760039460245190209585)
    ·
      refine ⟨37892820029595183892657189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50523760039460245190209585 37892820029595183892657189)
      ·
        refine ⟨7104903755549096979873223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37892820029595183892657189 7104903755549096979873223)
        ·
          refine ⟨10657355633323645469809835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7104903755549096979873223 10657355633323645469809835)
          ·
            refine ⟨15986033449985468204714753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10657355633323645469809835 15986033449985468204714753)
            ·
              refine ⟨11989525087489101153536065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15986033449985468204714753 11989525087489101153536065)
              ·
                refine ⟨8992143815616825865152049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11989525087489101153536065 8992143815616825865152049)
                ·
                  refine ⟨6744107861712619398864037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8992143815616825865152049 6744107861712619398864037)
                  ·
                    refine ⟨1264520224071116137287007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6744107861712619398864037 1264520224071116137287007)
                    ·
                      rfl

theorem cell23_7387933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_7387933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387933 prefixEnd_7387933 := by exact prefixLift 7387933
  have htrace : WordTrace (prefixWord ++ tailWord_7387933) baseStart_7387933 baseEnd_7387933 := by
    simpa [prefixWord, tailWord_7387933, baseEnd_7387933] using wordTrace_append hprefix tailTrace_7387933
  have hstable : (prefixWord ++ tailWord_7387933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387933).length < 2 ^ (prefixWord ++ tailWord_7387933).sum := by decide
  have hdescent : baseEnd_7387933 < baseStart_7387933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387940 : List Nat := [2, 3, 1, 3, 3, 1, 1, 4, 1, 2, 2]
def baseStart_7387940 : Nat := 118140960795 + 7387940 * 2 ^ 59
def prefixEnd_7387940 : Nat := 4983230072969 + 3 ^ 40 * 7387940 * 2
def baseEnd_7387940 : Nat := 3793564266577929884473489

theorem tailTrace_7387940 : CollatzResearch.WordTrace tailWord_7387940 prefixEnd_7387940 3793564266577929884473489 := by
  unfold tailWord_7387940
  simp only [CollatzResearch.WordTrace]
  refine ⟨134730154427381307271644637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179640205903175076362192849 134730154427381307271644637)
  ·
    refine ⟨50523807910267990226866739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134730154427381307271644637 50523807910267990226866739)
    ·
      refine ⟨75785711865401985340300109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50523807910267990226866739 75785711865401985340300109)
      ·
        refine ⟨28419641949525744502612541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75785711865401985340300109 28419641949525744502612541)
        ·
          refine ⟨10657365731072154188479703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28419641949525744502612541 10657365731072154188479703)
          ·
            refine ⟨15986048596608231282719555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10657365731072154188479703 15986048596608231282719555)
            ·
              refine ⟨23979072894912346924079333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15986048596608231282719555 23979072894912346924079333)
              ·
                refine ⟨4496076167796065048264875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23979072894912346924079333 4496076167796065048264875)
                ·
                  refine ⟨6744114251694097572397313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4496076167796065048264875 6744114251694097572397313)
                  ·
                    refine ⟨5058085688770573179297985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6744114251694097572397313 5058085688770573179297985)
                    ·
                      refine ⟨3793564266577929884473489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5058085688770573179297985 3793564266577929884473489)
                      ·
                        rfl

theorem cell23_7387940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_7387940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387940 prefixEnd_7387940 := by exact prefixLift 7387940
  have htrace : WordTrace (prefixWord ++ tailWord_7387940) baseStart_7387940 baseEnd_7387940 := by
    simpa [prefixWord, tailWord_7387940, baseEnd_7387940] using wordTrace_append hprefix tailTrace_7387940
  have hstable : (prefixWord ++ tailWord_7387940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387940).length < 2 ^ (prefixWord ++ tailWord_7387940).sum := by decide
  have hdescent : baseEnd_7387940 < baseStart_7387940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387946 : List Nat := [3, 1, 4, 3, 1, 2, 1, 8]
def baseStart_7387946 : Nat := 118140960795 + 7387946 * 2 ^ 59
def prefixEnd_7387946 : Nat := 4983230072969 + 3 ^ 40 * 7387946 * 2
def baseEnd_7387946 : Nat := 140502494350439142999943

theorem tailTrace_7387946 : CollatzResearch.WordTrace tailWord_7387946 prefixEnd_7387946 140502494350439142999943 := by
  unfold tailWord_7387946
  simp only [CollatzResearch.WordTrace]
  refine ⟨67365131923185219392001923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179640351795160585045338461 67365131923185219392001923)
  ·
    refine ⟨101047697884777829088002885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67365131923185219392001923 101047697884777829088002885)
    ·
      refine ⟨18946443353395842954000541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101047697884777829088002885 18946443353395842954000541)
      ·
        refine ⟨7104916257523441107750203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18946443353395842954000541 7104916257523441107750203)
        ·
          refine ⟨10657374386285161661625305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7104916257523441107750203 10657374386285161661625305)
          ·
            refine ⟨7993030789713871246218979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10657374386285161661625305 7993030789713871246218979)
            ·
              refine ⟨11989546184570806869328469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7993030789713871246218979 11989546184570806869328469)
              ·
                refine ⟨140502494350439142999943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11989546184570806869328469 140502494350439142999943)
                ·
                  rfl

theorem cell23_7387946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 8].length) (baseStart_7387946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387946 prefixEnd_7387946 := by exact prefixLift 7387946
  have htrace : WordTrace (prefixWord ++ tailWord_7387946) baseStart_7387946 baseEnd_7387946 := by
    simpa [prefixWord, tailWord_7387946, baseEnd_7387946] using wordTrace_append hprefix tailTrace_7387946
  have hstable : (prefixWord ++ tailWord_7387946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387946).length < 2 ^ (prefixWord ++ tailWord_7387946).sum := by decide
  have hdescent : baseEnd_7387946 < baseStart_7387946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387974 : List Nat := [6, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_7387974 : Nat := 118140960795 + 7387974 * 2 ^ 59
def prefixEnd_7387974 : Nat := 4983230072969 + 3 ^ 40 * 7387974 * 2
def baseEnd_7387974 : Nat := 3793581724920182751448333

theorem tailTrace_7387974 : CollatzResearch.WordTrace tailWord_7387974 prefixEnd_7387974 3793581724920182751448333 := by
  unfold tailWord_7387974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8420673404269982448438343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 179641032624426292233351317 8420673404269982448438343)
  ·
    refine ⟨12631010106404973672657515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8420673404269982448438343 12631010106404973672657515)
    ·
      refine ⟨18946515159607460508986273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12631010106404973672657515 18946515159607460508986273)
      ·
        refine ⟨14209886369705595381739705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18946515159607460508986273 14209886369705595381739705)
        ·
          refine ⟨10657414777279196536304779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14209886369705595381739705 10657414777279196536304779)
          ·
            refine ⟨15986122165918794804457169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10657414777279196536304779 15986122165918794804457169)
            ·
              refine ⟨11989591624439096103342877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15986122165918794804457169 11989591624439096103342877)
              ·
                refine ⟨4496096859164661038753579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11989591624439096103342877 4496096859164661038753579)
                ·
                  refine ⟨6744145288746991558130369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4496096859164661038753579 6744145288746991558130369)
                  ·
                    refine ⟨5058108966560243668597777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6744145288746991558130369 5058108966560243668597777)
                    ·
                      refine ⟨3793581724920182751448333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5058108966560243668597777 3793581724920182751448333)
                      ·
                        rfl

theorem cell23_7387974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_7387974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387974 prefixEnd_7387974 := by exact prefixLift 7387974
  have htrace : WordTrace (prefixWord ++ tailWord_7387974) baseStart_7387974 baseEnd_7387974 := by
    simpa [prefixWord, tailWord_7387974, baseEnd_7387974] using wordTrace_append hprefix tailTrace_7387974
  have hstable : (prefixWord ++ tailWord_7387974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387974).length < 2 ^ (prefixWord ++ tailWord_7387974).sum := by decide
  have hdescent : baseEnd_7387974 < baseStart_7387974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7387982 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_7387982 : Nat := 118140960795 + 7387982 * 2 ^ 59
def prefixEnd_7387982 : Nat := 4983230072969 + 3 ^ 40 * 7387982 * 2
def baseEnd_7387982 : Nat := 3793585832765418720148295

theorem tailTrace_7387982 : CollatzResearch.WordTrace tailWord_7387982 prefixEnd_7387982 3793585832765418720148295 := by
  unfold tailWord_7387982
  simp only [CollatzResearch.WordTrace]
  refine ⟨33682730090076306964539775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179641227147073637144212133 33682730090076306964539775)
  ·
    refine ⟨50524095135114460446809663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33682730090076306964539775 50524095135114460446809663)
    ·
      refine ⟨75786142702671690670214495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50524095135114460446809663 75786142702671690670214495)
      ·
        refine ⟨113679214054007536005321743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75786142702671690670214495 113679214054007536005321743)
        ·
          refine ⟨170518821081011304007982615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113679214054007536005321743 170518821081011304007982615)
          ·
            refine ⟨255778231621516956011973923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170518821081011304007982615 255778231621516956011973923)
            ·
              refine ⟨383667347432275434017960885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255778231621516956011973923 383667347432275434017960885)
              ·
                refine ⟨35968813821775821939183833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 383667347432275434017960885 35968813821775821939183833)
                ·
                  refine ⟨26976610366331866454387875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35968813821775821939183833 26976610366331866454387875)
                  ·
                    refine ⟨40464915549497799681581813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26976610366331866454387875 40464915549497799681581813)
                    ·
                      refine ⟨3793585832765418720148295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40464915549497799681581813 3793585832765418720148295)
                      ·
                        rfl

theorem cell23_7387982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_7387982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7387982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7387982 prefixEnd_7387982 := by exact prefixLift 7387982
  have htrace : WordTrace (prefixWord ++ tailWord_7387982) baseStart_7387982 baseEnd_7387982 := by
    simpa [prefixWord, tailWord_7387982, baseEnd_7387982] using wordTrace_append hprefix tailTrace_7387982
  have hstable : (prefixWord ++ tailWord_7387982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7387982).length < 2 ^ (prefixWord ++ tailWord_7387982).sum := by decide
  have hdescent : baseEnd_7387982 < baseStart_7387982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7387982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388082 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_7388082 : Nat := 118140960795 + 7388082 * 2 ^ 59
def prefixEnd_7388082 : Nat := 4983230072969 + 3 ^ 40 * 7388082 * 2
def baseEnd_7388082 : Nat := 3793637180830868328897835

theorem tailTrace_7388082 : CollatzResearch.WordTrace tailWord_7388082 prefixEnd_7388082 3793637180830868328897835 := by
  unfold tailWord_7388082
  simp only [CollatzResearch.WordTrace]
  refine ⟨67366372005062043198739625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179643658680165448529972333 67366372005062043198739625)
  ·
    refine ⟨50524779003796532399054719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67366372005062043198739625 50524779003796532399054719)
    ·
      refine ⟨75787168505694798598582079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50524779003796532399054719 75787168505694798598582079)
      ·
        refine ⟨113680752758542197897873119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75787168505694798598582079 113680752758542197897873119)
        ·
          refine ⟨170521129137813296846809679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113680752758542197897873119 170521129137813296846809679)
          ·
            refine ⟨255781693706719945270214519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170521129137813296846809679 255781693706719945270214519)
            ·
              refine ⟨383672540560079917905321779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255781693706719945270214519 383672540560079917905321779)
              ·
                refine ⟨575508810840119876857982669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383672540560079917905321779 575508810840119876857982669)
                ·
                  refine ⟨215815804065044953821743501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 575508810840119876857982669 215815804065044953821743501)
                  ·
                    refine ⟨80930926524391857683153813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 215815804065044953821743501 80930926524391857683153813)
                    ·
                      refine ⟨3793637180830868328897835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80930926524391857683153813 3793637180830868328897835)
                      ·
                        rfl

theorem cell23_7388082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_7388082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388082 prefixEnd_7388082 := by exact prefixLift 7388082
  have htrace : WordTrace (prefixWord ++ tailWord_7388082) baseStart_7388082 baseEnd_7388082 := by
    simpa [prefixWord, tailWord_7388082, baseEnd_7388082] using wordTrace_append hprefix tailTrace_7388082
  have hstable : (prefixWord ++ tailWord_7388082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388082).length < 2 ^ (prefixWord ++ tailWord_7388082).sum := by decide
  have hdescent : baseEnd_7388082 < baseStart_7388082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388112 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 6]
def baseStart_7388112 : Nat := 118140960795 + 7388112 * 2 ^ 59
def prefixEnd_7388112 : Nat := 4983230072969 + 3 ^ 40 * 7388112 * 2
def baseEnd_7388112 : Nat := 3793652585250503211522697

theorem tailTrace_7388112 : CollatzResearch.WordTrace tailWord_7388112 prefixEnd_7388112 3793652585250503211522697 := by
  unfold tailWord_7388112
  simp only [CollatzResearch.WordTrace]
  refine ⟨134733291105069743959275295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179644388140092991945700393 134733291105069743959275295)
  ·
    refine ⟨202099936657604615938912943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134733291105069743959275295 202099936657604615938912943)
    ·
      refine ⟨303149904986406923908369415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202099936657604615938912943 303149904986406923908369415)
      ·
        refine ⟨454724857479610385862554123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303149904986406923908369415 454724857479610385862554123)
        ·
          refine ⟨682087286219415578793831185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454724857479610385862554123 682087286219415578793831185)
          ·
            refine ⟨511565464664561684095373389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682087286219415578793831185 511565464664561684095373389)
            ·
              refine ⟨191837049249210631535765021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 511565464664561684095373389 191837049249210631535765021)
              ·
                refine ⟨71938893468453986825911883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191837049249210631535765021 71938893468453986825911883)
                ·
                  refine ⟨107908340202680980238867825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71938893468453986825911883 107908340202680980238867825)
                  ·
                    refine ⟨80931255152010735179150869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107908340202680980238867825 80931255152010735179150869)
                    ·
                      refine ⟨3793652585250503211522697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80931255152010735179150869 3793652585250503211522697)
                      ·
                        rfl

theorem cell23_7388112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_7388112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388112 prefixEnd_7388112 := by exact prefixLift 7388112
  have htrace : WordTrace (prefixWord ++ tailWord_7388112) baseStart_7388112 baseEnd_7388112 := by
    simpa [prefixWord, tailWord_7388112, baseEnd_7388112] using wordTrace_append hprefix tailTrace_7388112
  have hstable : (prefixWord ++ tailWord_7388112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388112).length < 2 ^ (prefixWord ++ tailWord_7388112).sum := by decide
  have hdescent : baseEnd_7388112 < baseStart_7388112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388136 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_7388136 : Nat := 118140960795 + 7388136 * 2 ^ 59
def prefixEnd_7388136 : Nat := 4983230072969 + 3 ^ 40 * 7388136 * 2
def baseEnd_7388136 : Nat := 3793664908786211117622587

theorem tailTrace_7388136 : CollatzResearch.WordTrace tailWord_7388136 prefixEnd_7388136 3793664908786211117622587 := by
  unfold tailWord_7388136
  simp only [CollatzResearch.WordTrace]
  refine ⟨134733728781026270008712131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179644971708035026678282841 134733728781026270008712131)
  ·
    refine ⟨202100593171539405013068197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134733728781026270008712131 202100593171539405013068197)
    ·
      refine ⟨37893861219663638439950287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202100593171539405013068197 37893861219663638439950287)
      ·
        refine ⟨56840791829495457659925431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37893861219663638439950287 56840791829495457659925431)
        ·
          refine ⟨85261187744243186489888147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56840791829495457659925431 85261187744243186489888147)
          ·
            refine ⟨127891781616364779734832221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85261187744243186489888147 127891781616364779734832221)
            ·
              refine ⟨47959418106136792400562083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127891781616364779734832221 47959418106136792400562083)
              ·
                refine ⟨71939127159205188600843125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47959418106136792400562083 71939127159205188600843125)
                ·
                  refine ⟨6744293171175486431329043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71939127159205188600843125 6744293171175486431329043)
                  ·
                    refine ⟨10116439756763229646993565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6744293171175486431329043 10116439756763229646993565)
                    ·
                      refine ⟨3793664908786211117622587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10116439756763229646993565 3793664908786211117622587)
                      ·
                        rfl

theorem cell23_7388136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_7388136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388136 prefixEnd_7388136 := by exact prefixLift 7388136
  have htrace : WordTrace (prefixWord ++ tailWord_7388136) baseStart_7388136 baseEnd_7388136 := by
    simpa [prefixWord, tailWord_7388136, baseEnd_7388136] using wordTrace_append hprefix tailTrace_7388136
  have hstable : (prefixWord ++ tailWord_7388136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388136).length < 2 ^ (prefixWord ++ tailWord_7388136).sum := by decide
  have hdescent : baseEnd_7388136 < baseStart_7388136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388156 : List Nat := [2, 2, 2, 1, 2, 4, 1, 3, 1, 5]
def baseStart_7388156 : Nat := 118140960795 + 7388156 * 2 ^ 59
def prefixEnd_7388156 : Nat := 4983230072969 + 3 ^ 40 * 7388156 * 2
def baseEnd_7388156 : Nat := 1264558392799767013124165

theorem tailTrace_7388156 : CollatzResearch.WordTrace tailWord_7388156 prefixEnd_7388156 1264558392799767013124165 := by
  unfold tailWord_7388156
  simp only [CollatzResearch.WordTrace]
  refine ⟨134734093510990041716576161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179645458014653388955434881 134734093510990041716576161)
  ·
    refine ⟨101050570133242531287432121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134734093510990041716576161 101050570133242531287432121)
    ·
      refine ⟨75787927599931898465574091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101050570133242531287432121 75787927599931898465574091)
      ·
        refine ⟨113681891399897847698361137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75787927599931898465574091 113681891399897847698361137)
        ·
          refine ⟨85261418549923385773770853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113681891399897847698361137 85261418549923385773770853)
          ·
            refine ⟨15986515978110634832582035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85261418549923385773770853 15986515978110634832582035)
            ·
              refine ⟨23979773967165952248873053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15986515978110634832582035 23979773967165952248873053)
              ·
                refine ⟨8992415237687232093327395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23979773967165952248873053 8992415237687232093327395)
                ·
                  refine ⟨13488622856530848139991093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8992415237687232093327395 13488622856530848139991093)
                  ·
                    refine ⟨1264558392799767013124165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13488622856530848139991093 1264558392799767013124165)
                    ·
                      rfl

theorem cell23_7388156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_7388156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388156 prefixEnd_7388156 := by exact prefixLift 7388156
  have htrace : WordTrace (prefixWord ++ tailWord_7388156) baseStart_7388156 baseEnd_7388156 := by
    simpa [prefixWord, tailWord_7388156, baseEnd_7388156] using wordTrace_append hprefix tailTrace_7388156
  have hstable : (prefixWord ++ tailWord_7388156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388156).length < 2 ^ (prefixWord ++ tailWord_7388156).sum := by decide
  have hdescent : baseEnd_7388156 < baseStart_7388156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388170 : List Nat := [3, 1, 2, 2, 3, 1, 2, 4, 1, 1, 3]
def baseStart_7388170 : Nat := 118140960795 + 7388170 * 2 ^ 59
def prefixEnd_7388170 : Nat := 4983230072969 + 3 ^ 40 * 7388170 * 2
def baseEnd_7388170 : Nat := 3793682367128463984597431

theorem tailTrace_7388170 : CollatzResearch.WordTrace tailWord_7388170 prefixEnd_7388170 3793682367128463984597431 := by
  unfold tailWord_7388170
  simp only [CollatzResearch.WordTrace]
  refine ⟨67367174410982340956040491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179645798429286242549441309 67367174410982340956040491)
  ·
    refine ⟨101050761616473511434060737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67367174410982340956040491 101050761616473511434060737)
    ·
      refine ⟨75788071212355133575545553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101050761616473511434060737 75788071212355133575545553)
      ·
        refine ⟨56841053409266350181659165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75788071212355133575545553 56841053409266350181659165)
        ·
          refine ⟨21315395028474881318122187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56841053409266350181659165 21315395028474881318122187)
          ·
            refine ⟨31973092542712321977183281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21315395028474881318122187 31973092542712321977183281)
            ·
              refine ⟨23979819407034241482887461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31973092542712321977183281 23979819407034241482887461)
              ·
                refine ⟨4496216138818920278041399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23979819407034241482887461 4496216138818920278041399)
                ·
                  refine ⟨6744324208228380417062099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4496216138818920278041399 6744324208228380417062099)
                  ·
                    refine ⟨10116486312342570625593149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6744324208228380417062099 10116486312342570625593149)
                    ·
                      refine ⟨3793682367128463984597431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10116486312342570625593149 3793682367128463984597431)
                      ·
                        rfl

theorem cell23_7388170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_7388170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388170 prefixEnd_7388170 := by exact prefixLift 7388170
  have htrace : WordTrace (prefixWord ++ tailWord_7388170) baseStart_7388170 baseEnd_7388170 := by
    simpa [prefixWord, tailWord_7388170, baseEnd_7388170] using wordTrace_append hprefix tailTrace_7388170
  have hstable : (prefixWord ++ tailWord_7388170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388170).length < 2 ^ (prefixWord ++ tailWord_7388170).sum := by decide
  have hdescent : baseEnd_7388170 < baseStart_7388170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388193 : List Nat := [1, 2, 3, 2, 3, 2, 2, 2, 1, 1, 4]
def baseStart_7388193 : Nat := 118140960795 + 7388193 * 2 ^ 59
def prefixEnd_7388193 : Nat := 4983230072969 + 3 ^ 40 * 7388193 * 2
def baseEnd_7388193 : Nat := 3793694177183517394609825

theorem tailTrace_7388193 : CollatzResearch.WordTrace tailWord_7388193 prefixEnd_7388193 3793694177183517394609825 := by
  unfold tailWord_7388193
  simp only [CollatzResearch.WordTrace]
  refine ⟨269469536522846038752249233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179646357681897359168166155 269469536522846038752249233)
  ·
    refine ⟨202102152392134529064186925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269469536522846038752249233 202102152392134529064186925)
    ·
      refine ⟨75788307147050448399070097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202102152392134529064186925 75788307147050448399070097)
      ·
        refine ⟨56841230360287836299302573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75788307147050448399070097 56841230360287836299302573)
        ·
          refine ⟨21315461385107938612238465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56841230360287836299302573 21315461385107938612238465)
          ·
            refine ⟨15986596038830953959178849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21315461385107938612238465 15986596038830953959178849)
            ·
              refine ⟨11989947029123215469384137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15986596038830953959178849 11989947029123215469384137)
              ·
                refine ⟨8992460271842411602038103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11989947029123215469384137 8992460271842411602038103)
                ·
                  refine ⟨13488690407763617403057155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8992460271842411602038103 13488690407763617403057155)
                  ·
                    refine ⟨20233035611645426104585733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13488690407763617403057155 20233035611645426104585733)
                    ·
                      refine ⟨3793694177183517394609825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20233035611645426104585733 3793694177183517394609825)
                      ·
                        rfl

theorem cell23_7388193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_7388193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388193 prefixEnd_7388193 := by exact prefixLift 7388193
  have htrace : WordTrace (prefixWord ++ tailWord_7388193) baseStart_7388193 baseEnd_7388193 := by
    simpa [prefixWord, tailWord_7388193, baseEnd_7388193] using wordTrace_append hprefix tailTrace_7388193
  have hstable : (prefixWord ++ tailWord_7388193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388193).length < 2 ^ (prefixWord ++ tailWord_7388193).sum := by decide
  have hdescent : baseEnd_7388193 < baseStart_7388193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388206 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_7388206 : Nat := 118140960795 + 7388206 * 2 ^ 59
def prefixEnd_7388206 : Nat := 4983230072969 + 3 ^ 40 * 7388206 * 2
def baseEnd_7388206 : Nat := 3793700852432025843747265

theorem tailTrace_7388206 : CollatzResearch.WordTrace tailWord_7388206 prefixEnd_7388206 3793700852432025843747265 := by
  unfold tailWord_7388206
  simp only [CollatzResearch.WordTrace]
  refine ⟨33683751333974867746559059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179646673781199294648314981 33683751333974867746559059)
  ·
    refine ⟨50525627000962301619838589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33683751333974867746559059 50525627000962301619838589)
    ·
      refine ⟨18947110125360863107439471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50525627000962301619838589 18947110125360863107439471)
      ·
        refine ⟨28420665188041294661159207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18947110125360863107439471 28420665188041294661159207)
        ·
          refine ⟨42630997782061941991738811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28420665188041294661159207 42630997782061941991738811)
          ·
            refine ⟨63946496673092912987608217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42630997782061941991738811 63946496673092912987608217)
            ·
              refine ⟨47959872504819684740706163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63946496673092912987608217 47959872504819684740706163)
              ·
                refine ⟨71939808757229527111059245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47959872504819684740706163 71939808757229527111059245)
                ·
                  refine ⟨26977428283961072666647217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71939808757229527111059245 26977428283961072666647217)
                  ·
                    refine ⟨20233071212970804499985413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26977428283961072666647217 20233071212970804499985413)
                    ·
                      refine ⟨3793700852432025843747265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20233071212970804499985413 3793700852432025843747265)
                      ·
                        rfl

theorem cell23_7388206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_7388206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388206 prefixEnd_7388206 := by exact prefixLift 7388206
  have htrace : WordTrace (prefixWord ++ tailWord_7388206) baseStart_7388206 baseEnd_7388206 := by
    simpa [prefixWord, tailWord_7388206, baseEnd_7388206] using wordTrace_append hprefix tailTrace_7388206
  have hstable : (prefixWord ++ tailWord_7388206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388206).length < 2 ^ (prefixWord ++ tailWord_7388206).sum := by decide
  have hdescent : baseEnd_7388206 < baseStart_7388206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388227 : List Nat := [1, 1, 1, 3, 1, 2, 7, 2, 1, 2, 2]
def baseStart_7388227 : Nat := 118140960795 + 7388227 * 2 ^ 59
def prefixEnd_7388227 : Nat := 4983230072969 + 3 ^ 40 * 7388227 * 2
def baseEnd_7388227 : Nat := 3793711635525770261584669

theorem tailTrace_7388227 : CollatzResearch.WordTrace tailWord_7388227 prefixEnd_7388227 3793711635525770261584669 := by
  unfold tailWord_7388227
  simp only [CollatzResearch.WordTrace]
  refine ⟨269470776604722862558986935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179647184403148575039324623 269470776604722862558986935)
  ·
    refine ⟨404206164907084293838480403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269470776604722862558986935 404206164907084293838480403)
    ·
      refine ⟨606309247360626440757720605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404206164907084293838480403 606309247360626440757720605)
      ·
        refine ⟨227365967760234915284145227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 606309247360626440757720605 227365967760234915284145227)
        ·
          refine ⟨341048951640352372926217841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227365967760234915284145227 341048951640352372926217841)
          ·
            refine ⟨255786713730264279694663381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341048951640352372926217841 255786713730264279694663381)
            ·
              refine ⟨5995001103053069055343673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 255786713730264279694663381 5995001103053069055343673)
              ·
                refine ⟨4496250827289801791507755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5995001103053069055343673 4496250827289801791507755)
                ·
                  refine ⟨6744376240934702687261633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4496250827289801791507755 6744376240934702687261633)
                  ·
                    refine ⟨5058282180701027015446225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6744376240934702687261633 5058282180701027015446225)
                    ·
                      refine ⟨3793711635525770261584669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5058282180701027015446225 3793711635525770261584669)
                      ·
                        rfl

theorem cell23_7388227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 1, 2, 2].length) (baseStart_7388227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388227 prefixEnd_7388227 := by exact prefixLift 7388227
  have htrace : WordTrace (prefixWord ++ tailWord_7388227) baseStart_7388227 baseEnd_7388227 := by
    simpa [prefixWord, tailWord_7388227, baseEnd_7388227] using wordTrace_append hprefix tailTrace_7388227
  have hstable : (prefixWord ++ tailWord_7388227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388227).length < 2 ^ (prefixWord ++ tailWord_7388227).sum := by decide
  have hdescent : baseEnd_7388227 < baseStart_7388227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388236 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 2, 7, 2]
def baseStart_7388236 : Nat := 118140960795 + 7388236 * 2 ^ 59
def prefixEnd_7388236 : Nat := 4983230072969 + 3 ^ 40 * 7388236 * 2
def baseEnd_7388236 : Nat := 3793716256851660726372127

theorem tailTrace_7388236 : CollatzResearch.WordTrace tailWord_7388236 prefixEnd_7388236 3793716256851660726372127 := by
  unfold tailWord_7388236
  simp only [CollatzResearch.WordTrace]
  refine ⟨134735552430845128548032281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179647403241126838064043041 134735552430845128548032281)
  ·
    refine ⟨101051664323133846411024211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134735552430845128548032281 101051664323133846411024211)
    ·
      refine ⟨151577496484700769616536317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101051664323133846411024211 151577496484700769616536317)
      ·
        refine ⟨56841561181762788606201119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151577496484700769616536317 56841561181762788606201119)
        ·
          refine ⟨85262341772644182909301679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56841561181762788606201119 85262341772644182909301679)
          ·
            refine ⟨127893512658966274363952519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85262341772644182909301679 127893512658966274363952519)
            ·
              refine ⟨191840268988449411545928779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127893512658966274363952519 191840268988449411545928779)
              ·
                refine ⟨287760403482674117318893169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191840268988449411545928779 287760403482674117318893169)
                ·
                  refine ⟨215820302612005587989169877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287760403482674117318893169 215820302612005587989169877)
                  ·
                    refine ⟨5058288342468880968496169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 215820302612005587989169877 5058288342468880968496169)
                    ·
                      refine ⟨3793716256851660726372127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5058288342468880968496169 3793716256851660726372127)
                      ·
                        rfl

theorem cell23_7388236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_7388236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388236 prefixEnd_7388236 := by exact prefixLift 7388236
  have htrace : WordTrace (prefixWord ++ tailWord_7388236) baseStart_7388236 baseEnd_7388236 := by
    simpa [prefixWord, tailWord_7388236, baseEnd_7388236] using wordTrace_append hprefix tailTrace_7388236
  have hstable : (prefixWord ++ tailWord_7388236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388236).length < 2 ^ (prefixWord ++ tailWord_7388236).sum := by decide
  have hdescent : baseEnd_7388236 < baseStart_7388236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388237 : List Nat := [1, 6, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_7388237 : Nat := 118140960795 + 7388237 * 2 ^ 59
def prefixEnd_7388237 : Nat := 4983230072969 + 3 ^ 40 * 7388237 * 2
def baseEnd_7388237 : Nat := 1264572256777438407486541

theorem tailTrace_7388237 : CollatzResearch.WordTrace tailWord_7388237 prefixEnd_7388237 1264572256777438407486541 := by
  unfold tailWord_7388237
  simp only [CollatzResearch.WordTrace]
  refine ⟨269471141334686634266850965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179647427556457756177900643 269471141334686634266850965)
  ·
    refine ⟨12631459750063435981258639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 269471141334686634266850965 12631459750063435981258639)
    ·
      refine ⟨18947189625095153971887959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12631459750063435981258639 18947189625095153971887959)
      ·
        refine ⟨28420784437642730957831939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18947189625095153971887959 28420784437642730957831939)
        ·
          refine ⟨42631176656464096436747909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28420784437642730957831939 42631176656464096436747909)
          ·
            refine ⟨7993345623087018081890233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42631176656464096436747909 7993345623087018081890233)
            ·
              refine ⟨5995009217315263561417675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7993345623087018081890233 5995009217315263561417675)
              ·
                refine ⟨8992513825972895342126513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5995009217315263561417675 8992513825972895342126513)
                ·
                  refine ⟨6744385369479671506594885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8992513825972895342126513 6744385369479671506594885)
                  ·
                    refine ⟨1264572256777438407486541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6744385369479671506594885 1264572256777438407486541)
                    ·
                      rfl

theorem cell23_7388237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_7388237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388237 prefixEnd_7388237 := by exact prefixLift 7388237
  have htrace : WordTrace (prefixWord ++ tailWord_7388237) baseStart_7388237 baseEnd_7388237 := by
    simpa [prefixWord, tailWord_7388237, baseEnd_7388237] using wordTrace_append hprefix tailTrace_7388237
  have hstable : (prefixWord ++ tailWord_7388237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388237).length < 2 ^ (prefixWord ++ tailWord_7388237).sum := by decide
  have hdescent : baseEnd_7388237 < baseStart_7388237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388249 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 4, 3, 4]
def baseStart_7388249 : Nat := 118140960795 + 7388249 * 2 ^ 59
def prefixEnd_7388249 : Nat := 4983230072969 + 3 ^ 40 * 7388249 * 2
def baseEnd_7388249 : Nat := 3793722932100169175509567

theorem tailTrace_7388249 : CollatzResearch.WordTrace tailWord_7388249 prefixEnd_7388249 3793722932100169175509567 := by
  unfold tailWord_7388249
  simp only [CollatzResearch.WordTrace]
  refine ⟨269471579010643160316287801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179647719340428773544191867 269471579010643160316287801)
  ·
    refine ⟨202103684257982370237215851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269471579010643160316287801 202103684257982370237215851)
    ·
      refine ⟨303155526386973555355823777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202103684257982370237215851 303155526386973555355823777)
      ·
        refine ⟨227366644790230166516867833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303155526386973555355823777 227366644790230166516867833)
        ·
          refine ⟨170524983592672624887650875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227366644790230166516867833 170524983592672624887650875)
          ·
            refine ⟨255787475389008937331476313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170524983592672624887650875 255787475389008937331476313)
            ·
              refine ⟨191840606541756702998607235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255787475389008937331476313 191840606541756702998607235)
              ·
                refine ⟨287760909812635054497910853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191840606541756702998607235 287760909812635054497910853)
                ·
                  refine ⟨53955170589869072718358285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 287760909812635054497910853 53955170589869072718358285)
                  ·
                    refine ⟨20233188971200902269384357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53955170589869072718358285 20233188971200902269384357)
                    ·
                      refine ⟨3793722932100169175509567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20233188971200902269384357 3793722932100169175509567)
                      ·
                        rfl

theorem cell23_7388249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_7388249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388249 prefixEnd_7388249 := by exact prefixLift 7388249
  have htrace : WordTrace (prefixWord ++ tailWord_7388249) baseStart_7388249 baseEnd_7388249 := by
    simpa [prefixWord, tailWord_7388249, baseEnd_7388249] using wordTrace_append hprefix tailTrace_7388249
  have hstable : (prefixWord ++ tailWord_7388249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388249).length < 2 ^ (prefixWord ++ tailWord_7388249).sum := by decide
  have hdescent : baseEnd_7388249 < baseStart_7388249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388259 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 4, 6]
def baseStart_7388259 : Nat := 118140960795 + 7388259 * 2 ^ 59
def prefixEnd_7388259 : Nat := 4983230072969 + 3 ^ 40 * 7388259 * 2
def baseEnd_7388259 : Nat := 1264576022302238045461507

theorem tailTrace_7388259 : CollatzResearch.WordTrace tailWord_7388259 prefixEnd_7388259 1264576022302238045461507 := by
  unfold tailWord_7388259
  simp only [CollatzResearch.WordTrace]
  refine ⟨269471943740606932024151831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179647962493737954682767887 269471943740606932024151831)
  ·
    refine ⟨404207915610910398036227747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269471943740606932024151831 404207915610910398036227747)
    ·
      refine ⟨606311873416365597054341621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404207915610910398036227747 606311873416365597054341621)
      ·
        refine ⟨56841738132784274723844527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 606311873416365597054341621 56841738132784274723844527)
        ·
          refine ⟨85262607199176412085766791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56841738132784274723844527 85262607199176412085766791)
          ·
            refine ⟨127893910798764618128650187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85262607199176412085766791 127893910798764618128650187)
            ·
              refine ⟨191840866198146927192975281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127893910798764618128650187 191840866198146927192975281)
              ·
                refine ⟨143880649648610195394731461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191840866198146927192975281 143880649648610195394731461)
                ·
                  refine ⟨26977621809114411636512149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143880649648610195394731461 26977621809114411636512149)
                  ·
                    refine ⟨1264576022302238045461507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26977621809114411636512149 1264576022302238045461507)
                    ·
                      rfl

theorem cell23_7388259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 6].length) (baseStart_7388259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388259 prefixEnd_7388259 := by exact prefixLift 7388259
  have htrace : WordTrace (prefixWord ++ tailWord_7388259) baseStart_7388259 baseEnd_7388259 := by
    simpa [prefixWord, tailWord_7388259, baseEnd_7388259] using wordTrace_append hprefix tailTrace_7388259
  have hstable : (prefixWord ++ tailWord_7388259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388259).length < 2 ^ (prefixWord ++ tailWord_7388259).sum := by decide
  have hdescent : baseEnd_7388259 < baseStart_7388259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388283 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 4, 2, 2]
def baseStart_7388283 : Nat := 118140960795 + 7388283 * 2 ^ 59
def prefixEnd_7388283 : Nat := 4983230072969 + 3 ^ 40 * 7388283 * 2
def baseEnd_7388283 : Nat := 3793740390442422042484411

theorem tailTrace_7388283 : CollatzResearch.WordTrace tailWord_7388283 prefixEnd_7388283 3793740390442422042484411 := by
  unfold tailWord_7388283
  simp only [CollatzResearch.WordTrace]
  refine ⟨269472819092519984123025503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179648546061679989415350335 269472819092519984123025503)
  ·
    refine ⟨404209228638779976184538255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269472819092519984123025503 404209228638779976184538255)
    ·
      refine ⟨606313842958169964276807383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404209228638779976184538255 606313842958169964276807383)
      ·
        refine ⟨909470764437254946415211075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606313842958169964276807383 909470764437254946415211075)
        ·
          refine ⟨1364206146655882419622816613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909470764437254946415211075 1364206146655882419622816613)
          ·
            refine ⟨255788652497977953679278115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1364206146655882419622816613 255788652497977953679278115)
            ·
              refine ⟨383682978746966930518917173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255788652497977953679278115 383682978746966930518917173)
              ·
                refine ⟨35970279257528149736148485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 383682978746966930518917173 35970279257528149736148485)
                ·
                  refine ⟨6744427360786528075527841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35970279257528149736148485 6744427360786528075527841)
                  ·
                    refine ⟨5058320520589896056645881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6744427360786528075527841 5058320520589896056645881)
                    ·
                      refine ⟨3793740390442422042484411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5058320520589896056645881 3793740390442422042484411)
                      ·
                        rfl

theorem cell23_7388283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 2, 2].length) (baseStart_7388283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388283 prefixEnd_7388283 := by exact prefixLift 7388283
  have htrace : WordTrace (prefixWord ++ tailWord_7388283) baseStart_7388283 baseEnd_7388283 := by
    simpa [prefixWord, tailWord_7388283, baseEnd_7388283] using wordTrace_append hprefix tailTrace_7388283
  have hstable : (prefixWord ++ tailWord_7388283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388283).length < 2 ^ (prefixWord ++ tailWord_7388283).sum := by decide
  have hdescent : baseEnd_7388283 < baseStart_7388283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388306 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 9]
def baseStart_7388306 : Nat := 118140960795 + 7388306 * 2 ^ 59
def prefixEnd_7388306 : Nat := 4983230072969 + 3 ^ 40 * 7388306 * 2
def baseEnd_7388306 : Nat := 421528022277497272499645

theorem tailTrace_7388306 : CollatzResearch.WordTrace tailWord_7388306 prefixEnd_7388306 421528022277497272499645 := by
  unfold tailWord_7388306
  simp only [CollatzResearch.WordTrace]
  refine ⟨67368414492859164762778193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179649105314291106034075181 67368414492859164762778193)
  ·
    refine ⟨50526310869644373572083645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67368414492859164762778193 50526310869644373572083645)
    ·
      refine ⟨18947366576116640089531367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50526310869644373572083645 18947366576116640089531367)
      ·
        refine ⟨28421049864174960134297051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18947366576116640089531367 28421049864174960134297051)
        ·
          refine ⟨42631574796262440201445577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28421049864174960134297051 42631574796262440201445577)
          ·
            refine ⟨31973681097196830151084183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42631574796262440201445577 31973681097196830151084183)
            ·
              refine ⟨47960521645795245226626275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31973681097196830151084183 47960521645795245226626275)
              ·
                refine ⟨71940782468692867839939413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47960521645795245226626275 71940782468692867839939413)
                ·
                  refine ⟨421528022277497272499645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71940782468692867839939413 421528022277497272499645)
                  ·
                    rfl

theorem cell23_7388306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_7388306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388306 prefixEnd_7388306 := by exact prefixLift 7388306
  have htrace : WordTrace (prefixWord ++ tailWord_7388306) baseStart_7388306 baseEnd_7388306 := by
    simpa [prefixWord, tailWord_7388306, baseEnd_7388306] using wordTrace_append hprefix tailTrace_7388306
  have hstable : (prefixWord ++ tailWord_7388306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388306).length < 2 ^ (prefixWord ++ tailWord_7388306).sum := by decide
  have hdescent : baseEnd_7388306 < baseStart_7388306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388329 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 5, 1, 7]
def baseStart_7388329 : Nat := 118140960795 + 7388329 * 2 ^ 59
def prefixEnd_7388329 : Nat := 4983230072969 + 3 ^ 40 * 7388329 * 2
def baseEnd_7388329 : Nat := 3793764010552528862509199

theorem tailTrace_7388329 : CollatzResearch.WordTrace tailWord_7388329 prefixEnd_7388329 3793764010552528862509199 := by
  unfold tailWord_7388329
  simp only [CollatzResearch.WordTrace]
  refine ⟨269474496850353333979200041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179649664566902222652800027 269474496850353333979200041)
  ·
    refine ⟨202105872637765000484400031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269474496850353333979200041 202105872637765000484400031)
    ·
      refine ⟨303158808956647500726600047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202105872637765000484400031 303158808956647500726600047)
      ·
        refine ⟨454738213434971251089900071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303158808956647500726600047 454738213434971251089900071)
        ·
          refine ⟨682107320152456876634850107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454738213434971251089900071 682107320152456876634850107)
          ·
            refine ⟨1023160980228685314952275161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682107320152456876634850107 1023160980228685314952275161)
            ·
              refine ⟨767370735171513986214206371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1023160980228685314952275161 767370735171513986214206371)
              ·
                refine ⟨1151056102757270979321309557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767370735171513986214206371 1151056102757270979321309557)
                ·
                  refine ⟨107911509633494154311372771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1151056102757270979321309557 107911509633494154311372771)
                  ·
                    refine ⟨161867264450241231467059157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107911509633494154311372771 161867264450241231467059157)
                    ·
                      refine ⟨3793764010552528862509199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161867264450241231467059157 3793764010552528862509199)
                      ·
                        rfl

theorem cell23_7388329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_7388329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388329 prefixEnd_7388329 := by exact prefixLift 7388329
  have htrace : WordTrace (prefixWord ++ tailWord_7388329) baseStart_7388329 baseEnd_7388329 := by
    simpa [prefixWord, tailWord_7388329, baseEnd_7388329] using wordTrace_append hprefix tailTrace_7388329
  have hstable : (prefixWord ++ tailWord_7388329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388329).length < 2 ^ (prefixWord ++ tailWord_7388329).sum := by decide
  have hdescent : baseEnd_7388329 < baseStart_7388329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388353 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 1, 7]
def baseStart_7388353 : Nat := 118140960795 + 7388353 * 2 ^ 59
def prefixEnd_7388353 : Nat := 4983230072969 + 3 ^ 40 * 7388353 * 2
def baseEnd_7388353 : Nat := 1264592111362745589536363

theorem tailTrace_7388353 : CollatzResearch.WordTrace tailWord_7388353 prefixEnd_7388353 1264592111362745589536363 := by
  unfold tailWord_7388353
  simp only [CollatzResearch.WordTrace]
  refine ⟨269475372202266386078073713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179650248134844257385382475 269475372202266386078073713)
  ·
    refine ⟨202106529151699789558555285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269475372202266386078073713 202106529151699789558555285)
    ·
      refine ⟨9473743553985927635557279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 202106529151699789558555285 9473743553985927635557279)
      ·
        refine ⟨14210615330978891453335919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9473743553985927635557279 14210615330978891453335919)
        ·
          refine ⟨21315922996468337180003879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14210615330978891453335919 21315922996468337180003879)
          ·
            refine ⟨31973884494702505770005819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21315922996468337180003879 31973884494702505770005819)
            ·
              refine ⟨47960826742053758655008729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31973884494702505770005819 47960826742053758655008729)
              ·
                refine ⟨35970620056540318991256547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47960826742053758655008729 35970620056540318991256547)
                ·
                  refine ⟨53955930084810478486884821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35970620056540318991256547 53955930084810478486884821)
                  ·
                    refine ⟨1264592111362745589536363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53955930084810478486884821 1264592111362745589536363)
                    ·
                      rfl

theorem cell23_7388353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_7388353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388353 prefixEnd_7388353 := by exact prefixLift 7388353
  have htrace : WordTrace (prefixWord ++ tailWord_7388353) baseStart_7388353 baseEnd_7388353 := by
    simpa [prefixWord, tailWord_7388353, baseEnd_7388353] using wordTrace_append hprefix tailTrace_7388353
  have hstable : (prefixWord ++ tailWord_7388353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388353).length < 2 ^ (prefixWord ++ tailWord_7388353).sum := by decide
  have hdescent : baseEnd_7388353 < baseStart_7388353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388373 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_7388373 : Nat := 118140960795 + 7388373 * 2 ^ 59
def prefixEnd_7388373 : Nat := 4983230072969 + 3 ^ 40 * 7388373 * 2
def baseEnd_7388373 : Nat := 3793786603701326690358997

theorem tailTrace_7388373 : CollatzResearch.WordTrace tailWord_7388373 prefixEnd_7388373 3793786603701326690358997 := by
  unfold tailWord_7388373
  simp only [CollatzResearch.WordTrace]
  refine ⟨269476101662193929493801773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179650734441462619662534515 269476101662193929493801773)
  ·
    refine ⟨101053538123322723560175665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269476101662193929493801773 101053538123322723560175665)
    ·
      refine ⟨75790153592492042670131749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101053538123322723560175665 75790153592492042670131749)
      ·
        refine ⟨14210653798592258000649703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75790153592492042670131749 14210653798592258000649703)
        ·
          refine ⟨21315980697888387000974555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14210653798592258000649703 21315980697888387000974555)
          ·
            refine ⟨31973971046832580501461833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21315980697888387000974555 31973971046832580501461833)
            ·
              refine ⟨23980478285124435376096375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31973971046832580501461833 23980478285124435376096375)
              ·
                refine ⟨35970717427686653064144563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23980478285124435376096375 35970717427686653064144563)
                ·
                  refine ⟨53956076141529979596216845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35970717427686653064144563 53956076141529979596216845)
                  ·
                    refine ⟨20233528553073742348581317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53956076141529979596216845 20233528553073742348581317)
                    ·
                      refine ⟨3793786603701326690358997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20233528553073742348581317 3793786603701326690358997)
                      ·
                        rfl

theorem cell23_7388373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_7388373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388373 prefixEnd_7388373 := by exact prefixLift 7388373
  have htrace : WordTrace (prefixWord ++ tailWord_7388373) baseStart_7388373 baseEnd_7388373 := by
    simpa [prefixWord, tailWord_7388373, baseEnd_7388373] using wordTrace_append hprefix tailTrace_7388373
  have hstable : (prefixWord ++ tailWord_7388373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388373).length < 2 ^ (prefixWord ++ tailWord_7388373).sum := by decide
  have hdescent : baseEnd_7388373 < baseStart_7388373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388374 : List Nat := [5, 2, 1, 2, 2, 2, 1, 3, 5]
def baseStart_7388374 : Nat := 118140960795 + 7388374 * 2 ^ 59
def prefixEnd_7388374 : Nat := 4983230072969 + 3 ^ 40 * 7388374 * 2
def baseEnd_7388374 : Nat := 421531901909109020716277

theorem tailTrace_7388374 : CollatzResearch.WordTrace tailWord_7388374 prefixEnd_7388374 421531901909109020716277 := by
  unfold tailWord_7388374
  simp only [CollatzResearch.WordTrace]
  refine ⟨16842258633449394166536761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179650758756793537776392117 16842258633449394166536761)
  ·
    refine ⟨12631693975087045624902571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16842258633449394166536761 12631693975087045624902571)
    ·
      refine ⟨18947540962630568437353857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12631693975087045624902571 18947540962630568437353857)
      ·
        refine ⟨14210655721972926328015393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18947540962630568437353857 14210655721972926328015393)
        ·
          refine ⟨10657991791479694746011545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14210655721972926328015393 10657991791479694746011545)
          ·
            refine ⟨7993493843609771059508659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10657991791479694746011545 7993493843609771059508659)
            ·
              refine ⟨11990240765414656589262989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7993493843609771059508659 11990240765414656589262989)
              ·
                refine ⟨4496340287030496220973621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11990240765414656589262989 4496340287030496220973621)
                ·
                  refine ⟨421531901909109020716277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4496340287030496220973621 421531901909109020716277)
                  ·
                    rfl

theorem cell23_7388374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_7388374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388374 prefixEnd_7388374 := by exact prefixLift 7388374
  have htrace : WordTrace (prefixWord ++ tailWord_7388374) baseStart_7388374 baseEnd_7388374 := by
    simpa [prefixWord, tailWord_7388374, baseEnd_7388374] using wordTrace_append hprefix tailTrace_7388374
  have hstable : (prefixWord ++ tailWord_7388374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388374).length < 2 ^ (prefixWord ++ tailWord_7388374).sum := by decide
  have hdescent : baseEnd_7388374 < baseStart_7388374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388396 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 8]
def baseStart_7388396 : Nat := 118140960795 + 7388396 * 2 ^ 59
def prefixEnd_7388396 : Nat := 4983230072969 + 3 ^ 40 * 7388396 * 2
def baseEnd_7388396 : Nat := 421533157084042233374599

theorem tailTrace_7388396 : CollatzResearch.WordTrace tailWord_7388396 prefixEnd_7388396 421533157084042233374599 := by
  unfold tailWord_7388396
  simp only [CollatzResearch.WordTrace]
  refine ⟨134738470270555302210944521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179651293694073736281259361 134738470270555302210944521)
  ·
    refine ⟨101053852702916476658208391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134738470270555302210944521 101053852702916476658208391)
    ·
      refine ⟨151580779054374714987312587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101053852702916476658208391 151580779054374714987312587)
      ·
        refine ⟨227371168581562072480968881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151580779054374714987312587 227371168581562072480968881)
        ·
          refine ⟨170528376436171554360726661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227371168581562072480968881 170528376436171554360726661)
          ·
            refine ⟨31974070581782166442636249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170528376436171554360726661 31974070581782166442636249)
            ·
              refine ⟨23980552936336624831977187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31974070581782166442636249 23980552936336624831977187)
              ·
                refine ⟨35970829404504937247965781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23980552936336624831977187 35970829404504937247965781)
                ·
                  refine ⟨421533157084042233374599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35970829404504937247965781 421533157084042233374599)
                  ·
                    rfl

theorem cell23_7388396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 8].length) (baseStart_7388396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388396 prefixEnd_7388396 := by exact prefixLift 7388396
  have htrace : WordTrace (prefixWord ++ tailWord_7388396) baseStart_7388396 baseEnd_7388396 := by
    simpa [prefixWord, tailWord_7388396, baseEnd_7388396] using wordTrace_append hprefix tailTrace_7388396
  have hstable : (prefixWord ++ tailWord_7388396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388396).length < 2 ^ (prefixWord ++ tailWord_7388396).sum := by decide
  have hdescent : baseEnd_7388396 < baseStart_7388396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388463 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 2, 6, 2]
def baseStart_7388463 : Nat := 118140960795 + 7388463 * 2 ^ 59
def prefixEnd_7388463 : Nat := 4983230072969 + 3 ^ 40 * 7388463 * 2
def baseEnd_7388463 : Nat := 3793832816960231338233583

theorem tailTrace_7388463 : CollatzResearch.WordTrace tailWord_7388463 prefixEnd_7388463 3793832816960231338233583 := by
  unfold tailWord_7388463
  simp only [CollatzResearch.WordTrace]
  refine ⟨269479384231867874864578043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179652922821245249909718695 269479384231867874864578043)
  ·
    refine ⟨404219076347801812296867065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269479384231867874864578043 404219076347801812296867065)
    ·
      refine ⟨303164307260851359222650299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404219076347801812296867065 303164307260851359222650299)
      ·
        refine ⟨454746460891277038833975449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303164307260851359222650299 454746460891277038833975449)
        ·
          refine ⟨341059845668457779125481587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454746460891277038833975449 341059845668457779125481587)
          ·
            refine ⟨511589768502686668688222381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341059845668457779125481587 511589768502686668688222381)
            ·
              refine ⟨191846163188507500758083393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 511589768502686668688222381 191846163188507500758083393)
              ·
                refine ⟨143884622391380625568562545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191846163188507500758083393 143884622391380625568562545)
                ·
                  refine ⟨107913466793535469176421909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143884622391380625568562545 107913466793535469176421909)
                  ·
                    refine ⟨5058443755946975117644777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107913466793535469176421909 5058443755946975117644777)
                    ·
                      refine ⟨3793832816960231338233583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5058443755946975117644777 3793832816960231338233583)
                      ·
                        rfl

theorem cell23_7388463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 6, 2].length) (baseStart_7388463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388463 prefixEnd_7388463 := by exact prefixLift 7388463
  have htrace : WordTrace (prefixWord ++ tailWord_7388463) baseStart_7388463 baseEnd_7388463 := by
    simpa [prefixWord, tailWord_7388463, baseEnd_7388463] using wordTrace_append hprefix tailTrace_7388463
  have hstable : (prefixWord ++ tailWord_7388463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388463).length < 2 ^ (prefixWord ++ tailWord_7388463).sum := by decide
  have hdescent : baseEnd_7388463 < baseStart_7388463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388484 : List Nat := [2, 3, 4, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_7388484 : Nat := 118140960795 + 7388484 * 2 ^ 59
def prefixEnd_7388484 : Nat := 4983230072969 + 3 ^ 40 * 7388484 * 2
def baseEnd_7388484 : Nat := 3793843600053975756070987

theorem tailTrace_7388484 : CollatzResearch.WordTrace tailWord_7388484 prefixEnd_7388484 3793843600053975756070987 := by
  unfold tailWord_7388484
  simp only [CollatzResearch.WordTrace]
  refine ⟨134740075082395897725546253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179653433443194530300728337 134740075082395897725546253)
  ·
    refine ⟨50527528155898461647079845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134740075082395897725546253 50527528155898461647079845)
    ·
      refine ⟨9473911529230961558827471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50527528155898461647079845 9473911529230961558827471)
      ·
        refine ⟨14210867293846442338241207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9473911529230961558827471 14210867293846442338241207)
        ·
          refine ⟨21316300940769663507361811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14210867293846442338241207 21316300940769663507361811)
          ·
            refine ⟨31974451411154495261042717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21316300940769663507361811 31974451411154495261042717)
            ·
              refine ⟨11990419279182935722891019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31974451411154495261042717 11990419279182935722891019)
              ·
                refine ⟨17985628918774403584336529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11990419279182935722891019 17985628918774403584336529)
                ·
                  refine ⟨13489221689080802688252397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17985628918774403584336529 13489221689080802688252397)
                  ·
                    refine ⟨5058458133405301008094649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13489221689080802688252397 5058458133405301008094649)
                    ·
                      refine ⟨3793843600053975756070987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5058458133405301008094649 3793843600053975756070987)
                      ·
                        rfl

theorem cell23_7388484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_7388484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388484 prefixEnd_7388484 := by exact prefixLift 7388484
  have htrace : WordTrace (prefixWord ++ tailWord_7388484) baseStart_7388484 baseEnd_7388484 := by
    simpa [prefixWord, tailWord_7388484, baseEnd_7388484] using wordTrace_append hprefix tailTrace_7388484
  have hstable : (prefixWord ++ tailWord_7388484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388484).length < 2 ^ (prefixWord ++ tailWord_7388484).sum := by decide
  have hdescent : baseEnd_7388484 < baseStart_7388484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388513 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 3, 3, 3]
def baseStart_7388513 : Nat := 118140960795 + 7388513 * 2 ^ 59
def prefixEnd_7388513 : Nat := 4983230072969 + 3 ^ 40 * 7388513 * 2
def baseEnd_7388513 : Nat := 3793858490992956142608353

theorem tailTrace_7388513 : CollatzResearch.WordTrace tailWord_7388513 prefixEnd_7388513 3793858490992956142608353 := by
  unfold tailWord_7388513
  simp only [CollatzResearch.WordTrace]
  refine ⟨269481207881686733403898193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179654138587791155602598795 269481207881686733403898193)
  ·
    refine ⟨202110905911265050052923645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269481207881686733403898193 202110905911265050052923645)
    ·
      refine ⟨75791589716724393769846367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202110905911265050052923645 75791589716724393769846367)
      ·
        refine ⟨113687384575086590654769551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75791589716724393769846367 113687384575086590654769551)
        ·
          refine ⟨170531076862629885982154327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113687384575086590654769551 170531076862629885982154327)
          ·
            refine ⟨255796615293944828973231491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170531076862629885982154327 255796615293944828973231491)
            ·
              refine ⟨383694922940917243459847237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255796615293944828973231491 383694922940917243459847237)
              ·
                refine ⟨71942798051421983148721357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 383694922940917243459847237 71942798051421983148721357)
                ·
                  refine ⟨26978549269283243680770509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71942798051421983148721357 26978549269283243680770509)
                  ·
                    refine ⟨10116955975981216380288941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26978549269283243680770509 10116955975981216380288941)
                    ·
                      refine ⟨3793858490992956142608353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10116955975981216380288941 3793858490992956142608353)
                      ·
                        rfl

theorem cell23_7388513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_7388513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388513 prefixEnd_7388513 := by exact prefixLift 7388513
  have htrace : WordTrace (prefixWord ++ tailWord_7388513) baseStart_7388513 baseEnd_7388513 := by
    simpa [prefixWord, tailWord_7388513, baseEnd_7388513] using wordTrace_append hprefix tailTrace_7388513
  have hstable : (prefixWord ++ tailWord_7388513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388513).length < 2 ^ (prefixWord ++ tailWord_7388513).sum := by decide
  have hdescent : baseEnd_7388513 < baseStart_7388513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388514 : List Nat := [3, 3, 2, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_7388514 : Nat := 118140960795 + 7388514 * 2 ^ 59
def prefixEnd_7388514 : Nat := 4983230072969 + 3 ^ 40 * 7388514 * 2
def baseEnd_7388514 : Nat := 3793859004473610638695849

theorem tailTrace_7388514 : CollatzResearch.WordTrace tailWord_7388514 prefixEnd_7388514 3793859004473610638695849 := by
  unfold tailWord_7388514
  simp only [CollatzResearch.WordTrace]
  refine ⟨67370311088670777643671149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179654162903122073716456397 67370311088670777643671149)
  ·
    refine ⟨25263866658251541616376681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67370311088670777643671149 25263866658251541616376681)
    ·
      refine ⟨18947899993688656212282511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25263866658251541616376681 18947899993688656212282511)
      ·
        refine ⟨28421849990532984318423767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18947899993688656212282511 28421849990532984318423767)
        ·
          refine ⟨42632774985799476477635651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28421849990532984318423767 42632774985799476477635651)
          ·
            refine ⟨63949162478699214716453477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42632774985799476477635651 63949162478699214716453477)
            ·
              refine ⟨11990467964756102759335027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63949162478699214716453477 11990467964756102759335027)
              ·
                refine ⟨17985701947134154139002541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11990467964756102759335027 17985701947134154139002541)
                ·
                  refine ⟨6744638230175307802125953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17985701947134154139002541 6744638230175307802125953)
                  ·
                    refine ⟨5058478672631480851594465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6744638230175307802125953 5058478672631480851594465)
                    ·
                      refine ⟨3793859004473610638695849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5058478672631480851594465 3793859004473610638695849)
                      ·
                        rfl

theorem cell23_7388514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_7388514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388514 prefixEnd_7388514 := by exact prefixLift 7388514
  have htrace : WordTrace (prefixWord ++ tailWord_7388514) baseStart_7388514 baseEnd_7388514 := by
    simpa [prefixWord, tailWord_7388514, baseEnd_7388514] using wordTrace_append hprefix tailTrace_7388514
  have hstable : (prefixWord ++ tailWord_7388514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388514).length < 2 ^ (prefixWord ++ tailWord_7388514).sum := by decide
  have hdescent : baseEnd_7388514 < baseStart_7388514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388593 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 9]
def baseStart_7388593 : Nat := 118140960795 + 7388593 * 2 ^ 59
def prefixEnd_7388593 : Nat := 4983230072969 + 3 ^ 40 * 7388593 * 2
def baseEnd_7388593 : Nat := 421544396605035092178665

theorem tailTrace_7388593 : CollatzResearch.WordTrace tailWord_7388593 prefixEnd_7388593 421544396605035092178665 := by
  unfold tailWord_7388593
  simp only [CollatzResearch.WordTrace]
  refine ⟨269484125721396907066810433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179656083814264604711206955 269484125721396907066810433)
  ·
    refine ⟨202113094291047680300107825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269484125721396907066810433 202113094291047680300107825)
    ·
      refine ⟨151584820718285760225080869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202113094291047680300107825 151584820718285760225080869)
      ·
        refine ⟨28422153884678580042202663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151584820718285760225080869 28422153884678580042202663)
        ·
          refine ⟨42633230827017870063303995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28422153884678580042202663 42633230827017870063303995)
          ·
            refine ⟨63949846240526805094955993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42633230827017870063303995 63949846240526805094955993)
            ·
              refine ⟨47962384680395103821216995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63949846240526805094955993 47962384680395103821216995)
              ·
                refine ⟨71943577020592655731825493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47962384680395103821216995 71943577020592655731825493)
                ·
                  refine ⟨421544396605035092178665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71943577020592655731825493 421544396605035092178665)
                  ·
                    rfl

theorem cell23_7388593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 9].length) (baseStart_7388593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388593 prefixEnd_7388593 := by exact prefixLift 7388593
  have htrace : WordTrace (prefixWord ++ tailWord_7388593) baseStart_7388593 baseEnd_7388593 := by
    simpa [prefixWord, tailWord_7388593, baseEnd_7388593] using wordTrace_append hprefix tailTrace_7388593
  have hstable : (prefixWord ++ tailWord_7388593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388593).length < 2 ^ (prefixWord ++ tailWord_7388593).sum := by decide
  have hdescent : baseEnd_7388593 < baseStart_7388593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388604 : List Nat := [2, 2, 2, 4, 2, 1, 1, 2, 1, 4, 2]
def baseStart_7388604 : Nat := 118140960795 + 7388604 * 2 ^ 59
def prefixEnd_7388604 : Nat := 4983230072969 + 3 ^ 40 * 7388604 * 2
def baseEnd_7388604 : Nat := 3793905217732515286570435

theorem tailTrace_7388604 : CollatzResearch.WordTrace tailWord_7388604 prefixEnd_7388604 3793905217732515286570435 := by
  unfold tailWord_7388604
  simp only [CollatzResearch.WordTrace]
  refine ⟨134742263462178527972730433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179656351282904703963640577 134742263462178527972730433)
  ·
    refine ⟨101056697596633895979547825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134742263462178527972730433 101056697596633895979547825)
    ·
      refine ⟨75792523197475421984660869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101056697596633895979547825 75792523197475421984660869)
      ·
        refine ⟨14211098099526641622123913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75792523197475421984660869 14211098099526641622123913)
        ·
          refine ⟨10658323574644981216592935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14211098099526641622123913 10658323574644981216592935)
          ·
            refine ⟨15987485361967471824889403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10658323574644981216592935 15987485361967471824889403)
            ·
              refine ⟨23981228042951207737334105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15987485361967471824889403 23981228042951207737334105)
              ·
                refine ⟨17985921032213405803000579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23981228042951207737334105 17985921032213405803000579)
                ·
                  refine ⟨26978881548320108704500869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17985921032213405803000579 26978881548320108704500869)
                  ·
                    refine ⟨5058540290310020382093913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26978881548320108704500869 5058540290310020382093913)
                    ·
                      refine ⟨3793905217732515286570435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5058540290310020382093913 3793905217732515286570435)
                      ·
                        rfl

theorem cell23_7388604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_7388604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388604 prefixEnd_7388604 := by exact prefixLift 7388604
  have htrace : WordTrace (prefixWord ++ tailWord_7388604) baseStart_7388604 baseEnd_7388604 := by
    simpa [prefixWord, tailWord_7388604, baseEnd_7388604] using wordTrace_append hprefix tailTrace_7388604
  have hstable : (prefixWord ++ tailWord_7388604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388604).length < 2 ^ (prefixWord ++ tailWord_7388604).sum := by decide
  have hdescent : baseEnd_7388604 < baseStart_7388604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388637 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_7388637 : Nat := 118140960795 + 7388637 * 2 ^ 59
def prefixEnd_7388637 : Nat := 4983230072969 + 3 ^ 40 * 7388637 * 2
def baseEnd_7388637 : Nat := 3793922162594113657457783

theorem tailTrace_7388637 : CollatzResearch.WordTrace tailWord_7388637 prefixEnd_7388637 3793922162594113657457783 := by
  unfold tailWord_7388637
  simp only [CollatzResearch.WordTrace]
  refine ⟨269485730533237502581412165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179657153688825001720941443 269485730533237502581412165)
  ·
    refine ⟨50528574474982031734014781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269485730533237502581412165 50528574474982031734014781)
    ·
      refine ⟨18948215428118261900255543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50528574474982031734014781 18948215428118261900255543)
      ·
        refine ⟨28422323142177392850383315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18948215428118261900255543 28422323142177392850383315)
        ·
          refine ⟨42633484713266089275574973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28422323142177392850383315 42633484713266089275574973)
          ·
            refine ⟨15987556767474783478340615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42633484713266089275574973 15987556767474783478340615)
            ·
              refine ⟨23981335151212175217510923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15987556767474783478340615 23981335151212175217510923)
              ·
                refine ⟨35972002726818262826266385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23981335151212175217510923 35972002726818262826266385)
                ·
                  refine ⟨26979002045113697119699789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35972002726818262826266385 26979002045113697119699789)
                  ·
                    refine ⟨10117125766917636419887421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26979002045113697119699789 10117125766917636419887421)
                    ·
                      refine ⟨3793922162594113657457783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10117125766917636419887421 3793922162594113657457783)
                      ·
                        rfl

theorem cell23_7388637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_7388637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388637 prefixEnd_7388637 := by exact prefixLift 7388637
  have htrace : WordTrace (prefixWord ++ tailWord_7388637) baseStart_7388637 baseEnd_7388637 := by
    simpa [prefixWord, tailWord_7388637, baseEnd_7388637] using wordTrace_append hprefix tailTrace_7388637
  have hstable : (prefixWord ++ tailWord_7388637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388637).length < 2 ^ (prefixWord ++ tailWord_7388637).sum := by decide
  have hdescent : baseEnd_7388637 < baseStart_7388637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388657 : List Nat := [1, 2, 2, 2, 3, 4, 1, 1, 2, 5]
def baseStart_7388657 : Nat := 118140960795 + 7388657 * 2 ^ 59
def prefixEnd_7388657 : Nat := 4983230072969 + 3 ^ 40 * 7388657 * 2
def baseEnd_7388657 : Nat := 1264644144069067859735897

theorem tailTrace_7388657 : CollatzResearch.WordTrace tailWord_7388657 prefixEnd_7388657 1264644144069067859735897 := by
  unfold tailWord_7388657
  simp only [CollatzResearch.WordTrace]
  refine ⟨269486459993165045997140225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179657639995443363998093483 269486459993165045997140225)
  ·
    refine ⟨202114844994873784497855169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269486459993165045997140225 202114844994873784497855169)
    ·
      refine ⟨151586133746155338373391377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202114844994873784497855169 151586133746155338373391377)
      ·
        refine ⟨113689600309616503780043533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151586133746155338373391377 113689600309616503780043533)
        ·
          refine ⟨42633600116106188917516325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113689600309616503780043533 42633600116106188917516325)
          ·
            refine ⟨7993800021769910422034311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42633600116106188917516325 7993800021769910422034311)
            ·
              refine ⟨11990700032654865633051467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7993800021769910422034311 11990700032654865633051467)
              ·
                refine ⟨17986050048982298449577201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11990700032654865633051467 17986050048982298449577201)
                ·
                  refine ⟨13489537536736723837182901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17986050048982298449577201 13489537536736723837182901)
                  ·
                    refine ⟨1264644144069067859735897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13489537536736723837182901 1264644144069067859735897)
                    ·
                      rfl

theorem cell23_7388657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_7388657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388657 prefixEnd_7388657 := by exact prefixLift 7388657
  have htrace : WordTrace (prefixWord ++ tailWord_7388657) baseStart_7388657 baseEnd_7388657 := by
    simpa [prefixWord, tailWord_7388657, baseEnd_7388657] using wordTrace_append hprefix tailTrace_7388657
  have hstable : (prefixWord ++ tailWord_7388657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388657).length < 2 ^ (prefixWord ++ tailWord_7388657).sum := by decide
  have hdescent : baseEnd_7388657 < baseStart_7388657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388663 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 5]
def baseStart_7388663 : Nat := 118140960795 + 7388663 * 2 ^ 59
def prefixEnd_7388663 : Nat := 4983230072969 + 3 ^ 40 * 7388663 * 2
def baseEnd_7388663 : Nat := 3793935513091130555732663

theorem tailTrace_7388663 : CollatzResearch.WordTrace tailWord_7388663 prefixEnd_7388663 3793935513091130555732663 := by
  unfold tailWord_7388663
  simp only [CollatzResearch.WordTrace]
  refine ⟨269486678831143309021858643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179657785887428872681239095 269486678831143309021858643)
  ·
    refine ⟨404230018246714963532787965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269486678831143309021858643 404230018246714963532787965)
    ·
      refine ⟨151586256842518111324795487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404230018246714963532787965 151586256842518111324795487)
      ·
        refine ⟨227379385263777166987193231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151586256842518111324795487 227379385263777166987193231)
        ·
          refine ⟨341069077895665750480789847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227379385263777166987193231 341069077895665750480789847)
          ·
            refine ⟨511603616843498625721184771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341069077895665750480789847 511603616843498625721184771)
            ·
              refine ⟨767405425265247938581777157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511603616843498625721184771 767405425265247938581777157)
              ·
                refine ⟨143888517237233988484083217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 767405425265247938581777157 143888517237233988484083217)
                ·
                  refine ⟨107916387927925491363062413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143888517237233988484083217 107916387927925491363062413)
                  ·
                    refine ⟨40468645472972059261148405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107916387927925491363062413 40468645472972059261148405)
                    ·
                      refine ⟨3793935513091130555732663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40468645472972059261148405 3793935513091130555732663)
                      ·
                        rfl

theorem cell23_7388663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_7388663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388663 prefixEnd_7388663 := by exact prefixLift 7388663
  have htrace : WordTrace (prefixWord ++ tailWord_7388663) baseStart_7388663 baseEnd_7388663 := by
    simpa [prefixWord, tailWord_7388663, baseEnd_7388663] using wordTrace_append hprefix tailTrace_7388663
  have hstable : (prefixWord ++ tailWord_7388663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388663).length < 2 ^ (prefixWord ++ tailWord_7388663).sum := by decide
  have hdescent : baseEnd_7388663 < baseStart_7388663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388750 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_7388750 : Nat := 118140960795 + 7388750 * 2 ^ 59
def prefixEnd_7388750 : Nat := 4983230072969 + 3 ^ 40 * 7388750 * 2
def baseEnd_7388750 : Nat := 3793980185908071715344763

theorem tailTrace_7388750 : CollatzResearch.WordTrace tailWord_7388750 prefixEnd_7388750 3793980185908071715344763 := by
  unfold tailWord_7388750
  simp only [CollatzResearch.WordTrace]
  refine ⟨33686231497728515360034463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179659901321218748586850469 33686231497728515360034463)
  ·
    refine ⟨50529347246592773040051695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33686231497728515360034463 50529347246592773040051695)
    ·
      refine ⟨75794020869889159560077543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50529347246592773040051695 75794020869889159560077543)
      ·
        refine ⟨113691031304833739340116315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75794020869889159560077543 113691031304833739340116315)
        ·
          refine ⟨170536546957250609010174473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113691031304833739340116315 170536546957250609010174473)
          ·
            refine ⟨127902410217937956757630855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170536546957250609010174473 127902410217937956757630855)
            ·
              refine ⟨191853615326906935136446283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127902410217937956757630855 191853615326906935136446283)
              ·
                refine ⟨287780422990360402704669425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191853615326906935136446283 287780422990360402704669425)
                ·
                  refine ⟨215835317242770302028502069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287780422990360402704669425 215835317242770302028502069)
                  ·
                    refine ⟨20234560991509715815172069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 215835317242770302028502069 20234560991509715815172069)
                    ·
                      refine ⟨3793980185908071715344763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20234560991509715815172069 3793980185908071715344763)
                      ·
                        rfl

theorem cell23_7388750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_7388750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388750 prefixEnd_7388750 := by exact prefixLift 7388750
  have htrace : WordTrace (prefixWord ++ tailWord_7388750) baseStart_7388750 baseEnd_7388750 := by
    simpa [prefixWord, tailWord_7388750, baseEnd_7388750] using wordTrace_append hprefix tailTrace_7388750
  have hstable : (prefixWord ++ tailWord_7388750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388750).length < 2 ^ (prefixWord ++ tailWord_7388750).sum := by decide
  have hdescent : baseEnd_7388750 < baseStart_7388750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388760 : List Nat := [2, 1, 2, 2, 1, 2, 1, 5, 1, 6]
def baseStart_7388760 : Nat := 118140960795 + 7388760 * 2 ^ 59
def prefixEnd_7388760 : Nat := 4983230072969 + 3 ^ 40 * 7388760 * 2
def baseEnd_7388760 : Nat := 1264661773571538892073239

theorem tailTrace_7388760 : CollatzResearch.WordTrace tailWord_7388760 prefixEnd_7388760 1264661773571538892073239 := by
  unfold tailWord_7388760
  simp only [CollatzResearch.WordTrace]
  refine ⟨134745108355895947294069867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179660144474527929725426489 134745108355895947294069867)
  ·
    refine ⟨202117662533843920941104801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134745108355895947294069867 202117662533843920941104801)
    ·
      refine ⟨151588246900382940705828601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202117662533843920941104801 151588246900382940705828601)
      ·
        refine ⟨113691185175287205529371451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151588246900382940705828601 113691185175287205529371451)
        ·
          refine ⟨170536777762930808294057177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113691185175287205529371451 170536777762930808294057177)
          ·
            refine ⟨127902583322198106220542883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170536777762930808294057177 127902583322198106220542883)
            ·
              refine ⟨191853874983297159330814325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127902583322198106220542883 191853874983297159330814325)
              ·
                refine ⟨17986300779684108687263843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191853874983297159330814325 17986300779684108687263843)
                ·
                  refine ⟨26979451169526163030895765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17986300779684108687263843 26979451169526163030895765)
                  ·
                    refine ⟨1264661773571538892073239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26979451169526163030895765 1264661773571538892073239)
                    ·
                      rfl

theorem cell23_7388760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_7388760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388760 prefixEnd_7388760 := by exact prefixLift 7388760
  have htrace : WordTrace (prefixWord ++ tailWord_7388760) baseStart_7388760 baseEnd_7388760 := by
    simpa [prefixWord, tailWord_7388760, baseEnd_7388760] using wordTrace_append hprefix tailTrace_7388760
  have hstable : (prefixWord ++ tailWord_7388760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388760).length < 2 ^ (prefixWord ++ tailWord_7388760).sum := by decide
  have hdescent : baseEnd_7388760 < baseStart_7388760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388764 : List Nat := [2, 2, 4, 1, 2, 1, 3, 2, 1, 5]
def baseStart_7388764 : Nat := 118140960795 + 7388764 * 2 ^ 59
def prefixEnd_7388764 : Nat := 4983230072969 + 3 ^ 40 * 7388764 * 2
def baseEnd_7388764 : Nat := 1264662458212411553523233

theorem tailTrace_7388764 : CollatzResearch.WordTrace tailWord_7388764 prefixEnd_7388764 1264662458212411553523233 := by
  unfold tailWord_7388764
  simp only [CollatzResearch.WordTrace]
  refine ⟨134745181301888701635642673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179660241735851602180856897 134745181301888701635642673)
  ·
    refine ⟨101058885976416526226732005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134745181301888701635642673 101058885976416526226732005)
    ·
      refine ⟨18948541120578098667512251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101058885976416526226732005 18948541120578098667512251)
      ·
        refine ⟨28422811680867148001268377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18948541120578098667512251 28422811680867148001268377)
        ·
          refine ⟨21317108760650361000951283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28422811680867148001268377 21317108760650361000951283)
          ·
            refine ⟨31975663140975541501426925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21317108760650361000951283 31975663140975541501426925)
            ·
              refine ⟨11990873677865828063035097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31975663140975541501426925 11990873677865828063035097)
              ·
                refine ⟨8993155258399371047276323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11990873677865828063035097 8993155258399371047276323)
                ·
                  refine ⟨13489732887599056570914485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8993155258399371047276323 13489732887599056570914485)
                  ·
                    refine ⟨1264662458212411553523233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13489732887599056570914485 1264662458212411553523233)
                    ·
                      rfl

theorem cell23_7388764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_7388764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388764 prefixEnd_7388764 := by exact prefixLift 7388764
  have htrace : WordTrace (prefixWord ++ tailWord_7388764) baseStart_7388764 baseEnd_7388764 := by
    simpa [prefixWord, tailWord_7388764, baseEnd_7388764] using wordTrace_append hprefix tailTrace_7388764
  have hstable : (prefixWord ++ tailWord_7388764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388764).length < 2 ^ (prefixWord ++ tailWord_7388764).sum := by decide
  have hdescent : baseEnd_7388764 < baseStart_7388764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388781 : List Nat := [1, 5, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_7388781 : Nat := 118140960795 + 7388781 * 2 ^ 59
def prefixEnd_7388781 : Nat := 4983230072969 + 3 ^ 40 * 7388781 * 2
def baseEnd_7388781 : Nat := 1264665367936120364685707

theorem tailTrace_7388781 : CollatzResearch.WordTrace tailWord_7388781 prefixEnd_7388781 1264665367936120364685707 := by
  unfold tailWord_7388781
  simp only [CollatzResearch.WordTrace]
  refine ⟨269490982644715815174654197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179660655096477210116436131 269490982644715815174654197)
  ·
    refine ⟨25264779622942107672623831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 269490982644715815174654197 25264779622942107672623831)
    ·
      refine ⟨37897169434413161508935747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25264779622942107672623831 37897169434413161508935747)
      ·
        refine ⟨56845754151619742263403621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37897169434413161508935747 56845754151619742263403621)
        ·
          refine ⟨10658578903428701674388179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56845754151619742263403621 10658578903428701674388179)
          ·
            refine ⟨15987868355143052511582269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10658578903428701674388179 15987868355143052511582269)
            ·
              refine ⟨5995450633178644691843351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15987868355143052511582269 5995450633178644691843351)
              ·
                refine ⟨8993175949767967037765027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5995450633178644691843351 8993175949767967037765027)
                ·
                  refine ⟨13489763924651950556647541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8993175949767967037765027 13489763924651950556647541)
                  ·
                    refine ⟨1264665367936120364685707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13489763924651950556647541 1264665367936120364685707)
                    ·
                      rfl

theorem cell23_7388781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_7388781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388781 prefixEnd_7388781 := by exact prefixLift 7388781
  have htrace : WordTrace (prefixWord ++ tailWord_7388781) baseStart_7388781 baseEnd_7388781 := by
    simpa [prefixWord, tailWord_7388781, baseEnd_7388781] using wordTrace_append hprefix tailTrace_7388781
  have hstable : (prefixWord ++ tailWord_7388781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388781).length < 2 ^ (prefixWord ++ tailWord_7388781).sum := by decide
  have hdescent : baseEnd_7388781 < baseStart_7388781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388807 : List Nat := [1, 1, 4, 2, 1, 5, 1, 8]
def baseStart_7388807 : Nat := 118140960795 + 7388807 * 2 ^ 59
def prefixEnd_7388807 : Nat := 4983230072969 + 3 ^ 40 * 7388807 * 2
def baseEnd_7388807 : Nat := 140518868677976962678963

theorem tailTrace_7388807 : CollatzResearch.WordTrace tailWord_7388807 prefixEnd_7388807 140518868677976962678963 := by
  unfold tailWord_7388807
  simp only [CollatzResearch.WordTrace]
  refine ⟨269491930942621621615100675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179661287295081081076733783 269491930942621621615100675)
  ·
    refine ⟨404237896413932432422651013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269491930942621621615100675 404237896413932432422651013)
    ·
      refine ⟨75794605577612331079247065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404237896413932432422651013 75794605577612331079247065)
      ·
        refine ⟨56845954183209248309435299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75794605577612331079247065 56845954183209248309435299)
        ·
          refine ⟨85268931274813872464152949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56845954183209248309435299 85268931274813872464152949)
          ·
            refine ⟨7993962307013800543514339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85268931274813872464152949 7993962307013800543514339)
            ·
              refine ⟨11990943460520700815271509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7993962307013800543514339 11990943460520700815271509)
              ·
                refine ⟨140518868677976962678963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11990943460520700815271509 140518868677976962678963)
                ·
                  rfl

theorem cell23_7388807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 8].length) (baseStart_7388807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388807 prefixEnd_7388807 := by exact prefixLift 7388807
  have htrace : WordTrace (prefixWord ++ tailWord_7388807) baseStart_7388807 baseEnd_7388807 := by
    simpa [prefixWord, tailWord_7388807, baseEnd_7388807] using wordTrace_append hprefix tailTrace_7388807
  have hstable : (prefixWord ++ tailWord_7388807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388807).length < 2 ^ (prefixWord ++ tailWord_7388807).sum := by decide
  have hdescent : baseEnd_7388807 < baseStart_7388807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388814 : List Nat := [4, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4]
def baseStart_7388814 : Nat := 118140960795 + 7388814 * 2 ^ 59
def prefixEnd_7388814 : Nat := 4983230072969 + 3 ^ 40 * 7388814 * 2
def baseEnd_7388814 : Nat := 3794013048669959464944469

theorem tailTrace_7388814 : CollatzResearch.WordTrace tailWord_7388814 prefixEnd_7388814 3794013048669959464944469 := by
  unfold tailWord_7388814
  simp only [CollatzResearch.WordTrace]
  refine ⟨33686523281699532726325687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179661457502397507873736997 33686523281699532726325687)
  ·
    refine ⟨50529784922549299089488531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33686523281699532726325687 50529784922549299089488531)
    ·
      refine ⟨75794677383823948634232797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50529784922549299089488531 75794677383823948634232797)
      ·
        refine ⟨28423004018933980737837299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75794677383823948634232797 28423004018933980737837299)
        ·
          refine ⟨42634506028400971106755949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28423004018933980737837299 42634506028400971106755949)
          ·
            refine ⟨15987939760650364165033481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42634506028400971106755949 15987939760650364165033481)
            ·
              refine ⟨11990954820487773123775111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15987939760650364165033481 11990954820487773123775111)
              ·
                refine ⟨17986432230731659685662667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11990954820487773123775111 17986432230731659685662667)
                ·
                  refine ⟨26979648346097489528494001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17986432230731659685662667 26979648346097489528494001)
                  ·
                    refine ⟨20234736259573117146370501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26979648346097489528494001 20234736259573117146370501)
                    ·
                      refine ⟨3794013048669959464944469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20234736259573117146370501 3794013048669959464944469)
                      ·
                        rfl

theorem cell23_7388814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_7388814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388814 prefixEnd_7388814 := by exact prefixLift 7388814
  have htrace : WordTrace (prefixWord ++ tailWord_7388814) baseStart_7388814 baseEnd_7388814 := by
    simpa [prefixWord, tailWord_7388814, baseEnd_7388814] using wordTrace_append hprefix tailTrace_7388814
  have hstable : (prefixWord ++ tailWord_7388814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388814).length < 2 ^ (prefixWord ++ tailWord_7388814).sum := by decide
  have hdescent : baseEnd_7388814 < baseStart_7388814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388818 : List Nat := [3, 2, 3, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_7388818 : Nat := 118140960795 + 7388818 * 2 ^ 59
def prefixEnd_7388818 : Nat := 4983230072969 + 3 ^ 40 * 7388818 * 2
def baseEnd_7388818 : Nat := 3794015102592577449294451

theorem tailTrace_7388818 : CollatzResearch.WordTrace tailWord_7388818 prefixEnd_7388818 3794015102592577449294451 := by
  unfold tailWord_7388818
  simp only [CollatzResearch.WordTrace]
  refine ⟨67373083036395442623437777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179661554763721180329167405 67373083036395442623437777)
  ·
    refine ⟨50529812277296581967578333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67373083036395442623437777 50529812277296581967578333)
    ·
      refine ⟨18948679603986218237841875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50529812277296581967578333 18948679603986218237841875)
      ·
        refine ⟨28423019405979327356762813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18948679603986218237841875 28423019405979327356762813)
        ·
          refine ⟨10658632277242247758786055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28423019405979327356762813 10658632277242247758786055)
          ·
            refine ⟨15987948415863371638179083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10658632277242247758786055 15987948415863371638179083)
            ·
              refine ⟨23981922623795057457268625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15987948415863371638179083 23981922623795057457268625)
              ·
                refine ⟨17986441967846293092951469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23981922623795057457268625 17986441967846293092951469)
                ·
                  refine ⟨6744915737942359909856801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17986441967846293092951469 6744915737942359909856801)
                  ·
                    refine ⟨5058686803456769932392601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6744915737942359909856801 5058686803456769932392601)
                    ·
                      refine ⟨3794015102592577449294451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5058686803456769932392601 3794015102592577449294451)
                      ·
                        rfl

theorem cell23_7388818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_7388818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388818 prefixEnd_7388818 := by exact prefixLift 7388818
  have htrace : WordTrace (prefixWord ++ tailWord_7388818) baseStart_7388818 baseEnd_7388818 := by
    simpa [prefixWord, tailWord_7388818, baseEnd_7388818] using wordTrace_append hprefix tailTrace_7388818
  have hstable : (prefixWord ++ tailWord_7388818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388818).length < 2 ^ (prefixWord ++ tailWord_7388818).sum := by decide
  have hdescent : baseEnd_7388818 < baseStart_7388818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388868 : List Nat := [2, 3, 3, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_7388868 : Nat := 118140960795 + 7388868 * 2 ^ 59
def prefixEnd_7388868 : Nat := 4983230072969 + 3 ^ 40 * 7388868 * 2
def baseEnd_7388868 : Nat := 3794040776625302253669221

theorem tailTrace_7388868 : CollatzResearch.WordTrace tailWord_7388868 prefixEnd_7388868 3794040776625302253669221 := by
  unfold tailWord_7388868
  simp only [CollatzResearch.WordTrace]
  refine ⟨134747077897700314516535629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179662770530267086022047505 134747077897700314516535629)
  ·
    refine ⟨50530154211637617943700861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134747077897700314516535629 50530154211637617943700861)
    ·
      refine ⟨18948807829364106728887823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50530154211637617943700861 18948807829364106728887823)
      ·
        refine ⟨28423211744046160093331735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18948807829364106728887823 28423211744046160093331735)
        ·
          refine ⟨42634817616069240139997603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28423211744046160093331735 42634817616069240139997603)
          ·
            refine ⟨63952226424103860209996405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42634817616069240139997603 63952226424103860209996405)
            ·
              refine ⟨5995521227259736894687163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63952226424103860209996405 5995521227259736894687163)
              ·
                refine ⟨8993281840889605342030745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5995521227259736894687163 8993281840889605342030745)
                ·
                  refine ⟨6744961380667204006523059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8993281840889605342030745 6744961380667204006523059)
                  ·
                    refine ⟨10117442071000806009784589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6744961380667204006523059 10117442071000806009784589)
                    ·
                      refine ⟨3794040776625302253669221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10117442071000806009784589 3794040776625302253669221)
                      ·
                        rfl

theorem cell23_7388868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_7388868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388868 prefixEnd_7388868 := by exact prefixLift 7388868
  have htrace : WordTrace (prefixWord ++ tailWord_7388868) baseStart_7388868 baseEnd_7388868 := by
    simpa [prefixWord, tailWord_7388868, baseEnd_7388868] using wordTrace_append hprefix tailTrace_7388868
  have hstable : (prefixWord ++ tailWord_7388868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388868).length < 2 ^ (prefixWord ++ tailWord_7388868).sum := by decide
  have hdescent : baseEnd_7388868 < baseStart_7388868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388880 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 9]
def baseStart_7388880 : Nat := 118140960795 + 7388880 * 2 ^ 59
def prefixEnd_7388880 : Nat := 4983230072969 + 3 ^ 40 * 7388880 * 2
def baseEnd_7388880 : Nat := 421560770932572911857685

theorem tailTrace_7388880 : CollatzResearch.WordTrace tailWord_7388880 prefixEnd_7388880 421560770932572911857685 := by
  unfold tailWord_7388880
  simp only [CollatzResearch.WordTrace]
  refine ⟨134747296735678577541254047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179663062314238103388338729 134747296735678577541254047)
  ·
    refine ⟨202120945103517866311881071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134747296735678577541254047 202120945103517866311881071)
    ·
      refine ⟨303181417655276799467821607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202120945103517866311881071 303181417655276799467821607)
      ·
        refine ⟨454772126482915199201732411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303181417655276799467821607 454772126482915199201732411)
        ·
          refine ⟨682158189724372798802598617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454772126482915199201732411 682158189724372798802598617)
          ·
            refine ⟨511618642293279599101948963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682158189724372798802598617 511618642293279599101948963)
            ·
              refine ⟨767427963439919398652923445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511618642293279599101948963 767427963439919398652923445)
              ·
                refine ⟨71946371572492443623711573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 767427963439919398652923445 71946371572492443623711573)
                ·
                  refine ⟨421560770932572911857685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71946371572492443623711573 421560770932572911857685)
                  ·
                    rfl

theorem cell23_7388880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 9].length) (baseStart_7388880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388880 prefixEnd_7388880 := by exact prefixLift 7388880
  have htrace : WordTrace (prefixWord ++ tailWord_7388880) baseStart_7388880 baseEnd_7388880 := by
    simpa [prefixWord, tailWord_7388880, baseEnd_7388880] using wordTrace_append hprefix tailTrace_7388880
  have hstable : (prefixWord ++ tailWord_7388880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388880).length < 2 ^ (prefixWord ++ tailWord_7388880).sum := by decide
  have hdescent : baseEnd_7388880 < baseStart_7388880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388886 : List Nat := [5, 2, 1, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_7388886 : Nat := 118140960795 + 7388886 * 2 ^ 59
def prefixEnd_7388886 : Nat := 4983230072969 + 3 ^ 40 * 7388886 * 2
def baseEnd_7388886 : Nat := 3794050019277083183244139

theorem tailTrace_7388886 : CollatzResearch.WordTrace tailWord_7388886 prefixEnd_7388886 3794050019277083183244139 := by
  unfold tailWord_7388886
  simp only [CollatzResearch.WordTrace]
  refine ⟨16843425769333463631701657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179663208206223612071484341 16843425769333463631701657)
  ·
    refine ⟨12632569327000097723776243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16843425769333463631701657 12632569327000097723776243)
    ·
      refine ⟨18948853990500146585664365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12632569327000097723776243 18948853990500146585664365)
      ·
        refine ⟨7105820246437554969624137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18948853990500146585664365 7105820246437554969624137)
        ·
          refine ⟨5329365184828166227218103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7105820246437554969624137 5329365184828166227218103)
          ·
            refine ⟨7994047777242249340827155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5329365184828166227218103 7994047777242249340827155)
            ·
              refine ⟨11991071665863374011240733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7994047777242249340827155 11991071665863374011240733)
              ·
                refine ⟨4496651874698765254215275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11991071665863374011240733 4496651874698765254215275)
                ·
                  refine ⟨6744977812048147881322913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4496651874698765254215275 6744977812048147881322913)
                  ·
                    refine ⟨5058733359036110910992185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6744977812048147881322913 5058733359036110910992185)
                    ·
                      refine ⟨3794050019277083183244139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5058733359036110910992185 3794050019277083183244139)
                      ·
                        rfl

theorem cell23_7388886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_7388886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388886 prefixEnd_7388886 := by exact prefixLift 7388886
  have htrace : WordTrace (prefixWord ++ tailWord_7388886) baseStart_7388886 baseEnd_7388886 := by
    simpa [prefixWord, tailWord_7388886, baseEnd_7388886] using wordTrace_append hprefix tailTrace_7388886
  have hstable : (prefixWord ++ tailWord_7388886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388886).length < 2 ^ (prefixWord ++ tailWord_7388886).sum := by decide
  have hdescent : baseEnd_7388886 < baseStart_7388886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388907 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 3]
def baseStart_7388907 : Nat := 118140960795 + 7388907 * 2 ^ 59
def prefixEnd_7388907 : Nat := 4983230072969 + 3 ^ 40 * 7388907 * 2
def baseEnd_7388907 : Nat := 3794060802370827601081541

theorem tailTrace_7388907 : CollatzResearch.WordTrace tailWord_7388907 prefixEnd_7388907 3794060802370827601081541 := by
  unfold tailWord_7388907
  simp only [CollatzResearch.WordTrace]
  refine ⟨269495578242259338693740975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179663718828172892462493983 269495578242259338693740975)
  ·
    refine ⟨404243367363389008040611463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269495578242259338693740975 404243367363389008040611463)
    ·
      refine ⟨606365051045083512060917195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404243367363389008040611463 606365051045083512060917195)
      ·
        refine ⟨909547576567625268091375793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606365051045083512060917195 909547576567625268091375793)
        ·
          refine ⟨682160682425718951068531845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 909547576567625268091375793 682160682425718951068531845)
          ·
            refine ⟨127905127954822303325349721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 682160682425718951068531845 127905127954822303325349721)
            ·
              refine ⟨95928845966116727494012291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127905127954822303325349721 95928845966116727494012291)
              ·
                refine ⟨143893268949175091241018437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95928845966116727494012291 143893268949175091241018437)
                ·
                  refine ⟨26979987927970329607690957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143893268949175091241018437 26979987927970329607690957)
                  ·
                    refine ⟨10117495472988873602884109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26979987927970329607690957 10117495472988873602884109)
                    ·
                      refine ⟨3794060802370827601081541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10117495472988873602884109 3794060802370827601081541)
                      ·
                        rfl

theorem cell23_7388907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 3].length) (baseStart_7388907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388907 prefixEnd_7388907 := by exact prefixLift 7388907
  have htrace : WordTrace (prefixWord ++ tailWord_7388907) baseStart_7388907 baseEnd_7388907 := by
    simpa [prefixWord, tailWord_7388907, baseEnd_7388907] using wordTrace_append hprefix tailTrace_7388907
  have hstable : (prefixWord ++ tailWord_7388907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388907).length < 2 ^ (prefixWord ++ tailWord_7388907).sum := by decide
  have hdescent : baseEnd_7388907 < baseStart_7388907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388991 : List Nat := [1, 1, 2, 2, 6, 1, 1, 2, 3, 4]
def baseStart_7388991 : Nat := 118140960795 + 7388991 * 2 ^ 59
def prefixEnd_7388991 : Nat := 4983230072969 + 3 ^ 40 * 7388991 * 2
def baseEnd_7388991 : Nat := 1264701311581935090810385

theorem tailTrace_7388991 : CollatzResearch.WordTrace tailWord_7388991 prefixEnd_7388991 1264701311581935090810385 := by
  unfold tailWord_7388991
  simp only [CollatzResearch.WordTrace]
  refine ⟨269498641973955021039798827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179665761315970014026532551 269498641973955021039798827)
  ·
    refine ⟨404247962960932531559698241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269498641973955021039798827 404247962960932531559698241)
    ·
      refine ⟨303185972220699398669773681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404247962960932531559698241 303185972220699398669773681)
      ·
        refine ⟨227389479165524549002330261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303185972220699398669773681 227389479165524549002330261)
        ·
          refine ⟨10658881835883963234484231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 227389479165524549002330261 10658881835883963234484231)
          ·
            refine ⟨15988322753825944851726347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10658881835883963234484231 15988322753825944851726347)
            ·
              refine ⟨23982484130738917277589521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15988322753825944851726347 23982484130738917277589521)
              ·
                refine ⟨17986863098054187958192141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23982484130738917277589521 17986863098054187958192141)
                ·
                  refine ⟨6745073661770320484322053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17986863098054187958192141 6745073661770320484322053)
                  ·
                    refine ⟨1264701311581935090810385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6745073661770320484322053 1264701311581935090810385)
                    ·
                      rfl

theorem cell23_7388991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 4].length) (baseStart_7388991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388991 prefixEnd_7388991 := by exact prefixLift 7388991
  have htrace : WordTrace (prefixWord ++ tailWord_7388991) baseStart_7388991 baseEnd_7388991 := by
    simpa [prefixWord, tailWord_7388991, baseEnd_7388991] using wordTrace_append hprefix tailTrace_7388991
  have hstable : (prefixWord ++ tailWord_7388991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388991).length < 2 ^ (prefixWord ++ tailWord_7388991).sum := by decide
  have hdescent : baseEnd_7388991 < baseStart_7388991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7388998 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_7388998 : Nat := 118140960795 + 7388998 * 2 ^ 59
def prefixEnd_7388998 : Nat := 4983230072969 + 3 ^ 40 * 7388998 * 2
def baseEnd_7388998 : Nat := 3794107529110386745043623

theorem tailTrace_7388998 : CollatzResearch.WordTrace tailWord_7388998 prefixEnd_7388998 3794107529110386745043623 := by
  unfold tailWord_7388998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8421840540154051913603239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 179665931523286440823535765 8421840540154051913603239)
  ·
    refine ⟨12632760810231077870404859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8421840540154051913603239 12632760810231077870404859)
    ·
      refine ⟨18949141215346616805607289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12632760810231077870404859 18949141215346616805607289)
      ·
        refine ⟨14211855911509962604205467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18949141215346616805607289 14211855911509962604205467)
        ·
          refine ⟨21317783867264943906308201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14211855911509962604205467 21317783867264943906308201)
          ·
            refine ⟨15988337900448707929731151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21317783867264943906308201 15988337900448707929731151)
            ·
              refine ⟨23982506850673061894596727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15988337900448707929731151 23982506850673061894596727)
              ·
                refine ⟨35973760276009592841895091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23982506850673061894596727 35973760276009592841895091)
                ·
                  refine ⟨53960640414014389262842637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35973760276009592841895091 53960640414014389262842637)
                  ·
                    refine ⟨20235240155255395973565989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53960640414014389262842637 20235240155255395973565989)
                    ·
                      refine ⟨3794107529110386745043623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20235240155255395973565989 3794107529110386745043623)
                      ·
                        rfl

theorem cell23_7388998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_7388998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7388998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7388998 prefixEnd_7388998 := by exact prefixLift 7388998
  have htrace : WordTrace (prefixWord ++ tailWord_7388998) baseStart_7388998 baseEnd_7388998 := by
    simpa [prefixWord, tailWord_7388998, baseEnd_7388998] using wordTrace_append hprefix tailTrace_7388998
  have hstable : (prefixWord ++ tailWord_7388998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7388998).length < 2 ^ (prefixWord ++ tailWord_7388998).sum := by decide
  have hdescent : baseEnd_7388998 < baseStart_7388998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7388998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389038 : List Nat := [4, 1, 2, 3, 1, 2, 3, 1, 6]
def baseStart_7389038 : Nat := 118140960795 + 7389038 * 2 ^ 59
def prefixEnd_7389038 : Nat := 4983230072969 + 3 ^ 40 * 7389038 * 2
def baseEnd_7389038 : Nat := 421569785370729620949271

theorem tailTrace_7389038 : CollatzResearch.WordTrace tailWord_7389038 prefixEnd_7389038 421569785370729620949271 := by
  unfold tailWord_7389038
  simp only [CollatzResearch.WordTrace]
  refine ⟨33687544525598093508344971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179666904136523165377839845 33687544525598093508344971)
  ·
    refine ⟨50531316788397140262517457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33687544525598093508344971 50531316788397140262517457)
    ·
      refine ⟨37898487591297855196888093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50531316788397140262517457 37898487591297855196888093)
      ·
        refine ⟨14211932846736695698833035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37898487591297855196888093 14211932846736695698833035)
        ·
          refine ⟨21317899270105043548249553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14211932846736695698833035 21317899270105043548249553)
          ·
            refine ⟨15988424452578782661187165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21317899270105043548249553 15988424452578782661187165)
            ·
              refine ⟨5995659169717043497945187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15988424452578782661187165 5995659169717043497945187)
              ·
                refine ⟨8993488754575565246917781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5995659169717043497945187 8993488754575565246917781)
                ·
                  refine ⟨421569785370729620949271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8993488754575565246917781 421569785370729620949271)
                  ·
                    rfl

theorem cell23_7389038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_7389038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389038 prefixEnd_7389038 := by exact prefixLift 7389038
  have htrace : WordTrace (prefixWord ++ tailWord_7389038) baseStart_7389038 baseEnd_7389038 := by
    simpa [prefixWord, tailWord_7389038, baseEnd_7389038] using wordTrace_append hprefix tailTrace_7389038
  have hstable : (prefixWord ++ tailWord_7389038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389038).length < 2 ^ (prefixWord ++ tailWord_7389038).sum := by decide
  have hdescent : baseEnd_7389038 < baseStart_7389038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389082 : List Nat := [3, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3]
def baseStart_7389082 : Nat := 118140960795 + 7389082 * 2 ^ 59
def prefixEnd_7389082 : Nat := 4983230072969 + 3 ^ 40 * 7389082 * 2
def baseEnd_7389082 : Nat := 3794150661485364416393237

theorem tailTrace_7389082 : CollatzResearch.WordTrace tailWord_7389082 prefixEnd_7389082 3794150661485364416393237 := by
  unfold tailWord_7389082
  simp only [CollatzResearch.WordTrace]
  refine ⟨67375490254156335895340375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179667974011083562387574333 67375490254156335895340375)
  ·
    refine ⟨101063235381234503843010563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67375490254156335895340375 101063235381234503843010563)
    ·
      refine ⟨151594853071851755764515845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101063235381234503843010563 151594853071851755764515845)
      ·
        refine ⟨28424034950972204205846721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151594853071851755764515845 28424034950972204205846721)
        ·
          refine ⟨21318026213229153154385041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28424034950972204205846721 21318026213229153154385041)
          ·
            refine ⟨15988519659921864865788781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21318026213229153154385041 15988519659921864865788781)
            ·
              refine ⟨5995694872470699324670793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15988519659921864865788781 5995694872470699324670793)
              ·
                refine ⟨4496771154353024493503095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5995694872470699324670793 4496771154353024493503095)
                ·
                  refine ⟨6745156731529536740254643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4496771154353024493503095 6745156731529536740254643)
                  ·
                    refine ⟨10117735097294305110381965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6745156731529536740254643 10117735097294305110381965)
                    ·
                      refine ⟨3794150661485364416393237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10117735097294305110381965 3794150661485364416393237)
                      ·
                        rfl

theorem cell23_7389082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_7389082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389082 prefixEnd_7389082 := by exact prefixLift 7389082
  have htrace : WordTrace (prefixWord ++ tailWord_7389082) baseStart_7389082 baseEnd_7389082 := by
    simpa [prefixWord, tailWord_7389082, baseEnd_7389082] using wordTrace_append hprefix tailTrace_7389082
  have hstable : (prefixWord ++ tailWord_7389082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389082).length < 2 ^ (prefixWord ++ tailWord_7389082).sum := by decide
  have hdescent : baseEnd_7389082 < baseStart_7389082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389104 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 3]
def baseStart_7389104 : Nat := 118140960795 + 7389104 * 2 ^ 59
def prefixEnd_7389104 : Nat := 4983230072969 + 3 ^ 40 * 7389104 * 2
def baseEnd_7389104 : Nat := 3794161958059763330318135

theorem tailTrace_7389104 : CollatzResearch.WordTrace tailWord_7389104 prefixEnd_7389104 3794161958059763330318135 := by
  unfold tailWord_7389104
  simp only [CollatzResearch.WordTrace]
  refine ⟨134751381711272820669331183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179668508948363760892441577 134751381711272820669331183)
  ·
    refine ⟨202127072566909231003996775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134751381711272820669331183 202127072566909231003996775)
    ·
      refine ⟨303190608850363846505995163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202127072566909231003996775 303190608850363846505995163)
      ·
        refine ⟨454785913275545769758992745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303190608850363846505995163 454785913275545769758992745)
        ·
          refine ⟨341089434956659327319244559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454785913275545769758992745 341089434956659327319244559)
          ·
            refine ⟨511634152434988990978866839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341089434956659327319244559 511634152434988990978866839)
            ·
              refine ⟨767451228652483486468300259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511634152434988990978866839 767451228652483486468300259)
              ·
                refine ⟨1151176842978725229702450389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767451228652483486468300259 1151176842978725229702450389)
                ·
                  refine ⟨26980707257313872571151181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1151176842978725229702450389 26980707257313872571151181)
                  ·
                    refine ⟨10117765221492702214181693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26980707257313872571151181 10117765221492702214181693)
                    ·
                      refine ⟨3794161958059763330318135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10117765221492702214181693 3794161958059763330318135)
                      ·
                        rfl

theorem cell23_7389104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 3].length) (baseStart_7389104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389104 prefixEnd_7389104 := by exact prefixLift 7389104
  have htrace : WordTrace (prefixWord ++ tailWord_7389104) baseStart_7389104 baseEnd_7389104 := by
    simpa [prefixWord, tailWord_7389104, baseEnd_7389104] using wordTrace_append hprefix tailTrace_7389104
  have hstable : (prefixWord ++ tailWord_7389104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389104).length < 2 ^ (prefixWord ++ tailWord_7389104).sum := by decide
  have hdescent : baseEnd_7389104 < baseStart_7389104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389144 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 1, 5, 4]
def baseStart_7389144 : Nat := 118140960795 + 7389144 * 2 ^ 59
def prefixEnd_7389144 : Nat := 4983230072969 + 3 ^ 40 * 7389144 * 2
def baseEnd_7389144 : Nat := 3794182497285943173817951

theorem tailTrace_7389144 : CollatzResearch.WordTrace tailWord_7389144 prefixEnd_7389144 3794182497285943173817951 := by
  unfold tailWord_7389144
  simp only [CollatzResearch.WordTrace]
  refine ⟨134752111171200364085059243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179669481561600485446745657 134752111171200364085059243)
  ·
    refine ⟨202128166756800546127588865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134752111171200364085059243 202128166756800546127588865)
    ·
      refine ⟨151596125067600409595691649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202128166756800546127588865 151596125067600409595691649)
      ·
        refine ⟨113697093800700307196768737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151596125067600409595691649 113697093800700307196768737)
        ·
          refine ⟨85272820350525230397576553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113697093800700307196768737 85272820350525230397576553)
          ·
            refine ⟨63954615262893922798182415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85272820350525230397576553 63954615262893922798182415)
            ·
              refine ⟨95931922894340884197273623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63954615262893922798182415 95931922894340884197273623)
              ·
                refine ⟨143897884341511326295910435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95931922894340884197273623 143897884341511326295910435)
                ·
                  refine ⟨215846826512266989443865653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143897884341511326295910435 215846826512266989443865653)
                  ·
                    refine ⟨20235639985525030260362405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 215846826512266989443865653 20235639985525030260362405)
                    ·
                      refine ⟨3794182497285943173817951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20235639985525030260362405 3794182497285943173817951)
                      ·
                        rfl

theorem cell23_7389144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_7389144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389144 prefixEnd_7389144 := by exact prefixLift 7389144
  have htrace : WordTrace (prefixWord ++ tailWord_7389144) baseStart_7389144 baseEnd_7389144 := by
    simpa [prefixWord, tailWord_7389144, baseEnd_7389144] using wordTrace_append hprefix tailTrace_7389144
  have hstable : (prefixWord ++ tailWord_7389144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389144).length < 2 ^ (prefixWord ++ tailWord_7389144).sum := by decide
  have hdescent : baseEnd_7389144 < baseStart_7389144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389164 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 5]
def baseStart_7389164 : Nat := 118140960795 + 7389164 * 2 ^ 59
def prefixEnd_7389164 : Nat := 4983230072969 + 3 ^ 40 * 7389164 * 2
def baseEnd_7389164 : Nat := 3794192766899033095567859

theorem tailTrace_7389164 : CollatzResearch.WordTrace tailWord_7389164 prefixEnd_7389164 3794192766899033095567859 := by
  unfold tailWord_7389164
  simp only [CollatzResearch.WordTrace]
  refine ⟨134752475901164135792923273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179669967868218847723897697 134752475901164135792923273)
  ·
    refine ⟨101064356925873101844692455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134752475901164135792923273 101064356925873101844692455)
    ·
      refine ⟨151596535388809652767038683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101064356925873101844692455 151596535388809652767038683)
      ·
        refine ⟨227394803083214479150558025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151596535388809652767038683 227394803083214479150558025)
        ·
          refine ⟨170546102312410859362918519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227394803083214479150558025 170546102312410859362918519)
          ·
            refine ⟨255819153468616289044377779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170546102312410859362918519 255819153468616289044377779)
            ·
              refine ⟨383728730202924433566566669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255819153468616289044377779 383728730202924433566566669)
              ·
                refine ⟨143898273826096662587462501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383728730202924433566566669 143898273826096662587462501)
                ·
                  refine ⟨26980926342393124235149219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143898273826096662587462501 26980926342393124235149219)
                  ·
                    refine ⟨40471389513589686352723829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26980926342393124235149219 40471389513589686352723829)
                    ·
                      refine ⟨3794192766899033095567859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40471389513589686352723829 3794192766899033095567859)
                      ·
                        rfl

theorem cell23_7389164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_7389164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389164 prefixEnd_7389164 := by exact prefixLift 7389164
  have htrace : WordTrace (prefixWord ++ tailWord_7389164) baseStart_7389164 baseEnd_7389164 := by
    simpa [prefixWord, tailWord_7389164, baseEnd_7389164] using wordTrace_append hprefix tailTrace_7389164
  have hstable : (prefixWord ++ tailWord_7389164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389164).length < 2 ^ (prefixWord ++ tailWord_7389164).sum := by decide
  have hdescent : baseEnd_7389164 < baseStart_7389164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389182 : List Nat := [4, 2, 2, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_7389182 : Nat := 118140960795 + 7389182 * 2 ^ 59
def prefixEnd_7389182 : Nat := 4983230072969 + 3 ^ 40 * 7389182 * 2
def baseEnd_7389182 : Nat := 3794202009550814025142777

theorem tailTrace_7389182 : CollatzResearch.WordTrace tailWord_7389182 prefixEnd_7389182 3794202009550814025142777 := by
  unfold tailWord_7389182
  simp only [CollatzResearch.WordTrace]
  refine ⟨33688201039532882582500225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179670405544175373773334533 33688201039532882582500225)
  ·
    refine ⟨25266150779649661936875169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33688201039532882582500225 25266150779649661936875169)
    ·
      refine ⟨18949613084737246452656377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25266150779649661936875169 18949613084737246452656377)
      ·
        refine ⟨14212209813552934839492283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18949613084737246452656377 14212209813552934839492283)
        ·
          refine ⟨21318314720329402259238425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14212209813552934839492283 21318314720329402259238425)
          ·
            refine ⟨15988736040247051694428819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21318314720329402259238425 15988736040247051694428819)
            ·
              refine ⟨23983104060370577541643229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15988736040247051694428819 23983104060370577541643229)
              ·
                refine ⟨8993664022638966578116211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23983104060370577541643229 8993664022638966578116211)
                ·
                  refine ⟨13490496033958449867174317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8993664022638966578116211 13490496033958449867174317)
                  ·
                    refine ⟨5058936012734418700190369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13490496033958449867174317 5058936012734418700190369)
                    ·
                      refine ⟨3794202009550814025142777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5058936012734418700190369 3794202009550814025142777)
                      ·
                        rfl

theorem cell23_7389182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_7389182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389182 prefixEnd_7389182 := by exact prefixLift 7389182
  have htrace : WordTrace (prefixWord ++ tailWord_7389182) baseStart_7389182 baseEnd_7389182 := by
    simpa [prefixWord, tailWord_7389182, baseEnd_7389182] using wordTrace_append hprefix tailTrace_7389182
  have hstable : (prefixWord ++ tailWord_7389182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389182).length < 2 ^ (prefixWord ++ tailWord_7389182).sum := by decide
  have hdescent : baseEnd_7389182 < baseStart_7389182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389191 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_7389191 : Nat := 118140960795 + 7389191 * 2 ^ 59
def prefixEnd_7389191 : Nat := 4983230072969 + 3 ^ 40 * 7389191 * 2
def baseEnd_7389191 : Nat := 3794206630876704489930235

theorem tailTrace_7389191 : CollatzResearch.WordTrace tailWord_7389191 prefixEnd_7389191 3794206630876704489930235 := by
  unfold tailWord_7389191
  simp only [CollatzResearch.WordTrace]
  refine ⟨269505936573230455197079427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179670624382153636798052951 269505936573230455197079427)
  ·
    refine ⟨404258904859845682795619141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269505936573230455197079427 404258904859845682795619141)
    ·
      refine ⟨75798544661221065524178589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404258904859845682795619141 75798544661221065524178589)
      ·
        refine ⟨28424454247957899571566971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75798544661221065524178589 28424454247957899571566971)
        ·
          refine ⟨42636681371936849357350457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28424454247957899571566971 42636681371936849357350457)
          ·
            refine ⟨31977511028952637018012843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42636681371936849357350457 31977511028952637018012843)
            ·
              refine ⟨47966266543428955527019265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31977511028952637018012843 47966266543428955527019265)
              ·
                refine ⟨35974699907571716645264449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47966266543428955527019265 35974699907571716645264449)
                ·
                  refine ⟨26981024930678787483948337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35974699907571716645264449 26981024930678787483948337)
                  ·
                    refine ⟨20235768698009090612961253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26981024930678787483948337 20235768698009090612961253)
                    ·
                      refine ⟨3794206630876704489930235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20235768698009090612961253 3794206630876704489930235)
                      ·
                        rfl

theorem cell23_7389191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_7389191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389191 prefixEnd_7389191 := by exact prefixLift 7389191
  have htrace : WordTrace (prefixWord ++ tailWord_7389191) baseStart_7389191 baseEnd_7389191 := by
    simpa [prefixWord, tailWord_7389191, baseEnd_7389191] using wordTrace_append hprefix tailTrace_7389191
  have hstable : (prefixWord ++ tailWord_7389191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389191).length < 2 ^ (prefixWord ++ tailWord_7389191).sum := by decide
  have hdescent : baseEnd_7389191 < baseStart_7389191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389268 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 1, 6, 2]
def baseStart_7389268 : Nat := 118140960795 + 7389268 * 2 ^ 59
def prefixEnd_7389268 : Nat := 4983230072969 + 3 ^ 40 * 7389268 * 2
def baseEnd_7389268 : Nat := 3794246168887100688667381

theorem tailTrace_7389268 : CollatzResearch.WordTrace tailWord_7389268 prefixEnd_7389268 3794246168887100688667381 := by
  unfold tailWord_7389268
  simp only [CollatzResearch.WordTrace]
  refine ⟨134754372496975748673816229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179672496662634331565088305 134754372496975748673816229)
  ·
    refine ⟨25266444843182952876340543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134754372496975748673816229 25266444843182952876340543)
    ·
      refine ⟨37899667264774429314510815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25266444843182952876340543 37899667264774429314510815)
      ·
        refine ⟨56849500897161643971766223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37899667264774429314510815 56849500897161643971766223)
        ·
          refine ⟨85274251345742465957649335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56849500897161643971766223 85274251345742465957649335)
          ·
            refine ⟨127911377018613698936474003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85274251345742465957649335 127911377018613698936474003)
            ·
              refine ⟨191867065527920548404711005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127911377018613698936474003 191867065527920548404711005)
              ·
                refine ⟨71950149572970205651766627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191867065527920548404711005 71950149572970205651766627)
                ·
                  refine ⟨107925224359455308477649941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71950149572970205651766627 107925224359455308477649941)
                  ·
                    refine ⟨5058994891849467584889841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107925224359455308477649941 5058994891849467584889841)
                    ·
                      refine ⟨3794246168887100688667381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5058994891849467584889841 3794246168887100688667381)
                      ·
                        rfl

theorem cell23_7389268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_7389268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389268 prefixEnd_7389268 := by exact prefixLift 7389268
  have htrace : WordTrace (prefixWord ++ tailWord_7389268) baseStart_7389268 baseEnd_7389268 := by
    simpa [prefixWord, tailWord_7389268, baseEnd_7389268] using wordTrace_append hprefix tailTrace_7389268
  have hstable : (prefixWord ++ tailWord_7389268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389268).length < 2 ^ (prefixWord ++ tailWord_7389268).sum := by decide
  have hdescent : baseEnd_7389268 < baseStart_7389268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389271 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 3]
def baseStart_7389271 : Nat := 118140960795 + 7389271 * 2 ^ 59
def prefixEnd_7389271 : Nat := 4983230072969 + 3 ^ 40 * 7389271 * 2
def baseEnd_7389271 : Nat := 3794247709329064176929867

theorem tailTrace_7389271 : CollatzResearch.WordTrace tailWord_7389271 prefixEnd_7389271 3794247709329064176929867 := by
  unfold tailWord_7389271
  simp only [CollatzResearch.WordTrace]
  refine ⟨269508854412940628859991667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179672569608627085906661111 269508854412940628859991667)
  ·
    refine ⟨404263281619410943289987501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269508854412940628859991667 404263281619410943289987501)
    ·
      refine ⟨151598730607279103733745313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404263281619410943289987501 151598730607279103733745313)
      ·
        refine ⟨113699047955459327800308985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151598730607279103733745313 113699047955459327800308985)
        ·
          refine ⟨85274285966594495850231739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113699047955459327800308985 85274285966594495850231739)
          ·
            refine ⟨127911428949891743775347609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85274285966594495850231739 127911428949891743775347609)
            ·
              refine ⟨95933571712418807831510707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127911428949891743775347609 95933571712418807831510707)
              ·
                refine ⟨143900357568628211747266061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95933571712418807831510707 143900357568628211747266061)
                ·
                  refine ⟨53962634088235579405224773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143900357568628211747266061 53962634088235579405224773)
                  ·
                    refine ⟨10117993891544171138479645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53962634088235579405224773 10117993891544171138479645)
                    ·
                      refine ⟨3794247709329064176929867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10117993891544171138479645 3794247709329064176929867)
                      ·
                        rfl

theorem cell23_7389271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_7389271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389271 prefixEnd_7389271 := by exact prefixLift 7389271
  have htrace : WordTrace (prefixWord ++ tailWord_7389271) baseStart_7389271 baseEnd_7389271 := by
    simpa [prefixWord, tailWord_7389271, baseEnd_7389271] using wordTrace_append hprefix tailTrace_7389271
  have hstable : (prefixWord ++ tailWord_7389271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389271).length < 2 ^ (prefixWord ++ tailWord_7389271).sum := by decide
  have hdescent : baseEnd_7389271 < baseStart_7389271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389308 : List Nat := [2, 2, 2, 1, 1, 5, 2, 2, 6]
def baseStart_7389308 : Nat := 118140960795 + 7389308 * 2 ^ 59
def prefixEnd_7389308 : Nat := 4983230072969 + 3 ^ 40 * 7389308 * 2
def baseEnd_7389308 : Nat := 421585189790364503574133

theorem tailTrace_7389308 : CollatzResearch.WordTrace tailWord_7389308 prefixEnd_7389308 421585189790364503574133 := by
  unfold tailWord_7389308
  simp only [CollatzResearch.WordTrace]
  refine ⟨134755101956903292089544289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179673469275871056119392385 134755101956903292089544289)
  ·
    refine ⟨101066326467677469067158217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134755101956903292089544289 101066326467677469067158217)
    ·
      refine ⟨75799744850758101800368663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101066326467677469067158217 75799744850758101800368663)
      ·
        refine ⟨113699617276137152700552995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75799744850758101800368663 113699617276137152700552995)
        ·
          refine ⟨170549425914205729050829493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113699617276137152700552995 170549425914205729050829493)
          ·
            refine ⟨15989008679456787098515265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170549425914205729050829493 15989008679456787098515265)
            ·
              refine ⟨11991756509592590323886449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15989008679456787098515265 11991756509592590323886449)
              ·
                refine ⟨8993817382194442742914837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11991756509592590323886449 8993817382194442742914837)
                ·
                  refine ⟨421585189790364503574133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8993817382194442742914837 421585189790364503574133)
                  ·
                    rfl

theorem cell23_7389308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 6].length) (baseStart_7389308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389308 prefixEnd_7389308 := by exact prefixLift 7389308
  have htrace : WordTrace (prefixWord ++ tailWord_7389308) baseStart_7389308 baseEnd_7389308 := by
    simpa [prefixWord, tailWord_7389308, baseEnd_7389308] using wordTrace_append hprefix tailTrace_7389308
  have hstable : (prefixWord ++ tailWord_7389308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389308).length < 2 ^ (prefixWord ++ tailWord_7389308).sum := by decide
  have hdescent : baseEnd_7389308 < baseStart_7389308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389321 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 5, 5]
def baseStart_7389321 : Nat := 118140960795 + 7389321 * 2 ^ 59
def prefixEnd_7389321 : Nat := 4983230072969 + 3 ^ 40 * 7389321 * 2
def baseEnd_7389321 : Nat := 1264757794453929660434879

theorem tailTrace_7389321 : CollatzResearch.WordTrace tailWord_7389321 prefixEnd_7389321 1264757794453929660434879 := by
  unfold tailWord_7389321
  simp only [CollatzResearch.WordTrace]
  refine ⟨269510678062759487399311817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179673785375172991599541211 269510678062759487399311817)
  ·
    refine ⟨202133008547069615549483863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269510678062759487399311817 202133008547069615549483863)
    ·
      refine ⟨303199512820604423324225795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202133008547069615549483863 303199512820604423324225795)
      ·
        refine ⟨454799269230906634986338693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303199512820604423324225795 454799269230906634986338693)
        ·
          refine ⟨85274862980794994059938505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 454799269230906634986338693 85274862980794994059938505)
          ·
            refine ⟨63956147235596245544953879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85274862980794994059938505 63956147235596245544953879)
            ·
              refine ⟨95934220853394368317430819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63956147235596245544953879 95934220853394368317430819)
              ·
                refine ⟨143901331280091552476146229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95934220853394368317430819 143901331280091552476146229)
                ·
                  refine ⟨13490749807508583044638709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143901331280091552476146229 13490749807508583044638709)
                  ·
                    refine ⟨1264757794453929660434879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13490749807508583044638709 1264757794453929660434879)
                    ·
                      rfl

theorem cell23_7389321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 5].length) (baseStart_7389321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389321 prefixEnd_7389321 := by exact prefixLift 7389321
  have htrace : WordTrace (prefixWord ++ tailWord_7389321) baseStart_7389321 baseEnd_7389321 := by
    simpa [prefixWord, tailWord_7389321, baseEnd_7389321] using wordTrace_append hprefix tailTrace_7389321
  have hstable : (prefixWord ++ tailWord_7389321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389321).length < 2 ^ (prefixWord ++ tailWord_7389321).sum := by decide
  have hdescent : baseEnd_7389321 < baseStart_7389321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389328 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 1, 5, 2]
def baseStart_7389328 : Nat := 118140960795 + 7389328 * 2 ^ 59
def prefixEnd_7389328 : Nat := 4983230072969 + 3 ^ 40 * 7389328 * 2
def baseEnd_7389328 : Nat := 3794276977726370453917105

theorem tailTrace_7389328 : CollatzResearch.WordTrace tailWord_7389328 prefixEnd_7389328 3794276977726370453917105 := by
  unfold tailWord_7389328
  simp only [CollatzResearch.WordTrace]
  refine ⟨134755466686867063797408319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179673955582489418396544425 134755466686867063797408319)
  ·
    refine ⟨202133200030300595696112479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134755466686867063797408319 202133200030300595696112479)
    ·
      refine ⟨303199800045450893544168719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202133200030300595696112479 303199800045450893544168719)
      ·
        refine ⟨454799700068176340316253079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303199800045450893544168719 454799700068176340316253079)
        ·
          refine ⟨682199550102264510474379619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454799700068176340316253079 682199550102264510474379619)
          ·
            refine ⟨1023299325153396765711569429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682199550102264510474379619 1023299325153396765711569429)
            ·
              refine ⟨47967155866565473392729817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1023299325153396765711569429 47967155866565473392729817)
              ·
                refine ⟨35975366899924105044547363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47967155866565473392729817 35975366899924105044547363)
                ·
                  refine ⟨53963050349886157566821045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35975366899924105044547363 53963050349886157566821045)
                  ·
                    refine ⟨5059035970301827271889473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53963050349886157566821045 5059035970301827271889473)
                    ·
                      refine ⟨3794276977726370453917105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5059035970301827271889473 3794276977726370453917105)
                      ·
                        rfl

theorem cell23_7389328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 1, 5, 2].length) (baseStart_7389328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389328 prefixEnd_7389328 := by exact prefixLift 7389328
  have htrace : WordTrace (prefixWord ++ tailWord_7389328) baseStart_7389328 baseEnd_7389328 := by
    simpa [prefixWord, tailWord_7389328, baseEnd_7389328] using wordTrace_append hprefix tailTrace_7389328
  have hstable : (prefixWord ++ tailWord_7389328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389328).length < 2 ^ (prefixWord ++ tailWord_7389328).sum := by decide
  have hdescent : baseEnd_7389328 < baseStart_7389328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389345 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 1, 5, 2]
def baseStart_7389345 : Nat := 118140960795 + 7389345 * 2 ^ 59
def prefixEnd_7389345 : Nat := 4983230072969 + 3 ^ 40 * 7389345 * 2
def baseEnd_7389345 : Nat := 3794285706897496887404527

theorem tailTrace_7389345 : CollatzResearch.WordTrace tailWord_7389345 prefixEnd_7389345 3794285706897496887404527 := by
  unfold tailWord_7389345
  simp only [CollatzResearch.WordTrace]
  refine ⟨269511553414672539498185489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179674368943115026332123659 269511553414672539498185489)
  ·
    refine ⟨202133665061004404623639117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269511553414672539498185489 202133665061004404623639117)
    ·
      refine ⟨75800124397876651733864669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202133665061004404623639117 75800124397876651733864669)
      ·
        refine ⟨28425046649203744400199251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75800124397876651733864669 28425046649203744400199251)
        ·
          refine ⟨42637569973805616600298877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28425046649203744400199251 42637569973805616600298877)
          ·
            refine ⟨15989088740177106225112079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42637569973805616600298877 15989088740177106225112079)
            ·
              refine ⟨23983633110265659337668119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15989088740177106225112079 23983633110265659337668119)
              ·
                refine ⟨35975449665398489006502179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23983633110265659337668119 35975449665398489006502179)
                ·
                  refine ⟨53963174498097733509753269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35975449665398489006502179 53963174498097733509753269)
                  ·
                    refine ⟨5059047609196662516539369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53963174498097733509753269 5059047609196662516539369)
                    ·
                      refine ⟨3794285706897496887404527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5059047609196662516539369 3794285706897496887404527)
                      ·
                        rfl

theorem cell23_7389345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_7389345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389345 prefixEnd_7389345 := by exact prefixLift 7389345
  have htrace : WordTrace (prefixWord ++ tailWord_7389345) baseStart_7389345 baseEnd_7389345 := by
    simpa [prefixWord, tailWord_7389345, baseEnd_7389345] using wordTrace_append hprefix tailTrace_7389345
  have hstable : (prefixWord ++ tailWord_7389345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389345).length < 2 ^ (prefixWord ++ tailWord_7389345).sum := by decide
  have hdescent : baseEnd_7389345 < baseStart_7389345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389368 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 4, 4]
def baseStart_7389368 : Nat := 118140960795 + 7389368 * 2 ^ 59
def prefixEnd_7389368 : Nat := 4983230072969 + 3 ^ 40 * 7389368 * 2
def baseEnd_7389368 : Nat := 1264765838984183432472307

theorem tailTrace_7389368 : CollatzResearch.WordTrace tailWord_7389368 prefixEnd_7389368 1264765838984183432472307 := by
  unfold tailWord_7389368
  simp only [CollatzResearch.WordTrace]
  refine ⟨134756196146794607213136379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179674928195726142950848505 134756196146794607213136379)
  ·
    refine ⟨202134294220191910819704569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134756196146794607213136379 202134294220191910819704569)
    ·
      refine ⟨151600720665143933114778427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202134294220191910819704569 151600720665143933114778427)
      ·
        refine ⟨227401080997715899672167641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151600720665143933114778427 227401080997715899672167641)
        ·
          refine ⟨170550810748286924754125731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227401080997715899672167641 170550810748286924754125731)
          ·
            refine ⟨255826216122430387131188597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170550810748286924754125731 255826216122430387131188597)
            ·
              refine ⟨23983707761477848793548931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255826216122430387131188597 23983707761477848793548931)
              ·
                refine ⟨35975561642216773190323397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23983707761477848793548931 35975561642216773190323397)
                ·
                  refine ⟨6745417807915644973185637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35975561642216773190323397 6745417807915644973185637)
                  ·
                    refine ⟨1264765838984183432472307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6745417807915644973185637 1264765838984183432472307)
                    ·
                      rfl

theorem cell23_7389368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_7389368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389368 prefixEnd_7389368 := by exact prefixLift 7389368
  have htrace : WordTrace (prefixWord ++ tailWord_7389368) baseStart_7389368 baseEnd_7389368 := by
    simpa [prefixWord, tailWord_7389368, baseEnd_7389368] using wordTrace_append hprefix tailTrace_7389368
  have hstable : (prefixWord ++ tailWord_7389368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389368).length < 2 ^ (prefixWord ++ tailWord_7389368).sum := by decide
  have hdescent : baseEnd_7389368 < baseStart_7389368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389371 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 6]
def baseStart_7389371 : Nat := 118140960795 + 7389371 * 2 ^ 59
def prefixEnd_7389371 : Nat := 4983230072969 + 3 ^ 40 * 7389371 * 2
def baseEnd_7389371 : Nat := 3794299057394513785679407

theorem tailTrace_7389371 : CollatzResearch.WordTrace tailWord_7389371 prefixEnd_7389371 3794299057394513785679407 := by
  unfold tailWord_7389371
  simp only [CollatzResearch.WordTrace]
  refine ⟨269512501712578345938631967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179675001141718897292421311 269512501712578345938631967)
  ·
    refine ⟨404268752568867518907947951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269512501712578345938631967 404268752568867518907947951)
    ·
      refine ⟨606403128853301278361921927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404268752568867518907947951 606403128853301278361921927)
      ·
        refine ⟨909604693279951917542882891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606403128853301278361921927 909604693279951917542882891)
        ·
          refine ⟨1364407039919927876314324337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909604693279951917542882891 1364407039919927876314324337)
          ·
            refine ⟨1023305279939945907235743253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1364407039919927876314324337 1023305279939945907235743253)
            ·
              refine ⟨47967434997184964401675465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1023305279939945907235743253 47967434997184964401675465)
              ·
                refine ⟨35975576247888723301256599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47967434997184964401675465 35975576247888723301256599)
                ·
                  refine ⟨53963364371833084951884899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35975576247888723301256599 53963364371833084951884899)
                  ·
                    refine ⟨80945046557749627427827349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53963364371833084951884899 80945046557749627427827349)
                    ·
                      refine ⟨3794299057394513785679407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80945046557749627427827349 3794299057394513785679407)
                      ·
                        rfl

theorem cell23_7389371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 6].length) (baseStart_7389371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389371 prefixEnd_7389371 := by exact prefixLift 7389371
  have htrace : WordTrace (prefixWord ++ tailWord_7389371) baseStart_7389371 baseEnd_7389371 := by
    simpa [prefixWord, tailWord_7389371, baseEnd_7389371] using wordTrace_append hprefix tailTrace_7389371
  have hstable : (prefixWord ++ tailWord_7389371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389371).length < 2 ^ (prefixWord ++ tailWord_7389371).sum := by decide
  have hdescent : baseEnd_7389371 < baseStart_7389371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389408 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 3]
def baseStart_7389408 : Nat := 118140960795 + 7389408 * 2 ^ 59
def prefixEnd_7389408 : Nat := 4983230072969 + 3 ^ 40 * 7389408 * 2
def baseEnd_7389408 : Nat := 3794318056178730140916737

theorem tailTrace_7389408 : CollatzResearch.WordTrace tailWord_7389408 prefixEnd_7389408 3794318056178730140916737 := by
  unfold tailWord_7389408
  simp only [CollatzResearch.WordTrace]
  refine ⟨134756925606722150628864439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179675900808962867505152585 134756925606722150628864439)
  ·
    refine ⟨202135388410083225943296659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134756925606722150628864439 202135388410083225943296659)
    ·
      refine ⟨303203082615124838914944989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202135388410083225943296659 303203082615124838914944989)
      ·
        refine ⟨113701155980671814593104371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303203082615124838914944989 113701155980671814593104371)
        ·
          refine ⟨170551733971007721889656557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113701155980671814593104371 170551733971007721889656557)
          ·
            refine ⟨63956900239127895708621209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170551733971007721889656557 63956900239127895708621209)
            ·
              refine ⟨47967675179345921781465907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63956900239127895708621209 47967675179345921781465907)
              ·
                refine ⟨71951512769018882672198861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47967675179345921781465907 71951512769018882672198861)
                ·
                  refine ⟨26981817288382081002074573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71951512769018882672198861 26981817288382081002074573)
                  ·
                    refine ⟨10118181483143280375777965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26981817288382081002074573 10118181483143280375777965)
                    ·
                      refine ⟨3794318056178730140916737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10118181483143280375777965 3794318056178730140916737)
                      ·
                        rfl

theorem cell23_7389408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_7389408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389408 prefixEnd_7389408 := by exact prefixLift 7389408
  have htrace : WordTrace (prefixWord ++ tailWord_7389408) baseStart_7389408 baseEnd_7389408 := by
    simpa [prefixWord, tailWord_7389408, baseEnd_7389408] using wordTrace_append hprefix tailTrace_7389408
  have hstable : (prefixWord ++ tailWord_7389408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389408).length < 2 ^ (prefixWord ++ tailWord_7389408).sum := by decide
  have hdescent : baseEnd_7389408 < baseStart_7389408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389425 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 4, 1, 3]
def baseStart_7389425 : Nat := 118140960795 + 7389425 * 2 ^ 59
def prefixEnd_7389425 : Nat := 4983230072969 + 3 ^ 40 * 7389425 * 2
def baseEnd_7389425 : Nat := 3794326785349856574404159

theorem tailTrace_7389425 : CollatzResearch.WordTrace tailWord_7389425 prefixEnd_7389425 3794326785349856574404159 := by
  unfold tailWord_7389425
  simp only [CollatzResearch.WordTrace]
  refine ⟨269514471254382713161097729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179676314169588475440731819 269514471254382713161097729)
  ·
    refine ⟨202135853440787034870823297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269514471254382713161097729 202135853440787034870823297)
    ·
      refine ⟨151601890080590276153117473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202135853440787034870823297 151601890080590276153117473)
      ·
        refine ⟨113701417560442707114838105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151601890080590276153117473 113701417560442707114838105)
        ·
          refine ⟨85276063170332030336128579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113701417560442707114838105 85276063170332030336128579)
          ·
            refine ⟨127914094755498045504192869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85276063170332030336128579 127914094755498045504192869)
            ·
              refine ⟨23983892766655883532036163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127914094755498045504192869 23983892766655883532036163)
              ·
                refine ⟨35975839149983825298054245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23983892766655883532036163 35975839149983825298054245)
                ·
                  refine ⟨6745469840621967243385171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35975839149983825298054245 6745469840621967243385171)
                  ·
                    refine ⟨10118204760932950865077757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6745469840621967243385171 10118204760932950865077757)
                    ·
                      refine ⟨3794326785349856574404159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10118204760932950865077757 3794326785349856574404159)
                      ·
                        rfl

theorem cell23_7389425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_7389425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389425 prefixEnd_7389425 := by exact prefixLift 7389425
  have htrace : WordTrace (prefixWord ++ tailWord_7389425) baseStart_7389425 baseEnd_7389425 := by
    simpa [prefixWord, tailWord_7389425, baseEnd_7389425] using wordTrace_append hprefix tailTrace_7389425
  have hstable : (prefixWord ++ tailWord_7389425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389425).length < 2 ^ (prefixWord ++ tailWord_7389425).sum := by decide
  have hdescent : baseEnd_7389425 < baseStart_7389425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389528 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 1, 2, 5]
def baseStart_7389528 : Nat := 118140960795 + 7389528 * 2 ^ 59
def prefixEnd_7389528 : Nat := 4983230072969 + 3 ^ 40 * 7389528 * 2
def baseEnd_7389528 : Nat := 3794379673857269671416185

theorem tailTrace_7389528 : CollatzResearch.WordTrace tailWord_7389528 prefixEnd_7389528 3794379673857269671416185 := by
  unfold tailWord_7389528
  simp only [CollatzResearch.WordTrace]
  refine ⟨134759113986504780876048619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179678818648673041168064825 134759113986504780876048619)
  ·
    refine ⟨202138670979757171314072929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134759113986504780876048619 202138670979757171314072929)
    ·
      refine ⟨151604003234817878485554697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202138670979757171314072929 151604003234817878485554697)
      ·
        refine ⟨113703002426113408864166023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151604003234817878485554697 113703002426113408864166023)
        ·
          refine ⟨170554503639170113296249035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113703002426113408864166023 170554503639170113296249035)
          ·
            refine ⟨255831755458755169944373553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170554503639170113296249035 255831755458755169944373553)
            ·
              refine ⟨191873816594066377458280165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255831755458755169944373553 191873816594066377458280165)
              ·
                refine ⟨35976340611387445773427531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191873816594066377458280165 35976340611387445773427531)
                ·
                  refine ⟨53964510917081168660141297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35976340611387445773427531 53964510917081168660141297)
                  ·
                    refine ⟨40473383187810876495105973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53964510917081168660141297 40473383187810876495105973)
                    ·
                      refine ⟨3794379673857269671416185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40473383187810876495105973 3794379673857269671416185)
                      ·
                        rfl

theorem cell23_7389528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_7389528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389528 prefixEnd_7389528 := by exact prefixLift 7389528
  have htrace : WordTrace (prefixWord ++ tailWord_7389528) baseStart_7389528 baseEnd_7389528 := by
    simpa [prefixWord, tailWord_7389528, baseEnd_7389528] using wordTrace_append hprefix tailTrace_7389528
  have hstable : (prefixWord ++ tailWord_7389528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389528).length < 2 ^ (prefixWord ++ tailWord_7389528).sum := by decide
  have hdescent : baseEnd_7389528 < baseStart_7389528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389575 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 3]
def baseStart_7389575 : Nat := 118140960795 + 7389575 * 2 ^ 59
def prefixEnd_7389575 : Nat := 4983230072969 + 3 ^ 40 * 7389575 * 2
def baseEnd_7389575 : Nat := 3794403807448030987528469

theorem tailTrace_7389575 : CollatzResearch.WordTrace tailWord_7389575 prefixEnd_7389575 3794403807448030987528469 := by
  unfold tailWord_7389575
  simp only [CollatzResearch.WordTrace]
  refine ⟨269519942203839288779058179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179679961469226192519372119 269519942203839288779058179)
  ·
    refine ⟨404279913305758933168587269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269519942203839288779058179 404279913305758933168587269)
    ·
      refine ⟨75802483744829799969110113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404279913305758933168587269 75802483744829799969110113)
      ·
        refine ⟨56851862808622349976832585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75802483744829799969110113 56851862808622349976832585)
        ·
          refine ⟨42638897106466762482624439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56851862808622349976832585 42638897106466762482624439)
          ·
            refine ⟨63958345659700143723936659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42638897106466762482624439 63958345659700143723936659)
            ·
              refine ⟨95937518489550215585904989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63958345659700143723936659 95937518489550215585904989)
              ·
                refine ⟨35976569433581330844714371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95937518489550215585904989 35976569433581330844714371)
                ·
                  refine ⟨53964854150371996267071557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35976569433581330844714371 53964854150371996267071557)
                  ·
                    refine ⟨10118410153194749300075917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53964854150371996267071557 10118410153194749300075917)
                    ·
                      refine ⟨3794403807448030987528469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10118410153194749300075917 3794403807448030987528469)
                      ·
                        rfl

theorem cell23_7389575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_7389575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389575 prefixEnd_7389575 := by exact prefixLift 7389575
  have htrace : WordTrace (prefixWord ++ tailWord_7389575) baseStart_7389575 baseEnd_7389575 := by
    simpa [prefixWord, tailWord_7389575, baseEnd_7389575] using wordTrace_append hprefix tailTrace_7389575
  have hstable : (prefixWord ++ tailWord_7389575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389575).length < 2 ^ (prefixWord ++ tailWord_7389575).sum := by decide
  have hdescent : baseEnd_7389575 < baseStart_7389575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389590 : List Nat := [5, 3, 1, 2, 1, 1, 3, 2, 5]
def baseStart_7389590 : Nat := 118140960795 + 7389590 * 2 ^ 59
def prefixEnd_7389590 : Nat := 4983230072969 + 3 ^ 40 * 7389590 * 2
def baseEnd_7389590 : Nat := 421601278850872047648989

theorem tailTrace_7389590 : CollatzResearch.WordTrace tailWord_7389590 prefixEnd_7389590 421601278850872047648989 := by
  unfold tailWord_7389590
  simp only [CollatzResearch.WordTrace]
  refine ⟨16845030581174059146303389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179680326199189964227236149 16845030581174059146303389)
  ·
    refine ⟨6316886467940272179863771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16845030581174059146303389 6316886467940272179863771)
    ·
      refine ⟨9475329701910408269795657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6316886467940272179863771 9475329701910408269795657)
      ·
        refine ⟨7106497276432806202346743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9475329701910408269795657 7106497276432806202346743)
        ·
          refine ⟨10659745914649209303520115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7106497276432806202346743 10659745914649209303520115)
          ·
            refine ⟨15989618871973813955280173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10659745914649209303520115 15989618871973813955280173)
            ·
              refine ⟨5996107076990180233230065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15989618871973813955280173 5996107076990180233230065)
              ·
                refine ⟨4497080307742635174922549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5996107076990180233230065 4497080307742635174922549)
                ·
                  refine ⟨421601278850872047648989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4497080307742635174922549 421601278850872047648989)
                  ·
                    rfl

theorem cell23_7389590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_7389590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389590 prefixEnd_7389590 := by exact prefixLift 7389590
  have htrace : WordTrace (prefixWord ++ tailWord_7389590) baseStart_7389590 baseEnd_7389590 := by
    simpa [prefixWord, tailWord_7389590, baseEnd_7389590] using wordTrace_append hprefix tailTrace_7389590
  have hstable : (prefixWord ++ tailWord_7389590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389590).length < 2 ^ (prefixWord ++ tailWord_7389590).sum := by decide
  have hdescent : baseEnd_7389590 < baseStart_7389590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389592 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 4, 2, 3]
def baseStart_7389592 : Nat := 118140960795 + 7389592 * 2 ^ 59
def prefixEnd_7389592 : Nat := 4983230072969 + 3 ^ 40 * 7389592 * 2
def baseEnd_7389592 : Nat := 3794412536619157421015891

theorem tailTrace_7389592 : CollatzResearch.WordTrace tailWord_7389592 prefixEnd_7389592 3794412536619157421015891 := by
  unfold tailWord_7389592
  simp only [CollatzResearch.WordTrace]
  refine ⟨134760281122388850341213515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179680374829851800454951353 134760281122388850341213515)
  ·
    refine ⟨202140421683583275511820273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134760281122388850341213515 202140421683583275511820273)
    ·
      refine ⟨151605316262687456633865205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202140421683583275511820273 151605316262687456633865205)
      ·
        refine ⟨14212998399626949059424863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151605316262687456633865205 14212998399626949059424863)
        ·
          refine ⟨21319497599440423589137295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14212998399626949059424863 21319497599440423589137295)
          ·
            refine ⟨31979246399160635383705943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21319497599440423589137295 31979246399160635383705943)
            ·
              refine ⟨47968869598740953075558915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31979246399160635383705943 47968869598740953075558915)
              ·
                refine ⟨71953304398111429613338373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47968869598740953075558915 71953304398111429613338373)
                ·
                  refine ⟨13491244574645893052500945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71953304398111429613338373 13491244574645893052500945)
                  ·
                    refine ⟨10118433430984419789375709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13491244574645893052500945 10118433430984419789375709)
                    ·
                      refine ⟨3794412536619157421015891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10118433430984419789375709 3794412536619157421015891)
                      ·
                        rfl

theorem cell23_7389592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_7389592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389592 prefixEnd_7389592 := by exact prefixLift 7389592
  have htrace : WordTrace (prefixWord ++ tailWord_7389592) baseStart_7389592 baseEnd_7389592 := by
    simpa [prefixWord, tailWord_7389592, baseEnd_7389592] using wordTrace_append hprefix tailTrace_7389592
  have hstable : (prefixWord ++ tailWord_7389592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389592).length < 2 ^ (prefixWord ++ tailWord_7389592).sum := by decide
  have hdescent : baseEnd_7389592 < baseStart_7389592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389650 : List Nat := [3, 2, 2, 4, 1, 2, 2, 2, 1, 4]
def baseStart_7389650 : Nat := 118140960795 + 7389650 * 2 ^ 59
def prefixEnd_7389650 : Nat := 4983230072969 + 3 ^ 40 * 7389650 * 2
def baseEnd_7389650 : Nat := 1264814106165706064696875

theorem tailTrace_7389650 : CollatzResearch.WordTrace tailWord_7389650 prefixEnd_7389650 1264814106165706064696875 := by
  unfold tailWord_7389650
  simp only [CollatzResearch.WordTrace]
  refine ⟨67380669419641894147009601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179681785119045051058692269 67380669419641894147009601)
  ·
    refine ⟨50535502064731420610257201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67380669419641894147009601 50535502064731420610257201)
    ·
      refine ⟨37901626548548565457692901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50535502064731420610257201 37901626548548565457692901)
      ·
        refine ⟨7106554977852856023317419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37901626548548565457692901 7106554977852856023317419)
        ·
          refine ⟨10659832466779284034976129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7106554977852856023317419 10659832466779284034976129)
          ·
            refine ⟨7994874350084463026232097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10659832466779284034976129 7994874350084463026232097)
            ·
              refine ⟨5996155762563347269674073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7994874350084463026232097 5996155762563347269674073)
              ·
                refine ⟨4497116821922510452255555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5996155762563347269674073 4497116821922510452255555)
                ·
                  refine ⟨6745675232883765678383333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4497116821922510452255555 6745675232883765678383333)
                  ·
                    refine ⟨1264814106165706064696875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6745675232883765678383333 1264814106165706064696875)
                    ·
                      rfl

theorem cell23_7389650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_7389650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389650 prefixEnd_7389650 := by exact prefixLift 7389650
  have htrace : WordTrace (prefixWord ++ tailWord_7389650) baseStart_7389650 baseEnd_7389650 := by
    simpa [prefixWord, tailWord_7389650, baseEnd_7389650] using wordTrace_append hprefix tailTrace_7389650
  have hstable : (prefixWord ++ tailWord_7389650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389650).length < 2 ^ (prefixWord ++ tailWord_7389650).sum := by decide
  have hdescent : baseEnd_7389650 < baseStart_7389650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389665 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_7389665 : Nat := 118140960795 + 7389665 * 2 ^ 59
def prefixEnd_7389665 : Nat := 4983230072969 + 3 ^ 40 * 7389665 * 2
def baseEnd_7389665 : Nat := 3794450020706935635403055

theorem tailTrace_7389665 : CollatzResearch.WordTrace tailWord_7389665 prefixEnd_7389665 3794450020706935635403055 := by
  unfold tailWord_7389665
  simp only [CollatzResearch.WordTrace]
  refine ⟨269523224773513234149834449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179682149849008822766556299 269523224773513234149834449)
  ·
    refine ⟨202142418580134925612375837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269523224773513234149834449 202142418580134925612375837)
    ·
      refine ⟨75803406967550597104640939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202142418580134925612375837 75803406967550597104640939)
      ·
        refine ⟨113705110451325895656961409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75803406967550597104640939 113705110451325895656961409)
        ·
          refine ⟨85278832838494421742721057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113705110451325895656961409 85278832838494421742721057)
          ·
            refine ⟨63959124628870816307040793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85278832838494421742721057 63959124628870816307040793)
            ·
              refine ⟨47969343471653112230280595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63959124628870816307040793 47969343471653112230280595)
              ·
                refine ⟨71954015207479668345420893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47969343471653112230280595 71954015207479668345420893)
                ·
                  refine ⟨26982755702804875629532835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71954015207479668345420893 26982755702804875629532835)
                  ·
                    refine ⟨40474133554207313444299253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26982755702804875629532835 40474133554207313444299253)
                    ·
                      refine ⟨3794450020706935635403055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40474133554207313444299253 3794450020706935635403055)
                      ·
                        rfl

theorem cell23_7389665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_7389665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389665 prefixEnd_7389665 := by exact prefixLift 7389665
  have htrace : WordTrace (prefixWord ++ tailWord_7389665) baseStart_7389665 baseEnd_7389665 := by
    simpa [prefixWord, tailWord_7389665, baseEnd_7389665] using wordTrace_append hprefix tailTrace_7389665
  have hstable : (prefixWord ++ tailWord_7389665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389665).length < 2 ^ (prefixWord ++ tailWord_7389665).sum := by decide
  have hdescent : baseEnd_7389665 < baseStart_7389665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389672 : List Nat := [2, 1, 4, 1, 1, 4, 2, 1, 1, 6]
def baseStart_7389672 : Nat := 118140960795 + 7389672 * 2 ^ 59
def prefixEnd_7389672 : Nat := 4983230072969 + 3 ^ 40 * 7389672 * 2
def baseEnd_7389672 : Nat := 1264817871690505702671841

theorem tailTrace_7389672 : CollatzResearch.WordTrace tailWord_7389672 prefixEnd_7389672 1264817871690505702671841 := by
  unfold tailWord_7389672
  simp only [CollatzResearch.WordTrace]
  refine ⟨134761740042243937172669635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179682320056325249563559513 134761740042243937172669635)
  ·
    refine ⟨202142610063365905759004453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134761740042243937172669635 202142610063365905759004453)
    ·
      refine ⟨37901739386881107329813335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202142610063365905759004453 37901739386881107329813335)
      ·
        refine ⟨56852609080321660994720003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37901739386881107329813335 56852609080321660994720003)
        ·
          refine ⟨85278913620482491492080005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56852609080321660994720003 85278913620482491492080005)
          ·
            refine ⟨15989796303840467154765001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85278913620482491492080005 15989796303840467154765001)
            ·
              refine ⟨11992347227880350366073751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15989796303840467154765001 11992347227880350366073751)
              ·
                refine ⟨17988520841820525549110627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11992347227880350366073751 17988520841820525549110627)
                ·
                  refine ⟨26982781262730788323665941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17988520841820525549110627 26982781262730788323665941)
                  ·
                    refine ⟨1264817871690505702671841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26982781262730788323665941 1264817871690505702671841)
                    ·
                      rfl

theorem cell23_7389672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_7389672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389672 prefixEnd_7389672 := by exact prefixLift 7389672
  have htrace : WordTrace (prefixWord ++ tailWord_7389672) baseStart_7389672 baseEnd_7389672 := by
    simpa [prefixWord, tailWord_7389672, baseEnd_7389672] using wordTrace_append hprefix tailTrace_7389672
  have hstable : (prefixWord ++ tailWord_7389672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389672).length < 2 ^ (prefixWord ++ tailWord_7389672).sum := by decide
  have hdescent : baseEnd_7389672 < baseStart_7389672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389745 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 1, 8]
def baseStart_7389745 : Nat := 118140960795 + 7389745 * 2 ^ 59
def prefixEnd_7389745 : Nat := 4983230072969 + 3 ^ 40 * 7389745 * 2
def baseEnd_7389745 : Nat := 1264830366386431774134229

theorem tailTrace_7389745 : CollatzResearch.WordTrace tailWord_7389745 prefixEnd_7389745 1264830366386431774134229 := by
  unfold tailWord_7389745
  simp only [CollatzResearch.WordTrace]
  refine ⟨269526142613223407812746689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179684095075482271875164459 269526142613223407812746689)
  ·
    refine ⟨202144606959917555859560017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269526142613223407812746689 202144606959917555859560017)
    ·
      refine ⟨151608455219938166894670013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202144606959917555859560017 151608455219938166894670013)
      ·
        refine ⟨56853170707476812585501255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151608455219938166894670013 56853170707476812585501255)
        ·
          refine ⟨85279756061215218878251883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56853170707476812585501255 85279756061215218878251883)
          ·
            refine ⟨127919634091822828317377825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85279756061215218878251883 127919634091822828317377825)
            ·
              refine ⟨95939725568867121238033369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127919634091822828317377825 95939725568867121238033369)
              ·
                refine ⟨71954794176650340928525027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95939725568867121238033369 71954794176650340928525027)
                ·
                  refine ⟨107932191264975511392787541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71954794176650340928525027 107932191264975511392787541)
                  ·
                    refine ⟨1264830366386431774134229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107932191264975511392787541 1264830366386431774134229)
                    ·
                      rfl

theorem cell23_7389745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_7389745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389745 prefixEnd_7389745 := by exact prefixLift 7389745
  have htrace : WordTrace (prefixWord ++ tailWord_7389745) baseStart_7389745 baseEnd_7389745 := by
    simpa [prefixWord, tailWord_7389745, baseEnd_7389745] using wordTrace_append hprefix tailTrace_7389745
  have hstable : (prefixWord ++ tailWord_7389745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389745).length < 2 ^ (prefixWord ++ tailWord_7389745).sum := by decide
  have hdescent : baseEnd_7389745 < baseStart_7389745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389756 : List Nat := [2, 2, 2, 2, 3, 1, 2, 3, 1, 3, 2]
def baseStart_7389756 : Nat := 118140960795 + 7389756 * 2 ^ 59
def prefixEnd_7389756 : Nat := 4983230072969 + 3 ^ 40 * 7389756 * 2
def baseEnd_7389756 : Nat := 3794496747446494779365137

theorem tailTrace_7389756 : CollatzResearch.WordTrace tailWord_7389756 prefixEnd_7389756 3794496747446494779365137 := by
  unfold tailWord_7389756
  simp only [CollatzResearch.WordTrace]
  refine ⟨134763271908091778345698561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179684362544122371127598081 134763271908091778345698561)
  ·
    refine ⟨101072453931068833759273921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134763271908091778345698561 101072453931068833759273921)
    ·
      refine ⟨75804340448301625319455441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101072453931068833759273921 75804340448301625319455441)
      ·
        refine ⟨56853255336226218989591581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75804340448301625319455441 56853255336226218989591581)
        ·
          refine ⟨21319970751084832121096843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56853255336226218989591581 21319970751084832121096843)
          ·
            refine ⟨31979956126627248181645265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21319970751084832121096843 31979956126627248181645265)
            ·
              refine ⟨23984967094970436136233949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31979956126627248181645265 23984967094970436136233949)
              ·
                refine ⟨8994362660613913551087731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23984967094970436136233949 8994362660613913551087731)
                ·
                  refine ⟨13491543990920870326631597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8994362660613913551087731 13491543990920870326631597)
                  ·
                    refine ⟨5059328996595326372486849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13491543990920870326631597 5059328996595326372486849)
                    ·
                      refine ⟨3794496747446494779365137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5059328996595326372486849 3794496747446494779365137)
                      ·
                        rfl

theorem cell23_7389756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_7389756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389756 prefixEnd_7389756 := by exact prefixLift 7389756
  have htrace : WordTrace (prefixWord ++ tailWord_7389756) baseStart_7389756 baseEnd_7389756 := by
    simpa [prefixWord, tailWord_7389756, baseEnd_7389756] using wordTrace_append hprefix tailTrace_7389756
  have hstable : (prefixWord ++ tailWord_7389756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389756).length < 2 ^ (prefixWord ++ tailWord_7389756).sum := by decide
  have hdescent : baseEnd_7389756 < baseStart_7389756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389764 : List Nat := [2, 3, 5, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_7389764 : Nat := 118140960795 + 7389764 * 2 ^ 59
def prefixEnd_7389764 : Nat := 4983230072969 + 3 ^ 40 * 7389764 * 2
def baseEnd_7389764 : Nat := 3794500855291730748065101

theorem tailTrace_7389764 : CollatzResearch.WordTrace tailWord_7389764 prefixEnd_7389764 3794500855291730748065101 := by
  unfold tailWord_7389764
  simp only [CollatzResearch.WordTrace]
  refine ⟨134763417800077287028844173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179684557066769716038458897 134763417800077287028844173)
  ·
    refine ⟨50536281675028982635816565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134763417800077287028844173 50536281675028982635816565)
    ·
      refine ⟨4737776407033967122107803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50536281675028982635816565 4737776407033967122107803)
      ·
        refine ⟨7106664610550950683161705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4737776407033967122107803 7106664610550950683161705)
        ·
          refine ⟨5329998457913213012371279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7106664610550950683161705 5329998457913213012371279)
          ·
            refine ⟨7994997686869819518556919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5329998457913213012371279 7994997686869819518556919)
            ·
              refine ⟨11992496530304729277835379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7994997686869819518556919 11992496530304729277835379)
              ·
                refine ⟨17988744795457093916753069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11992496530304729277835379 17988744795457093916753069)
                ·
                  refine ⟨6745779298296410218782401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17988744795457093916753069 6745779298296410218782401)
                  ·
                    refine ⟨5059334473722307664086801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6745779298296410218782401 5059334473722307664086801)
                    ·
                      refine ⟨3794500855291730748065101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5059334473722307664086801 3794500855291730748065101)
                      ·
                        rfl

theorem cell23_7389764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_7389764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389764 prefixEnd_7389764 := by exact prefixLift 7389764
  have htrace : WordTrace (prefixWord ++ tailWord_7389764) baseStart_7389764 baseEnd_7389764 := by
    simpa [prefixWord, tailWord_7389764, baseEnd_7389764] using wordTrace_append hprefix tailTrace_7389764
  have hstable : (prefixWord ++ tailWord_7389764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389764).length < 2 ^ (prefixWord ++ tailWord_7389764).sum := by decide
  have hdescent : baseEnd_7389764 < baseStart_7389764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389772 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 2, 4, 3]
def baseStart_7389772 : Nat := 118140960795 + 7389772 * 2 ^ 59
def prefixEnd_7389772 : Nat := 4983230072969 + 3 ^ 40 * 7389772 * 2
def baseEnd_7389772 : Nat := 3794504963136966716765063

theorem tailTrace_7389772 : CollatzResearch.WordTrace tailWord_7389772 prefixEnd_7389772 3794504963136966716765063 := by
  unfold tailWord_7389772
  simp only [CollatzResearch.WordTrace]
  refine ⟨134763563692062795711989785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179684751589417060949319713 134763563692062795711989785)
  ·
    refine ⟨101072672769047096783992339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134763563692062795711989785 101072672769047096783992339)
    ·
      refine ⟨151609009153570645175988509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101072672769047096783992339 151609009153570645175988509)
      ·
        refine ⟨56853378432588991940995691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151609009153570645175988509 56853378432588991940995691)
        ·
          refine ⟨85280067648883487911493537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56853378432588991940995691 85280067648883487911493537)
          ·
            refine ⟨63960050736662615933620153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85280067648883487911493537 63960050736662615933620153)
            ·
              refine ⟨47970038052496961950215115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63960050736662615933620153 47970038052496961950215115)
              ·
                refine ⟨71955057078745442925322673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47970038052496961950215115 71955057078745442925322673)
                ·
                  refine ⟨53966292809059082193992005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71955057078745442925322673 53966292809059082193992005)
                  ·
                    refine ⟨10118679901698577911373501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53966292809059082193992005 10118679901698577911373501)
                    ·
                      refine ⟨3794504963136966716765063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10118679901698577911373501 3794504963136966716765063)
                      ·
                        rfl

theorem cell23_7389772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_7389772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389772 prefixEnd_7389772 := by exact prefixLift 7389772
  have htrace : WordTrace (prefixWord ++ tailWord_7389772) baseStart_7389772 baseEnd_7389772 := by
    simpa [prefixWord, tailWord_7389772, baseEnd_7389772] using wordTrace_append hprefix tailTrace_7389772
  have hstable : (prefixWord ++ tailWord_7389772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389772).length < 2 ^ (prefixWord ++ tailWord_7389772).sum := by decide
  have hdescent : baseEnd_7389772 < baseStart_7389772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389829 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 2, 5, 2]
def baseStart_7389829 : Nat := 118140960795 + 7389829 * 2 ^ 59
def prefixEnd_7389829 : Nat := 4983230072969 + 3 ^ 40 * 7389829 * 2
def baseEnd_7389829 : Nat := 3794534231534272993752301

theorem tailTrace_7389829 : CollatzResearch.WordTrace tailWord_7389829 prefixEnd_7389829 3794534231534272993752301 := by
  unfold tailWord_7389829
  simp only [CollatzResearch.WordTrace]
  refine ⟨269529206344919090158804541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179686137563279393439203027 269529206344919090158804541)
  ·
    refine ⟨101073452379344658809551703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269529206344919090158804541 101073452379344658809551703)
    ·
      refine ⟨151610178569016988214327555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101073452379344658809551703 151610178569016988214327555)
      ·
        refine ⟨227415267853525482321491333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151610178569016988214327555 227415267853525482321491333)
        ·
          refine ⟨42640362722536027935279625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227415267853525482321491333 42640362722536027935279625)
          ·
            refine ⟨31980272041902020951459719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42640362722536027935279625 31980272041902020951459719)
            ·
              refine ⟨47970408062853031427189579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31980272041902020951459719 47970408062853031427189579)
              ·
                refine ⟨71955612094279547140784369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47970408062853031427189579 71955612094279547140784369)
                ·
                  refine ⟨53966709070709660355588277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71955612094279547140784369 53966709070709660355588277)
                  ·
                    refine ⟨5059378975379030658336401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53966709070709660355588277 5059378975379030658336401)
                    ·
                      refine ⟨3794534231534272993752301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5059378975379030658336401 3794534231534272993752301)
                      ·
                        rfl

theorem cell23_7389829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 5, 2].length) (baseStart_7389829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389829 prefixEnd_7389829 := by exact prefixLift 7389829
  have htrace : WordTrace (prefixWord ++ tailWord_7389829) baseStart_7389829 baseEnd_7389829 := by
    simpa [prefixWord, tailWord_7389829, baseEnd_7389829] using wordTrace_append hprefix tailTrace_7389829
  have hstable : (prefixWord ++ tailWord_7389829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389829).length < 2 ^ (prefixWord ++ tailWord_7389829).sum := by decide
  have hdescent : baseEnd_7389829 < baseStart_7389829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389856 : List Nat := [2, 1, 1, 4, 4, 2, 1, 1, 2, 5]
def baseStart_7389856 : Nat := 118140960795 + 7389856 * 2 ^ 59
def prefixEnd_7389856 : Nat := 4983230072969 + 3 ^ 40 * 7389856 * 2
def baseEnd_7389856 : Nat := 1264849365170648129371559

theorem tailTrace_7389856 : CollatzResearch.WordTrace tailWord_7389856 prefixEnd_7389856 1264849365170648129371559 := by
  unfold tailWord_7389856
  simp only [CollatzResearch.WordTrace]
  refine ⟨134765095557910636885018711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179686794077214182513358281 134765095557910636885018711)
  ·
    refine ⟨202147643336865955327528067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134765095557910636885018711 202147643336865955327528067)
    ·
      refine ⟨303221465005298932991292101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202147643336865955327528067 303221465005298932991292101)
      ·
        refine ⟨56854024688493549935867269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303221465005298932991292101 56854024688493549935867269)
        ·
          refine ⟨10660129629092540612975113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56854024688493549935867269 10660129629092540612975113)
          ·
            refine ⟨7995097221819405459731335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10660129629092540612975113 7995097221819405459731335)
            ·
              refine ⟨11992645832729108189597003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7995097221819405459731335 11992645832729108189597003)
              ·
                refine ⟨17988968749093662284395505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11992645832729108189597003 17988968749093662284395505)
                ·
                  refine ⟨13491726561820246713296629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17988968749093662284395505 13491726561820246713296629)
                  ·
                    refine ⟨1264849365170648129371559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13491726561820246713296629 1264849365170648129371559)
                    ·
                      rfl

theorem cell23_7389856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 2, 5].length) (baseStart_7389856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389856 prefixEnd_7389856 := by exact prefixLift 7389856
  have htrace : WordTrace (prefixWord ++ tailWord_7389856) baseStart_7389856 baseEnd_7389856 := by
    simpa [prefixWord, tailWord_7389856, baseEnd_7389856] using wordTrace_append hprefix tailTrace_7389856
  have hstable : (prefixWord ++ tailWord_7389856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389856).length < 2 ^ (prefixWord ++ tailWord_7389856).sum := by decide
  have hdescent : baseEnd_7389856 < baseStart_7389856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389882 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 8]
def baseStart_7389882 : Nat := 118140960795 + 7389882 * 2 ^ 59
def prefixEnd_7389882 : Nat := 4983230072969 + 3 ^ 40 * 7389882 * 2
def baseEnd_7389882 : Nat := 421617938445440142932173

theorem tailTrace_7389882 : CollatzResearch.WordTrace tailWord_7389882 prefixEnd_7389882 421617938445440142932173 := by
  unfold tailWord_7389882
  simp only [CollatzResearch.WordTrace]
  refine ⟨67382784853431770052620975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179687426275818053473655933 67382784853431770052620975)
  ·
    refine ⟨101074177280147655078931463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67382784853431770052620975 101074177280147655078931463)
    ·
      refine ⟨151611265920221482618397195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101074177280147655078931463 151611265920221482618397195)
      ·
        refine ⟨227416898880332223927595793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151611265920221482618397195 227416898880332223927595793)
        ·
          refine ⟨170562674160249167945696845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227416898880332223927595793 170562674160249167945696845)
          ·
            refine ⟨63961002810093437979636317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170562674160249167945696845 63961002810093437979636317)
            ·
              refine ⟨23985376053785039242363619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63961002810093437979636317 23985376053785039242363619)
              ·
                refine ⟨35978064080677558863545429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23985376053785039242363619 35978064080677558863545429)
                ·
                  refine ⟨421617938445440142932173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35978064080677558863545429 421617938445440142932173)
                  ·
                    rfl

theorem cell23_7389882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 8].length) (baseStart_7389882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389882 prefixEnd_7389882 := by exact prefixLift 7389882
  have htrace : WordTrace (prefixWord ++ tailWord_7389882) baseStart_7389882 baseEnd_7389882 := by
    simpa [prefixWord, tailWord_7389882, baseEnd_7389882] using wordTrace_append hprefix tailTrace_7389882
  have hstable : (prefixWord ++ tailWord_7389882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389882).length < 2 ^ (prefixWord ++ tailWord_7389882).sum := by decide
  have hdescent : baseEnd_7389882 < baseStart_7389882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389886 : List Nat := [4, 2, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_7389886 : Nat := 118140960795 + 7389886 * 2 ^ 59
def prefixEnd_7389886 : Nat := 4983230072969 + 3 ^ 40 * 7389886 * 2
def baseEnd_7389886 : Nat := 1264854499977193090246513

theorem tailTrace_7389886 : CollatzResearch.WordTrace tailWord_7389886 prefixEnd_7389886 1264854499977193090246513 := by
  unfold tailWord_7389886
  simp only [CollatzResearch.WordTrace]
  refine ⟨33691410663214073611703689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179687523537141725929086341 33691410663214073611703689)
  ·
    refine ⟨25268557997410555208777767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33691410663214073611703689 25268557997410555208777767)
    ·
      refine ⟨37902836996115832813166651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25268557997410555208777767 37902836996115832813166651)
      ·
        refine ⟨56854255494173749219749977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37902836996115832813166651 56854255494173749219749977)
        ·
          refine ⟨42640691620630311914812483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56854255494173749219749977 42640691620630311914812483)
          ·
            refine ⟨63961037430945467872218725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42640691620630311914812483 63961037430945467872218725)
            ·
              refine ⟨11992694518302275226041011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63961037430945467872218725 11992694518302275226041011)
              ·
                refine ⟨17989041777453412839061517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11992694518302275226041011 17989041777453412839061517)
                ·
                  refine ⟨6745890666545029814648069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17989041777453412839061517 6745890666545029814648069)
                  ·
                    refine ⟨1264854499977193090246513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6745890666545029814648069 1264854499977193090246513)
                    ·
                      rfl

theorem cell23_7389886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_7389886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389886 prefixEnd_7389886 := by exact prefixLift 7389886
  have htrace : WordTrace (prefixWord ++ tailWord_7389886) baseStart_7389886 baseEnd_7389886 := by
    simpa [prefixWord, tailWord_7389886, baseEnd_7389886] using wordTrace_append hprefix tailTrace_7389886
  have hstable : (prefixWord ++ tailWord_7389886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389886).length < 2 ^ (prefixWord ++ tailWord_7389886).sum := by decide
  have hdescent : baseEnd_7389886 < baseStart_7389886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389929 : List Nat := [1, 2, 1, 1, 1, 2, 6, 3, 1, 5]
def baseStart_7389929 : Nat := 118140960795 + 7389929 * 2 ^ 59
def prefixEnd_7389929 : Nat := 4983230072969 + 3 ^ 40 * 7389929 * 2
def baseEnd_7389929 : Nat := 1264861859866574200833947

theorem tailTrace_7389929 : CollatzResearch.WordTrace tailWord_7389929 prefixEnd_7389929 1264861859866574200833947 := by
  unfold tailWord_7389929
  simp only [CollatzResearch.WordTrace]
  refine ⟨269532853644556807237444841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179688569096371204824963227 269532853644556807237444841)
  ·
    refine ⟨202149640233417605428083631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269532853644556807237444841 202149640233417605428083631)
    ·
      refine ⟨303224460350126408142125447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202149640233417605428083631 303224460350126408142125447)
      ·
        refine ⟨454836690525189612213188171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303224460350126408142125447 454836690525189612213188171)
        ·
          refine ⟨682255035787784418319782257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454836690525189612213188171 682255035787784418319782257)
          ·
            refine ⟨511691276840838313739836693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682255035787784418319782257 511691276840838313739836693)
            ·
              refine ⟨23985528601914295956554845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 511691276840838313739836693 23985528601914295956554845)
              ·
                refine ⟨8994573225717860983708067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23985528601914295956554845 8994573225717860983708067)
                ·
                  refine ⟨13491859838576791475562101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8994573225717860983708067 13491859838576791475562101)
                  ·
                    refine ⟨1264861859866574200833947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13491859838576791475562101 1264861859866574200833947)
                    ·
                      rfl

theorem cell23_7389929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 5].length) (baseStart_7389929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389929 prefixEnd_7389929 := by exact prefixLift 7389929
  have htrace : WordTrace (prefixWord ++ tailWord_7389929) baseStart_7389929 baseEnd_7389929 := by
    simpa [prefixWord, tailWord_7389929, baseEnd_7389929] using wordTrace_append hprefix tailTrace_7389929
  have hstable : (prefixWord ++ tailWord_7389929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389929).length < 2 ^ (prefixWord ++ tailWord_7389929).sum := by decide
  have hdescent : baseEnd_7389929 < baseStart_7389929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389936 : List Nat := [2, 1, 1, 1, 3, 1, 5, 2, 2, 3, 2]
def baseStart_7389936 : Nat := 118140960795 + 7389936 * 2 ^ 59
def prefixEnd_7389936 : Nat := 4983230072969 + 3 ^ 40 * 7389936 * 2
def baseEnd_7389936 : Nat := 3794589173964304075114309

theorem tailTrace_7389936 : CollatzResearch.WordTrace tailWord_7389936 prefixEnd_7389936 3794589173964304075114309 := by
  unfold tailWord_7389936
  simp only [CollatzResearch.WordTrace]
  refine ⟨134766554477765723716474831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179688739303687631621966441 134766554477765723716474831)
  ·
    refine ⟨202149831716648585574712247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134766554477765723716474831 202149831716648585574712247)
    ·
      refine ⟨303224747574972878362068371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202149831716648585574712247 303224747574972878362068371)
      ·
        refine ⟨454837121362459317543102557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303224747574972878362068371 454837121362459317543102557)
        ·
          refine ⟨170563920510922244078663459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454837121362459317543102557 170563920510922244078663459)
          ·
            refine ⟨255845880766383366117995189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170563920510922244078663459 255845880766383366117995189)
            ·
              refine ⟨23985551321848440573562049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255845880766383366117995189 23985551321848440573562049)
              ·
                refine ⟨17989163491386330430171537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23985551321848440573562049 17989163491386330430171537)
                ·
                  refine ⟨13491872618539747822628653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17989163491386330430171537 13491872618539747822628653)
                  ·
                    refine ⟨5059452231952405433485745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13491872618539747822628653 5059452231952405433485745)
                    ·
                      refine ⟨3794589173964304075114309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5059452231952405433485745 3794589173964304075114309)
                      ·
                        rfl

theorem cell23_7389936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 2, 3, 2].length) (baseStart_7389936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389936 prefixEnd_7389936 := by exact prefixLift 7389936
  have htrace : WordTrace (prefixWord ++ tailWord_7389936) baseStart_7389936 baseEnd_7389936 := by
    simpa [prefixWord, tailWord_7389936, baseEnd_7389936] using wordTrace_append hprefix tailTrace_7389936
  have hstable : (prefixWord ++ tailWord_7389936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389936).length < 2 ^ (prefixWord ++ tailWord_7389936).sum := by decide
  have hdescent : baseEnd_7389936 < baseStart_7389936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389949 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_7389949 : Nat := 118140960795 + 7389949 * 2 ^ 59
def prefixEnd_7389949 : Nat := 4983230072969 + 3 ^ 40 * 7389949 * 2
def baseEnd_7389949 : Nat := 3794595849212812524251749

theorem tailTrace_7389949 : CollatzResearch.WordTrace tailWord_7389949 prefixEnd_7389949 3794595849212812524251749 := by
  unfold tailWord_7389949
  simp only [CollatzResearch.WordTrace]
  refine ⟨269533583104484350653172901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179689055402989567102115267 269533583104484350653172901)
  ·
    refine ⟨50537546832090815747469919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269533583104484350653172901 50537546832090815747469919)
    ·
      refine ⟨75806320248136223621204879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50537546832090815747469919 75806320248136223621204879)
      ·
        refine ⟨113709480372204335431807319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75806320248136223621204879 113709480372204335431807319)
        ·
          refine ⟨170564220558306503147710979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113709480372204335431807319 170564220558306503147710979)
          ·
            refine ⟨255846330837459754721566469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170564220558306503147710979 255846330837459754721566469)
            ·
              refine ⟨47971187032023704010293713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255846330837459754721566469 47971187032023704010293713)
              ·
                refine ⟨35978390274017778007720285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47971187032023704010293713 35978390274017778007720285)
                ·
                  refine ⟨13491896352756666752895107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35978390274017778007720285 13491896352756666752895107)
                  ·
                    refine ⟨20237844529135000129342661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13491896352756666752895107 20237844529135000129342661)
                    ·
                      refine ⟨3794595849212812524251749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20237844529135000129342661 3794595849212812524251749)
                      ·
                        rfl

theorem cell23_7389949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_7389949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389949 prefixEnd_7389949 := by exact prefixLift 7389949
  have htrace : WordTrace (prefixWord ++ tailWord_7389949) baseStart_7389949 baseEnd_7389949 := by
    simpa [prefixWord, tailWord_7389949, baseEnd_7389949] using wordTrace_append hprefix tailTrace_7389949
  have hstable : (prefixWord ++ tailWord_7389949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389949).length < 2 ^ (prefixWord ++ tailWord_7389949).sum := by decide
  have hdescent : baseEnd_7389949 < baseStart_7389949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389983 : List Nat := [1, 1, 2, 4, 2, 3, 3, 1, 1, 1, 4]
def baseStart_7389983 : Nat := 118140960795 + 7389983 * 2 ^ 59
def prefixEnd_7389983 : Nat := 4983230072969 + 3 ^ 40 * 7389983 * 2
def baseEnd_7389983 : Nat := 3794613307555065391226593

theorem tailTrace_7389983 : CollatzResearch.WordTrace tailWord_7389983 prefixEnd_7389983 3794613307555065391226593 := by
  unfold tailWord_7389983
  simp only [CollatzResearch.WordTrace]
  refine ⟨269534823186361174459910603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179689882124240782973273735 269534823186361174459910603)
  ·
    refine ⟨404302234779541761689865905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269534823186361174459910603 404302234779541761689865905)
    ·
      refine ⟨303226676084656321267399429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404302234779541761689865905 303226676084656321267399429)
      ·
        refine ⟨56855001765873060237637393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303226676084656321267399429 56855001765873060237637393)
        ·
          refine ⟨42641251324404795178228045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56855001765873060237637393 42641251324404795178228045)
          ·
            refine ⟨15990469246651798191835517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42641251324404795178228045 15990469246651798191835517)
            ·
              refine ⟨5996425967494424321938319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15990469246651798191835517 5996425967494424321938319)
              ·
                refine ⟨8994638951241636482907479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5996425967494424321938319 8994638951241636482907479)
                ·
                  refine ⟨13491958426862454724361219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8994638951241636482907479 13491958426862454724361219)
                  ·
                    refine ⟨20237937640293682086541829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13491958426862454724361219 20237937640293682086541829)
                    ·
                      refine ⟨3794613307555065391226593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20237937640293682086541829 3794613307555065391226593)
                      ·
                        rfl

theorem cell23_7389983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_7389983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389983 prefixEnd_7389983 := by exact prefixLift 7389983
  have htrace : WordTrace (prefixWord ++ tailWord_7389983) baseStart_7389983 baseEnd_7389983 := by
    simpa [prefixWord, tailWord_7389983, baseEnd_7389983] using wordTrace_append hprefix tailTrace_7389983
  have hstable : (prefixWord ++ tailWord_7389983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389983).length < 2 ^ (prefixWord ++ tailWord_7389983).sum := by decide
  have hdescent : baseEnd_7389983 < baseStart_7389983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7389986 : List Nat := [3, 3, 1, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_7389986 : Nat := 118140960795 + 7389986 * 2 ^ 59
def prefixEnd_7389986 : Nat := 4983230072969 + 3 ^ 40 * 7389986 * 2
def baseEnd_7389986 : Nat := 3794614847997028879489079

theorem tailTrace_7389986 : CollatzResearch.WordTrace tailWord_7389986 prefixEnd_7389986 3794614847997028879489079 := by
  unfold tailWord_7389986
  simp only [CollatzResearch.WordTrace]
  refine ⟨67383733151337576493067453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179689955070233537314846541 67383733151337576493067453)
  ·
    refine ⟨25268899931751591184900295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67383733151337576493067453 25268899931751591184900295)
    ·
      refine ⟨37903349897627386777350443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25268899931751591184900295 37903349897627386777350443)
      ·
        refine ⟨56855024846441080166025665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37903349897627386777350443 56855024846441080166025665)
        ·
          refine ⟨42641268634830810124519249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56855024846441080166025665 42641268634830810124519249)
          ·
            refine ⟨31980951476123107593389437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42641268634830810124519249 31980951476123107593389437)
            ·
              refine ⟨11992856803546165347521039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31980951476123107593389437 11992856803546165347521039)
              ·
                refine ⟨17989285205319248021281559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11992856803546165347521039 17989285205319248021281559)
                ·
                  refine ⟨26983927807978872031922339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17989285205319248021281559 26983927807978872031922339)
                  ·
                    refine ⟨40475891711968308047883509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26983927807978872031922339 40475891711968308047883509)
                    ·
                      refine ⟨3794614847997028879489079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40475891711968308047883509 3794614847997028879489079)
                      ·
                        rfl

theorem cell23_7389986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_7389986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7389986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7389986 prefixEnd_7389986 := by exact prefixLift 7389986
  have htrace : WordTrace (prefixWord ++ tailWord_7389986) baseStart_7389986 baseEnd_7389986 := by
    simpa [prefixWord, tailWord_7389986, baseEnd_7389986] using wordTrace_append hprefix tailTrace_7389986
  have hstable : (prefixWord ++ tailWord_7389986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7389986).length < 2 ^ (prefixWord ++ tailWord_7389986).sum := by decide
  have hdescent : baseEnd_7389986 < baseStart_7389986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7389986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390013 : List Nat := [1, 4, 1, 4, 2, 1, 2, 1, 1, 2, 4]
def baseStart_7390013 : Nat := 118140960795 + 7390013 * 2 ^ 59
def prefixEnd_7390013 : Nat := 4983230072969 + 3 ^ 40 * 7390013 * 2
def baseEnd_7390013 : Nat := 3794628711974700273851455

theorem tailTrace_7390013 : CollatzResearch.WordTrace tailWord_7390013 prefixEnd_7390013 3794628711974700273851455 := by
  unfold tailWord_7390013
  simp only [CollatzResearch.WordTrace]
  refine ⟨269535917376252489583502693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179690611584168326389001795 269535917376252489583502693)
  ·
    refine ⟨50537984508047341796906755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269535917376252489583502693 50537984508047341796906755)
    ·
      refine ⟨75806976762071012695360133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50537984508047341796906755 75806976762071012695360133)
      ·
        refine ⟨14213808142888314880380025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75806976762071012695360133 14213808142888314880380025)
        ·
          refine ⟨10660356107166236160285019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14213808142888314880380025 10660356107166236160285019)
          ·
            refine ⟨15990534160749354240427529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10660356107166236160285019 15990534160749354240427529)
            ·
              refine ⟨11992900620562015680320647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15990534160749354240427529 11992900620562015680320647)
              ·
                refine ⟨17989350930843023520480971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11992900620562015680320647 17989350930843023520480971)
                ·
                  refine ⟨26984026396264535280721457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17989350930843023520480971 26984026396264535280721457)
                  ·
                    refine ⟨20238019797198401460541093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26984026396264535280721457 20238019797198401460541093)
                    ·
                      refine ⟨3794628711974700273851455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20238019797198401460541093 3794628711974700273851455)
                      ·
                        rfl

theorem cell23_7390013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_7390013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390013 prefixEnd_7390013 := by exact prefixLift 7390013
  have htrace : WordTrace (prefixWord ++ tailWord_7390013) baseStart_7390013 baseEnd_7390013 := by
    simpa [prefixWord, tailWord_7390013, baseEnd_7390013] using wordTrace_append hprefix tailTrace_7390013
  have hstable : (prefixWord ++ tailWord_7390013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390013).length < 2 ^ (prefixWord ++ tailWord_7390013).sum := by decide
  have hdescent : baseEnd_7390013 < baseStart_7390013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390017 : List Nat := [1, 2, 5, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_7390017 : Nat := 118140960795 + 7390017 * 2 ^ 59
def prefixEnd_7390017 : Nat := 4983230072969 + 3 ^ 40 * 7390017 * 2
def baseEnd_7390017 : Nat := 3794630765897318258201437

theorem tailTrace_7390017 : CollatzResearch.WordTrace tailWord_7390017 prefixEnd_7390017 3794630765897318258201437 := by
  unfold tailWord_7390017
  simp only [CollatzResearch.WordTrace]
  refine ⟨269536063268237998266648305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179690708845491998844432203 269536063268237998266648305)
  ·
    refine ⟨202152047451178498699986229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269536063268237998266648305 202152047451178498699986229)
    ·
      refine ⟨18951754448547984253123709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202152047451178498699986229 18951754448547984253123709)
      ·
        refine ⟨7106907918205494094921391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18951754448547984253123709 7106907918205494094921391)
        ·
          refine ⟨10660361877308241142382087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7106907918205494094921391 10660361877308241142382087)
          ·
            refine ⟨15990542815962361713573131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10660361877308241142382087 15990542815962361713573131)
            ·
              refine ⟨23985814223943542570359697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15990542815962361713573131 23985814223943542570359697)
              ·
                refine ⟨17989360667957656927769773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23985814223943542570359697 17989360667957656927769773)
                ·
                  refine ⟨6746010250484121347913665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17989360667957656927769773 6746010250484121347913665)
                  ·
                    refine ⟨5059507687863091010935249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6746010250484121347913665 5059507687863091010935249)
                    ·
                      refine ⟨3794630765897318258201437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5059507687863091010935249 3794630765897318258201437)
                      ·
                        rfl

theorem cell23_7390017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_7390017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390017 prefixEnd_7390017 := by exact prefixLift 7390017
  have htrace : WordTrace (prefixWord ++ tailWord_7390017) baseStart_7390017 baseEnd_7390017 := by
    simpa [prefixWord, tailWord_7390017, baseEnd_7390017] using wordTrace_append hprefix tailTrace_7390017
  have hstable : (prefixWord ++ tailWord_7390017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390017).length < 2 ^ (prefixWord ++ tailWord_7390017).sum := by decide
  have hdescent : baseEnd_7390017 < baseStart_7390017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390050 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_7390050 : Nat := 118140960795 + 7390050 * 2 ^ 59
def prefixEnd_7390050 : Nat := 4983230072969 + 3 ^ 40 * 7390050 * 2
def baseEnd_7390050 : Nat := 3794647710758916629088785

theorem tailTrace_7390050 : CollatzResearch.WordTrace tailWord_7390050 prefixEnd_7390050 3794647710758916629088785 := by
  unfold tailWord_7390050
  simp only [CollatzResearch.WordTrace]
  refine ⟨67384316719279611225649901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179691511251412296601733069 67384316719279611225649901)
  ·
    refine ⟨25269118769729854209618713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67384316719279611225649901 25269118769729854209618713)
    ·
      refine ⟨18951839077297390657214035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25269118769729854209618713 18951839077297390657214035)
      ·
        refine ⟨28427758615946085985821053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18951839077297390657214035 28427758615946085985821053)
        ·
          refine ⟨10660409480979782244682895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28427758615946085985821053 10660409480979782244682895)
          ·
            refine ⟨15990614221469673367024343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10660409480979782244682895 15990614221469673367024343)
            ·
              refine ⟨23985921332204510050536515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15990614221469673367024343 23985921332204510050536515)
              ·
                refine ⟨35978881998306765075804773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23985921332204510050536515 35978881998306765075804773)
                ·
                  refine ⟨6746040374682518451713395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35978881998306765075804773 6746040374682518451713395)
                  ·
                    refine ⟨10119060562023777677570093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6746040374682518451713395 10119060562023777677570093)
                    ·
                      refine ⟨3794647710758916629088785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10119060562023777677570093 3794647710758916629088785)
                      ·
                        rfl

theorem cell23_7390050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_7390050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390050 prefixEnd_7390050 := by exact prefixLift 7390050
  have htrace : WordTrace (prefixWord ++ tailWord_7390050) baseStart_7390050 baseEnd_7390050 := by
    simpa [prefixWord, tailWord_7390050, baseEnd_7390050] using wordTrace_append hprefix tailTrace_7390050
  have hstable : (prefixWord ++ tailWord_7390050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390050).length < 2 ^ (prefixWord ++ tailWord_7390050).sum := by decide
  have hdescent : baseEnd_7390050 < baseStart_7390050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390059 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 3]
def baseStart_7390059 : Nat := 118140960795 + 7390059 * 2 ^ 59
def prefixEnd_7390059 : Nat := 4983230072969 + 3 ^ 40 * 7390059 * 2
def baseEnd_7390059 : Nat := 3794652332084807093876243

theorem tailTrace_7390059 : CollatzResearch.WordTrace tailWord_7390059 prefixEnd_7390059 3794652332084807093876243 := by
  unfold tailWord_7390059
  simp only [CollatzResearch.WordTrace]
  refine ⟨269537595134085839439677231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179691730089390559626451487 269537595134085839439677231)
  ·
    refine ⟨404306392701128759159515847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269537595134085839439677231 404306392701128759159515847)
    ·
      refine ⟨606459589051693138739273771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404306392701128759159515847 606459589051693138739273771)
      ·
        refine ⟨909689383577539708108910657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606459589051693138739273771 909689383577539708108910657)
        ·
          refine ⟨682267037683154781081682993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 909689383577539708108910657 682267037683154781081682993)
          ·
            refine ⟨511700278262366085811262245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682267037683154781081682993 511700278262366085811262245)
            ·
              refine ⟨95943802174193641089611671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 511700278262366085811262245 95943802174193641089611671)
              ·
                refine ⟨143915703261290461634417507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95943802174193641089611671 143915703261290461634417507)
                ·
                  refine ⟨215873554891935692451626261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143915703261290461634417507 215873554891935692451626261)
                  ·
                    refine ⟨10119072885559485583669981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 215873554891935692451626261 10119072885559485583669981)
                    ·
                      refine ⟨3794652332084807093876243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10119072885559485583669981 3794652332084807093876243)
                      ·
                        rfl

theorem cell23_7390059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 3].length) (baseStart_7390059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390059 prefixEnd_7390059 := by exact prefixLift 7390059
  have htrace : WordTrace (prefixWord ++ tailWord_7390059) baseStart_7390059 baseEnd_7390059 := by
    simpa [prefixWord, tailWord_7390059, baseEnd_7390059] using wordTrace_append hprefix tailTrace_7390059
  have hstable : (prefixWord ++ tailWord_7390059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390059).length < 2 ^ (prefixWord ++ tailWord_7390059).sum := by decide
  have hdescent : baseEnd_7390059 < baseStart_7390059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390073 : List Nat := [1, 2, 1, 3, 2, 3, 3, 1, 1, 4, 2]
def baseStart_7390073 : Nat := 118140960795 + 7390073 * 2 ^ 59
def prefixEnd_7390073 : Nat := 4983230072969 + 3 ^ 40 * 7390073 * 2
def baseEnd_7390073 : Nat := 3794659520813970039101179

theorem tailTrace_7390073 : CollatzResearch.WordTrace tailWord_7390073 prefixEnd_7390073 3794659520813970039101179 := by
  unfold tailWord_7390073
  simp only [CollatzResearch.WordTrace]
  refine ⟨269538105756035119830686873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179692070504023413220457915 269538105756035119830686873)
  ·
    refine ⟨202153579317026339873015155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269538105756035119830686873 202153579317026339873015155)
    ·
      refine ⟨303230368975539509809522733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202153579317026339873015155 303230368975539509809522733)
      ·
        refine ⟨113711388365827316178571025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303230368975539509809522733 113711388365827316178571025)
        ·
          refine ⟨85283541274370487133928269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113711388365827316178571025 85283541274370487133928269)
          ·
            refine ⟨31981327977888932675223101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85283541274370487133928269 31981327977888932675223101)
            ·
              refine ⟨11992997991708349753208663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31981327977888932675223101 11992997991708349753208663)
              ·
                refine ⟨17989496987562524629812995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11992997991708349753208663 17989496987562524629812995)
                ·
                  refine ⟨26984245481343786944719493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17989496987562524629812995 26984245481343786944719493)
                  ·
                    refine ⟨5059546027751960052134905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26984245481343786944719493 5059546027751960052134905)
                    ·
                      refine ⟨3794659520813970039101179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5059546027751960052134905 3794659520813970039101179)
                      ·
                        rfl

theorem cell23_7390073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_7390073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390073 prefixEnd_7390073 := by exact prefixLift 7390073
  have htrace : WordTrace (prefixWord ++ tailWord_7390073) baseStart_7390073 baseEnd_7390073 := by
    simpa [prefixWord, tailWord_7390073, baseEnd_7390073] using wordTrace_append hprefix tailTrace_7390073
  have hstable : (prefixWord ++ tailWord_7390073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390073).length < 2 ^ (prefixWord ++ tailWord_7390073).sum := by decide
  have hdescent : baseEnd_7390073 < baseStart_7390073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390079 : List Nat := [1, 1, 2, 2, 1, 1, 6, 2, 7]
def baseStart_7390079 : Nat := 118140960795 + 7390079 * 2 ^ 59
def prefixEnd_7390079 : Nat := 4983230072969 + 3 ^ 40 * 7390079 * 2
def baseEnd_7390079 : Nat := 421629177966433001736239

theorem tailTrace_7390079 : CollatzResearch.WordTrace tailWord_7390079 prefixEnd_7390079 421629177966433001736239 := by
  unfold tailWord_7390079
  simp only [CollatzResearch.WordTrace]
  refine ⟨269538324594013382855405291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179692216396008921903603527 269538324594013382855405291)
  ·
    refine ⟨404307486891020074283107937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269538324594013382855405291 404307486891020074283107937)
    ·
      refine ⟨303230615168265055712330953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404307486891020074283107937 303230615168265055712330953)
      ·
        refine ⟨227422961376198791784248215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303230615168265055712330953 227422961376198791784248215)
        ·
          refine ⟨341134442064298187676372323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227422961376198791784248215 341134442064298187676372323)
          ·
            refine ⟨511701663096447281514558485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341134442064298187676372323 511701663096447281514558485)
            ·
              refine ⟨23986015457645966320994929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 511701663096447281514558485 23986015457645966320994929)
              ·
                refine ⟨17989511593234474740746197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23986015457645966320994929 17989511593234474740746197)
                ·
                  refine ⟨421629177966433001736239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17989511593234474740746197 421629177966433001736239)
                  ·
                    rfl

theorem cell23_7390079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 7].length) (baseStart_7390079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390079 prefixEnd_7390079 := by exact prefixLift 7390079
  have htrace : WordTrace (prefixWord ++ tailWord_7390079) baseStart_7390079 baseEnd_7390079 := by
    simpa [prefixWord, tailWord_7390079, baseEnd_7390079] using wordTrace_append hprefix tailTrace_7390079
  have hstable : (prefixWord ++ tailWord_7390079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390079).length < 2 ^ (prefixWord ++ tailWord_7390079).sum := by decide
  have hdescent : baseEnd_7390079 < baseStart_7390079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390090 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 4, 2, 2]
def baseStart_7390090 : Nat := 118140960795 + 7390090 * 2 ^ 59
def prefixEnd_7390090 : Nat := 4983230072969 + 3 ^ 40 * 7390090 * 2
def baseEnd_7390090 : Nat := 3794668249985096472588601

theorem tailTrace_7390090 : CollatzResearch.WordTrace tailWord_7390090 prefixEnd_7390090 3794668249985096472588601 := by
  unfold tailWord_7390090
  simp only [CollatzResearch.WordTrace]
  refine ⟨67384681449243382933513931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179692483864649021156037149 67384681449243382933513931)
  ·
    refine ⟨101077022173865074400270897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67384681449243382933513931 101077022173865074400270897)
    ·
      refine ⟨75807766630398805800203173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101077022173865074400270897 75807766630398805800203173)
      ·
        refine ⟨14213956243199776087538095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75807766630398805800203173 14213956243199776087538095)
        ·
          refine ⟨21320934364799664131307143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14213956243199776087538095 21320934364799664131307143)
          ·
            refine ⟨31981401547199496196960715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21320934364799664131307143 31981401547199496196960715)
            ·
              refine ⟨47972102320799244295441073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31981401547199496196960715 47972102320799244295441073)
              ·
                refine ⟨35979076740599433221580805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47972102320799244295441073 35979076740599433221580805)
                ·
                  refine ⟨6746076888862393729046401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35979076740599433221580805 6746076888862393729046401)
                  ·
                    refine ⟨5059557666646795296784801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6746076888862393729046401 5059557666646795296784801)
                    ·
                      refine ⟨3794668249985096472588601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5059557666646795296784801 3794668249985096472588601)
                      ·
                        rfl

theorem cell23_7390090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_7390090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390090 prefixEnd_7390090 := by exact prefixLift 7390090
  have htrace : WordTrace (prefixWord ++ tailWord_7390090) baseStart_7390090 baseEnd_7390090 := by
    simpa [prefixWord, tailWord_7390090, baseEnd_7390090] using wordTrace_append hprefix tailTrace_7390090
  have hstable : (prefixWord ++ tailWord_7390090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390090).length < 2 ^ (prefixWord ++ tailWord_7390090).sum := by decide
  have hdescent : baseEnd_7390090 < baseStart_7390090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390113 : List Nat := [1, 2, 3, 4, 1, 3, 1, 1, 7]
def baseStart_7390113 : Nat := 118140960795 + 7390113 * 2 ^ 59
def prefixEnd_7390113 : Nat := 4983230072969 + 3 ^ 40 * 7390113 * 2
def baseEnd_7390113 : Nat := 421631117782238875844555

theorem tailTrace_7390113 : CollatzResearch.WordTrace tailWord_7390113 prefixEnd_7390113 421631117782238875844555 := by
  unfold tailWord_7390113
  simp only [CollatzResearch.WordTrace]
  refine ⟨269539564675890206662142993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179693043117260137774761995 269539564675890206662142993)
  ·
    refine ⟨202154673506917654996607245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269539564675890206662142993 202154673506917654996607245)
    ·
      refine ⟨75808002565094120623727717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202154673506917654996607245 75808002565094120623727717)
      ·
        refine ⟨14214000480955147616948947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75808002565094120623727717 14214000480955147616948947)
        ·
          refine ⟨21321000721432721425423421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14214000480955147616948947 21321000721432721425423421)
          ·
            refine ⟨7995375270537270534533783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21321000721432721425423421 7995375270537270534533783)
            ·
              refine ⟨11993062905805905801800675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7995375270537270534533783 11993062905805905801800675)
              ·
                refine ⟨17989594358708858702701013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11993062905805905801800675 17989594358708858702701013)
                ·
                  refine ⟨421631117782238875844555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17989594358708858702701013 421631117782238875844555)
                  ·
                    rfl

theorem cell23_7390113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 7].length) (baseStart_7390113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390113 prefixEnd_7390113 := by exact prefixLift 7390113
  have htrace : WordTrace (prefixWord ++ tailWord_7390113) baseStart_7390113 baseEnd_7390113 := by
    simpa [prefixWord, tailWord_7390113, baseEnd_7390113] using wordTrace_append hprefix tailTrace_7390113
  have hstable : (prefixWord ++ tailWord_7390113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390113).length < 2 ^ (prefixWord ++ tailWord_7390113).sum := by decide
  have hdescent : baseEnd_7390113 < baseStart_7390113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390190 : List Nat := [4, 1, 2, 1, 4, 1, 1, 2, 3, 4]
def baseStart_7390190 : Nat := 118140960795 + 7390190 * 2 ^ 59
def prefixEnd_7390190 : Nat := 4983230072969 + 3 ^ 40 * 7390190 * 2
def baseEnd_7390190 : Nat := 1264906532683515360446047

theorem tailTrace_7390190 : CollatzResearch.WordTrace tailWord_7390190 prefixEnd_7390190 1264906532683515360446047 := by
  unfold tailWord_7390190
  simp only [CollatzResearch.WordTrace]
  refine ⟨33692796637076406101587003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179694915397740832541797349 33692796637076406101587003)
  ·
    refine ⟨50539194955614609152380505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33692796637076406101587003 50539194955614609152380505)
    ·
      refine ⟨37904396216710956864285379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50539194955614609152380505 37904396216710956864285379)
      ·
        refine ⟨56856594325066435296428069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37904396216710956864285379 56856594325066435296428069)
        ·
          refine ⟨10660611435949956618080263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56856594325066435296428069 10660611435949956618080263)
          ·
            refine ⟨15990917153924934927120395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10660611435949956618080263 15990917153924934927120395)
            ·
              refine ⟨23986375730887402390680593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15990917153924934927120395 23986375730887402390680593)
              ·
                refine ⟨17989781798165551793010445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23986375730887402390680593 17989781798165551793010445)
                ·
                  refine ⟨6746168174312081922378917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17989781798165551793010445 6746168174312081922378917)
                  ·
                    refine ⟨1264906532683515360446047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6746168174312081922378917 1264906532683515360446047)
                    ·
                      rfl

theorem cell23_7390190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_7390190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390190 prefixEnd_7390190 := by exact prefixLift 7390190
  have htrace : WordTrace (prefixWord ++ tailWord_7390190) baseStart_7390190 baseEnd_7390190 := by
    simpa [prefixWord, tailWord_7390190, baseEnd_7390190] using wordTrace_append hprefix tailTrace_7390190
  have hstable : (prefixWord ++ tailWord_7390190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390190).length < 2 ^ (prefixWord ++ tailWord_7390190).sum := by decide
  have hdescent : baseEnd_7390190 < baseStart_7390190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390213 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 5, 1, 3]
def baseStart_7390213 : Nat := 118140960795 + 7390213 * 2 ^ 59
def prefixEnd_7390213 : Nat := 4983230072969 + 3 ^ 40 * 7390213 * 2
def baseEnd_7390213 : Nat := 3794731408105599491350535

theorem tailTrace_7390213 : CollatzResearch.WordTrace tailWord_7390213 prefixEnd_7390213 3794731408105599491350535 := by
  unfold tailWord_7390213
  simp only [CollatzResearch.WordTrace]
  refine ⟨269543211975527923740783293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179695474650351949160522195 269543211975527923740783293)
  ·
    refine ⟨101078704490822971402793735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269543211975527923740783293 101078704490822971402793735)
    ·
      refine ⟨151618056736234457104190603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101078704490822971402793735 151618056736234457104190603)
      ·
        refine ⟨227427085104351685656285905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151618056736234457104190603 227427085104351685656285905)
        ·
          refine ⟨170570313828263764242214429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227427085104351685656285905 170570313828263764242214429)
          ·
            refine ⟨63963867685598911590830411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170570313828263764242214429 63963867685598911590830411)
            ·
              refine ⟨95945801528398367386245617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63963867685598911590830411 95945801528398367386245617)
              ·
                refine ⟨71959351146298775539684213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95945801528398367386245617 71959351146298775539684213)
                ·
                  refine ⟨6746189169965510206845395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71959351146298775539684213 6746189169965510206845395)
                  ·
                    refine ⟨10119283754948265310268093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6746189169965510206845395 10119283754948265310268093)
                    ·
                      refine ⟨3794731408105599491350535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10119283754948265310268093 3794731408105599491350535)
                      ·
                        rfl

theorem cell23_7390213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 1, 3].length) (baseStart_7390213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390213 prefixEnd_7390213 := by exact prefixLift 7390213
  have htrace : WordTrace (prefixWord ++ tailWord_7390213) baseStart_7390213 baseEnd_7390213 := by
    simpa [prefixWord, tailWord_7390213, baseEnd_7390213] using wordTrace_append hprefix tailTrace_7390213
  have hstable : (prefixWord ++ tailWord_7390213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390213).length < 2 ^ (prefixWord ++ tailWord_7390213).sum := by decide
  have hdescent : baseEnd_7390213 < baseStart_7390213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390247 : List Nat := [1, 1, 7, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_7390247 : Nat := 118140960795 + 7390247 * 2 ^ 59
def prefixEnd_7390247 : Nat := 4983230072969 + 3 ^ 40 * 7390247 * 2
def baseEnd_7390247 : Nat := 3794748866447852358325379

theorem tailTrace_7390247 : CollatzResearch.WordTrace tailWord_7390247 prefixEnd_7390247 3794748866447852358325379 := by
  unfold tailWord_7390247
  simp only [CollatzResearch.WordTrace]
  refine ⟨269544452057404747547520995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179696301371603165031680663 269544452057404747547520995)
  ·
    refine ⟨404316678086107121321281493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269544452057404747547520995 404316678086107121321281493)
    ·
      refine ⟨9476172142643135655967535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 404316678086107121321281493 9476172142643135655967535)
      ·
        refine ⟨14214258213964703483951303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9476172142643135655967535 14214258213964703483951303)
        ·
          refine ⟨21321387320947055225926955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14214258213964703483951303 21321387320947055225926955)
          ·
            refine ⟨31982080981420582838890433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21321387320947055225926955 31982080981420582838890433)
            ·
              refine ⟨23986560736065437129167825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31982080981420582838890433 23986560736065437129167825)
              ·
                refine ⟨17989920552049077846875869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23986560736065437129167825 17989920552049077846875869)
                ·
                  refine ⟨6746220207018404192578451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17989920552049077846875869 6746220207018404192578451)
                  ·
                    refine ⟨10119330310527606288867677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6746220207018404192578451 10119330310527606288867677)
                    ·
                      refine ⟨3794748866447852358325379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10119330310527606288867677 3794748866447852358325379)
                      ·
                        rfl

theorem cell23_7390247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_7390247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390247 prefixEnd_7390247 := by exact prefixLift 7390247
  have htrace : WordTrace (prefixWord ++ tailWord_7390247) baseStart_7390247 baseEnd_7390247 := by
    simpa [prefixWord, tailWord_7390247, baseEnd_7390247] using wordTrace_append hprefix tailTrace_7390247
  have hstable : (prefixWord ++ tailWord_7390247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390247).length < 2 ^ (prefixWord ++ tailWord_7390247).sum := by decide
  have hdescent : baseEnd_7390247 < baseStart_7390247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390256 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 5]
def baseStart_7390256 : Nat := 118140960795 + 7390256 * 2 ^ 59
def prefixEnd_7390256 : Nat := 4983230072969 + 3 ^ 40 * 7390256 * 2
def baseEnd_7390256 : Nat := 3794753487773742823112837

theorem tailTrace_7390256 : CollatzResearch.WordTrace tailWord_7390256 prefixEnd_7390256 3794753487773742823112837 := by
  unfold tailWord_7390256
  simp only [CollatzResearch.WordTrace]
  refine ⟨134772390157186071042299311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179696520209581428056399081 134772390157186071042299311)
  ·
    refine ⟨202158585235779106563448967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134772390157186071042299311 202158585235779106563448967)
    ·
      refine ⟨303237877853668659845173451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202158585235779106563448967 303237877853668659845173451)
      ·
        refine ⟨454856816780502989767760177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303237877853668659845173451 454856816780502989767760177)
        ·
          refine ⟨341142612585377242325820133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454856816780502989767760177 341142612585377242325820133)
          ·
            refine ⟨63964239859758232936091275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 341142612585377242325820133 63964239859758232936091275)
            ·
              refine ⟨95946359789637349404136913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63964239859758232936091275 95946359789637349404136913)
              ·
                refine ⟨71959769842228012053102685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95946359789637349404136913 71959769842228012053102685)
                ·
                  refine ⟨26984913690835504519913507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71959769842228012053102685 26984913690835504519913507)
                  ·
                    refine ⟨40477370536253256779870261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26984913690835504519913507 40477370536253256779870261)
                    ·
                      refine ⟨3794753487773742823112837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40477370536253256779870261 3794753487773742823112837)
                      ·
                        rfl

theorem cell23_7390256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_7390256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390256 prefixEnd_7390256 := by exact prefixLift 7390256
  have htrace : WordTrace (prefixWord ++ tailWord_7390256) baseStart_7390256 baseEnd_7390256 := by
    simpa [prefixWord, tailWord_7390256, baseEnd_7390256] using wordTrace_append hprefix tailTrace_7390256
  have hstable : (prefixWord ++ tailWord_7390256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390256).length < 2 ^ (prefixWord ++ tailWord_7390256).sum := by decide
  have hdescent : baseEnd_7390256 < baseStart_7390256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390264 : List Nat := [2, 1, 2, 1, 5, 3, 1, 3, 1, 1, 3]
def baseStart_7390264 : Nat := 118140960795 + 7390264 * 2 ^ 59
def prefixEnd_7390264 : Nat := 4983230072969 + 3 ^ 40 * 7390264 * 2
def baseEnd_7390264 : Nat := 3794757595618978791812801

theorem tailTrace_7390264 : CollatzResearch.WordTrace tailWord_7390264 prefixEnd_7390264 3794757595618978791812801 := by
  unfold tailWord_7390264
  simp only [CollatzResearch.WordTrace]
  refine ⟨134772536049171579725444923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179696714732228772967259897 134772536049171579725444923)
  ·
    refine ⟨202158804073757369588167385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134772536049171579725444923 202158804073757369588167385)
    ·
      refine ⟨151619103055318027191125539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202158804073757369588167385 151619103055318027191125539)
      ·
        refine ⟨227428654582977040786688309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151619103055318027191125539 227428654582977040786688309)
        ·
          refine ⟨21321436367154097573752029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 227428654582977040786688309 21321436367154097573752029)
          ·
            refine ⟨7995538637682786590157011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21321436367154097573752029 7995538637682786590157011)
            ·
              refine ⟨11993307956524179885235517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7995538637682786590157011 11993307956524179885235517)
              ·
                refine ⟨4497490483696567456963319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11993307956524179885235517 4497490483696567456963319)
                ·
                  refine ⟨6746235725544851185444979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4497490483696567456963319 6746235725544851185444979)
                  ·
                    refine ⟨10119353588317276778167469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6746235725544851185444979 10119353588317276778167469)
                    ·
                      refine ⟨3794757595618978791812801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10119353588317276778167469 3794757595618978791812801)
                      ·
                        rfl

theorem cell23_7390264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 1, 1, 3].length) (baseStart_7390264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390264 prefixEnd_7390264 := by exact prefixLift 7390264
  have htrace : WordTrace (prefixWord ++ tailWord_7390264) baseStart_7390264 baseEnd_7390264 := by
    simpa [prefixWord, tailWord_7390264, baseEnd_7390264] using wordTrace_append hprefix tailTrace_7390264
  have hstable : (prefixWord ++ tailWord_7390264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390264).length < 2 ^ (prefixWord ++ tailWord_7390264).sum := by decide
  have hdescent : baseEnd_7390264 < baseStart_7390264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390296 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 2, 2, 6]
def baseStart_7390296 : Nat := 118140960795 + 7390296 * 2 ^ 59
def prefixEnd_7390296 : Nat := 4983230072969 + 3 ^ 40 * 7390296 * 2
def baseEnd_7390296 : Nat := 3794774026999922666612653

theorem tailTrace_7390296 : CollatzResearch.WordTrace tailWord_7390296 prefixEnd_7390296 3794774026999922666612653 := by
  unfold tailWord_7390296
  simp only [CollatzResearch.WordTrace]
  refine ⟨134773119617113614458027371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179697492822818152610703161 134773119617113614458027371)
  ·
    refine ⟨202159679425670421687041057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134773119617113614458027371 202159679425670421687041057)
    ·
      refine ⟨151619759569252816265280793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202159679425670421687041057 151619759569252816265280793)
      ·
        refine ⟨113714819676939612198960595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151619759569252816265280793 113714819676939612198960595)
        ·
          refine ⟨170572229515409418298440893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113714819676939612198960595 170572229515409418298440893)
          ·
            refine ⟨63964586068278531861915335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170572229515409418298440893 63964586068278531861915335)
            ·
              refine ⟨95946879102417797792873003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63964586068278531861915335 95946879102417797792873003)
              ·
                refine ⟨143920318653626696689309505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95946879102417797792873003 143920318653626696689309505)
                ·
                  refine ⟨107940238990220022516982129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143920318653626696689309505 107940238990220022516982129)
                  ·
                    refine ⟨80955179242665016887736597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107940238990220022516982129 80955179242665016887736597)
                    ·
                      refine ⟨3794774026999922666612653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80955179242665016887736597 3794774026999922666612653)
                      ·
                        rfl

theorem cell23_7390296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_7390296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390296 prefixEnd_7390296 := by exact prefixLift 7390296
  have htrace : WordTrace (prefixWord ++ tailWord_7390296) baseStart_7390296 baseEnd_7390296 := by
    simpa [prefixWord, tailWord_7390296, baseEnd_7390296] using wordTrace_append hprefix tailTrace_7390296
  have hstable : (prefixWord ++ tailWord_7390296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390296).length < 2 ^ (prefixWord ++ tailWord_7390296).sum := by decide
  have hdescent : baseEnd_7390296 < baseStart_7390296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390303 : List Nat := [1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 3]
def baseStart_7390303 : Nat := 118140960795 + 7390303 * 2 ^ 59
def prefixEnd_7390303 : Nat := 4983230072969 + 3 ^ 40 * 7390303 * 2
def baseEnd_7390303 : Nat := 3794777621364504139225121

theorem tailTrace_7390303 : CollatzResearch.WordTrace tailWord_7390303 prefixEnd_7390303 3794777621364504139225121 := by
  unfold tailWord_7390303
  simp only [CollatzResearch.WordTrace]
  refine ⟨269546494545201869111559563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179697663030134579407706375 269546494545201869111559563)
  ·
    refine ⟨404319741817802803667339345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269546494545201869111559563 404319741817802803667339345)
    ·
      refine ⟨303239806363352102750504509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404319741817802803667339345 303239806363352102750504509)
      ·
        refine ⟨113714927386257038531439191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303239806363352102750504509 113714927386257038531439191)
        ·
          refine ⟨170572391079385557797158787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113714927386257038531439191 170572391079385557797158787)
          ·
            refine ⟨255858586619078336695738181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170572391079385557797158787 255858586619078336695738181)
            ·
              refine ⟨47973484991077188130450909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255858586619078336695738181 47973484991077188130450909)
              ·
                refine ⟨17990056871653945548919091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47973484991077188130450909 17990056871653945548919091)
                ·
                  refine ⟨26985085307480918323378637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17990056871653945548919091 26985085307480918323378637)
                  ·
                    refine ⟨10119406990305344371266989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26985085307480918323378637 10119406990305344371266989)
                    ·
                      refine ⟨3794777621364504139225121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10119406990305344371266989 3794777621364504139225121)
                      ·
                        rfl

theorem cell23_7390303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_7390303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390303 prefixEnd_7390303 := by exact prefixLift 7390303
  have htrace : WordTrace (prefixWord ++ tailWord_7390303) baseStart_7390303 baseEnd_7390303 := by
    simpa [prefixWord, tailWord_7390303, baseEnd_7390303] using wordTrace_append hprefix tailTrace_7390303
  have hstable : (prefixWord ++ tailWord_7390303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390303).length < 2 ^ (prefixWord ++ tailWord_7390303).sum := by decide
  have hdescent : baseEnd_7390303 < baseStart_7390303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390337 : List Nat := [1, 2, 4, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_7390337 : Nat := 118140960795 + 7390337 * 2 ^ 59
def prefixEnd_7390337 : Nat := 4983230072969 + 3 ^ 40 * 7390337 * 2
def baseEnd_7390337 : Nat := 3794795079706757006199965

theorem tailTrace_7390337 : CollatzResearch.WordTrace tailWord_7390337 prefixEnd_7390337 3794795079706757006199965 := by
  unfold tailWord_7390337
  simp only [CollatzResearch.WordTrace]
  refine ⟨269547734627078692918297265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179698489751385795278864843 269547734627078692918297265)
  ·
    refine ⟨202160800970309019688722949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269547734627078692918297265 202160800970309019688722949)
    ·
      refine ⟨37905150181932941191635553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202160800970309019688722949 37905150181932941191635553)
      ·
        refine ⟨28428862636449705893726665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37905150181932941191635553 28428862636449705893726665)
        ·
          refine ⟨21321646977337279420294999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28428862636449705893726665 21321646977337279420294999)
          ·
            refine ⟨31982470466005919130442499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21321646977337279420294999 31982470466005919130442499)
            ·
              refine ⟨47973705699008878695663749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31982470466005919130442499 47973705699008878695663749)
              ·
                refine ⟨8995069818564164755436953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47973705699008878695663749 8995069818564164755436953)
                ·
                  refine ⟨6746302363923123566577715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8995069818564164755436953 6746302363923123566577715)
                  ·
                    refine ⟨10119453545884685349866573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6746302363923123566577715 10119453545884685349866573)
                    ·
                      refine ⟨3794795079706757006199965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10119453545884685349866573 3794795079706757006199965)
                      ·
                        rfl

theorem cell23_7390337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_7390337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390337 prefixEnd_7390337 := by exact prefixLift 7390337
  have htrace : WordTrace (prefixWord ++ tailWord_7390337) baseStart_7390337 baseEnd_7390337 := by
    simpa [prefixWord, tailWord_7390337, baseEnd_7390337] using wordTrace_append hprefix tailTrace_7390337
  have hstable : (prefixWord ++ tailWord_7390337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390337).length < 2 ^ (prefixWord ++ tailWord_7390337).sum := by decide
  have hdescent : baseEnd_7390337 < baseStart_7390337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390400 : List Nat := [2, 1, 1, 2, 6, 1, 2, 1, 7]
def baseStart_7390400 : Nat := 118140960795 + 7390400 * 2 ^ 59
def prefixEnd_7390400 : Nat := 4983230072969 + 3 ^ 40 * 7390400 * 2
def baseEnd_7390400 : Nat := 421647492109776695523575

theorem tailTrace_7390400 : CollatzResearch.WordTrace tailWord_7390400 prefixEnd_7390400 421647492109776695523575 := by
  unfold tailWord_7390400
  simp only [CollatzResearch.WordTrace]
  refine ⟨134775016212925227338920327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179700021617233636451893769 134775016212925227338920327)
  ·
    refine ⟨202162524319387841008380491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134775016212925227338920327 202162524319387841008380491)
    ·
      refine ⟨303243786479081761512570737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202162524319387841008380491 303243786479081761512570737)
      ·
        refine ⟨227432839859311321134428053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303243786479081761512570737 227432839859311321134428053)
        ·
          refine ⟨10660914368405218178176315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 227432839859311321134428053 10660914368405218178176315)
          ·
            refine ⟨15991371552607827267264473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10660914368405218178176315 15991371552607827267264473)
            ·
              refine ⟨11993528664455870450448355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15991371552607827267264473 11993528664455870450448355)
              ·
                refine ⟨17990292996683805675672533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11993528664455870450448355 17990292996683805675672533)
                ·
                  refine ⟨421647492109776695523575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17990292996683805675672533 421647492109776695523575)
                  ·
                    rfl

theorem cell23_7390400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 7].length) (baseStart_7390400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390400 prefixEnd_7390400 := by exact prefixLift 7390400
  have htrace : WordTrace (prefixWord ++ tailWord_7390400) baseStart_7390400 baseEnd_7390400 := by
    simpa [prefixWord, tailWord_7390400, baseEnd_7390400] using wordTrace_append hprefix tailTrace_7390400
  have hstable : (prefixWord ++ tailWord_7390400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390400).length < 2 ^ (prefixWord ++ tailWord_7390400).sum := by decide
  have hdescent : baseEnd_7390400 < baseStart_7390400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390410 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 2, 3, 3]
def baseStart_7390410 : Nat := 118140960795 + 7390410 * 2 ^ 59
def prefixEnd_7390410 : Nat := 4983230072969 + 3 ^ 40 * 7390410 * 2
def baseEnd_7390410 : Nat := 3794832563794535220587129

theorem tailTrace_7390410 : CollatzResearch.WordTrace tailWord_7390410 prefixEnd_7390410 3794832563794535220587129 := by
  unfold tailWord_7390410
  simp only [CollatzResearch.WordTrace]
  refine ⟨67387599288953556596426171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179700264770542817590469789 67387599288953556596426171)
  ·
    refine ⟨101081398933430334894639257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67387599288953556596426171 101081398933430334894639257)
    ·
      refine ⟨75811049200072751170979443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101081398933430334894639257 75811049200072751170979443)
      ·
        refine ⟨113716573800109126756469165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75811049200072751170979443 113716573800109126756469165)
        ·
          refine ⟨42643715175040922533675937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113716573800109126756469165 42643715175040922533675937)
          ·
            refine ⟨31982786381280691900256953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42643715175040922533675937 31982786381280691900256953)
            ·
              refine ⟨23987089785960518925192715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31982786381280691900256953 23987089785960518925192715)
              ·
                refine ⟨35980634678940778387789073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23987089785960518925192715 35980634678940778387789073)
                ·
                  refine ⟨26985476009205583790841805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35980634678940778387789073 26985476009205583790841805)
                  ·
                    refine ⟨10119553503452093921565677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26985476009205583790841805 10119553503452093921565677)
                    ·
                      refine ⟨3794832563794535220587129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10119553503452093921565677 3794832563794535220587129)
                      ·
                        rfl

theorem cell23_7390410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_7390410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390410 prefixEnd_7390410 := by exact prefixLift 7390410
  have htrace : WordTrace (prefixWord ++ tailWord_7390410) baseStart_7390410 baseEnd_7390410 := by
    simpa [prefixWord, tailWord_7390410, baseEnd_7390410] using wordTrace_append hprefix tailTrace_7390410
  have hstable : (prefixWord ++ tailWord_7390410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390410).length < 2 ^ (prefixWord ++ tailWord_7390410).sum := by decide
  have hdescent : baseEnd_7390410 < baseStart_7390410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390487 : List Nat := [1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 3]
def baseStart_7390487 : Nat := 118140960795 + 7390487 * 2 ^ 59
def prefixEnd_7390487 : Nat := 4983230072969 + 3 ^ 40 * 7390487 * 2
def baseEnd_7390487 : Nat := 3794872101804931419324275

theorem tailTrace_7390487 : CollatzResearch.WordTrace tailWord_7390487 prefixEnd_7390487 3794872101804931419324275 := by
  unfold tailWord_7390487
  simp only [CollatzResearch.WordTrace]
  refine ⟨269553205576535268536257715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179702137051023512357505143 269553205576535268536257715)
  ·
    refine ⟨404329808364802902804386573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269553205576535268536257715 404329808364802902804386573)
    ·
      refine ⟨151623678136801088551644965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404329808364802902804386573 151623678136801088551644965)
      ·
        refine ⟨28429439650650204103433431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151623678136801088551644965 28429439650650204103433431)
        ·
          refine ⟨42644159475975306155150147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28429439650650204103433431 42644159475975306155150147)
          ·
            refine ⟨63966239213962959232725221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42644159475975306155150147 63966239213962959232725221)
            ·
              refine ⟨11993669852618054856135979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63966239213962959232725221 11993669852618054856135979)
              ·
                refine ⟨17990504778927082284203969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11993669852618054856135979 17990504778927082284203969)
                ·
                  refine ⟨13492878584195311713152977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17990504778927082284203969 13492878584195311713152977)
                  ·
                    refine ⟨10119658938146483784864733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13492878584195311713152977 10119658938146483784864733)
                    ·
                      refine ⟨3794872101804931419324275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10119658938146483784864733 3794872101804931419324275)
                      ·
                        rfl

theorem cell23_7390487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_7390487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390487 prefixEnd_7390487 := by exact prefixLift 7390487
  have htrace : WordTrace (prefixWord ++ tailWord_7390487) baseStart_7390487 baseEnd_7390487 := by
    simpa [prefixWord, tailWord_7390487, baseEnd_7390487] using wordTrace_append hprefix tailTrace_7390487
  have hstable : (prefixWord ++ tailWord_7390487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390487).length < 2 ^ (prefixWord ++ tailWord_7390487).sum := by decide
  have hdescent : baseEnd_7390487 < baseStart_7390487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390551 : List Nat := [1, 1, 3, 2, 3, 3, 2, 3, 1, 1, 3]
def baseStart_7390551 : Nat := 118140960795 + 7390551 * 2 ^ 59
def prefixEnd_7390551 : Nat := 4983230072969 + 3 ^ 40 * 7390551 * 2
def baseEnd_7390551 : Nat := 3794904964566819168923981

theorem tailTrace_7390551 : CollatzResearch.WordTrace tailWord_7390551 prefixEnd_7390551 3794904964566819168923981 := by
  unfold tailWord_7390551
  simp only [CollatzResearch.WordTrace]
  refine ⟨269555539848303407466587507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179703693232202271644391671 269555539848303407466587507)
  ·
    refine ⟨404333309772455111199881261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269555539848303407466587507 404333309772455111199881261)
    ·
      refine ⟨151624991164670666699955473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404333309772455111199881261 151624991164670666699955473)
      ·
        refine ⟨113718743373503000024966605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151624991164670666699955473 113718743373503000024966605)
        ·
          refine ⟨42644528765063625009362477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113718743373503000024966605 42644528765063625009362477)
          ·
            refine ⟨15991698286898859378510929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42644528765063625009362477 15991698286898859378510929)
            ·
              refine ⟨11993773715174144533883197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15991698286898859378510929 11993773715174144533883197)
              ·
                refine ⟨4497665143190304200206199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11993773715174144533883197 4497665143190304200206199)
                ·
                  refine ⟨6746497714785456300309299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4497665143190304200206199 6746497714785456300309299)
                  ·
                    refine ⟨10119746572178184450463949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6746497714785456300309299 10119746572178184450463949)
                    ·
                      refine ⟨3794904964566819168923981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10119746572178184450463949 3794904964566819168923981)
                      ·
                        rfl

theorem cell23_7390551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 1, 1, 3].length) (baseStart_7390551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390551 prefixEnd_7390551 := by exact prefixLift 7390551
  have htrace : WordTrace (prefixWord ++ tailWord_7390551) baseStart_7390551 baseEnd_7390551 := by
    simpa [prefixWord, tailWord_7390551, baseEnd_7390551] using wordTrace_append hprefix tailTrace_7390551
  have hstable : (prefixWord ++ tailWord_7390551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390551).length < 2 ^ (prefixWord ++ tailWord_7390551).sum := by decide
  have hdescent : baseEnd_7390551 < baseStart_7390551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390624 : List Nat := [2, 1, 1, 4, 1, 2, 2, 4, 2, 1, 3]
def baseStart_7390624 : Nat := 118140960795 + 7390624 * 2 ^ 59
def prefixEnd_7390624 : Nat := 4983230072969 + 3 ^ 40 * 7390624 * 2
def baseEnd_7390624 : Nat := 3794942448654597383311145

theorem tailTrace_7390624 : CollatzResearch.WordTrace tailWord_7390624 prefixEnd_7390624 3794942448654597383311145 := by
  unfold tailWord_7390624
  simp only [CollatzResearch.WordTrace]
  refine ⟨134779101188519470466997463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179705468251359293955996617 134779101188519470466997463)
  ·
    refine ⟨202168651782779205700496195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134779101188519470466997463 202168651782779205700496195)
    ·
      refine ⟨303252977674168808550744293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202168651782779205700496195 303252977674168808550744293)
      ·
        refine ⟨56859933313906651603264555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303252977674168808550744293 56859933313906651603264555)
        ·
          refine ⟨85289899970859977404896833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56859933313906651603264555 85289899970859977404896833)
          ·
            refine ⟨63967424978144983053672625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85289899970859977404896833 63967424978144983053672625)
            ·
              refine ⟨47975568733608737290254469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63967424978144983053672625 47975568733608737290254469)
              ·
                refine ⟨8995419137551638241922713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47975568733608737290254469 8995419137551638241922713)
                ·
                  refine ⟨6746564353163728681442035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8995419137551638241922713 6746564353163728681442035)
                  ·
                    refine ⟨10119846529745593022163053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6746564353163728681442035 10119846529745593022163053)
                    ·
                      refine ⟨3794942448654597383311145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10119846529745593022163053 3794942448654597383311145)
                      ·
                        rfl

theorem cell23_7390624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_7390624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390624 prefixEnd_7390624 := by exact prefixLift 7390624
  have htrace : WordTrace (prefixWord ++ tailWord_7390624) baseStart_7390624 baseEnd_7390624 := by
    simpa [prefixWord, tailWord_7390624, baseEnd_7390624] using wordTrace_append hprefix tailTrace_7390624
  have hstable : (prefixWord ++ tailWord_7390624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390624).length < 2 ^ (prefixWord ++ tailWord_7390624).sum := by decide
  have hdescent : baseEnd_7390624 < baseStart_7390624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390664 : List Nat := [2, 1, 3, 1, 3, 1, 3, 2, 1, 4, 2]
def baseStart_7390664 : Nat := 118140960795 + 7390664 * 2 ^ 59
def prefixEnd_7390664 : Nat := 4983230072969 + 3 ^ 40 * 7390664 * 2
def baseEnd_7390664 : Nat := 3794962987880777226810961

theorem tailTrace_7390664 : CollatzResearch.WordTrace tailWord_7390664 prefixEnd_7390664 3794962987880777226810961 := by
  unfold tailWord_7390664
  simp only [CollatzResearch.WordTrace]
  refine ⟨134779830648447013882725523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179706440864596018510300697 134779830648447013882725523)
  ·
    refine ⟨202169745972670520824088285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134779830648447013882725523 202169745972670520824088285)
    ·
      refine ⟨75813654739751445309033107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202169745972670520824088285 75813654739751445309033107)
      ·
        refine ⟨113720482109627167963549661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75813654739751445309033107 113720482109627167963549661)
        ·
          refine ⟨42645180791110187986331123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113720482109627167963549661 42645180791110187986331123)
          ·
            refine ⟨63967771186665281979496685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42645180791110187986331123 63967771186665281979496685)
            ·
              refine ⟨23987914194999480742311257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63967771186665281979496685 23987914194999480742311257)
              ·
                refine ⟨17990935646249610556733443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23987914194999480742311257 17990935646249610556733443)
                ·
                  refine ⟨26986403469374415835100165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17990935646249610556733443 26986403469374415835100165)
                  ·
                    refine ⟨5059950650507702969081281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26986403469374415835100165 5059950650507702969081281)
                    ·
                      refine ⟨3794962987880777226810961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5059950650507702969081281 3794962987880777226810961)
                      ·
                        rfl

theorem cell23_7390664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_7390664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390664 prefixEnd_7390664 := by exact prefixLift 7390664
  have htrace : WordTrace (prefixWord ++ tailWord_7390664) baseStart_7390664 baseEnd_7390664 := by
    simpa [prefixWord, tailWord_7390664, baseEnd_7390664] using wordTrace_append hprefix tailTrace_7390664
  have hstable : (prefixWord ++ tailWord_7390664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390664).length < 2 ^ (prefixWord ++ tailWord_7390664).sum := by decide
  have hdescent : baseEnd_7390664 < baseStart_7390664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390668 : List Nat := [2, 2, 1, 4, 2, 2, 3, 1, 1, 3, 2]
def baseStart_7390668 : Nat := 118140960795 + 7390668 * 2 ^ 59
def prefixEnd_7390668 : Nat := 4983230072969 + 3 ^ 40 * 7390668 * 2
def baseEnd_7390668 : Nat := 3794965041803395211160943

theorem tailTrace_7390668 : CollatzResearch.WordTrace tailWord_7390668 prefixEnd_7390668 3794965041803395211160943 := by
  unfold tailWord_7390668
  simp only [CollatzResearch.WordTrace]
  refine ⟨134779903594439768224298329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179706538125919690965731105 134779903594439768224298329)
  ·
    refine ⟨101084927695829826168223747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134779903594439768224298329 101084927695829826168223747)
    ·
      refine ⟨151627391543744739252335621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101084927695829826168223747 151627391543744739252335621)
      ·
        refine ⟨28430135914452138609812929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151627391543744739252335621 28430135914452138609812929)
        ·
          refine ⟨21322601935839103957359697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28430135914452138609812929 21322601935839103957359697)
          ·
            refine ⟨15991951451879327968019773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21322601935839103957359697 15991951451879327968019773)
            ·
              refine ⟨5996981794454747988007415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15991951451879327968019773 5996981794454747988007415)
              ·
                refine ⟨8995472691682121982011123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5996981794454747988007415 8995472691682121982011123)
                ·
                  refine ⟨13493209037523182973016685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8995472691682121982011123 13493209037523182973016685)
                  ·
                    refine ⟨5059953389071193614881257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13493209037523182973016685 5059953389071193614881257)
                    ·
                      refine ⟨3794965041803395211160943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5059953389071193614881257 3794965041803395211160943)
                      ·
                        rfl

theorem cell23_7390668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_7390668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390668 prefixEnd_7390668 := by exact prefixLift 7390668
  have htrace : WordTrace (prefixWord ++ tailWord_7390668) baseStart_7390668 baseEnd_7390668 := by
    simpa [prefixWord, tailWord_7390668, baseEnd_7390668] using wordTrace_append hprefix tailTrace_7390668
  have hstable : (prefixWord ++ tailWord_7390668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390668).length < 2 ^ (prefixWord ++ tailWord_7390668).sum := by decide
  have hdescent : baseEnd_7390668 < baseStart_7390668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390677 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_7390677 : Nat := 118140960795 + 7390677 * 2 ^ 59
def prefixEnd_7390677 : Nat := 4983230072969 + 3 ^ 40 * 7390677 * 2
def baseEnd_7390677 : Nat := 3794969663129285675948401

theorem tailTrace_7390677 : CollatzResearch.WordTrace tailWord_7390677 prefixEnd_7390677 3794969663129285675948401 := by
  unfold tailWord_7390677
  simp only [CollatzResearch.WordTrace]
  refine ⟨269560135445846930985674285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179706756963897953990449523 269560135445846930985674285)
  ·
    refine ⟨101085050792192599119627857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269560135445846930985674285 101085050792192599119627857)
    ·
      refine ⟨75813788094144449339720893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101085050792192599119627857 75813788094144449339720893)
      ·
        refine ⟨28430170535304168502395335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75813788094144449339720893 28430170535304168502395335)
        ·
          refine ⟨42645255802956252753593003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28430170535304168502395335 42645255802956252753593003)
          ·
            refine ⟨63967883704434379130389505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42645255802956252753593003 63967883704434379130389505)
            ·
              refine ⟨47975912778325784347792129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63967883704434379130389505 47975912778325784347792129)
              ·
                refine ⟨35981934583744338260844097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47975912778325784347792129 35981934583744338260844097)
                ·
                  refine ⟨26986450937808253695633073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35981934583744338260844097 26986450937808253695633073)
                  ·
                    refine ⟨20239838203356190271724805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26986450937808253695633073 20239838203356190271724805)
                    ·
                      refine ⟨3794969663129285675948401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20239838203356190271724805 3794969663129285675948401)
                      ·
                        rfl

theorem cell23_7390677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_7390677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390677 prefixEnd_7390677 := by exact prefixLift 7390677
  have htrace : WordTrace (prefixWord ++ tailWord_7390677) baseStart_7390677 baseEnd_7390677 := by
    simpa [prefixWord, tailWord_7390677, baseEnd_7390677] using wordTrace_append hprefix tailTrace_7390677
  have hstable : (prefixWord ++ tailWord_7390677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390677).length < 2 ^ (prefixWord ++ tailWord_7390677).sum := by decide
  have hdescent : baseEnd_7390677 < baseStart_7390677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390680 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 1, 2, 7]
def baseStart_7390680 : Nat := 118140960795 + 7390680 * 2 ^ 59
def prefixEnd_7390680 : Nat := 4983230072969 + 3 ^ 40 * 7390680 * 2
def baseEnd_7390680 : Nat := 3794971203571249164210887

theorem tailTrace_7390680 : CollatzResearch.WordTrace tailWord_7390680 prefixEnd_7390680 3794971203571249164210887 := by
  unfold tailWord_7390680
  simp only [CollatzResearch.WordTrace]
  refine ⟨134780122432418031249016747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179706829909890708332022329 134780122432418031249016747)
  ·
    refine ⟨202170183648627046873525121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134780122432418031249016747 202170183648627046873525121)
    ·
      refine ⟨151627637736470285155143841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202170183648627046873525121 151627637736470285155143841)
      ·
        refine ⟨113720728302352713866357881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151627637736470285155143841 113720728302352713866357881)
        ·
          refine ⟨85290546226764535399768411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113720728302352713866357881 85290546226764535399768411)
          ·
            refine ⟨127935819340146803099652617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85290546226764535399768411 127935819340146803099652617)
            ·
              refine ⟨95951864505110102324739463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127935819340146803099652617 95951864505110102324739463)
              ·
                refine ⟨143927796757665153487109195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95951864505110102324739463 143927796757665153487109195)
                ·
                  refine ⟨215891695136497730230663793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143927796757665153487109195 215891695136497730230663793)
                  ·
                    refine ⟨161918771352373297672997845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 215891695136497730230663793 161918771352373297672997845)
                    ·
                      refine ⟨3794971203571249164210887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161918771352373297672997845 3794971203571249164210887)
                      ·
                        rfl

theorem cell23_7390680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_7390680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390680 prefixEnd_7390680 := by exact prefixLift 7390680
  have htrace : WordTrace (prefixWord ++ tailWord_7390680) baseStart_7390680 baseEnd_7390680 := by
    simpa [prefixWord, tailWord_7390680, baseEnd_7390680] using wordTrace_append hprefix tailTrace_7390680
  have hstable : (prefixWord ++ tailWord_7390680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390680).length < 2 ^ (prefixWord ++ tailWord_7390680).sum := by decide
  have hdescent : baseEnd_7390680 < baseStart_7390680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390681 : List Nat := [1, 2, 1, 2, 4, 2, 1, 4, 2, 2, 2]
def baseStart_7390681 : Nat := 118140960795 + 7390681 * 2 ^ 59
def prefixEnd_7390681 : Nat := 4983230072969 + 3 ^ 40 * 7390681 * 2
def baseEnd_7390681 : Nat := 3794971717051903660298383

theorem tailTrace_7390681 : CollatzResearch.WordTrace tailWord_7390681 prefixEnd_7390681 3794971717051903660298383 := by
  unfold tailWord_7390681
  simp only [CollatzResearch.WordTrace]
  refine ⟨269560281337832439668819897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179706854225221626445879931 269560281337832439668819897)
  ·
    refine ⟨202170211003374329751614923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269560281337832439668819897 202170211003374329751614923)
    ·
      refine ⟨303255316505061494627422385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202170211003374329751614923 303255316505061494627422385)
      ·
        refine ⟨227441487378796120970566789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303255316505061494627422385 227441487378796120970566789)
        ·
          refine ⟨42645278883524272681981273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227441487378796120970566789 42645278883524272681981273)
          ·
            refine ⟨31983959162643204511485955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42645278883524272681981273 31983959162643204511485955)
            ·
              refine ⟨47975938743964806767228933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31983959162643204511485955 47975938743964806767228933)
              ·
                refine ⟨8995488514493401268855425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47975938743964806767228933 8995488514493401268855425)
                ·
                  refine ⟨6746616385870050951641569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8995488514493401268855425 6746616385870050951641569)
                  ·
                    refine ⟨5059962289402538213731177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6746616385870050951641569 5059962289402538213731177)
                    ·
                      refine ⟨3794971717051903660298383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5059962289402538213731177 3794971717051903660298383)
                      ·
                        rfl

theorem cell23_7390681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 2, 2].length) (baseStart_7390681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390681 prefixEnd_7390681 := by exact prefixLift 7390681
  have htrace : WordTrace (prefixWord ++ tailWord_7390681) baseStart_7390681 baseEnd_7390681 := by
    simpa [prefixWord, tailWord_7390681, baseEnd_7390681] using wordTrace_append hprefix tailTrace_7390681
  have hstable : (prefixWord ++ tailWord_7390681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390681).length < 2 ^ (prefixWord ++ tailWord_7390681).sum := by decide
  have hdescent : baseEnd_7390681 < baseStart_7390681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390717 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 1, 7]
def baseStart_7390717 : Nat := 118140960795 + 7390717 * 2 ^ 59
def prefixEnd_7390717 : Nat := 4983230072969 + 3 ^ 40 * 7390717 * 2
def baseEnd_7390717 : Nat := 1264996734118488506482739

theorem tailTrace_7390717 : CollatzResearch.WordTrace tailWord_7390717 prefixEnd_7390717 1264996734118488506482739 := by
  unfold tailWord_7390717
  simp only [CollatzResearch.WordTrace]
  refine ⟨269561594365702017817130405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179707729577134678544753603 269561594365702017817130405)
  ·
    refine ⟨50542798943569128340711951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269561594365702017817130405 50542798943569128340711951)
    ·
      refine ⟨75814198415353692511067927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50542798943569128340711951 75814198415353692511067927)
      ·
        refine ⟨113721297623030538766601891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75814198415353692511067927 113721297623030538766601891)
        ·
          refine ⟨170581946434545808149902837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113721297623030538766601891 170581946434545808149902837)
          ·
            refine ⟨15992057478238669514053391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170581946434545808149902837 15992057478238669514053391)
            ·
              refine ⟨23988086217358004271080087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15992057478238669514053391 23988086217358004271080087)
              ·
                refine ⟨35982129326037006406620131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23988086217358004271080087 35982129326037006406620131)
                ·
                  refine ⟨53973193989055509609930197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35982129326037006406620131 53973193989055509609930197)
                  ·
                    refine ⟨1264996734118488506482739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53973193989055509609930197 1264996734118488506482739)
                    ·
                      rfl

theorem cell23_7390717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_7390717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390717 prefixEnd_7390717 := by exact prefixLift 7390717
  have htrace : WordTrace (prefixWord ++ tailWord_7390717) baseStart_7390717 baseEnd_7390717 := by
    simpa [prefixWord, tailWord_7390717, baseEnd_7390717] using wordTrace_append hprefix tailTrace_7390717
  have hstable : (prefixWord ++ tailWord_7390717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390717).length < 2 ^ (prefixWord ++ tailWord_7390717).sum := by decide
  have hdescent : baseEnd_7390717 < baseStart_7390717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390721 : List Nat := [1, 2, 4, 1, 4, 1, 2, 3, 5]
def baseStart_7390721 : Nat := 118140960795 + 7390721 * 2 ^ 59
def prefixEnd_7390721 : Nat := 4983230072969 + 3 ^ 40 * 7390721 * 2
def baseEnd_7390721 : Nat := 421665806253120389310911

theorem tailTrace_7390721 : CollatzResearch.WordTrace tailWord_7390721 prefixEnd_7390721 421665806253120389310911 := by
  unfold tailWord_7390721
  simp only [CollatzResearch.WordTrace]
  refine ⟨269561740257687526500276017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179707826838458351000184011 269561740257687526500276017)
  ·
    refine ⟨202171305193265644875207013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269561740257687526500276017 202171305193265644875207013)
    ·
      refine ⟨37907119723737308414101315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202171305193265644875207013 37907119723737308414101315)
      ·
        refine ⟨56860679585605962621151973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37907119723737308414101315 56860679585605962621151973)
        ·
          refine ⟨10661377422301117991465995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56860679585605962621151973 10661377422301117991465995)
          ·
            refine ⟨15992066133451676987198993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10661377422301117991465995 15992066133451676987198993)
            ·
              refine ⟨11994049600088757740399245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15992066133451676987198993 11994049600088757740399245)
              ·
                refine ⟨4497768600033284152649717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11994049600088757740399245 4497768600033284152649717)
                ·
                  refine ⟨421665806253120389310911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4497768600033284152649717 421665806253120389310911)
                  ·
                    rfl

theorem cell23_7390721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 5].length) (baseStart_7390721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390721 prefixEnd_7390721 := by exact prefixLift 7390721
  have htrace : WordTrace (prefixWord ++ tailWord_7390721) baseStart_7390721 baseEnd_7390721 := by
    simpa [prefixWord, tailWord_7390721, baseEnd_7390721] using wordTrace_append hprefix tailTrace_7390721
  have hstable : (prefixWord ++ tailWord_7390721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390721).length < 2 ^ (prefixWord ++ tailWord_7390721).sum := by decide
  have hdescent : baseEnd_7390721 < baseStart_7390721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390737 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 4]
def baseStart_7390737 : Nat := 118140960795 + 7390737 * 2 ^ 59
def prefixEnd_7390737 : Nat := 4983230072969 + 3 ^ 40 * 7390737 * 2
def baseEnd_7390737 : Nat := 3795000471968555441198125

theorem tailTrace_7390737 : CollatzResearch.WordTrace tailWord_7390737 prefixEnd_7390737 3795000471968555441198125 := by
  unfold tailWord_7390737
  simp only [CollatzResearch.WordTrace]
  refine ⟨269562323825629561232858465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179708215883753040821905643 269562323825629561232858465)
  ·
    refine ⟨202171742869222170924643849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269562323825629561232858465 202171742869222170924643849)
    ·
      refine ⟨151628807151916628193482887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202171742869222170924643849 151628807151916628193482887)
      ·
        refine ⟨227443210727874942290224331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151628807151916628193482887 227443210727874942290224331)
        ·
          refine ⟨341164816091812413435336497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227443210727874942290224331 341164816091812413435336497)
          ·
            refine ⟨255873612068859310076502373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341164816091812413435336497 255873612068859310076502373)
            ·
              refine ⟨47976302262911120639344195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255873612068859310076502373 47976302262911120639344195)
              ·
                refine ⟨71964453394366680959016293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47976302262911120639344195 71964453394366680959016293)
                ·
                  refine ⟨13493335011443752679815555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71964453394366680959016293 13493335011443752679815555)
                  ·
                    refine ⟨20240002517165629019723333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13493335011443752679815555 20240002517165629019723333)
                    ·
                      refine ⟨3795000471968555441198125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20240002517165629019723333 3795000471968555441198125)
                      ·
                        rfl

theorem cell23_7390737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_7390737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390737 prefixEnd_7390737 := by exact prefixLift 7390737
  have htrace : WordTrace (prefixWord ++ tailWord_7390737) baseStart_7390737 baseEnd_7390737 := by
    simpa [prefixWord, tailWord_7390737, baseEnd_7390737] using wordTrace_append hprefix tailTrace_7390737
  have hstable : (prefixWord ++ tailWord_7390737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390737).length < 2 ^ (prefixWord ++ tailWord_7390737).sum := by decide
  have hdescent : baseEnd_7390737 < baseStart_7390737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390777 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 8]
def baseStart_7390777 : Nat := 118140960795 + 7390777 * 2 ^ 59
def prefixEnd_7390777 : Nat := 4983230072969 + 3 ^ 40 * 7390777 * 2
def baseEnd_7390777 : Nat := 421669001243859476077549

theorem tailTrace_7390777 : CollatzResearch.WordTrace tailWord_7390777 prefixEnd_7390777 421669001243859476077549 := by
  unfold tailWord_7390777
  simp only [CollatzResearch.WordTrace]
  refine ⟨269563782745484648064314585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179709188496989765376209723 269563782745484648064314585)
  ·
    refine ⟨202172837059113486048235939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269563782745484648064314585 202172837059113486048235939)
    ·
      refine ⟨303259255588670229072353909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202172837059113486048235939 303259255588670229072353909)
      ·
        refine ⟨28430555211437833975533179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 303259255588670229072353909 28430555211437833975533179)
        ·
          refine ⟨42645832817156750963299769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28430555211437833975533179 42645832817156750963299769)
          ·
            refine ⟨31984374612867563222474827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42645832817156750963299769 31984374612867563222474827)
            ·
              refine ⟨47976561919301344833712241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31984374612867563222474827 47976561919301344833712241)
              ·
                refine ⟨35982421439476008625284181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47976561919301344833712241 35982421439476008625284181)
                ·
                  refine ⟨421669001243859476077549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35982421439476008625284181 421669001243859476077549)
                  ·
                    rfl

theorem cell23_7390777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 8].length) (baseStart_7390777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390777 prefixEnd_7390777 := by exact prefixLift 7390777
  have htrace : WordTrace (prefixWord ++ tailWord_7390777) baseStart_7390777 baseEnd_7390777 := by
    simpa [prefixWord, tailWord_7390777, baseEnd_7390777] using wordTrace_append hprefix tailTrace_7390777
  have hstable : (prefixWord ++ tailWord_7390777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390777).length < 2 ^ (prefixWord ++ tailWord_7390777).sum := by decide
  have hdescent : baseEnd_7390777 < baseStart_7390777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390791 : List Nat := [1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 3]
def baseStart_7390791 : Nat := 118140960795 + 7390791 * 2 ^ 59
def prefixEnd_7390791 : Nat := 4983230072969 + 3 ^ 40 * 7390791 * 2
def baseEnd_7390791 : Nat := 3795028199923898229922877

theorem tailTrace_7390791 : CollatzResearch.WordTrace tailWord_7390791 prefixEnd_7390791 3795028199923898229922877 := by
  unfold tailWord_7390791
  simp only [CollatzResearch.WordTrace]
  refine ⟨269564293367433928455324227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179709528911622618970216151 269564293367433928455324227)
  ·
    refine ⟨404346440051150892682986341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269564293367433928455324227 404346440051150892682986341)
    ·
      refine ⟨75814957509590792378059939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404346440051150892682986341 75814957509590792378059939)
      ·
        refine ⟨113722436264386188567089909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75814957509590792378059939 113722436264386188567089909)
        ·
          refine ⟨10661478399786205178164679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113722436264386188567089909 10661478399786205178164679)
          ·
            refine ⟨15992217599679307767247019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10661478399786205178164679 15992217599679307767247019)
            ·
              refine ⟨23988326399518961650870529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15992217599679307767247019 23988326399518961650870529)
              ·
                refine ⟨17991244799639221238152897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23988326399518961650870529 17991244799639221238152897)
                ·
                  refine ⟨13493433599729415928614673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17991244799639221238152897 13493433599729415928614673)
                  ·
                    refine ⟨10120075199797061946461005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13493433599729415928614673 10120075199797061946461005)
                    ·
                      refine ⟨3795028199923898229922877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10120075199797061946461005 3795028199923898229922877)
                      ·
                        rfl

theorem cell23_7390791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_7390791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390791 prefixEnd_7390791 := by exact prefixLift 7390791
  have htrace : WordTrace (prefixWord ++ tailWord_7390791) baseStart_7390791 baseEnd_7390791 := by
    simpa [prefixWord, tailWord_7390791, baseEnd_7390791] using wordTrace_append hprefix tailTrace_7390791
  have hstable : (prefixWord ++ tailWord_7390791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390791).length < 2 ^ (prefixWord ++ tailWord_7390791).sum := by decide
  have hdescent : baseEnd_7390791 < baseStart_7390791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390841 : List Nat := [1, 2, 1, 3, 3, 1, 5, 1, 1, 5]
def baseStart_7390841 : Nat := 118140960795 + 7390841 * 2 ^ 59
def prefixEnd_7390841 : Nat := 4983230072969 + 3 ^ 40 * 7390841 * 2
def baseEnd_7390841 : Nat := 1265017957985541011432549

theorem tailTrace_7390841 : CollatzResearch.WordTrace tailWord_7390841 prefixEnd_7390841 1265017957985541011432549 := by
  unfold tailWord_7390841
  simp only [CollatzResearch.WordTrace]
  refine ⟨269566117017252786994644377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179710744678168524663096251 269566117017252786994644377)
  ·
    refine ⟨202174587762939590245983283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269566117017252786994644377 202174587762939590245983283)
    ·
      refine ⟨303261881644409385368974925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202174587762939590245983283 303261881644409385368974925)
      ·
        refine ⟨113723205616653519513365597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303261881644409385368974925 113723205616653519513365597)
        ·
          refine ⟨42646202106245069817512099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113723205616653519513365597 42646202106245069817512099)
          ·
            refine ⟨63969303159367604726268149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42646202106245069817512099 63969303159367604726268149)
            ·
              refine ⟨5997122171190712943087639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63969303159367604726268149 5997122171190712943087639)
              ·
                refine ⟨8995683256786069414631459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5997122171190712943087639 8995683256786069414631459)
                ·
                  refine ⟨13493524885179104121947189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8995683256786069414631459 13493524885179104121947189)
                  ·
                    refine ⟨1265017957985541011432549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13493524885179104121947189 1265017957985541011432549)
                    ·
                      rfl

theorem cell23_7390841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 1, 5].length) (baseStart_7390841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390841 prefixEnd_7390841 := by exact prefixLift 7390841
  have htrace : WordTrace (prefixWord ++ tailWord_7390841) baseStart_7390841 baseEnd_7390841 := by
    simpa [prefixWord, tailWord_7390841, baseEnd_7390841] using wordTrace_append hprefix tailTrace_7390841
  have hstable : (prefixWord ++ tailWord_7390841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390841).length < 2 ^ (prefixWord ++ tailWord_7390841).sum := by decide
  have hdescent : baseEnd_7390841 < baseStart_7390841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390855 : List Nat := [1, 1, 4, 2, 1, 3, 4, 2, 1, 1, 3]
def baseStart_7390855 : Nat := 118140960795 + 7390855 * 2 ^ 59
def prefixEnd_7390855 : Nat := 4983230072969 + 3 ^ 40 * 7390855 * 2
def baseEnd_7390855 : Nat := 3795061062685785979522583

theorem tailTrace_7390855 : CollatzResearch.WordTrace tailWord_7390855 prefixEnd_7390855 3795061062685785979522583 := by
  unfold tailWord_7390855
  simp only [CollatzResearch.WordTrace]
  refine ⟨269566627639202067385654019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179711085092801378257102679 269566627639202067385654019)
  ·
    refine ⟨404349941458803101078481029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269566627639202067385654019 404349941458803101078481029)
    ·
      refine ⟨75815614023525581452215193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404349941458803101078481029 75815614023525581452215193)
      ·
        refine ⟨56861710517644186089161395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75815614023525581452215193 56861710517644186089161395)
        ·
          refine ⟨85292565776466279133742093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56861710517644186089161395 85292565776466279133742093)
          ·
            refine ⟨31984712166174854675153285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85292565776466279133742093 31984712166174854675153285)
            ·
              refine ⟨5997133531157785251591241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31984712166174854675153285 5997133531157785251591241)
              ·
                refine ⟨4497850148368338938693431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5997133531157785251591241 4497850148368338938693431)
                ·
                  refine ⟨6746775222552508408040147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4497850148368338938693431 6746775222552508408040147)
                  ·
                    refine ⟨10120162833828762612060221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6746775222552508408040147 10120162833828762612060221)
                    ·
                      refine ⟨3795061062685785979522583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10120162833828762612060221 3795061062685785979522583)
                      ·
                        rfl

theorem cell23_7390855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_7390855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390855 prefixEnd_7390855 := by exact prefixLift 7390855
  have htrace : WordTrace (prefixWord ++ tailWord_7390855) baseStart_7390855 baseEnd_7390855 := by
    simpa [prefixWord, tailWord_7390855, baseEnd_7390855] using wordTrace_append hprefix tailTrace_7390855
  have hstable : (prefixWord ++ tailWord_7390855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390855).length < 2 ^ (prefixWord ++ tailWord_7390855).sum := by decide
  have hdescent : baseEnd_7390855 < baseStart_7390855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390857 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 3, 1, 6]
def baseStart_7390857 : Nat := 118140960795 + 7390857 * 2 ^ 59
def prefixEnd_7390857 : Nat := 4983230072969 + 3 ^ 40 * 7390857 * 2
def baseEnd_7390857 : Nat := 3795062089647094971697573

theorem tailTrace_7390857 : CollatzResearch.WordTrace tailWord_7390857 prefixEnd_7390857 3795062089647094971697573 := by
  unfold tailWord_7390857
  simp only [CollatzResearch.WordTrace]
  refine ⟨269566700585194821727226825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179711133723463214484817883 269566700585194821727226825)
  ·
    refine ⟨202175025438896116295420119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269566700585194821727226825 202175025438896116295420119)
    ·
      refine ⟨303262538158344174443130179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202175025438896116295420119 303262538158344174443130179)
      ·
        refine ⟨454893807237516261664695269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303262538158344174443130179 454893807237516261664695269)
        ·
          refine ⟨85292588857034299062130363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 454893807237516261664695269 85292588857034299062130363)
          ·
            refine ⟨127938883285551448593195545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85292588857034299062130363 127938883285551448593195545)
            ·
              refine ⟨95954162464163586444896659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127938883285551448593195545 95954162464163586444896659)
              ·
                refine ⟨143931243696245379667344989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95954162464163586444896659 143931243696245379667344989)
                ·
                  refine ⟨53974216386092017375254371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143931243696245379667344989 53974216386092017375254371)
                  ·
                    refine ⟨80961324579138026062881557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53974216386092017375254371 80961324579138026062881557)
                    ·
                      refine ⟨3795062089647094971697573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80961324579138026062881557 3795062089647094971697573)
                      ·
                        rfl

theorem cell23_7390857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_7390857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390857 prefixEnd_7390857 := by exact prefixLift 7390857
  have htrace : WordTrace (prefixWord ++ tailWord_7390857) baseStart_7390857 baseEnd_7390857 := by
    simpa [prefixWord, tailWord_7390857, baseEnd_7390857] using wordTrace_append hprefix tailTrace_7390857
  have hstable : (prefixWord ++ tailWord_7390857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390857).length < 2 ^ (prefixWord ++ tailWord_7390857).sum := by decide
  have hdescent : baseEnd_7390857 < baseStart_7390857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390871 : List Nat := [1, 1, 3, 3, 2, 2, 2, 3, 2, 4]
def baseStart_7390871 : Nat := 118140960795 + 7390871 * 2 ^ 59
def prefixEnd_7390871 : Nat := 4983230072969 + 3 ^ 40 * 7390871 * 2
def baseEnd_7390871 : Nat := 1265023092792085972307503

theorem tailTrace_7390871 : CollatzResearch.WordTrace tailWord_7390871 prefixEnd_7390871 1265023092792085972307503 := by
  unfold tailWord_7390871
  simp only [CollatzResearch.WordTrace]
  refine ⟨269567211207144102118236467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179711474138096068078824311 269567211207144102118236467)
  ·
    refine ⟨404350816810716153177354701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269567211207144102118236467 404350816810716153177354701)
    ·
      refine ⟨151631556304018557441508013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404350816810716153177354701 151631556304018557441508013)
      ·
        refine ⟨56861833614006959040565505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151631556304018557441508013 56861833614006959040565505)
        ·
          refine ⟨42646375210505219280424129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56861833614006959040565505 42646375210505219280424129)
          ·
            refine ⟨31984781407878914460318097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42646375210505219280424129 31984781407878914460318097)
            ·
              refine ⟨23988586055909185845238573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31984781407878914460318097 23988586055909185845238573)
              ·
                refine ⟨8995719770965944691964465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23988586055909185845238573 8995719770965944691964465)
                ·
                  refine ⟨6746789828224458518973349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8995719770965944691964465 6746789828224458518973349)
                  ·
                    refine ⟨1265023092792085972307503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6746789828224458518973349 1265023092792085972307503)
                    ·
                      rfl

theorem cell23_7390871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_7390871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390871 prefixEnd_7390871 := by exact prefixLift 7390871
  have htrace : WordTrace (prefixWord ++ tailWord_7390871) baseStart_7390871 baseEnd_7390871 := by
    simpa [prefixWord, tailWord_7390871, baseEnd_7390871] using wordTrace_append hprefix tailTrace_7390871
  have hstable : (prefixWord ++ tailWord_7390871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390871).length < 2 ^ (prefixWord ++ tailWord_7390871).sum := by decide
  have hdescent : baseEnd_7390871 < baseStart_7390871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390881 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 3, 2, 3]
def baseStart_7390881 : Nat := 118140960795 + 7390881 * 2 ^ 59
def prefixEnd_7390881 : Nat := 4983230072969 + 3 ^ 40 * 7390881 * 2
def baseEnd_7390881 : Nat := 3795074413182802877797463

theorem tailTrace_7390881 : CollatzResearch.WordTrace tailWord_7390881 prefixEnd_7390881 3795074413182802877797463 := by
  unfold tailWord_7390881
  simp only [CollatzResearch.WordTrace]
  refine ⟨269567575937107873826100497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179711717291405249217400331 269567575937107873826100497)
  ·
    refine ⟨202175681952830905369575373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269567575937107873826100497 202175681952830905369575373)
    ·
      refine ⟨75815880732311589513590765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202175681952830905369575373 75815880732311589513590765)
      ·
        refine ⟨28430955274616846067596537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75815880732311589513590765 28430955274616846067596537)
        ·
          refine ⟨21323216455962634550697403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28430955274616846067596537 21323216455962634550697403)
          ·
            refine ⟨31984824683943951826046105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21323216455962634550697403 31984824683943951826046105)
            ·
              refine ⟨23988618512957963869534579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31984824683943951826046105 23988618512957963869534579)
              ·
                refine ⟨35982927769436945804301869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23988618512957963869534579 35982927769436945804301869)
                ·
                  refine ⟨13493597913538854676613201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35982927769436945804301869 13493597913538854676613201)
                  ·
                    refine ⟨10120198435154141007459901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13493597913538854676613201 10120198435154141007459901)
                    ·
                      refine ⟨3795074413182802877797463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10120198435154141007459901 3795074413182802877797463)
                      ·
                        rfl

theorem cell23_7390881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_7390881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390881 prefixEnd_7390881 := by exact prefixLift 7390881
  have htrace : WordTrace (prefixWord ++ tailWord_7390881) baseStart_7390881 baseEnd_7390881 := by
    simpa [prefixWord, tailWord_7390881, baseEnd_7390881] using wordTrace_append hprefix tailTrace_7390881
  have hstable : (prefixWord ++ tailWord_7390881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390881).length < 2 ^ (prefixWord ++ tailWord_7390881).sum := by decide
  have hdescent : baseEnd_7390881 < baseStart_7390881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390882 : List Nat := [3, 3, 1, 4, 1, 2, 1, 1, 2, 3, 2]
def baseStart_7390882 : Nat := 118140960795 + 7390882 * 2 ^ 59
def prefixEnd_7390882 : Nat := 4983230072969 + 3 ^ 40 * 7390882 * 2
def baseEnd_7390882 : Nat := 3795074926663457373884959

theorem tailTrace_7390882 : CollatzResearch.WordTrace tailWord_7390882 prefixEnd_7390882 3795074926663457373884959 := by
  unfold tailWord_7390882
  simp only [CollatzResearch.WordTrace]
  refine ⟨67391903102526062749221725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179711741606736167331257933 67391903102526062749221725)
  ·
    refine ⟨25271963663447273530958147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67391903102526062749221725 25271963663447273530958147)
    ·
      refine ⟨37907945495170910296437221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25271963663447273530958147 37907945495170910296437221)
      ·
        refine ⟨7107739780344545680581979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37907945495170910296437221 7107739780344545680581979)
        ·
          refine ⟨10661609670516818520872969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7107739780344545680581979 10661609670516818520872969)
          ·
            refine ⟨7996207252887613890654727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10661609670516818520872969 7996207252887613890654727)
            ·
              refine ⟨11994310879331420835982091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7996207252887613890654727 11994310879331420835982091)
              ·
                refine ⟨17991466318997131253973137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11994310879331420835982091 17991466318997131253973137)
                ·
                  refine ⟨13493599739247848440479853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17991466318997131253973137 13493599739247848440479853)
                  ·
                    refine ⟨5060099902217943165179945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13493599739247848440479853 5060099902217943165179945)
                    ·
                      refine ⟨3795074926663457373884959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5060099902217943165179945 3795074926663457373884959)
                      ·
                        rfl

theorem cell23_7390882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_7390882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390882 prefixEnd_7390882 := by exact prefixLift 7390882
  have htrace : WordTrace (prefixWord ++ tailWord_7390882) baseStart_7390882 baseEnd_7390882 := by
    simpa [prefixWord, tailWord_7390882, baseEnd_7390882] using wordTrace_append hprefix tailTrace_7390882
  have hstable : (prefixWord ++ tailWord_7390882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390882).length < 2 ^ (prefixWord ++ tailWord_7390882).sum := by decide
  have hdescent : baseEnd_7390882 < baseStart_7390882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390895 : List Nat := [1, 1, 2, 1, 2, 4, 4, 3, 1, 2, 2]
def baseStart_7390895 : Nat := 118140960795 + 7390895 * 2 ^ 59
def prefixEnd_7390895 : Nat := 4983230072969 + 3 ^ 40 * 7390895 * 2
def baseEnd_7390895 : Nat := 3795081601911965823022399

theorem tailTrace_7390895 : CollatzResearch.WordTrace tailWord_7390895 prefixEnd_7390895 3795081601911965823022399 := by
  unfold tailWord_7390895
  simp only [CollatzResearch.WordTrace]
  refine ⟨269568086559057154217110139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179712057706038102811406759 269568086559057154217110139)
  ·
    refine ⟨404352129838585731325665209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269568086559057154217110139 404352129838585731325665209)
    ·
      refine ⟨303264097378939298494248907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404352129838585731325665209 303264097378939298494248907)
      ·
        refine ⟨454896146068408947741373361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303264097378939298494248907 454896146068408947741373361)
        ·
          refine ⟨341172109551306710806030021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454896146068408947741373361 341172109551306710806030021)
          ·
            refine ⟨63969770540870008276130629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 341172109551306710806030021 63969770540870008276130629)
            ·
              refine ⟨11994331976413126551774493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63969770540870008276130629 11994331976413126551774493)
              ·
                refine ⟨4497874491154922456915435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11994331976413126551774493 4497874491154922456915435)
                ·
                  refine ⟨6746811736732383685373153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4497874491154922456915435 6746811736732383685373153)
                  ·
                    refine ⟨5060108802549287764029865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6746811736732383685373153 5060108802549287764029865)
                    ·
                      refine ⟨3795081601911965823022399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5060108802549287764029865 3795081601911965823022399)
                      ·
                        rfl

theorem cell23_7390895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 1, 2, 2].length) (baseStart_7390895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390895 prefixEnd_7390895 := by exact prefixLift 7390895
  have htrace : WordTrace (prefixWord ++ tailWord_7390895) baseStart_7390895 baseEnd_7390895 := by
    simpa [prefixWord, tailWord_7390895, baseEnd_7390895] using wordTrace_append hprefix tailTrace_7390895
  have hstable : (prefixWord ++ tailWord_7390895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390895).length < 2 ^ (prefixWord ++ tailWord_7390895).sum := by decide
  have hdescent : baseEnd_7390895 < baseStart_7390895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390898 : List Nat := [3, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3]
def baseStart_7390898 : Nat := 118140960795 + 7390898 * 2 ^ 59
def prefixEnd_7390898 : Nat := 4983230072969 + 3 ^ 40 * 7390898 * 2
def baseEnd_7390898 : Nat := 3795083142353929311284885

theorem tailTrace_7390898 : CollatzResearch.WordTrace tailWord_7390898 prefixEnd_7390898 3795083142353929311284885 := by
  unfold tailWord_7390898
  simp only [CollatzResearch.WordTrace]
  refine ⟨67392048994511571432367337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179712130652030857152979565 67392048994511571432367337)
  ·
    refine ⟨50544036745883678574275503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67392048994511571432367337 50544036745883678574275503)
    ·
      refine ⟨75816055118825517861413255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50544036745883678574275503 75816055118825517861413255)
      ·
        refine ⟨113724082678238276792119883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75816055118825517861413255 113724082678238276792119883)
        ·
          refine ⟨170586124017357415188179825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113724082678238276792119883 170586124017357415188179825)
          ·
            refine ⟨127939593013018061391134869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170586124017357415188179825 127939593013018061391134869)
            ·
              refine ⟨5997168422485221627709447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127939593013018061391134869 5997168422485221627709447)
              ·
                refine ⟨8995752633727832441564171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5997168422485221627709447 8995752633727832441564171)
                ·
                  refine ⟨13493628950591748662346257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8995752633727832441564171 13493628950591748662346257)
                  ·
                    refine ⟨10120221712943811496759693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13493628950591748662346257 10120221712943811496759693)
                    ·
                      refine ⟨3795083142353929311284885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10120221712943811496759693 3795083142353929311284885)
                      ·
                        rfl

theorem cell23_7390898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_7390898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390898 prefixEnd_7390898 := by exact prefixLift 7390898
  have htrace : WordTrace (prefixWord ++ tailWord_7390898) baseStart_7390898 baseEnd_7390898 := by
    simpa [prefixWord, tailWord_7390898, baseEnd_7390898] using wordTrace_append hprefix tailTrace_7390898
  have hstable : (prefixWord ++ tailWord_7390898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390898).length < 2 ^ (prefixWord ++ tailWord_7390898).sum := by decide
  have hdescent : baseEnd_7390898 < baseStart_7390898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390911 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 4, 1, 3]
def baseStart_7390911 : Nat := 118140960795 + 7390911 * 2 ^ 59
def prefixEnd_7390911 : Nat := 4983230072969 + 3 ^ 40 * 7390911 * 2
def baseEnd_7390911 : Nat := 3795089817602437760422325

theorem tailTrace_7390911 : CollatzResearch.WordTrace tailWord_7390911 prefixEnd_7390911 3795089817602437760422325 := by
  unfold tailWord_7390911
  simp only [CollatzResearch.WordTrace]
  refine ⟨269568670126999188949692587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179712446751332792633128391 269568670126999188949692587)
  ·
    refine ⟨404353005190498783424538881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269568670126999188949692587 404353005190498783424538881)
    ·
      refine ⟨303264753892874087568404161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404353005190498783424538881 303264753892874087568404161)
      ·
        refine ⟨227448565419655565676303121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303264753892874087568404161 227448565419655565676303121)
        ·
          refine ⟨170586424064741674257227341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227448565419655565676303121 170586424064741674257227341)
          ·
            refine ⟨63969909024278127846460253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170586424064741674257227341 63969909024278127846460253)
            ·
              refine ⟨23988715884104297942422595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63969909024278127846460253 23988715884104297942422595)
              ·
                refine ⟨35983073826156446913633893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23988715884104297942422595 35983073826156446913633893)
                ·
                  refine ⟨6746826342404333796306355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35983073826156446913633893 6746826342404333796306355)
                  ·
                    refine ⟨10120239513606500694459533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6746826342404333796306355 10120239513606500694459533)
                    ·
                      refine ⟨3795089817602437760422325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10120239513606500694459533 3795089817602437760422325)
                      ·
                        rfl

theorem cell23_7390911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 1, 3].length) (baseStart_7390911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390911 prefixEnd_7390911 := by exact prefixLift 7390911
  have htrace : WordTrace (prefixWord ++ tailWord_7390911) baseStart_7390911 baseEnd_7390911 := by
    simpa [prefixWord, tailWord_7390911, baseEnd_7390911] using wordTrace_append hprefix tailTrace_7390911
  have hstable : (prefixWord ++ tailWord_7390911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390911).length < 2 ^ (prefixWord ++ tailWord_7390911).sum := by decide
  have hdescent : baseEnd_7390911 < baseStart_7390911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390925 : List Nat := [1, 6, 2, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_7390925 : Nat := 118140960795 + 7390925 * 2 ^ 59
def prefixEnd_7390925 : Nat := 4983230072969 + 3 ^ 40 * 7390925 * 2
def baseEnd_7390925 : Nat := 3795097006331600705647261

theorem tailTrace_7390925 : CollatzResearch.WordTrace tailWord_7390925 prefixEnd_7390925 3795097006331600705647261 := by
  unfold tailWord_7390925
  simp only [CollatzResearch.WordTrace]
  refine ⟨269569180748948469340702229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179712787165965646227134819 269569180748948469340702229)
  ·
    refine ⟨12636055347606959500345417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 269569180748948469340702229 12636055347606959500345417)
    ·
      refine ⟨9477041510705219625259063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12636055347606959500345417 9477041510705219625259063)
      ·
        refine ⟨14215562266057829437888595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9477041510705219625259063 14215562266057829437888595)
        ·
          refine ⟨21323343399086744156832893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14215562266057829437888595 21323343399086744156832893)
          ·
            refine ⟨7996253774657529058812335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21323343399086744156832893 7996253774657529058812335)
            ·
              refine ⟨11994380661986293588218503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7996253774657529058812335 11994380661986293588218503)
              ·
                refine ⟨17991570992979440382327755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11994380661986293588218503 17991570992979440382327755)
                ·
                  refine ⟨26987356489469160573491633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17991570992979440382327755 26987356489469160573491633)
                  ·
                    refine ⟨20240517367101870430118725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26987356489469160573491633 20240517367101870430118725)
                    ·
                      refine ⟨3795097006331600705647261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20240517367101870430118725 3795097006331600705647261)
                      ·
                        rfl

theorem cell23_7390925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_7390925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390925 prefixEnd_7390925 := by exact prefixLift 7390925
  have htrace : WordTrace (prefixWord ++ tailWord_7390925) baseStart_7390925 baseEnd_7390925 := by
    simpa [prefixWord, tailWord_7390925, baseEnd_7390925] using wordTrace_append hprefix tailTrace_7390925
  have hstable : (prefixWord ++ tailWord_7390925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390925).length < 2 ^ (prefixWord ++ tailWord_7390925).sum := by decide
  have hdescent : baseEnd_7390925 < baseStart_7390925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390938 : List Nat := [3, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2]
def baseStart_7390938 : Nat := 118140960795 + 7390938 * 2 ^ 59
def prefixEnd_7390938 : Nat := 4983230072969 + 3 ^ 40 * 7390938 * 2
def baseEnd_7390938 : Nat := 3795103681580109154784701

theorem tailTrace_7390938 : CollatzResearch.WordTrace tailWord_7390938 prefixEnd_7390938 3795103681580109154784701 := by
  unfold tailWord_7390938
  simp only [CollatzResearch.WordTrace]
  refine ⟨67392413724475343140231367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179713103265267581707283645 67392413724475343140231367)
  ·
    refine ⟨101088620586713014710347051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67392413724475343140231367 101088620586713014710347051)
    ·
      refine ⟨151632930880069522065520577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101088620586713014710347051 151632930880069522065520577)
      ·
        refine ⟨113724698160052141549140433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151632930880069522065520577 113724698160052141549140433)
        ·
          refine ⟨85293523620039106161855325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113724698160052141549140433 85293523620039106161855325)
          ·
            refine ⟨31985071357514664810695747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85293523620039106161855325 31985071357514664810695747)
            ·
              refine ⟨47977607036271997216043621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31985071357514664810695747 47977607036271997216043621)
              ·
                refine ⟨8995801319300999478008179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47977607036271997216043621 8995801319300999478008179)
                ·
                  refine ⟨13493701978951499217012269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8995801319300999478008179 13493701978951499217012269)
                  ·
                    refine ⟨5060138242106812206379601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13493701978951499217012269 5060138242106812206379601)
                    ·
                      refine ⟨3795103681580109154784701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5060138242106812206379601 3795103681580109154784701)
                      ·
                        rfl

theorem cell23_7390938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_7390938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390938 prefixEnd_7390938 := by exact prefixLift 7390938
  have htrace : WordTrace (prefixWord ++ tailWord_7390938) baseStart_7390938 baseEnd_7390938 := by
    simpa [prefixWord, tailWord_7390938, baseEnd_7390938] using wordTrace_append hprefix tailTrace_7390938
  have hstable : (prefixWord ++ tailWord_7390938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390938).length < 2 ^ (prefixWord ++ tailWord_7390938).sum := by decide
  have hdescent : baseEnd_7390938 < baseStart_7390938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7390954 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_7390954 : Nat := 118140960795 + 7390954 * 2 ^ 59
def prefixEnd_7390954 : Nat := 4983230072969 + 3 ^ 40 * 7390954 * 2
def baseEnd_7390954 : Nat := 3795111897270581092184627

theorem tailTrace_7390954 : CollatzResearch.WordTrace tailWord_7390954 prefixEnd_7390954 3795111897270581092184627 := by
  unfold tailWord_7390954
  simp only [CollatzResearch.WordTrace]
  refine ⟨67392559616460851823376979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179713492310562271529005277 67392559616460851823376979)
  ·
    refine ⟨101088839424691277735065469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67392559616460851823376979 101088839424691277735065469)
    ·
      refine ⟨37908314784259229150649551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101088839424691277735065469 37908314784259229150649551)
      ·
        refine ⟨56862472176388843725974327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37908314784259229150649551 56862472176388843725974327)
        ·
          refine ⟨85293708264583265588961491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56862472176388843725974327 85293708264583265588961491)
          ·
            refine ⟨127940562396874898383442237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85293708264583265588961491 127940562396874898383442237)
            ·
              refine ⟨47977710898828086893790839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127940562396874898383442237 47977710898828086893790839)
              ·
                refine ⟨71966566348242130340686259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47977710898828086893790839 71966566348242130340686259)
                ·
                  refine ⟨107949849522363195511029389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71966566348242130340686259 107949849522363195511029389)
                  ·
                    refine ⟨40481193570886198316636021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107949849522363195511029389 40481193570886198316636021)
                    ·
                      refine ⟨3795111897270581092184627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40481193570886198316636021 3795111897270581092184627)
                      ·
                        rfl

theorem cell23_7390954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_7390954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7390954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7390954 prefixEnd_7390954 := by exact prefixLift 7390954
  have htrace : WordTrace (prefixWord ++ tailWord_7390954) baseStart_7390954 baseEnd_7390954 := by
    simpa [prefixWord, tailWord_7390954, baseEnd_7390954] using wordTrace_append hprefix tailTrace_7390954
  have hstable : (prefixWord ++ tailWord_7390954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7390954).length < 2 ^ (prefixWord ++ tailWord_7390954).sum := by decide
  have hdescent : baseEnd_7390954 < baseStart_7390954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7390954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391006 : List Nat := [4, 3, 2, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_7391006 : Nat := 118140960795 + 7391006 * 2 ^ 59
def prefixEnd_7391006 : Nat := 4983230072969 + 3 ^ 40 * 7391006 * 2
def baseEnd_7391006 : Nat := 3795138598264614888734389

theorem tailTrace_7391006 : CollatzResearch.WordTrace tailWord_7391006 prefixEnd_7391006 3795138598264614888734389 := by
  unfold tailWord_7391006
  simp only [CollatzResearch.WordTrace]
  refine ⟨33696516882706877521800109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179714756707770013449600581 33696516882706877521800109)
  ·
    refine ⟨12636193831015079070675041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33696516882706877521800109 12636193831015079070675041)
    ·
      refine ⟨9477145373261309303006281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12636193831015079070675041 9477145373261309303006281)
      ·
        refine ⟨7107859029945981977254711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9477145373261309303006281 7107859029945981977254711)
        ·
          refine ⟨10661788544918972965882067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7107859029945981977254711 10661788544918972965882067)
          ·
            refine ⟨15992682817378459448823101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10661788544918972965882067 15992682817378459448823101)
            ·
              refine ⟨5997256056516922293308663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15992682817378459448823101 5997256056516922293308663)
              ·
                refine ⟨8995884084775383439962995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5997256056516922293308663 8995884084775383439962995)
                ·
                  refine ⟨13493826127163075159944493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8995884084775383439962995 13493826127163075159944493)
                  ·
                    refine ⟨5060184797686153184979185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13493826127163075159944493 5060184797686153184979185)
                    ·
                      refine ⟨3795138598264614888734389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5060184797686153184979185 3795138598264614888734389)
                      ·
                        rfl

theorem cell23_7391006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_7391006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391006 prefixEnd_7391006 := by exact prefixLift 7391006
  have htrace : WordTrace (prefixWord ++ tailWord_7391006) baseStart_7391006 baseEnd_7391006 := by
    simpa [prefixWord, tailWord_7391006, baseEnd_7391006] using wordTrace_append hprefix tailTrace_7391006
  have hstable : (prefixWord ++ tailWord_7391006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391006).length < 2 ^ (prefixWord ++ tailWord_7391006).sum := by decide
  have hdescent : baseEnd_7391006 < baseStart_7391006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391024 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 4]
def baseStart_7391024 : Nat := 118140960795 + 7391024 * 2 ^ 59
def prefixEnd_7391024 : Nat := 4983230072969 + 3 ^ 40 * 7391024 * 2
def baseEnd_7391024 : Nat := 3795147840916395818309305

theorem tailTrace_7391024 : CollatzResearch.WordTrace tailWord_7391024 prefixEnd_7391024 3795147840916395818309305 := by
  unfold tailWord_7391024
  simp only [CollatzResearch.WordTrace]
  refine ⟨134786395787794904624278063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179715194383726539499037417 134786395787794904624278063)
  ·
    refine ⟨202179593681692356936417095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134786395787794904624278063 202179593681692356936417095)
    ·
      refine ⟨303269390522538535404625643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202179593681692356936417095 303269390522538535404625643)
      ·
        refine ⟨454904085783807803106938465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303269390522538535404625643 454904085783807803106938465)
        ·
          refine ⟨341178064337855852330203849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454904085783807803106938465 341178064337855852330203849)
          ·
            refine ⟨255883548253391889247652887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341178064337855852330203849 255883548253391889247652887)
            ·
              refine ⟨383825322380087833871479331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255883548253391889247652887 383825322380087833871479331)
              ·
                refine ⟨575737983570131750807218997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383825322380087833871479331 575737983570131750807218997)
                ·
                  refine ⟨53975435959699851638176781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 575737983570131750807218997 53975435959699851638176781)
                  ·
                    refine ⟨20240788484887444364316293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53975435959699851638176781 20240788484887444364316293)
                    ·
                      refine ⟨3795147840916395818309305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20240788484887444364316293 3795147840916395818309305)
                      ·
                        rfl

theorem cell23_7391024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_7391024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391024 prefixEnd_7391024 := by exact prefixLift 7391024
  have htrace : WordTrace (prefixWord ++ tailWord_7391024) baseStart_7391024 baseEnd_7391024 := by
    simpa [prefixWord, tailWord_7391024, baseEnd_7391024] using wordTrace_append hprefix tailTrace_7391024
  have hstable : (prefixWord ++ tailWord_7391024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391024).length < 2 ^ (prefixWord ++ tailWord_7391024).sum := by decide
  have hdescent : baseEnd_7391024 < baseStart_7391024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391025 : List Nat := [1, 2, 2, 3, 2, 4, 2, 2, 5]
def baseStart_7391025 : Nat := 118140960795 + 7391025 * 2 ^ 59
def prefixEnd_7391025 : Nat := 4983230072969 + 3 ^ 40 * 7391025 * 2
def baseEnd_7391025 : Nat := 421683150488561146044089

theorem tailTrace_7391025 : CollatzResearch.WordTrace tailWord_7391025 prefixEnd_7391025 421683150488561146044089 := by
  unfold tailWord_7391025
  simp only [CollatzResearch.WordTrace]
  refine ⟨269572828048586186419342529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179715218699057457612895019 269572828048586186419342529)
  ·
    refine ⟨202179621036439639814506897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269572828048586186419342529 202179621036439639814506897)
    ·
      refine ⟨151634715777329729860880173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202179621036439639814506897 151634715777329729860880173)
      ·
        refine ⟨56863018416498648697830065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151634715777329729860880173 56863018416498648697830065)
        ·
          refine ⟨42647263812373986523372549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56863018416498648697830065 42647263812373986523372549)
          ·
            refine ⟨7996361964820122473132353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42647263812373986523372549 7996361964820122473132353)
            ·
              refine ⟨5997271473615091854849265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7996361964820122473132353 5997271473615091854849265)
              ·
                refine ⟨4497953605211318891136949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5997271473615091854849265 4497953605211318891136949)
                ·
                  refine ⟨421683150488561146044089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4497953605211318891136949 421683150488561146044089)
                  ·
                    rfl

theorem cell23_7391025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 5].length) (baseStart_7391025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391025 prefixEnd_7391025 := by exact prefixLift 7391025
  have htrace : WordTrace (prefixWord ++ tailWord_7391025) baseStart_7391025 baseEnd_7391025 := by
    simpa [prefixWord, tailWord_7391025, baseEnd_7391025] using wordTrace_append hprefix tailTrace_7391025
  have hstable : (prefixWord ++ tailWord_7391025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391025).length < 2 ^ (prefixWord ++ tailWord_7391025).sum := by decide
  have hdescent : baseEnd_7391025 < baseStart_7391025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391058 : List Nat := [3, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_7391058 : Nat := 118140960795 + 7391058 * 2 ^ 59
def prefixEnd_7391058 : Nat := 4983230072969 + 3 ^ 40 * 7391058 * 2
def baseEnd_7391058 : Nat := 3795165299258648685284149

theorem tailTrace_7391058 : CollatzResearch.WordTrace tailWord_7391058 prefixEnd_7391058 3795165299258648685284149 := by
  unfold tailWord_7391058
  simp only [CollatzResearch.WordTrace]
  refine ⟨67393507914366658263823457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179716021104977755370195885 67393507914366658263823457)
  ·
    refine ⟨50545130935774993697867593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67393507914366658263823457 50545130935774993697867593)
    ·
      refine ⟨37908848201831245273400695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50545130935774993697867593 37908848201831245273400695)
      ·
        refine ⟨56863272302746867910101043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37908848201831245273400695 56863272302746867910101043)
        ·
          refine ⟨85294908454120301865151565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56863272302746867910101043 85294908454120301865151565)
          ·
            refine ⟨31985590670295113199431837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85294908454120301865151565 31985590670295113199431837)
            ·
              refine ⟨11994596501360667449786939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31985590670295113199431837 11994596501360667449786939)
              ·
                refine ⟨17991894752041001174680409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11994596501360667449786939 17991894752041001174680409)
                ·
                  refine ⟨13493921064030750881010307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17991894752041001174680409 13493921064030750881010307)
                  ·
                    refine ⟨20240881596046126321515461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13493921064030750881010307 20240881596046126321515461)
                    ·
                      refine ⟨3795165299258648685284149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20240881596046126321515461 3795165299258648685284149)
                      ·
                        rfl

theorem cell23_7391058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_7391058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391058 prefixEnd_7391058 := by exact prefixLift 7391058
  have htrace : WordTrace (prefixWord ++ tailWord_7391058) baseStart_7391058 baseEnd_7391058 := by
    simpa [prefixWord, tailWord_7391058, baseEnd_7391058] using wordTrace_append hprefix tailTrace_7391058
  have hstable : (prefixWord ++ tailWord_7391058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391058).length < 2 ^ (prefixWord ++ tailWord_7391058).sum := by decide
  have hdescent : baseEnd_7391058 < baseStart_7391058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391085 : List Nat := [1, 5, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_7391085 : Nat := 118140960795 + 7391085 * 2 ^ 59
def prefixEnd_7391085 : Nat := 4983230072969 + 3 ^ 40 * 7391085 * 2
def baseEnd_7391085 : Nat := 1265059721078773359882175

theorem tailTrace_7391085 : CollatzResearch.WordTrace tailWord_7391085 prefixEnd_7391085 1265059721078773359882175 := by
  unfold tailWord_7391085
  simp only [CollatzResearch.WordTrace]
  refine ⟨269575016428368816666526709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179716677618912544444351139 269575016428368816666526709)
  ·
    refine ⟨25272657790159576562486879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 269575016428368816666526709 25272657790159576562486879)
    ·
      refine ⟨37908986685239364843730319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25272657790159576562486879 37908986685239364843730319)
      ·
        refine ⟨56863480027859047265595479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37908986685239364843730319 56863480027859047265595479)
        ·
          refine ⟨85295220041788570898393219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56863480027859047265595479 85295220041788570898393219)
          ·
            refine ⟨127942830062682856347589829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85295220041788570898393219 127942830062682856347589829)
            ·
              refine ⟨23989280636753035565173093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127942830062682856347589829 23989280636753035565173093)
              ·
                refine ⟨4497990119391194168469955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23989280636753035565173093 4497990119391194168469955)
                ·
                  refine ⟨6746985179086791252704933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4497990119391194168469955 6746985179086791252704933)
                  ·
                    refine ⟨1265059721078773359882175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6746985179086791252704933 1265059721078773359882175)
                    ·
                      rfl

theorem cell23_7391085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_7391085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391085 prefixEnd_7391085 := by exact prefixLift 7391085
  have htrace : WordTrace (prefixWord ++ tailWord_7391085) baseStart_7391085 baseEnd_7391085 := by
    simpa [prefixWord, tailWord_7391085, baseEnd_7391085] using wordTrace_append hprefix tailTrace_7391085
  have hstable : (prefixWord ++ tailWord_7391085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391085).length < 2 ^ (prefixWord ++ tailWord_7391085).sum := by decide
  have hdescent : baseEnd_7391085 < baseStart_7391085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391151 : List Nat := [1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 5]
def baseStart_7391151 : Nat := 118140960795 + 7391151 * 2 ^ 59
def prefixEnd_7391151 : Nat := 4983230072969 + 3 ^ 40 * 7391151 * 2
def baseEnd_7391151 : Nat := 3795213052959516821421221

theorem tailTrace_7391151 : CollatzResearch.WordTrace tailWord_7391151 prefixEnd_7391151 3795213052959516821421221 := by
  unfold tailWord_7391151
  simp only [CollatzResearch.WordTrace]
  refine ⟨269577423646129709938429307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179718282430753139958952871 269577423646129709938429307)
  ·
    refine ⟨404366135469194564907643961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269577423646129709938429307 404366135469194564907643961)
    ·
      refine ⟨303274601601895923680732971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404366135469194564907643961 303274601601895923680732971)
      ·
        refine ⟨454911902402843885521099457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303274601601895923680732971 454911902402843885521099457)
        ·
          refine ⟨341183926802132914140824593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454911902402843885521099457 341183926802132914140824593)
          ·
            refine ⟨255887945101599685605618445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341183926802132914140824593 255887945101599685605618445)
            ·
              refine ⟨95957979413099882102106917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255887945101599685605618445 95957979413099882102106917)
              ·
                refine ⟨17992121139956227894145047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95957979413099882102106917 17992121139956227894145047)
                ·
                  refine ⟨26988181709934341841217571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17992121139956227894145047 26988181709934341841217571)
                  ·
                    refine ⟨40482272564901512761826357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26988181709934341841217571 40482272564901512761826357)
                    ·
                      refine ⟨3795213052959516821421221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40482272564901512761826357 3795213052959516821421221)
                      ·
                        rfl

theorem cell23_7391151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 5].length) (baseStart_7391151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391151 prefixEnd_7391151 := by exact prefixLift 7391151
  have htrace : WordTrace (prefixWord ++ tailWord_7391151) baseStart_7391151 baseEnd_7391151 := by
    simpa [prefixWord, tailWord_7391151, baseEnd_7391151] using wordTrace_append hprefix tailTrace_7391151
  have hstable : (prefixWord ++ tailWord_7391151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391151).length < 2 ^ (prefixWord ++ tailWord_7391151).sum := by decide
  have hdescent : baseEnd_7391151 < baseStart_7391151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391161 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 1, 1, 6]
def baseStart_7391161 : Nat := 118140960795 + 7391161 * 2 ^ 59
def prefixEnd_7391161 : Nat := 4983230072969 + 3 ^ 40 * 7391161 * 2
def baseEnd_7391161 : Nat := 3795218187766061782296175

theorem tailTrace_7391161 : CollatzResearch.WordTrace tailWord_7391161 prefixEnd_7391161 3795218187766061782296175 := by
  unfold tailWord_7391161
  simp only [CollatzResearch.WordTrace]
  refine ⟨269577788376093481646293337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179718525584062321097528891 269577788376093481646293337)
  ·
    refine ⟨202183341282070111234720003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269577788376093481646293337 202183341282070111234720003)
    ·
      refine ⟨303275011923105166852080005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202183341282070111234720003 303275011923105166852080005)
      ·
        refine ⟨56864064735582218784765001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303275011923105166852080005 56864064735582218784765001)
        ·
          refine ⟨42648048551686664088573751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56864064735582218784765001 42648048551686664088573751)
          ·
            refine ⟨63972072827529996132860627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42648048551686664088573751 63972072827529996132860627)
            ·
              refine ⟨95958109241294994199290941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63972072827529996132860627 95958109241294994199290941)
              ·
                refine ⟨35984290965485622824734103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95958109241294994199290941 35984290965485622824734103)
                ·
                  refine ⟨53976436448228434237101155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35984290965485622824734103 53976436448228434237101155)
                  ·
                    refine ⟨80964654672342651355651733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53976436448228434237101155 80964654672342651355651733)
                    ·
                      refine ⟨3795218187766061782296175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80964654672342651355651733 3795218187766061782296175)
                      ·
                        rfl

theorem cell23_7391161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_7391161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391161 prefixEnd_7391161 := by exact prefixLift 7391161
  have htrace : WordTrace (prefixWord ++ tailWord_7391161) baseStart_7391161 baseEnd_7391161 := by
    simpa [prefixWord, tailWord_7391161, baseEnd_7391161] using wordTrace_append hprefix tailTrace_7391161
  have hstable : (prefixWord ++ tailWord_7391161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391161).length < 2 ^ (prefixWord ++ tailWord_7391161).sum := by decide
  have hdescent : baseEnd_7391161 < baseStart_7391161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391165 : List Nat := [1, 4, 1, 2, 3, 1, 3, 2, 1, 1, 4]
def baseStart_7391165 : Nat := 118140960795 + 7391165 * 2 ^ 59
def prefixEnd_7391165 : Nat := 4983230072969 + 3 ^ 40 * 7391165 * 2
def baseEnd_7391165 : Nat := 3795220241688679766646157

theorem tailTrace_7391165 : CollatzResearch.WordTrace tailWord_7391165 prefixEnd_7391165 3795220241688679766646157 := by
  unfold tailWord_7391165
  simp only [CollatzResearch.WordTrace]
  refine ⟨269577934268078990329438949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179718622845385993552959299 269577934268078990329438949)
  ·
    refine ⟨50545862675264810686769803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269577934268078990329438949 50545862675264810686769803)
    ·
      refine ⟨75818794012897216030154705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50545862675264810686769803 75818794012897216030154705)
      ·
        refine ⟨56864095509672912022616029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75818794012897216030154705 56864095509672912022616029)
        ·
          refine ⟨21324035816127342008481011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56864095509672912022616029 21324035816127342008481011)
          ·
            refine ⟨31986053724191013012721517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21324035816127342008481011 31986053724191013012721517)
            ·
              refine ⟨11994770146571629879770569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31986053724191013012721517 11994770146571629879770569)
              ·
                refine ⟨8996077609928722409827927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11994770146571629879770569 8996077609928722409827927)
                ·
                  refine ⟨13494116414893083614741891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8996077609928722409827927 13494116414893083614741891)
                  ·
                    refine ⟨20241174622339625422112837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13494116414893083614741891 20241174622339625422112837)
                    ·
                      refine ⟨3795220241688679766646157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20241174622339625422112837 3795220241688679766646157)
                      ·
                        rfl

theorem cell23_7391165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_7391165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391165 prefixEnd_7391165 := by exact prefixLift 7391165
  have htrace : WordTrace (prefixWord ++ tailWord_7391165) baseStart_7391165 baseEnd_7391165 := by
    simpa [prefixWord, tailWord_7391165, baseEnd_7391165] using wordTrace_append hprefix tailTrace_7391165
  have hstable : (prefixWord ++ tailWord_7391165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391165).length < 2 ^ (prefixWord ++ tailWord_7391165).sum := by decide
  have hdescent : baseEnd_7391165 < baseStart_7391165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391168 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 3]
def baseStart_7391168 : Nat := 118140960795 + 7391168 * 2 ^ 59
def prefixEnd_7391168 : Nat := 4983230072969 + 3 ^ 40 * 7391168 * 2
def baseEnd_7391168 : Nat := 3795221782130643254908643

theorem tailTrace_7391168 : CollatzResearch.WordTrace tailWord_7391168 prefixEnd_7391168 3795221782130643254908643 := by
  unfold tailWord_7391168
  simp only [CollatzResearch.WordTrace]
  refine ⟨134789021843534060920899079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179718695791378747894532105 134789021843534060920899079)
  ·
    refine ⟨202183532765301091381348619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134789021843534060920899079 202183532765301091381348619)
    ·
      refine ⟨303275299147951637072022929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202183532765301091381348619 303275299147951637072022929)
      ·
        refine ⟨227456474360963727804017197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303275299147951637072022929 227456474360963727804017197)
        ·
          refine ⟨85296177885361397926506449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227456474360963727804017197 85296177885361397926506449)
          ·
            refine ⟨63972133414021048444879837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85296177885361397926506449 63972133414021048444879837)
            ·
              refine ⟨23989550030257893166829939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63972133414021048444879837 23989550030257893166829939)
              ·
                refine ⟨35984325045386839750244909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23989550030257893166829939 35984325045386839750244909)
                ·
                  refine ⟨13494121892020064906341841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35984325045386839750244909 13494121892020064906341841)
                  ·
                    refine ⟨10120591419015048679756381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13494121892020064906341841 10120591419015048679756381)
                    ·
                      refine ⟨3795221782130643254908643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10120591419015048679756381 3795221782130643254908643)
                      ·
                        rfl

theorem cell23_7391168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_7391168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391168 prefixEnd_7391168 := by exact prefixLift 7391168
  have htrace : WordTrace (prefixWord ++ tailWord_7391168) baseStart_7391168 baseEnd_7391168 := by
    simpa [prefixWord, tailWord_7391168, baseEnd_7391168] using wordTrace_append hprefix tailTrace_7391168
  have hstable : (prefixWord ++ tailWord_7391168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391168).length < 2 ^ (prefixWord ++ tailWord_7391168).sum := by decide
  have hdescent : baseEnd_7391168 < baseStart_7391168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391199 : List Nat := [1, 1, 2, 3, 4, 2, 1, 4, 1, 2, 2]
def baseStart_7391199 : Nat := 118140960795 + 7391199 * 2 ^ 59
def prefixEnd_7391199 : Nat := 4983230072969 + 3 ^ 40 * 7391199 * 2
def baseEnd_7391199 : Nat := 3795237700030932633621001

theorem tailTrace_7391199 : CollatzResearch.WordTrace tailWord_7391199 prefixEnd_7391199 3795237700030932633621001 := by
  unfold tailWord_7391199
  simp only [CollatzResearch.WordTrace]
  refine ⟨269579174349955814136176651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179719449566637209424117767 269579174349955814136176651)
  ·
    refine ⟨404368761524933721204264977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269579174349955814136176651 404368761524933721204264977)
    ·
      refine ⟨303276571143700290903198733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404368761524933721204264977 303276571143700290903198733)
      ·
        refine ⟨113728714178887609088699525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303276571143700290903198733 113728714178887609088699525)
        ·
          refine ⟨21324133908541426704131161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113728714178887609088699525 21324133908541426704131161)
          ·
            refine ⟨15993100431406070028098371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21324133908541426704131161 15993100431406070028098371)
            ·
              refine ⟨23989650647109105042147557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15993100431406070028098371 23989650647109105042147557)
              ·
                refine ⟨4498059496332957195402667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23989650647109105042147557 4498059496332957195402667)
                ·
                  refine ⟨6747089244499435793104001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4498059496332957195402667 6747089244499435793104001)
                  ·
                    refine ⟨5060316933374576844828001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6747089244499435793104001 5060316933374576844828001)
                    ·
                      refine ⟨3795237700030932633621001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5060316933374576844828001 3795237700030932633621001)
                      ·
                        rfl

theorem cell23_7391199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 1, 2, 2].length) (baseStart_7391199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391199 prefixEnd_7391199 := by exact prefixLift 7391199
  have htrace : WordTrace (prefixWord ++ tailWord_7391199) baseStart_7391199 baseEnd_7391199 := by
    simpa [prefixWord, tailWord_7391199, baseEnd_7391199] using wordTrace_append hprefix tailTrace_7391199
  have hstable : (prefixWord ++ tailWord_7391199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391199).length < 2 ^ (prefixWord ++ tailWord_7391199).sum := by decide
  have hdescent : baseEnd_7391199 < baseStart_7391199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391201 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 2, 7]
def baseStart_7391201 : Nat := 118140960795 + 7391201 * 2 ^ 59
def prefixEnd_7391201 : Nat := 4983230072969 + 3 ^ 40 * 7391201 * 2
def baseEnd_7391201 : Nat := 1265079575664080541931997

theorem tailTrace_7391201 : CollatzResearch.WordTrace tailWord_7391201 prefixEnd_7391201 1265079575664080541931997 := by
  unfold tailWord_7391201
  simp only [CollatzResearch.WordTrace]
  refine ⟨269579247295948568477749457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179719498197299045651832971 269579247295948568477749457)
  ·
    refine ⟨202184435471961426358312093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269579247295948568477749457 202184435471961426358312093)
    ·
      refine ⟨75819163301985534884367035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202184435471961426358312093 75819163301985534884367035)
      ·
        refine ⟨113728744952978302326550553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75819163301985534884367035 113728744952978302326550553)
        ·
          refine ⟨85296558714733726744912915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113728744952978302326550553 85296558714733726744912915)
          ·
            refine ⟨127944838072100590117369373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85296558714733726744912915 127944838072100590117369373)
            ·
              refine ⟨47979314277037721294013515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127944838072100590117369373 47979314277037721294013515)
              ·
                refine ⟨71968971415556581941020273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47979314277037721294013515 71968971415556581941020273)
                ·
                  refine ⟨53976728561667436455765205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71968971415556581941020273 53976728561667436455765205)
                  ·
                    refine ⟨1265079575664080541931997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53976728561667436455765205 1265079575664080541931997)
                    ·
                      rfl

theorem cell23_7391201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_7391201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391201 prefixEnd_7391201 := by exact prefixLift 7391201
  have htrace : WordTrace (prefixWord ++ tailWord_7391201) baseStart_7391201 baseEnd_7391201 := by
    simpa [prefixWord, tailWord_7391201, baseEnd_7391201] using wordTrace_append hprefix tailTrace_7391201
  have hstable : (prefixWord ++ tailWord_7391201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391201).length < 2 ^ (prefixWord ++ tailWord_7391201).sum := by decide
  have hdescent : baseEnd_7391201 < baseStart_7391201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391215 : List Nat := [1, 1, 2, 1, 4, 2, 1, 5, 2, 1, 3]
def baseStart_7391215 : Nat := 118140960795 + 7391215 * 2 ^ 59
def prefixEnd_7391215 : Nat := 4983230072969 + 3 ^ 40 * 7391215 * 2
def baseEnd_7391215 : Nat := 3795245915721404571020927

theorem tailTrace_7391215 : CollatzResearch.WordTrace tailWord_7391215 prefixEnd_7391215 3795245915721404571020927 := by
  unfold tailWord_7391215
  simp only [CollatzResearch.WordTrace]
  refine ⟨269579757917897848868759099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179719838611931899245839399 269579757917897848868759099)
  ·
    refine ⟨404369636876846773303138649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269579757917897848868759099 404369636876846773303138649)
    ·
      refine ⟨303277227657635079977353987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404369636876846773303138649 303277227657635079977353987)
      ·
        refine ⟨454915841486452619966030981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303277227657635079977353987 454915841486452619966030981)
        ·
          refine ⟨85296720278709866243630809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 454915841486452619966030981 85296720278709866243630809)
          ·
            refine ⟨63972540209032399682723107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85296720278709866243630809 63972540209032399682723107)
            ·
              refine ⟨95958810313548599524084661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63972540209032399682723107 95958810313548599524084661)
              ·
                refine ⟨8996138466895181205382937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95958810313548599524084661 8996138466895181205382937)
                ·
                  refine ⟨6747103850171385904037203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8996138466895181205382937 6747103850171385904037203)
                  ·
                    refine ⟨10120655775257078856055805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6747103850171385904037203 10120655775257078856055805)
                    ·
                      refine ⟨3795245915721404571020927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10120655775257078856055805 3795245915721404571020927)
                      ·
                        rfl

theorem cell23_7391215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 1, 3].length) (baseStart_7391215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391215 prefixEnd_7391215 := by exact prefixLift 7391215
  have htrace : WordTrace (prefixWord ++ tailWord_7391215) baseStart_7391215 baseEnd_7391215 := by
    simpa [prefixWord, tailWord_7391215, baseEnd_7391215] using wordTrace_append hprefix tailTrace_7391215
  have hstable : (prefixWord ++ tailWord_7391215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391215).length < 2 ^ (prefixWord ++ tailWord_7391215).sum := by decide
  have hdescent : baseEnd_7391215 < baseStart_7391215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391225 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 3, 3, 2]
def baseStart_7391225 : Nat := 118140960795 + 7391225 * 2 ^ 59
def prefixEnd_7391225 : Nat := 4983230072969 + 3 ^ 40 * 7391225 * 2
def baseEnd_7391225 : Nat := 3795251050527949531895881

theorem tailTrace_7391225 : CollatzResearch.WordTrace tailWord_7391225 prefixEnd_7391225 3795251050527949531895881 := by
  unfold tailWord_7391225
  simp only [CollatzResearch.WordTrace]
  refine ⟨269580122647861620576623129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179720081765241080384415419 269580122647861620576623129)
  ·
    refine ⟨202185091985896215432467347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269580122647861620576623129 202185091985896215432467347)
    ·
      refine ⟨303277637978844323148701021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202185091985896215432467347 303277637978844323148701021)
      ·
        refine ⟨113729114242066621180762883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303277637978844323148701021 113729114242066621180762883)
        ·
          refine ⟨170593671363099931771144325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113729114242066621180762883 170593671363099931771144325)
          ·
            refine ⟨31986313380581237207089561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170593671363099931771144325 31986313380581237207089561)
            ·
              refine ⟨23989735035435927905317171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31986313380581237207089561 23989735035435927905317171)
              ·
                refine ⟨35984602553153891857975757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23989735035435927905317171 35984602553153891857975757)
                ·
                  refine ⟨13494225957432709446740909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35984602553153891857975757 13494225957432709446740909)
                  ·
                    refine ⟨5060334734037266042527841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13494225957432709446740909 5060334734037266042527841)
                    ·
                      refine ⟨3795251050527949531895881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5060334734037266042527841 3795251050527949531895881)
                      ·
                        rfl

theorem cell23_7391225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_7391225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391225 prefixEnd_7391225 := by exact prefixLift 7391225
  have htrace : WordTrace (prefixWord ++ tailWord_7391225) baseStart_7391225 baseEnd_7391225 := by
    simpa [prefixWord, tailWord_7391225, baseEnd_7391225] using wordTrace_append hprefix tailTrace_7391225
  have hstable : (prefixWord ++ tailWord_7391225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391225).length < 2 ^ (prefixWord ++ tailWord_7391225).sum := by decide
  have hdescent : baseEnd_7391225 < baseStart_7391225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391236 : List Nat := [2, 3, 2, 4, 1, 2, 2, 1, 1, 2, 3]
def baseStart_7391236 : Nat := 118140960795 + 7391236 * 2 ^ 59
def prefixEnd_7391236 : Nat := 4983230072969 + 3 ^ 40 * 7391236 * 2
def baseEnd_7391236 : Nat := 3795256698815148988858331

theorem tailTrace_7391236 : CollatzResearch.WordTrace tailWord_7391236 prefixEnd_7391236 3795256698815148988858331 := by
  unfold tailWord_7391236
  simp only [CollatzResearch.WordTrace]
  refine ⟨134790261925410884727636781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179720349233881179636849041 134790261925410884727636781)
  ·
    refine ⟨50546348222029081772863793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134790261925410884727636781 50546348222029081772863793)
    ·
      refine ⟨37909761166521811329647845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50546348222029081772863793 37909761166521811329647845)
      ·
        refine ⟨7108080218722839624308971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37909761166521811329647845 7108080218722839624308971)
        ·
          refine ⟨10662120328084259436463457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7108080218722839624308971 10662120328084259436463457)
          ·
            refine ⟨7996590246063194577347593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10662120328084259436463457 7996590246063194577347593)
            ·
              refine ⟨5997442684547395933010695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7996590246063194577347593 5997442684547395933010695)
              ·
                refine ⟨8996164026821093899516043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5997442684547395933010695 8996164026821093899516043)
                ·
                  refine ⟨13494246040231640849274065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8996164026821093899516043 13494246040231640849274065)
                  ·
                    refine ⟨10120684530173730636955549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13494246040231640849274065 10120684530173730636955549)
                    ·
                      refine ⟨3795256698815148988858331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10120684530173730636955549 3795256698815148988858331)
                      ·
                        rfl

theorem cell23_7391236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_7391236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391236 prefixEnd_7391236 := by exact prefixLift 7391236
  have htrace : WordTrace (prefixWord ++ tailWord_7391236) baseStart_7391236 baseEnd_7391236 := by
    simpa [prefixWord, tailWord_7391236, baseEnd_7391236] using wordTrace_append hprefix tailTrace_7391236
  have hstable : (prefixWord ++ tailWord_7391236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391236).length < 2 ^ (prefixWord ++ tailWord_7391236).sum := by decide
  have hdescent : baseEnd_7391236 < baseStart_7391236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391295 : List Nat := [1, 1, 2, 2, 3, 1, 5, 3, 5]
def baseStart_7391295 : Nat := 118140960795 + 7391295 * 2 ^ 59
def prefixEnd_7391295 : Nat := 4983230072969 + 3 ^ 40 * 7391295 * 2
def baseEnd_7391295 : Nat := 421698554908196028668951

theorem tailTrace_7391295 : CollatzResearch.WordTrace tailWord_7391295 prefixEnd_7391295 421698554908196028668951 := by
  unfold tailWord_7391295
  simp only [CollatzResearch.WordTrace]
  refine ⟨269582675757608022531671339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179721783838405348354447559 269582675757608022531671339)
  ·
    refine ⟨404374013636412033797507009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269582675757608022531671339 404374013636412033797507009)
    ·
      refine ⟨303280510227309025348130257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404374013636412033797507009 303280510227309025348130257)
      ·
        refine ⟨227460382670481769011097693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303280510227309025348130257 227460382670481769011097693)
        ·
          refine ⟨85297643501430663379161635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227460382670481769011097693 85297643501430663379161635)
          ·
            refine ⟨127946465252145995068742453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85297643501430663379161635 127946465252145995068742453)
            ·
              refine ⟨11994981117388687037694605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127946465252145995068742453 11994981117388687037694605)
              ·
                refine ⟨4498117919020757639135477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11994981117388687037694605 4498117919020757639135477)
                ·
                  refine ⟨421698554908196028668951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4498117919020757639135477 421698554908196028668951)
                  ·
                    rfl

theorem cell23_7391295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 5].length) (baseStart_7391295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391295 prefixEnd_7391295 := by exact prefixLift 7391295
  have htrace : WordTrace (prefixWord ++ tailWord_7391295) baseStart_7391295 baseEnd_7391295 := by
    simpa [prefixWord, tailWord_7391295, baseEnd_7391295] using wordTrace_append hprefix tailTrace_7391295
  have hstable : (prefixWord ++ tailWord_7391295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391295).length < 2 ^ (prefixWord ++ tailWord_7391295).sum := by decide
  have hdescent : baseEnd_7391295 < baseStart_7391295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391308 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 4, 5]
def baseStart_7391308 : Nat := 118140960795 + 7391308 * 2 ^ 59
def prefixEnd_7391308 : Nat := 4983230072969 + 3 ^ 40 * 7391308 * 2
def baseEnd_7391308 : Nat := 1265097889807424235719333

theorem tailTrace_7391308 : CollatzResearch.WordTrace tailWord_7391308 prefixEnd_7391308 1265097889807424235719333 := by
  unfold tailWord_7391308
  simp only [CollatzResearch.WordTrace]
  refine ⟨134791574953280462875947289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179722099937707283834596385 134791574953280462875947289)
  ·
    refine ⟨101093681214960347156960467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134791574953280462875947289 101093681214960347156960467)
    ·
      refine ⟨151640521822440520735440701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101093681214960347156960467 151640521822440520735440701)
      ·
        refine ⟨56865195683415195275790263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151640521822440520735440701 56865195683415195275790263)
        ·
          refine ⟨85297793525122792913685395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56865195683415195275790263 85297793525122792913685395)
          ·
            refine ⟨127946690287684189370528093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85297793525122792913685395 127946690287684189370528093)
            ·
              refine ⟨47980008857881571013948035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127946690287684189370528093 47980008857881571013948035)
              ·
                refine ⟨71970013286822356520922053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47980008857881571013948035 71970013286822356520922053)
                ·
                  refine ⟨13494377491279191847672885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71970013286822356520922053 13494377491279191847672885)
                  ·
                    refine ⟨1265097889807424235719333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13494377491279191847672885 1265097889807424235719333)
                    ·
                      rfl

theorem cell23_7391308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_7391308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391308 prefixEnd_7391308 := by exact prefixLift 7391308
  have htrace : WordTrace (prefixWord ++ tailWord_7391308) baseStart_7391308 baseEnd_7391308 := by
    simpa [prefixWord, tailWord_7391308, baseEnd_7391308] using wordTrace_append hprefix tailTrace_7391308
  have hstable : (prefixWord ++ tailWord_7391308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391308).length < 2 ^ (prefixWord ++ tailWord_7391308).sum := by decide
  have hdescent : baseEnd_7391308 < baseStart_7391308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391345 : List Nat := [1, 2, 2, 2, 1, 1, 6, 1, 2, 1, 4]
def baseStart_7391345 : Nat := 118140960795 + 7391345 * 2 ^ 59
def prefixEnd_7391345 : Nat := 4983230072969 + 3 ^ 40 * 7391345 * 2
def baseEnd_7391345 : Nat := 3795312668206489062395329

theorem tailTrace_7391345 : CollatzResearch.WordTrace tailWord_7391345 prefixEnd_7391345 3795312668206489062395329 := by
  unfold tailWord_7391345
  simp only [CollatzResearch.WordTrace]
  refine ⟨269584499407426881070991489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179722999604951254047327659 269584499407426881070991489)
  ·
    refine ⟨202188374555570160803243617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269584499407426881070991489 202188374555570160803243617)
    ·
      refine ⟨151641280916677620602432713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202188374555570160803243617 151641280916677620602432713)
      ·
        refine ⟨113730960687508215451824535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151641280916677620602432713 113730960687508215451824535)
        ·
          refine ⟨170596441031262323177736803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113730960687508215451824535 170596441031262323177736803)
          ·
            refine ⟨255894661546893484766605205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170596441031262323177736803 255894661546893484766605205)
            ·
              refine ⟨11995062260010632098434619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 255894661546893484766605205 11995062260010632098434619)
              ·
                refine ⟨17992593390015948147651929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11995062260010632098434619 17992593390015948147651929)
                ·
                  refine ⟨13494445042511961110738947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17992593390015948147651929 13494445042511961110738947)
                  ·
                    refine ⟨20241667563767941666108421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13494445042511961110738947 20241667563767941666108421)
                    ·
                      refine ⟨3795312668206489062395329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20241667563767941666108421 3795312668206489062395329)
                      ·
                        rfl

theorem cell23_7391345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_7391345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391345 prefixEnd_7391345 := by exact prefixLift 7391345
  have htrace : WordTrace (prefixWord ++ tailWord_7391345) baseStart_7391345 baseEnd_7391345 := by
    simpa [prefixWord, tailWord_7391345, baseEnd_7391345] using wordTrace_append hprefix tailTrace_7391345
  have hstable : (prefixWord ++ tailWord_7391345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391345).length < 2 ^ (prefixWord ++ tailWord_7391345).sum := by decide
  have hdescent : baseEnd_7391345 < baseStart_7391345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391429 : List Nat := [1, 3, 1, 1, 1, 1, 6, 4, 1, 1, 3]
def baseStart_7391429 : Nat := 118140960795 + 7391429 * 2 ^ 59
def prefixEnd_7391429 : Nat := 4983230072969 + 3 ^ 40 * 7391429 * 2
def baseEnd_7391429 : Nat := 3795355800581466733744943

theorem tailTrace_7391429 : CollatzResearch.WordTrace tailWord_7391429 prefixEnd_7391429 3795355800581466733744943 := by
  unfold tailWord_7391429
  simp only [CollatzResearch.WordTrace]
  refine ⟨269587563139122563417049341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179725042092748375611366227 269587563139122563417049341)
  ·
    refine ⟨101095336177170961281393503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269587563139122563417049341 101095336177170961281393503)
    ·
      refine ⟨151643004265756441922090255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101095336177170961281393503 151643004265756441922090255)
      ·
        refine ⟨227464506398634662883135383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151643004265756441922090255 227464506398634662883135383)
        ·
          refine ⟨341196759597951994324703075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227464506398634662883135383 341196759597951994324703075)
          ·
            refine ⟨511795139396927991487054613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341196759597951994324703075 511795139396927991487054613)
            ·
              refine ⟨23990397159230999600955685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 511795139396927991487054613 23990397159230999600955685)
              ·
                refine ⟨4498199467355812425179191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23990397159230999600955685 4498199467355812425179191)
                ·
                  refine ⟨6747299201033718637768787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4498199467355812425179191 6747299201033718637768787)
                  ·
                    refine ⟨10120948801550577956653181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6747299201033718637768787 10120948801550577956653181)
                    ·
                      refine ⟨3795355800581466733744943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10120948801550577956653181 3795355800581466733744943)
                      ·
                        rfl

theorem cell23_7391429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 1, 1, 3].length) (baseStart_7391429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391429 prefixEnd_7391429 := by exact prefixLift 7391429
  have htrace : WordTrace (prefixWord ++ tailWord_7391429) baseStart_7391429 baseEnd_7391429 := by
    simpa [prefixWord, tailWord_7391429, baseEnd_7391429] using wordTrace_append hprefix tailTrace_7391429
  have hstable : (prefixWord ++ tailWord_7391429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391429).length < 2 ^ (prefixWord ++ tailWord_7391429).sum := by decide
  have hdescent : baseEnd_7391429 < baseStart_7391429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391446 : List Nat := [5, 2, 1, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_7391446 : Nat := 118140960795 + 7391446 * 2 ^ 59
def prefixEnd_7391446 : Nat := 4983230072969 + 3 ^ 40 * 7391446 * 2
def baseEnd_7391446 : Nat := 3795364529752593167232365

theorem tailTrace_7391446 : CollatzResearch.WordTrace tailWord_7391446 prefixEnd_7391446 3795364529752593167232365 := by
  unfold tailWord_7391446
  simp only [CollatzResearch.WordTrace]
  refine ⟨16849261448753810957526137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179725455453373983546945461 16849261448753810957526137)
  ·
    refine ⟨12636946086565358218144603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16849261448753810957526137 12636946086565358218144603)
    ·
      refine ⟨18955419129848037327216905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12636946086565358218144603 18955419129848037327216905)
      ·
        refine ⟨14216564347386027995412679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18955419129848037327216905 14216564347386027995412679)
        ·
          refine ⟨21324846521079041993119019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14216564347386027995412679 21324846521079041993119019)
          ·
            refine ⟨31987269781618562989678529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21324846521079041993119019 31987269781618562989678529)
            ·
              refine ⟨23990452336213922242258897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31987269781618562989678529 23990452336213922242258897)
              ·
                refine ⟨17992839252160441681694173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23990452336213922242258897 17992839252160441681694173)
                ·
                  refine ⟨6747314719560165630635315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17992839252160441681694173 6747314719560165630635315)
                  ·
                    refine ⟨10120972079340248445952973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6747314719560165630635315 10120972079340248445952973)
                    ·
                      refine ⟨3795364529752593167232365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10120972079340248445952973 3795364529752593167232365)
                      ·
                        rfl

theorem cell23_7391446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_7391446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391446 prefixEnd_7391446 := by exact prefixLift 7391446
  have htrace : WordTrace (prefixWord ++ tailWord_7391446) baseStart_7391446 baseEnd_7391446 := by
    simpa [prefixWord, tailWord_7391446, baseEnd_7391446] using wordTrace_append hprefix tailTrace_7391446
  have hstable : (prefixWord ++ tailWord_7391446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391446).length < 2 ^ (prefixWord ++ tailWord_7391446).sum := by decide
  have hdescent : baseEnd_7391446 < baseStart_7391446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391463 : List Nat := [1, 1, 5, 3, 1, 3, 1, 3, 1, 1, 3]
def baseStart_7391463 : Nat := 118140960795 + 7391463 * 2 ^ 59
def prefixEnd_7391463 : Nat := 4983230072969 + 3 ^ 40 * 7391463 * 2
def baseEnd_7391463 : Nat := 3795373258923719600719787

theorem tailTrace_7391463 : CollatzResearch.WordTrace tailWord_7391463 prefixEnd_7391463 3795373258923719600719787 := by
  unfold tailWord_7391463
  simp only [CollatzResearch.WordTrace]
  refine ⟨269588803220999387223787043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179725868813999591482524695 269588803220999387223787043)
  ·
    refine ⟨404383204831499080835680565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269588803220999387223787043 404383204831499080835680565)
    ·
      refine ⟨37910925452953038828345053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 404383204831499080835680565 37910925452953038828345053)
      ·
        refine ⟨14216597044857389560629395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37910925452953038828345053 14216597044857389560629395)
        ·
          refine ⟨21324895567286084340944093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14216597044857389560629395 21324895567286084340944093)
          ·
            refine ⟨7996835837732281627854035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21324895567286084340944093 7996835837732281627854035)
            ·
              refine ⟨11995253756598422441781053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7996835837732281627854035 11995253756598422441781053)
              ·
                refine ⟨4498220158724408415667895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11995253756598422441781053 4498220158724408415667895)
                ·
                  refine ⟨6747330238086612623501843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4498220158724408415667895 6747330238086612623501843)
                  ·
                    refine ⟨10120995357129918935252765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6747330238086612623501843 10120995357129918935252765)
                    ·
                      refine ⟨3795373258923719600719787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10120995357129918935252765 3795373258923719600719787)
                      ·
                        rfl

theorem cell23_7391463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_7391463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391463 prefixEnd_7391463 := by exact prefixLift 7391463
  have htrace : WordTrace (prefixWord ++ tailWord_7391463) baseStart_7391463 baseEnd_7391463 := by
    simpa [prefixWord, tailWord_7391463, baseEnd_7391463] using wordTrace_append hprefix tailTrace_7391463
  have hstable : (prefixWord ++ tailWord_7391463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391463).length < 2 ^ (prefixWord ++ tailWord_7391463).sum := by decide
  have hdescent : baseEnd_7391463 < baseStart_7391463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391492 : List Nat := [2, 3, 2, 2, 3, 1, 2, 8]
def baseStart_7391492 : Nat := 118140960795 + 7391492 * 2 ^ 59
def prefixEnd_7391492 : Nat := 4983230072969 + 3 ^ 40 * 7391492 * 2
def baseEnd_7391492 : Nat := 140569931476396295824339

theorem tailTrace_7391492 : CollatzResearch.WordTrace tailWord_7391492 prefixEnd_7391492 140569931476396295824339 := by
  unfold tailWord_7391492
  simp only [CollatzResearch.WordTrace]
  refine ⟨134794930468947162588296365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179726573958596216784395153 134794930468947162588296365)
  ·
    refine ⟨50548098925855185970611137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134794930468947162588296365 50548098925855185970611137)
    ·
      refine ⟨37911074194391389477958353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50548098925855185970611137 37911074194391389477958353)
      ·
        refine ⟨28433305645793542108468765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37911074194391389477958353 28433305645793542108468765)
        ·
          refine ⟨10662489617172578290675787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28433305645793542108468765 10662489617172578290675787)
          ·
            refine ⟨15993734425758867436013681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10662489617172578290675787 15993734425758867436013681)
            ·
              refine ⟨11995300819319150577010261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15993734425758867436013681 11995300819319150577010261)
              ·
                refine ⟨140569931476396295824339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11995300819319150577010261 140569931476396295824339)
                ·
                  rfl

theorem cell23_7391492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 8].length) (baseStart_7391492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391492 prefixEnd_7391492 := by exact prefixLift 7391492
  have htrace : WordTrace (prefixWord ++ tailWord_7391492) baseStart_7391492 baseEnd_7391492 := by
    simpa [prefixWord, tailWord_7391492, baseEnd_7391492] using wordTrace_append hprefix tailTrace_7391492
  have hstable : (prefixWord ++ tailWord_7391492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391492).length < 2 ^ (prefixWord ++ tailWord_7391492).sum := by decide
  have hdescent : baseEnd_7391492 < baseStart_7391492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391496 : List Nat := [2, 1, 3, 2, 3, 3, 2, 1, 2, 4]
def baseStart_7391496 : Nat := 118140960795 + 7391496 * 2 ^ 59
def prefixEnd_7391496 : Nat := 4983230072969 + 3 ^ 40 * 7391496 * 2
def baseEnd_7391496 : Nat := 1265130067928439323869045

theorem tailTrace_7391496 : CollatzResearch.WordTrace tailWord_7391496 prefixEnd_7391496 1265130067928439323869045 := by
  unfold tailWord_7391496
  simp only [CollatzResearch.WordTrace]
  refine ⟨134795003414939916929869171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179726671219919889239825561 134795003414939916929869171)
  ·
    refine ⟨202192505122409875394803757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134795003414939916929869171 202192505122409875394803757)
    ·
      refine ⟨75822189420903703273051409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202192505122409875394803757 75822189420903703273051409)
      ·
        refine ⟨56866642065677777454788557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75822189420903703273051409 56866642065677777454788557)
        ·
          refine ⟨21324990774629166545545709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56866642065677777454788557 21324990774629166545545709)
          ·
            refine ⟨7996871540485937454579641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21324990774629166545545709 7996871540485937454579641)
            ·
              refine ⟨5997653655364453090934731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7996871540485937454579641 5997653655364453090934731)
              ·
                refine ⟨8996480483046679636402097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5997653655364453090934731 8996480483046679636402097)
                ·
                  refine ⟨6747360362285009727301573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8996480483046679636402097 6747360362285009727301573)
                  ·
                    refine ⟨1265130067928439323869045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6747360362285009727301573 1265130067928439323869045)
                    ·
                      rfl

theorem cell23_7391496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_7391496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391496 prefixEnd_7391496 := by exact prefixLift 7391496
  have htrace : WordTrace (prefixWord ++ tailWord_7391496) baseStart_7391496 baseEnd_7391496 := by
    simpa [prefixWord, tailWord_7391496, baseEnd_7391496] using wordTrace_append hprefix tailTrace_7391496
  have hstable : (prefixWord ++ tailWord_7391496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391496).length < 2 ^ (prefixWord ++ tailWord_7391496).sum := by decide
  have hdescent : baseEnd_7391496 < baseStart_7391496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391502 : List Nat := [4, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3]
def baseStart_7391502 : Nat := 118140960795 + 7391502 * 2 ^ 59
def prefixEnd_7391502 : Nat := 4983230072969 + 3 ^ 40 * 7391502 * 2
def baseEnd_7391502 : Nat := 3795393284669244948132107

theorem tailTrace_7391502 : CollatzResearch.WordTrace tailWord_7391502 prefixEnd_7391502 3795393284669244948132107 := by
  unfold tailWord_7391502
  simp only [CollatzResearch.WordTrace]
  refine ⟨33698778208482262110557095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179726817111905397922971173 33698778208482262110557095)
  ·
    refine ⟨50548167312723393165835643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33698778208482262110557095 50548167312723393165835643)
    ·
      refine ⟨75822250969085089748753465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50548167312723393165835643 75822250969085089748753465)
      ·
        refine ⟨56866688226813817311565099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75822250969085089748753465 56866688226813817311565099)
        ·
          refine ⟨85300032340220725967347649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56866688226813817311565099 85300032340220725967347649)
          ·
            refine ⟨63975024255165544475510737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85300032340220725967347649 63975024255165544475510737)
            ·
              refine ⟨47981268191374158356633053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63975024255165544475510737 47981268191374158356633053)
              ·
                refine ⟨17992975571765309383737395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47981268191374158356633053 17992975571765309383737395)
                ·
                  refine ⟨26989463357647964075606093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17992975571765309383737395 26989463357647964075606093)
                  ·
                    refine ⟨10121048759117986528352285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26989463357647964075606093 10121048759117986528352285)
                    ·
                      refine ⟨3795393284669244948132107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10121048759117986528352285 3795393284669244948132107)
                      ·
                        rfl

theorem cell23_7391502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_7391502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391502 prefixEnd_7391502 := by exact prefixLift 7391502
  have htrace : WordTrace (prefixWord ++ tailWord_7391502) baseStart_7391502 baseEnd_7391502 := by
    simpa [prefixWord, tailWord_7391502, baseEnd_7391502] using wordTrace_append hprefix tailTrace_7391502
  have hstable : (prefixWord ++ tailWord_7391502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391502).length < 2 ^ (prefixWord ++ tailWord_7391502).sum := by decide
  have hdescent : baseEnd_7391502 < baseStart_7391502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391537 : List Nat := [1, 2, 2, 3, 5, 1, 2, 2, 1, 2, 2]
def baseStart_7391537 : Nat := 118140960795 + 7391537 * 2 ^ 59
def prefixEnd_7391537 : Nat := 4983230072969 + 3 ^ 40 * 7391537 * 2
def baseEnd_7391537 : Nat := 3795411256492152311194447

theorem tailTrace_7391537 : CollatzResearch.WordTrace tailWord_7391537 prefixEnd_7391537 3795411256492152311194447 := by
  unfold tailWord_7391537
  simp only [CollatzResearch.WordTrace]
  refine ⟨269591502222731297861980865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179727668148487531907987243 269591502222731297861980865)
  ·
    refine ⟨202193626667048473396485649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269591502222731297861980865 202193626667048473396485649)
    ·
      refine ⟨151645220000286355047364237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202193626667048473396485649 151645220000286355047364237)
      ·
        refine ⟨56866957500107383142761589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151645220000286355047364237 56866957500107383142761589)
        ·
          refine ⟨5331277265635067169633899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56866957500107383142761589 5331277265635067169633899)
          ·
            refine ⟨7996915898452600754450849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5331277265635067169633899 7996915898452600754450849)
            ·
              refine ⟨5997686923839450565838137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7996915898452600754450849 5997686923839450565838137)
              ·
                refine ⟨4498265192879587924378603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5997686923839450565838137 4498265192879587924378603)
                ·
                  refine ⟨6747397789319381886567905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4498265192879587924378603 6747397789319381886567905)
                  ·
                    refine ⟨5060548341989536414925929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6747397789319381886567905 5060548341989536414925929)
                    ·
                      refine ⟨3795411256492152311194447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5060548341989536414925929 3795411256492152311194447)
                      ·
                        rfl

theorem cell23_7391537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_7391537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391537 prefixEnd_7391537 := by exact prefixLift 7391537
  have htrace : WordTrace (prefixWord ++ tailWord_7391537) baseStart_7391537 baseEnd_7391537 := by
    simpa [prefixWord, tailWord_7391537, baseEnd_7391537] using wordTrace_append hprefix tailTrace_7391537
  have hstable : (prefixWord ++ tailWord_7391537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391537).length < 2 ^ (prefixWord ++ tailWord_7391537).sum := by decide
  have hdescent : baseEnd_7391537 < baseStart_7391537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391555 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 4]
def baseStart_7391555 : Nat := 118140960795 + 7391555 * 2 ^ 59
def prefixEnd_7391555 : Nat := 4983230072969 + 3 ^ 40 * 7391555 * 2
def baseEnd_7391555 : Nat := 3795420499143933240769363

theorem tailTrace_7391555 : CollatzResearch.WordTrace tailWord_7391555 prefixEnd_7391555 3795420499143933240769363 := by
  unfold tailWord_7391555
  simp only [CollatzResearch.WordTrace]
  refine ⟨269592158736666086936136119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179728105824444057957424079 269592158736666086936136119)
  ·
    refine ⟨404388238104999130404204179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269592158736666086936136119 404388238104999130404204179)
    ·
      refine ⟨606582357157498695606306269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404388238104999130404204179 606582357157498695606306269)
      ·
        refine ⟨227468383934062010852364851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 606582357157498695606306269 227468383934062010852364851)
        ·
          refine ⟨341202575901093016278547277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227468383934062010852364851 341202575901093016278547277)
          ·
            refine ⟨127950965962909881104455229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341202575901093016278547277 127950965962909881104455229)
            ·
              refine ⟨47981612236091205414170711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127950965962909881104455229 47981612236091205414170711)
              ·
                refine ⟨71972418354136808121256067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47981612236091205414170711 71972418354136808121256067)
                ·
                  refine ⟨107958627531205212181884101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71972418354136808121256067 107958627531205212181884101)
                  ·
                    refine ⟨20242242662100977284103269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107958627531205212181884101 20242242662100977284103269)
                    ·
                      refine ⟨3795420499143933240769363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20242242662100977284103269 3795420499143933240769363)
                      ·
                        rfl

theorem cell23_7391555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_7391555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391555 prefixEnd_7391555 := by exact prefixLift 7391555
  have htrace : WordTrace (prefixWord ++ tailWord_7391555) baseStart_7391555 baseEnd_7391555 := by
    simpa [prefixWord, tailWord_7391555, baseEnd_7391555] using wordTrace_append hprefix tailTrace_7391555
  have hstable : (prefixWord ++ tailWord_7391555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391555).length < 2 ^ (prefixWord ++ tailWord_7391555).sum := by decide
  have hdescent : baseEnd_7391555 < baseStart_7391555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391559 : List Nat := [1, 1, 4, 1, 2, 2, 4, 1, 1, 4, 2]
def baseStart_7391559 : Nat := 118140960795 + 7391559 * 2 ^ 59
def prefixEnd_7391559 : Nat := 4983230072969 + 3 ^ 40 * 7391559 * 2
def baseEnd_7391559 : Nat := 3795422553066551225119345

theorem tailTrace_7391559 : CollatzResearch.WordTrace tailWord_7391559 prefixEnd_7391559 3795422553066551225119345 := by
  unfold tailWord_7391559
  simp only [CollatzResearch.WordTrace]
  refine ⟨269592304628651595619281731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179728203085767730412854487 269592304628651595619281731)
  ·
    refine ⟨404388456942977393428922597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269592304628651595619281731 404388456942977393428922597)
    ·
      refine ⟨75822835676808261267922987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404388456942977393428922597 75822835676808261267922987)
      ·
        refine ⟨113734253515212391901884481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75822835676808261267922987 113734253515212391901884481)
        ·
          refine ⟨85300690136409293926413361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113734253515212391901884481 85300690136409293926413361)
          ·
            refine ⟨63975517602306970444810021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85300690136409293926413361 63975517602306970444810021)
            ·
              refine ⟨11995409550432556958401879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63975517602306970444810021 11995409550432556958401879)
              ·
                refine ⟨17993114325648835437602819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11995409550432556958401879 17993114325648835437602819)
                ·
                  refine ⟨26989671488473253156404229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17993114325648835437602819 26989671488473253156404229)
                  ·
                    refine ⟨5060563404088734966825793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26989671488473253156404229 5060563404088734966825793)
                    ·
                      refine ⟨3795422553066551225119345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5060563404088734966825793 3795422553066551225119345)
                      ·
                        rfl

theorem cell23_7391559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_7391559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391559 prefixEnd_7391559 := by exact prefixLift 7391559
  have htrace : WordTrace (prefixWord ++ tailWord_7391559) baseStart_7391559 baseEnd_7391559 := by
    simpa [prefixWord, tailWord_7391559, baseEnd_7391559] using wordTrace_append hprefix tailTrace_7391559
  have hstable : (prefixWord ++ tailWord_7391559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391559).length < 2 ^ (prefixWord ++ tailWord_7391559).sum := by decide
  have hdescent : baseEnd_7391559 < baseStart_7391559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391646 : List Nat := [4, 3, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_7391646 : Nat := 118140960795 + 7391646 * 2 ^ 59
def prefixEnd_7391646 : Nat := 4983230072969 + 3 ^ 40 * 7391646 * 2
def baseEnd_7391646 : Nat := 1265155741961164128243815

theorem tailTrace_7391646 : CollatzResearch.WordTrace tailWord_7391646 prefixEnd_7391646 1265155741961164128243815 := by
  unfold tailWord_7391646
  simp only [CollatzResearch.WordTrace]
  refine ⟨33699434722417051184712349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179730318519557606318465861 33699434722417051184712349)
  ·
    refine ⟨12637288020906394194267131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33699434722417051184712349 12637288020906394194267131)
    ·
      refine ⟨18955932031359591291400697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12637288020906394194267131 18955932031359591291400697)
      ·
        refine ⟨14216949023519693468550523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18955932031359591291400697 14216949023519693468550523)
        ·
          refine ⟨21325423535279540202825785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14216949023519693468550523 21325423535279540202825785)
          ·
            refine ⟨15994067651459655152119339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21325423535279540202825785 15994067651459655152119339)
            ·
              refine ⟨23991101477189482728179009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15994067651459655152119339 23991101477189482728179009)
              ·
                refine ⟨17993326107892112046134257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23991101477189482728179009 17993326107892112046134257)
                ·
                  refine ⟨13494994580919084034600693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17993326107892112046134257 13494994580919084034600693)
                  ·
                    refine ⟨1265155741961164128243815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13494994580919084034600693 1265155741961164128243815)
                    ·
                      rfl

theorem cell23_7391646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_7391646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391646 prefixEnd_7391646 := by exact prefixLift 7391646
  have htrace : WordTrace (prefixWord ++ tailWord_7391646) baseStart_7391646 baseEnd_7391646 := by
    simpa [prefixWord, tailWord_7391646, baseEnd_7391646] using wordTrace_append hprefix tailTrace_7391646
  have hstable : (prefixWord ++ tailWord_7391646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391646).length < 2 ^ (prefixWord ++ tailWord_7391646).sum := by decide
  have hdescent : baseEnd_7391646 < baseStart_7391646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391752 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_7391752 : Nat := 118140960795 + 7391752 * 2 ^ 59
def prefixEnd_7391752 : Nat := 4983230072969 + 3 ^ 40 * 7391752 * 2
def baseEnd_7391752 : Nat := 3795521654832868970005957

theorem tailTrace_7391752 : CollatzResearch.WordTrace tailWord_7391752 prefixEnd_7391752 3795521654832868970005957 := by
  unfold tailWord_7391752
  simp only [CollatzResearch.WordTrace]
  refine ⟨134799671958476194790528755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179732895944634926387371673 134799671958476194790528755)
  ·
    refine ⟨202199507937714292185793133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134799671958476194790528755 202199507937714292185793133)
    ·
      refine ⟨75824815476642859569672425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202199507937714292185793133 75824815476642859569672425)
      ·
        refine ⟨56868611607482144677254319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75824815476642859569672425 56868611607482144677254319)
        ·
          refine ⟨85302917411223217015881479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56868611607482144677254319 85302917411223217015881479)
          ·
            refine ⟨127954376116834825523822219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85302917411223217015881479 127954376116834825523822219)
            ·
              refine ⟨191931564175252238285733329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127954376116834825523822219 191931564175252238285733329)
              ·
                refine ⟨143948673131439178714299997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191931564175252238285733329 143948673131439178714299997)
                ·
                  refine ⟨53980752424289692017862499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143948673131439178714299997 53980752424289692017862499)
                  ·
                    refine ⟨80971128636434538026793749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53980752424289692017862499 80971128636434538026793749)
                    ·
                      refine ⟨3795521654832868970005957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80971128636434538026793749 3795521654832868970005957)
                      ·
                        rfl

theorem cell23_7391752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_7391752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391752 prefixEnd_7391752 := by exact prefixLift 7391752
  have htrace : WordTrace (prefixWord ++ tailWord_7391752) baseStart_7391752 baseEnd_7391752 := by
    simpa [prefixWord, tailWord_7391752, baseEnd_7391752] using wordTrace_append hprefix tailTrace_7391752
  have hstable : (prefixWord ++ tailWord_7391752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391752).length < 2 ^ (prefixWord ++ tailWord_7391752).sum := by decide
  have hdescent : baseEnd_7391752 < baseStart_7391752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391756 : List Nat := [2, 2, 1, 2, 4, 2, 1, 3, 1, 1, 4]
def baseStart_7391756 : Nat := 118140960795 + 7391756 * 2 ^ 59
def prefixEnd_7391756 : Nat := 4983230072969 + 3 ^ 40 * 7391756 * 2
def baseEnd_7391756 : Nat := 3795523708755486954355939

theorem tailTrace_7391756 : CollatzResearch.WordTrace tailWord_7391756 prefixEnd_7391756 3795523708755486954355939 := by
  unfold tailWord_7391756
  simp only [CollatzResearch.WordTrace]
  refine ⟨134799744904468949132101561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179732993205958598842802081 134799744904468949132101561)
  ·
    refine ⟨101099808678351711849076171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134799744904468949132101561 101099808678351711849076171)
    ·
      refine ⟨151649713017527567773614257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101099808678351711849076171 151649713017527567773614257)
      ·
        refine ⟨113737284763145675830210693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151649713017527567773614257 113737284763145675830210693)
        ·
          refine ⟨21325740893089814218164505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113737284763145675830210693 21325740893089814218164505)
          ·
            refine ⟨15994305669817360663623379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21325740893089814218164505 15994305669817360663623379)
            ·
              refine ⟨23991458504726040995435069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15994305669817360663623379 23991458504726040995435069)
              ·
                refine ⟨8996796939272265373288151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23991458504726040995435069 8996796939272265373288151)
                ·
                  refine ⟨13495195408908398059932227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8996796939272265373288151 13495195408908398059932227)
                  ·
                    refine ⟨20242793113362597089898341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13495195408908398059932227 20242793113362597089898341)
                    ·
                      refine ⟨3795523708755486954355939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20242793113362597089898341 3795523708755486954355939)
                      ·
                        rfl

theorem cell23_7391756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_7391756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391756 prefixEnd_7391756 := by exact prefixLift 7391756
  have htrace : WordTrace (prefixWord ++ tailWord_7391756) baseStart_7391756 baseEnd_7391756 := by
    simpa [prefixWord, tailWord_7391756, baseEnd_7391756] using wordTrace_append hprefix tailTrace_7391756
  have hstable : (prefixWord ++ tailWord_7391756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391756).length < 2 ^ (prefixWord ++ tailWord_7391756).sum := by decide
  have hdescent : baseEnd_7391756 < baseStart_7391756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391773 : List Nat := [1, 4, 2, 2, 1, 2, 1, 3, 3, 2, 2]
def baseStart_7391773 : Nat := 118140960795 + 7391773 * 2 ^ 59
def prefixEnd_7391773 : Nat := 4983230072969 + 3 ^ 40 * 7391773 * 2
def baseEnd_7391773 : Nat := 3795532437926613387843361

theorem tailTrace_7391773 : CollatzResearch.WordTrace tailWord_7391773 prefixEnd_7391773 3795532437926613387843361 := by
  unfold tailWord_7391773
  simp only [CollatzResearch.WordTrace]
  refine ⟨269600109849876310167571973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179733406566584206778381315 269600109849876310167571973)
  ·
    refine ⟨50550020596851808156419745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269600109849876310167571973 50550020596851808156419745)
    ·
      refine ⟨37912515447638856117314809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50550020596851808156419745 37912515447638856117314809)
      ·
        refine ⟨28434386585729142087986107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37912515447638856117314809 28434386585729142087986107)
        ·
          refine ⟨42651579878593713131979161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28434386585729142087986107 42651579878593713131979161)
          ·
            refine ⟨31988684908945284848984371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42651579878593713131979161 31988684908945284848984371)
            ·
              refine ⟨47983027363417927273476557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31988684908945284848984371 47983027363417927273476557)
              ·
                refine ⟨17993635261281722727553709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47983027363417927273476557 17993635261281722727553709)
                ·
                  refine ⟨6747613222980646022832641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17993635261281722727553709 6747613222980646022832641)
                  ·
                    refine ⟨5060709917235484517124481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6747613222980646022832641 5060709917235484517124481)
                    ·
                      refine ⟨3795532437926613387843361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5060709917235484517124481 3795532437926613387843361)
                      ·
                        rfl

theorem cell23_7391773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_7391773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391773 prefixEnd_7391773 := by exact prefixLift 7391773
  have htrace : WordTrace (prefixWord ++ tailWord_7391773) baseStart_7391773 baseEnd_7391773 := by
    simpa [prefixWord, tailWord_7391773, baseEnd_7391773] using wordTrace_append hprefix tailTrace_7391773
  have hstable : (prefixWord ++ tailWord_7391773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391773).length < 2 ^ (prefixWord ++ tailWord_7391773).sum := by decide
  have hdescent : baseEnd_7391773 < baseStart_7391773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391776 : List Nat := [2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 5]
def baseStart_7391776 : Nat := 118140960795 + 7391776 * 2 ^ 59
def prefixEnd_7391776 : Nat := 4983230072969 + 3 ^ 40 * 7391776 * 2
def baseEnd_7391776 : Nat := 3795533978368576876105847

theorem tailTrace_7391776 : CollatzResearch.WordTrace tailWord_7391776 prefixEnd_7391776 3795533978368576876105847 := by
  unfold tailWord_7391776
  simp only [CollatzResearch.WordTrace]
  refine ⟨134800109634432720839965591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179733479512576961119954121 134800109634432720839965591)
  ·
    refine ⟨202200164451649081259948387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134800109634432720839965591 202200164451649081259948387)
    ·
      refine ⟨303300246677473621889922581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202200164451649081259948387 303300246677473621889922581)
      ·
        refine ⟨14217199063006576026090121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 303300246677473621889922581 14217199063006576026090121)
        ·
          refine ⟨10662899297254932019567591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14217199063006576026090121 10662899297254932019567591)
          ·
            refine ⟨15994348945882398029351387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10662899297254932019567591 15994348945882398029351387)
            ·
              refine ⟨23991523418823597044027081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15994348945882398029351387 23991523418823597044027081)
              ·
                refine ⟨17993642564117697783020311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23991523418823597044027081 17993642564117697783020311)
                ·
                  refine ⟨26990463846176546674530467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17993642564117697783020311 26990463846176546674530467)
                  ·
                    refine ⟨40485695769264820011795701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26990463846176546674530467 40485695769264820011795701)
                    ·
                      refine ⟨3795533978368576876105847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40485695769264820011795701 3795533978368576876105847)
                      ·
                        rfl

theorem cell23_7391776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_7391776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391776 prefixEnd_7391776 := by exact prefixLift 7391776
  have htrace : WordTrace (prefixWord ++ tailWord_7391776) baseStart_7391776 baseEnd_7391776 := by
    simpa [prefixWord, tailWord_7391776, baseEnd_7391776] using wordTrace_append hprefix tailTrace_7391776
  have hstable : (prefixWord ++ tailWord_7391776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391776).length < 2 ^ (prefixWord ++ tailWord_7391776).sum := by decide
  have hdescent : baseEnd_7391776 < baseStart_7391776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391786 : List Nat := [3, 1, 4, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_7391786 : Nat := 118140960795 + 7391786 * 2 ^ 59
def prefixEnd_7391786 : Nat := 4983230072969 + 3 ^ 40 * 7391786 * 2
def baseEnd_7391786 : Nat := 3795539113175121836980801

theorem tailTrace_7391786 : CollatzResearch.WordTrace tailWord_7391786 prefixEnd_7391786 3795539113175121836980801 := by
  unfold tailWord_7391786
  simp only [CollatzResearch.WordTrace]
  refine ⟨67400145999707303346948803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179733722665886142258530141 67400145999707303346948803)
  ·
    refine ⟨101100218999560955020423205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67400145999707303346948803 101100218999560955020423205)
    ·
      refine ⟨18956291062417679066329351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101100218999560955020423205 18956291062417679066329351)
      ·
        refine ⟨28434436593626518599494027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18956291062417679066329351 28434436593626518599494027)
        ·
          refine ⟨42651654890439777899241041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28434436593626518599494027 42651654890439777899241041)
          ·
            refine ⟨31988741167829833424430781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42651654890439777899241041 31988741167829833424430781)
            ·
              refine ⟨11995777937936187534161543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31988741167829833424430781 11995777937936187534161543)
              ·
                refine ⟨17993666906904281301242315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11995777937936187534161543 17993666906904281301242315)
                ·
                  refine ⟨26990500360356421951863473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17993666906904281301242315 26990500360356421951863473)
                  ·
                    refine ⟨20242875270267316463897605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26990500360356421951863473 20242875270267316463897605)
                    ·
                      refine ⟨3795539113175121836980801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20242875270267316463897605 3795539113175121836980801)
                      ·
                        rfl

theorem cell23_7391786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_7391786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391786 prefixEnd_7391786 := by exact prefixLift 7391786
  have htrace : WordTrace (prefixWord ++ tailWord_7391786) baseStart_7391786 baseEnd_7391786 := by
    simpa [prefixWord, tailWord_7391786, baseEnd_7391786] using wordTrace_append hprefix tailTrace_7391786
  have hstable : (prefixWord ++ tailWord_7391786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391786).length < 2 ^ (prefixWord ++ tailWord_7391786).sum := by decide
  have hdescent : baseEnd_7391786 < baseStart_7391786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391792 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 2, 7]
def baseStart_7391792 : Nat := 118140960795 + 7391792 * 2 ^ 59
def prefixEnd_7391792 : Nat := 4983230072969 + 3 ^ 40 * 7391792 * 2
def baseEnd_7391792 : Nat := 1265180731353016271168591

theorem tailTrace_7391792 : CollatzResearch.WordTrace tailWord_7391792 prefixEnd_7391792 1265180731353016271168591 := by
  unfold tailWord_7391792
  simp only [CollatzResearch.WordTrace]
  refine ⟨134800401418403738206256815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179733868557871650941675753 134800401418403738206256815)
  ·
    refine ⟨202200602127605607309385223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134800401418403738206256815 202200602127605607309385223)
    ·
      refine ⟨303300903191408410964077835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202200602127605607309385223 303300903191408410964077835)
      ·
        refine ⟨454951354787112616446116753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303300903191408410964077835 454951354787112616446116753)
        ·
          refine ⟨341213516090334462334587565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454951354787112616446116753 341213516090334462334587565)
          ·
            refine ⟨127955068533875423375470337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341213516090334462334587565 127955068533875423375470337)
            ·
              refine ⟨95966301400406567531602753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127955068533875423375470337 95966301400406567531602753)
              ·
                refine ⟨71974726050304925648702065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95966301400406567531602753 71974726050304925648702065)
                ·
                  refine ⟨53981044537728694236526549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71974726050304925648702065 53981044537728694236526549)
                  ·
                    refine ⟨1265180731353016271168591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53981044537728694236526549 1265180731353016271168591)
                    ·
                      rfl

theorem cell23_7391792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2, 7].length) (baseStart_7391792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391792 prefixEnd_7391792 := by exact prefixLift 7391792
  have htrace : WordTrace (prefixWord ++ tailWord_7391792) baseStart_7391792 baseEnd_7391792 := by
    simpa [prefixWord, tailWord_7391792, baseEnd_7391792] using wordTrace_append hprefix tailTrace_7391792
  have hstable : (prefixWord ++ tailWord_7391792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391792).length < 2 ^ (prefixWord ++ tailWord_7391792).sum := by decide
  have hdescent : baseEnd_7391792 < baseStart_7391792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391896 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 2, 3, 3]
def baseStart_7391896 : Nat := 118140960795 + 7391896 * 2 ^ 59
def prefixEnd_7391896 : Nat := 4983230072969 + 3 ^ 40 * 7391896 * 2
def baseEnd_7391896 : Nat := 3795595596047116406605295

theorem tailTrace_7391896 : CollatzResearch.WordTrace tailWord_7391896 prefixEnd_7391896 3795595596047116406605295 := by
  unfold tailWord_7391896
  simp only [CollatzResearch.WordTrace]
  refine ⟨134802298014215351087149771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179736397352287134782866361 134802298014215351087149771)
  ·
    refine ⟨202203447021323026630724657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134802298014215351087149771 202203447021323026630724657)
    ·
      refine ⟨151652585265992269973043493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202203447021323026630724657 151652585265992269973043493)
      ·
        refine ⟨28434859737373550619945655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151652585265992269973043493 28434859737373550619945655)
        ·
          refine ⟨42652289606060325929918483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28434859737373550619945655 42652289606060325929918483)
          ·
            refine ⟨63978434409090488894877725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42652289606060325929918483 63978434409090488894877725)
            ·
              refine ⟨23991912903408933335579147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63978434409090488894877725 23991912903408933335579147)
              ·
                refine ⟨35987869355113400003368721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23991912903408933335579147 35987869355113400003368721)
                ·
                  refine ⟨26990902016335050002526541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35987869355113400003368721 26990902016335050002526541)
                  ·
                    refine ⟨10121588256125643750947453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26990902016335050002526541 10121588256125643750947453)
                    ·
                      refine ⟨3795595596047116406605295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10121588256125643750947453 3795595596047116406605295)
                      ·
                        rfl

theorem cell23_7391896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_7391896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391896 prefixEnd_7391896 := by exact prefixLift 7391896
  have htrace : WordTrace (prefixWord ++ tailWord_7391896) baseStart_7391896 baseEnd_7391896 := by
    simpa [prefixWord, tailWord_7391896, baseEnd_7391896] using wordTrace_append hprefix tailTrace_7391896
  have hstable : (prefixWord ++ tailWord_7391896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391896).length < 2 ^ (prefixWord ++ tailWord_7391896).sum := by decide
  have hdescent : baseEnd_7391896 < baseStart_7391896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7391999 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 7]
def baseStart_7391999 : Nat := 118140960795 + 7391999 * 2 ^ 59
def prefixEnd_7391999 : Nat := 4983230072969 + 3 ^ 40 * 7391999 * 2
def baseEnd_7391999 : Nat := 3795648484554529503617321

theorem tailTrace_7391999 : CollatzResearch.WordTrace tailWord_7391999 prefixEnd_7391999 3795648484554529503617321 := by
  unfold tailWord_7391999
  simp only [CollatzResearch.WordTrace]
  refine ⟨269608352747057550765299051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179738901831371700510199367 269608352747057550765299051)
  ·
    refine ⟨404412529120586326147948577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269608352747057550765299051 404412529120586326147948577)
    ·
      refine ⟨303309396840439744610961433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404412529120586326147948577 303309396840439744610961433)
      ·
        refine ⟨227482047630329808458221075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303309396840439744610961433 227482047630329808458221075)
        ·
          refine ⟨341223071445494712687331613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227482047630329808458221075 341223071445494712687331613)
          ·
            refine ⟨127958651792060517257749355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341223071445494712687331613 127958651792060517257749355)
            ·
              refine ⟨191937977688090775886624033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127958651792060517257749355 191937977688090775886624033)
              ·
                refine ⟨143953483266068081914968025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191937977688090775886624033 143953483266068081914968025)
                ·
                  refine ⟨107965112449551061436226019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143953483266068081914968025 107965112449551061436226019)
                  ·
                    refine ⟨161947668674326592154339029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107965112449551061436226019 161947668674326592154339029)
                    ·
                      refine ⟨3795648484554529503617321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161947668674326592154339029 3795648484554529503617321)
                      ·
                        rfl

theorem cell23_7391999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_7391999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7391999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7391999 prefixEnd_7391999 := by exact prefixLift 7391999
  have htrace : WordTrace (prefixWord ++ tailWord_7391999) baseStart_7391999 baseEnd_7391999 := by
    simpa [prefixWord, tailWord_7391999, baseEnd_7391999] using wordTrace_append hprefix tailTrace_7391999
  have hstable : (prefixWord ++ tailWord_7391999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7391999).length < 2 ^ (prefixWord ++ tailWord_7391999).sum := by decide
  have hdescent : baseEnd_7391999 < baseStart_7391999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7391999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392023 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 3, 5]
def baseStart_7392023 : Nat := 118140960795 + 7392023 * 2 ^ 59
def prefixEnd_7392023 : Nat := 4983230072969 + 3 ^ 40 * 7392023 * 2
def baseEnd_7392023 : Nat := 1265220269363412469905737

theorem tailTrace_7392023 : CollatzResearch.WordTrace tailWord_7392023 prefixEnd_7392023 1265220269363412469905737 := by
  unfold tailWord_7392023
  simp only [CollatzResearch.WordTrace]
  refine ⟨269609228098970602864172723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179739485399313735242781815 269609228098970602864172723)
  ·
    refine ⟨404413842148455904296259085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269609228098970602864172723 404413842148455904296259085)
    ·
      refine ⟨151655190805670964111097157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404413842148455904296259085 151655190805670964111097157)
      ·
        refine ⟨28435348276063305770830717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151655190805670964111097157 28435348276063305770830717)
        ·
          refine ⟨10663255603523739664061519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28435348276063305770830717 10663255603523739664061519)
          ·
            refine ⟨15994883405285609496092279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10663255603523739664061519 15994883405285609496092279)
            ·
              refine ⟨23992325107928414244138419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15994883405285609496092279 23992325107928414244138419)
              ·
                refine ⟨35988487661892621366207629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23992325107928414244138419 35988487661892621366207629)
                ·
                  refine ⟨13495682873209733012327861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35988487661892621366207629 13495682873209733012327861)
                  ·
                    refine ⟨1265220269363412469905737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13495682873209733012327861 1265220269363412469905737)
                    ·
                      rfl

theorem cell23_7392023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_7392023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392023 prefixEnd_7392023 := by exact prefixLift 7392023
  have htrace : WordTrace (prefixWord ++ tailWord_7392023) baseStart_7392023 baseEnd_7392023 := by
    simpa [prefixWord, tailWord_7392023, baseEnd_7392023] using wordTrace_append hprefix tailTrace_7392023
  have hstable : (prefixWord ++ tailWord_7392023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392023).length < 2 ^ (prefixWord ++ tailWord_7392023).sum := by decide
  have hdescent : baseEnd_7392023 < baseStart_7392023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392040 : List Nat := [2, 1, 5, 1, 1, 1, 5, 1, 1, 5]
def baseStart_7392040 : Nat := 118140960795 + 7392040 * 2 ^ 59
def prefixEnd_7392040 : Nat := 4983230072969 + 3 ^ 40 * 7392040 * 2
def baseEnd_7392040 : Nat := 1265223179087121281068211

theorem tailTrace_7392040 : CollatzResearch.WordTrace tailWord_7392040 prefixEnd_7392040 1265223179087121281068211 := by
  unfold tailWord_7392040
  simp only [CollatzResearch.WordTrace]
  refine ⟨134804924069954507383770787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179739898759939343178361049 134804924069954507383770787)
  ·
    refine ⟨202207386104931761075656181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134804924069954507383770787 202207386104931761075656181)
    ·
      refine ⟨18956942447337352600842767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202207386104931761075656181 18956942447337352600842767)
      ·
        refine ⟨28435413671006028901264151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18956942447337352600842767 28435413671006028901264151)
        ·
          refine ⟨42653120506509043351896227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28435413671006028901264151 42653120506509043351896227)
          ·
            refine ⟨63979680759763565027844341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42653120506509043351896227 63979680759763565027844341)
            ·
              refine ⟨5998095071227834221360407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63979680759763565027844341 5998095071227834221360407)
              ·
                refine ⟨8997142606841751332040611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5998095071227834221360407 8997142606841751332040611)
                ·
                  refine ⟨13495713910262626998060917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8997142606841751332040611 13495713910262626998060917)
                  ·
                    refine ⟨1265223179087121281068211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13495713910262626998060917 1265223179087121281068211)
                    ·
                      rfl

theorem cell23_7392040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_7392040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392040 prefixEnd_7392040 := by exact prefixLift 7392040
  have htrace : WordTrace (prefixWord ++ tailWord_7392040) baseStart_7392040 baseEnd_7392040 := by
    simpa [prefixWord, tailWord_7392040, baseEnd_7392040] using wordTrace_append hprefix tailTrace_7392040
  have hstable : (prefixWord ++ tailWord_7392040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392040).length < 2 ^ (prefixWord ++ tailWord_7392040).sum := by decide
  have hdescent : baseEnd_7392040 < baseStart_7392040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392056 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 3, 2, 4]
def baseStart_7392056 : Nat := 118140960795 + 7392056 * 2 ^ 59
def prefixEnd_7392056 : Nat := 4983230072969 + 3 ^ 40 * 7392056 * 2
def baseEnd_7392056 : Nat := 3795677752951835780604559

theorem tailTrace_7392056 : CollatzResearch.WordTrace tailWord_7392056 prefixEnd_7392056 3795677752951835780604559 := by
  unfold tailWord_7392056
  simp only [CollatzResearch.WordTrace]
  refine ⟨134805215853925524750062011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179740287805234033000082681 134805215853925524750062011)
  ·
    refine ⟨202207823780888287125093017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134805215853925524750062011 202207823780888287125093017)
    ·
      refine ⟨151655867835666215343819763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202207823780888287125093017 151655867835666215343819763)
      ·
        refine ⟨227483801753499323015729645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151655867835666215343819763 227483801753499323015729645)
        ·
          refine ⟨85306425657562246130898617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227483801753499323015729645 85306425657562246130898617)
          ·
            refine ⟨63979819243171684598173963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85306425657562246130898617 63979819243171684598173963)
            ·
              refine ⟨95969728864757526897260945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63979819243171684598173963 95969728864757526897260945)
              ·
                refine ⟨71977296648568145172945709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95969728864757526897260945 71977296648568145172945709)
                ·
                  refine ⟨26991486243213054439854641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71977296648568145172945709 26991486243213054439854641)
                  ·
                    refine ⟨20243614682409790829890981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26991486243213054439854641 20243614682409790829890981)
                    ·
                      refine ⟨3795677752951835780604559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20243614682409790829890981 3795677752951835780604559)
                      ·
                        rfl

theorem cell23_7392056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_7392056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392056 prefixEnd_7392056 := by exact prefixLift 7392056
  have htrace : WordTrace (prefixWord ++ tailWord_7392056) baseStart_7392056 baseEnd_7392056 := by
    simpa [prefixWord, tailWord_7392056, baseEnd_7392056] using wordTrace_append hprefix tailTrace_7392056
  have hstable : (prefixWord ++ tailWord_7392056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392056).length < 2 ^ (prefixWord ++ tailWord_7392056).sum := by decide
  have hdescent : baseEnd_7392056 < baseStart_7392056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392060 : List Nat := [2, 2, 2, 2, 1, 1, 1, 5, 3, 2, 2]
def baseStart_7392060 : Nat := 118140960795 + 7392060 * 2 ^ 59
def prefixEnd_7392060 : Nat := 4983230072969 + 3 ^ 40 * 7392060 * 2
def baseEnd_7392060 : Nat := 3795679806874453764954541

theorem tailTrace_7392060 : CollatzResearch.WordTrace tailWord_7392060 prefixEnd_7392060 3795679806874453764954541 := by
  unfold tailWord_7392060
  simp only [CollatzResearch.WordTrace]
  refine ⟨134805288799918279091634817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179740385066557705455513089 134805288799918279091634817)
  ·
    refine ⟨101103966599938709318726113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134805288799918279091634817 101103966599938709318726113)
    ·
      refine ⟨75827974949954031989044585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101103966599938709318726113 75827974949954031989044585)
      ·
        refine ⟨56870981212465523991783439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75827974949954031989044585 56870981212465523991783439)
        ·
          refine ⟨85306471818698285987675159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56870981212465523991783439 85306471818698285987675159)
          ·
            refine ⟨127959707728047428981512739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85306471818698285987675159 127959707728047428981512739)
            ·
              refine ⟨191939561592071143472269109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127959707728047428981512739 191939561592071143472269109)
              ·
                refine ⟨17994333899256669700525229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191939561592071143472269109 17994333899256669700525229)
                ·
                  refine ⟨6747875212221251137696961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17994333899256669700525229 6747875212221251137696961)
                  ·
                    refine ⟨5060906409165938353272721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6747875212221251137696961 5060906409165938353272721)
                    ·
                      refine ⟨3795679806874453764954541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5060906409165938353272721 3795679806874453764954541)
                      ·
                        rfl

theorem cell23_7392060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_7392060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392060 prefixEnd_7392060 := by exact prefixLift 7392060
  have htrace : WordTrace (prefixWord ++ tailWord_7392060) baseStart_7392060 baseEnd_7392060 := by
    simpa [prefixWord, tailWord_7392060, baseEnd_7392060] using wordTrace_append hprefix tailTrace_7392060
  have hstable : (prefixWord ++ tailWord_7392060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392060).length < 2 ^ (prefixWord ++ tailWord_7392060).sum := by decide
  have hdescent : baseEnd_7392060 < baseStart_7392060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392063 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 3]
def baseStart_7392063 : Nat := 118140960795 + 7392063 * 2 ^ 59
def prefixEnd_7392063 : Nat := 4983230072969 + 3 ^ 40 * 7392063 * 2
def baseEnd_7392063 : Nat := 3795681347316417253217027

theorem tailTrace_7392063 : CollatzResearch.WordTrace tailWord_7392063 prefixEnd_7392063 3795681347316417253217027 := by
  unfold tailWord_7392063
  simp only [CollatzResearch.WordTrace]
  refine ⟨269610687018825689695628843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179740458012550459797085895 269610687018825689695628843)
  ·
    refine ⟨404416030528238534543443265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269610687018825689695628843 404416030528238534543443265)
    ·
      refine ⟨303312022896178900907582449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404416030528238534543443265 303312022896178900907582449)
      ·
        refine ⟨227484017172134175680686837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303312022896178900907582449 227484017172134175680686837)
        ·
          refine ⟨21326626609887578970064391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 227484017172134175680686837 21326626609887578970064391)
          ·
            refine ⟨31989939914831368455096587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21326626609887578970064391 31989939914831368455096587)
            ·
              refine ⟨47984909872247052682644881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31989939914831368455096587 47984909872247052682644881)
              ·
                refine ⟨35988682404185289511983661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47984909872247052682644881 35988682404185289511983661)
                ·
                  refine ⟨13495755901569483566993873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35988682404185289511983661 13495755901569483566993873)
                  ·
                    refine ⟨10121816926177112675245405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13495755901569483566993873 10121816926177112675245405)
                    ·
                      refine ⟨3795681347316417253217027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10121816926177112675245405 3795681347316417253217027)
                      ·
                        rfl

theorem cell23_7392063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_7392063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392063 prefixEnd_7392063 := by exact prefixLift 7392063
  have htrace : WordTrace (prefixWord ++ tailWord_7392063) baseStart_7392063 baseEnd_7392063 := by
    simpa [prefixWord, tailWord_7392063, baseEnd_7392063] using wordTrace_append hprefix tailTrace_7392063
  have hstable : (prefixWord ++ tailWord_7392063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392063).length < 2 ^ (prefixWord ++ tailWord_7392063).sum := by decide
  have hdescent : baseEnd_7392063 < baseStart_7392063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392073 : List Nat := [1, 2, 1, 1, 2, 6, 2, 1, 1, 2, 4]
def baseStart_7392073 : Nat := 118140960795 + 7392073 * 2 ^ 59
def prefixEnd_7392073 : Nat := 4983230072969 + 3 ^ 40 * 7392073 * 2
def baseEnd_7392073 : Nat := 3795686482122962214091981

theorem tailTrace_7392073 : CollatzResearch.WordTrace tailWord_7392073 prefixEnd_7392073 3795686482122962214091981 := by
  unfold tailWord_7392073
  simp only [CollatzResearch.WordTrace]
  refine ⟨269611051748789461403492873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179740701165859640935661915 269611051748789461403492873)
  ·
    refine ⟨202208288811592096052619655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269611051748789461403492873 202208288811592096052619655)
    ·
      refine ⟨303312433217388144078929483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202208288811592096052619655 303312433217388144078929483)
      ·
        refine ⟨454968649826082216118394225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303312433217388144078929483 454968649826082216118394225)
        ·
          refine ⟨341226487369561662088795669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454968649826082216118394225 341226487369561662088795669)
          ·
            refine ⟨15994991595448202910412297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 341226487369561662088795669 15994991595448202910412297)
            ·
              refine ⟨11996243696586152182809223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15994991595448202910412297 11996243696586152182809223)
              ·
                refine ⟨17994365544879228274213835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11996243696586152182809223 17994365544879228274213835)
                ·
                  refine ⟨26991548317318842411320753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17994365544879228274213835 26991548317318842411320753)
                  ·
                    refine ⟨20243661237989131808490565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26991548317318842411320753 20243661237989131808490565)
                    ·
                      refine ⟨3795686482122962214091981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20243661237989131808490565 3795686482122962214091981)
                      ·
                        rfl

theorem cell23_7392073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 2, 4].length) (baseStart_7392073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392073 prefixEnd_7392073 := by exact prefixLift 7392073
  have htrace : WordTrace (prefixWord ++ tailWord_7392073) baseStart_7392073 baseEnd_7392073 := by
    simpa [prefixWord, tailWord_7392073, baseEnd_7392073] using wordTrace_append hprefix tailTrace_7392073
  have hstable : (prefixWord ++ tailWord_7392073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392073).length < 2 ^ (prefixWord ++ tailWord_7392073).sum := by decide
  have hdescent : baseEnd_7392073 < baseStart_7392073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392137 : List Nat := [1, 2, 1, 1, 5, 3, 2, 2, 1, 3, 2]
def baseStart_7392137 : Nat := 118140960795 + 7392137 * 2 ^ 59
def prefixEnd_7392137 : Nat := 4983230072969 + 3 ^ 40 * 7392137 * 2
def baseEnd_7392137 : Nat := 3795719344884849963691687

theorem tailTrace_7392137 : CollatzResearch.WordTrace tailWord_7392137 prefixEnd_7392137 3795719344884849963691687 := by
  unfold tailWord_7392137
  simp only [CollatzResearch.WordTrace]
  refine ⟨269613386020557600333822665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179742257347038400222548443 269613386020557600333822665)
  ·
    refine ⟨202210039515418200250366999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269613386020557600333822665 202210039515418200250366999)
    ·
      refine ⟨303315059273127300375550499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202210039515418200250366999 303315059273127300375550499)
      ·
        refine ⟨454972588909690950563325749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303315059273127300375550499 454972588909690950563325749)
        ·
          refine ⟨42653680210283526615311789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 454972588909690950563325749 42653680210283526615311789)
          ·
            refine ⟨15995130078856322480741921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42653680210283526615311789 15995130078856322480741921)
            ·
              refine ⟨11996347559142241860556441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15995130078856322480741921 11996347559142241860556441)
              ·
                refine ⟨8997260669356681395417331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11996347559142241860556441 8997260669356681395417331)
                ·
                  refine ⟨13495891004035022093125997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8997260669356681395417331 13495891004035022093125997)
                  ·
                    refine ⟨5060959126513133284922249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13495891004035022093125997 5060959126513133284922249)
                    ·
                      refine ⟨3795719344884849963691687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5060959126513133284922249 3795719344884849963691687)
                      ·
                        rfl

theorem cell23_7392137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 3, 2].length) (baseStart_7392137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392137 prefixEnd_7392137 := by exact prefixLift 7392137
  have htrace : WordTrace (prefixWord ++ tailWord_7392137) baseStart_7392137 baseEnd_7392137 := by
    simpa [prefixWord, tailWord_7392137, baseEnd_7392137] using wordTrace_append hprefix tailTrace_7392137
  have hstable : (prefixWord ++ tailWord_7392137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392137).length < 2 ^ (prefixWord ++ tailWord_7392137).sum := by decide
  have hdescent : baseEnd_7392137 < baseStart_7392137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392183 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 3]
def baseStart_7392183 : Nat := 118140960795 + 7392183 * 2 ^ 59
def prefixEnd_7392183 : Nat := 4983230072969 + 3 ^ 40 * 7392183 * 2
def baseEnd_7392183 : Nat := 3795742964994956783716475

theorem tailTrace_7392183 : CollatzResearch.WordTrace tailWord_7392183 prefixEnd_7392183 3795742964994956783716475 := by
  unfold tailWord_7392183
  simp only [CollatzResearch.WordTrace]
  refine ⟨269615063778390950189997203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179743375852260633459998135 269615063778390950189997203)
  ·
    refine ⟨404422595667586425284995805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269615063778390950189997203 404422595667586425284995805)
    ·
      refine ⟨151658473375344909481873427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404422595667586425284995805 151658473375344909481873427)
      ·
        refine ⟨227487710063017364222810141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151658473375344909481873427 227487710063017364222810141)
        ·
          refine ⟨85307891273631511583553803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227487710063017364222810141 85307891273631511583553803)
          ·
            refine ⟨127961836910447267375330705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85307891273631511583553803 127961836910447267375330705)
            ·
              refine ⟨95971377682835450531498029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127961836910447267375330705 95971377682835450531498029)
              ·
                refine ⟨35989266631063293949311761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95971377682835450531498029 35989266631063293949311761)
                ·
                  refine ⟨26991949973297470461983821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35989266631063293949311761 26991949973297470461983821)
                  ·
                    refine ⟨10121981239986551423243933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26991949973297470461983821 10121981239986551423243933)
                    ·
                      refine ⟨3795742964994956783716475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10121981239986551423243933 3795742964994956783716475)
                      ·
                        rfl

theorem cell23_7392183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_7392183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392183 prefixEnd_7392183 := by exact prefixLift 7392183
  have htrace : WordTrace (prefixWord ++ tailWord_7392183) baseStart_7392183 baseEnd_7392183 := by
    simpa [prefixWord, tailWord_7392183, baseEnd_7392183] using wordTrace_append hprefix tailTrace_7392183
  have hstable : (prefixWord ++ tailWord_7392183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392183).length < 2 ^ (prefixWord ++ tailWord_7392183).sum := by decide
  have hdescent : baseEnd_7392183 < baseStart_7392183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392184 : List Nat := [2, 1, 2, 1, 2, 4, 4, 1, 2, 2, 2]
def baseStart_7392184 : Nat := 118140960795 + 7392184 * 2 ^ 59
def prefixEnd_7392184 : Nat := 4983230072969 + 3 ^ 40 * 7392184 * 2
def baseEnd_7392184 : Nat := 3795743478475611279803971

theorem tailTrace_7392184 : CollatzResearch.WordTrace tailWord_7392184 prefixEnd_7392184 3795743478475611279803971 := by
  unfold tailWord_7392184
  simp only [CollatzResearch.WordTrace]
  refine ⟨134807550125693663680391803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179743400167591551573855737 134807550125693663680391803)
  ·
    refine ⟨202211325188540495520587705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134807550125693663680391803 202211325188540495520587705)
    ·
      refine ⟨151658493891405371640440779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202211325188540495520587705 151658493891405371640440779)
      ·
        refine ⟨227487740837108057460661169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151658493891405371640440779 227487740837108057460661169)
        ·
          refine ⟨170615805627831043095495877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227487740837108057460661169 170615805627831043095495877)
          ·
            refine ⟨31990463555218320580405477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170615805627831043095495877 31990463555218320580405477)
            ·
              refine ⟨5998211916603435108826027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31990463555218320580405477 5998211916603435108826027)
              ·
                refine ⟨8997317874905152663239041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5998211916603435108826027 8997317874905152663239041)
                ·
                  refine ⟨6747988406178864497429281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8997317874905152663239041 6747988406178864497429281)
                  ·
                    refine ⟨5060991304634148373071961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6747988406178864497429281 5060991304634148373071961)
                    ·
                      refine ⟨3795743478475611279803971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5060991304634148373071961 3795743478475611279803971)
                      ·
                        rfl

theorem cell23_7392184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 2, 2, 2].length) (baseStart_7392184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392184 prefixEnd_7392184 := by exact prefixLift 7392184
  have htrace : WordTrace (prefixWord ++ tailWord_7392184) baseStart_7392184 baseEnd_7392184 := by
    simpa [prefixWord, tailWord_7392184, baseEnd_7392184] using wordTrace_append hprefix tailTrace_7392184
  have hstable : (prefixWord ++ tailWord_7392184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392184).length < 2 ^ (prefixWord ++ tailWord_7392184).sum := by decide
  have hdescent : baseEnd_7392184 < baseStart_7392184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392203 : List Nat := [1, 1, 1, 1, 3, 5, 1, 3, 2, 5]
def baseStart_7392203 : Nat := 118140960795 + 7392203 * 2 ^ 59
def prefixEnd_7392203 : Nat := 4983230072969 + 3 ^ 40 * 7392203 * 2
def baseEnd_7392203 : Nat := 1265251078202682235155461

theorem tailTrace_7392203 : CollatzResearch.WordTrace tailWord_7392203 prefixEnd_7392203 1265251078202682235155461 := by
  unfold tailWord_7392203
  simp only [CollatzResearch.WordTrace]
  refine ⟨269615793238318493605725263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179743862158878995737150175 269615793238318493605725263)
  ·
    refine ⟨404423689857477740408587895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269615793238318493605725263 404423689857477740408587895)
    ·
      refine ⟨606635534786216610612881843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404423689857477740408587895 606635534786216610612881843)
      ·
        refine ⟨909953302179324915919322765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606635534786216610612881843 909953302179324915919322765)
        ·
          refine ⟨341232488317246843469746037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 909953302179324915919322765 341232488317246843469746037)
          ·
            refine ⟨31990545779741891575288691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 341232488317246843469746037 31990545779741891575288691)
            ·
              refine ⟨47985818669612837362933037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31990545779741891575288691 47985818669612837362933037)
              ·
                refine ⟨17994682001104814011099889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47985818669612837362933037 17994682001104814011099889)
                ·
                  refine ⟨13496011500828610508324917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17994682001104814011099889 13496011500828610508324917)
                  ·
                    refine ⟨1265251078202682235155461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13496011500828610508324917 1265251078202682235155461)
                    ·
                      rfl

theorem cell23_7392203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 5].length) (baseStart_7392203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392203 prefixEnd_7392203 := by exact prefixLift 7392203
  have htrace : WordTrace (prefixWord ++ tailWord_7392203) baseStart_7392203 baseEnd_7392203 := by
    simpa [prefixWord, tailWord_7392203, baseEnd_7392203] using wordTrace_append hprefix tailTrace_7392203
  have hstable : (prefixWord ++ tailWord_7392203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392203).length < 2 ^ (prefixWord ++ tailWord_7392203).sum := by decide
  have hdescent : baseEnd_7392203 < baseStart_7392203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392205 : List Nat := [1, 6, 3, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_7392205 : Nat := 118140960795 + 7392205 * 2 ^ 59
def prefixEnd_7392205 : Nat := 4983230072969 + 3 ^ 40 * 7392205 * 2
def baseEnd_7392205 : Nat := 3795754261569355697641375

theorem tailTrace_7392205 : CollatzResearch.WordTrace tailWord_7392205 prefixEnd_7392205 3795754261569355697641375 := by
  unfold tailWord_7392205
  simp only [CollatzResearch.WordTrace]
  refine ⟨269615866184311247947298069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179743910789540831964865379 269615866184311247947298069)
  ·
    refine ⟨12638243727389589747529597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 269615866184311247947298069 12638243727389589747529597)
    ·
      refine ⟨4739341397771096155323599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12638243727389589747529597 4739341397771096155323599)
      ·
        refine ⟨7109012096656644232985399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4739341397771096155323599 7109012096656644232985399)
        ·
          refine ⟨10663518144984966349478099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7109012096656644232985399 10663518144984966349478099)
          ·
            refine ⟨15995277217477449524217149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10663518144984966349478099 15995277217477449524217149)
            ·
              refine ⟨5998228956554043571581431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15995277217477449524217149 5998228956554043571581431)
              ·
                refine ⟨8997343434831065357372147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5998228956554043571581431 8997343434831065357372147)
                ·
                  refine ⟨13496015152246598036058221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8997343434831065357372147 13496015152246598036058221)
                  ·
                    refine ⟨5061005682092474263521833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13496015152246598036058221 5061005682092474263521833)
                    ·
                      refine ⟨3795754261569355697641375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5061005682092474263521833 3795754261569355697641375)
                      ·
                        rfl

theorem cell23_7392205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_7392205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392205 prefixEnd_7392205 := by exact prefixLift 7392205
  have htrace : WordTrace (prefixWord ++ tailWord_7392205) baseStart_7392205 baseEnd_7392205 := by
    simpa [prefixWord, tailWord_7392205, baseEnd_7392205] using wordTrace_append hprefix tailTrace_7392205
  have hstable : (prefixWord ++ tailWord_7392205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392205).length < 2 ^ (prefixWord ++ tailWord_7392205).sum := by decide
  have hdescent : baseEnd_7392205 < baseStart_7392205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392233 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 9, 4]
def baseStart_7392233 : Nat := 118140960795 + 7392233 * 2 ^ 59
def prefixEnd_7392233 : Nat := 4983230072969 + 3 ^ 40 * 7392233 * 2
def baseEnd_7392233 : Nat := 1265256213009227196030415

theorem tailTrace_7392233 : CollatzResearch.WordTrace tailWord_7392233 prefixEnd_7392233 1265256213009227196030415 := by
  unfold tailWord_7392233
  simp only [CollatzResearch.WordTrace]
  refine ⟨269616887428209808729317353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179744591618806539152878235 269616887428209808729317353)
  ·
    refine ⟨202212665571157356546988015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269616887428209808729317353 202212665571157356546988015)
    ·
      refine ⟨303318998356736034820482023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202212665571157356546988015 303318998356736034820482023)
      ·
        refine ⟨454978497535104052230723035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303318998356736034820482023 454978497535104052230723035)
        ·
          refine ⟨682467746302656078346084553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454978497535104052230723035 682467746302656078346084553)
          ·
            refine ⟨511850809726992058759563415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682467746302656078346084553 511850809726992058759563415)
            ·
              refine ⟨767776214590488088139345123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511850809726992058759563415 767776214590488088139345123)
              ·
                refine ⟨1151664321885732132209017685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767776214590488088139345123 1151664321885732132209017685)
                ·
                  refine ⟨6748033136049211712162213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1151664321885732132209017685 6748033136049211712162213)
                  ·
                    refine ⟨1265256213009227196030415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6748033136049211712162213 1265256213009227196030415)
                    ·
                      rfl

theorem cell23_7392233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 4].length) (baseStart_7392233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392233 prefixEnd_7392233 := by exact prefixLift 7392233
  have htrace : WordTrace (prefixWord ++ tailWord_7392233) baseStart_7392233 baseEnd_7392233 := by
    simpa [prefixWord, tailWord_7392233, baseEnd_7392233] using wordTrace_append hprefix tailTrace_7392233
  have hstable : (prefixWord ++ tailWord_7392233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392233).length < 2 ^ (prefixWord ++ tailWord_7392233).sum := by decide
  have hdescent : baseEnd_7392233 < baseStart_7392233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392254 : List Nat := [4, 2, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_7392254 : Nat := 118140960795 + 7392254 * 2 ^ 59
def prefixEnd_7392254 : Nat := 4983230072969 + 3 ^ 40 * 7392254 * 2
def baseEnd_7392254 : Nat := 1265259807373808668642883

theorem tailTrace_7392254 : CollatzResearch.WordTrace tailWord_7392254 prefixEnd_7392254 1265259807373808668642883 := by
  unfold tailWord_7392254
  simp only [CollatzResearch.WordTrace]
  refine ⟨33702206670141716164478977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179745102240755819543887877 33702206670141716164478977)
  ·
    refine ⟨25276655002606287123359233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33702206670141716164478977 25276655002606287123359233)
    ·
      refine ⟨18957491251954715342519425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25276655002606287123359233 18957491251954715342519425)
      ·
        refine ⟨14218118438966036506889569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18957491251954715342519425 14218118438966036506889569)
        ·
          refine ⟨10663588829224527380167177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14218118438966036506889569 10663588829224527380167177)
          ·
            refine ⟨7997691621918395535125383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10663588829224527380167177 7997691621918395535125383)
            ·
              refine ⟨11996537432877593302688075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7997691621918395535125383 11996537432877593302688075)
              ·
                refine ⟨17994806149316389954032113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11996537432877593302688075 17994806149316389954032113)
                ·
                  refine ⟨13496104611987292465524085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17994806149316389954032113 13496104611987292465524085)
                  ·
                    refine ⟨1265259807373808668642883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13496104611987292465524085 1265259807373808668642883)
                    ·
                      rfl

theorem cell23_7392254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_7392254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392254 prefixEnd_7392254 := by exact prefixLift 7392254
  have htrace : WordTrace (prefixWord ++ tailWord_7392254) baseStart_7392254 baseEnd_7392254 := by
    simpa [prefixWord, tailWord_7392254, baseEnd_7392254] using wordTrace_append hprefix tailTrace_7392254
  have hstable : (prefixWord ++ tailWord_7392254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392254).length < 2 ^ (prefixWord ++ tailWord_7392254).sum := by decide
  have hdescent : baseEnd_7392254 < baseStart_7392254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392257 : List Nat := [1, 2, 4, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_7392257 : Nat := 118140960795 + 7392257 * 2 ^ 59
def prefixEnd_7392257 : Nat := 4983230072969 + 3 ^ 40 * 7392257 * 2
def baseEnd_7392257 : Nat := 3795780962563389494191135

theorem tailTrace_7392257 : CollatzResearch.WordTrace tailWord_7392257 prefixEnd_7392257 3795780962563389494191135 := by
  unfold tailWord_7392257
  simp only [CollatzResearch.WordTrace]
  refine ⟨269617762780122860828191025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179745175186748573885460683 269617762780122860828191025)
  ·
    refine ⟨202213322085092145621143269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269617762780122860828191025 202213322085092145621143269)
    ·
      refine ⟨37914997890954777303964363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202213322085092145621143269 37914997890954777303964363)
      ·
        refine ⟨56872496836432165955946545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37914997890954777303964363 56872496836432165955946545)
        ·
          refine ⟨42654372627324124466959909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56872496836432165955946545 42654372627324124466959909)
          ·
            refine ⟨7997694867623273337554983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42654372627324124466959909 7997694867623273337554983)
            ·
              refine ⟨11996542301434910006332475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7997694867623273337554983 11996542301434910006332475)
              ·
                refine ⟨17994813452152365009498713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11996542301434910006332475 17994813452152365009498713)
                ·
                  refine ⟨13496110089114273757124035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17994813452152365009498713 13496110089114273757124035)
                  ·
                    refine ⟨20244165133671410635686053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13496110089114273757124035 20244165133671410635686053)
                    ·
                      refine ⟨3795780962563389494191135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20244165133671410635686053 3795780962563389494191135)
                      ·
                        rfl

theorem cell23_7392257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_7392257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392257 prefixEnd_7392257 := by exact prefixLift 7392257
  have htrace : WordTrace (prefixWord ++ tailWord_7392257) baseStart_7392257 baseEnd_7392257 := by
    simpa [prefixWord, tailWord_7392257, baseEnd_7392257] using wordTrace_append hprefix tailTrace_7392257
  have hstable : (prefixWord ++ tailWord_7392257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392257).length < 2 ^ (prefixWord ++ tailWord_7392257).sum := by decide
  have hdescent : baseEnd_7392257 < baseStart_7392257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392263 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 8]
def baseStart_7392263 : Nat := 118140960795 + 7392263 * 2 ^ 59
def prefixEnd_7392263 : Nat := 4983230072969 + 3 ^ 40 * 7392263 * 2
def baseEnd_7392263 : Nat := 421753782605257385635123

theorem tailTrace_7392263 : CollatzResearch.WordTrace tailWord_7392263 prefixEnd_7392263 421753782605257385635123 := by
  unfold tailWord_7392263
  simp only [CollatzResearch.WordTrace]
  refine ⟨269617981618101123852909443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179745321078734082568606295 269617981618101123852909443)
  ·
    refine ⟨404426972427151685779364165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269617981618101123852909443 404426972427151685779364165)
    ·
      refine ⟨75830057330090941083630781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 404426972427151685779364165 75830057330090941083630781)
      ·
        refine ⟨28436271498784102906361543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75830057330090941083630781 28436271498784102906361543)
        ·
          refine ⟨42654407248176154359542315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28436271498784102906361543 42654407248176154359542315)
          ·
            refine ⟨63981610872264231539313473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42654407248176154359542315 63981610872264231539313473)
            ·
              refine ⟨47986208154198173654485105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63981610872264231539313473 47986208154198173654485105)
              ·
                refine ⟨35989656115648630240863829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47986208154198173654485105 35989656115648630240863829)
                ·
                  refine ⟨421753782605257385635123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35989656115648630240863829 421753782605257385635123)
                  ·
                    rfl

theorem cell23_7392263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 8].length) (baseStart_7392263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392263 prefixEnd_7392263 := by exact prefixLift 7392263
  have htrace : WordTrace (prefixWord ++ tailWord_7392263) baseStart_7392263 baseEnd_7392263 := by
    simpa [prefixWord, tailWord_7392263, baseEnd_7392263] using wordTrace_append hprefix tailTrace_7392263
  have hstable : (prefixWord ++ tailWord_7392263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392263).length < 2 ^ (prefixWord ++ tailWord_7392263).sum := by decide
  have hdescent : baseEnd_7392263 < baseStart_7392263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392267 : List Nat := [1, 1, 1, 1, 6, 2, 1, 5, 1, 4]
def baseStart_7392267 : Nat := 118140960795 + 7392267 * 2 ^ 59
def prefixEnd_7392267 : Nat := 4983230072969 + 3 ^ 40 * 7392267 * 2
def baseEnd_7392267 : Nat := 1265262032456644818355363

theorem tailTrace_7392267 : CollatzResearch.WordTrace tailWord_7392267 prefixEnd_7392267 1265262032456644818355363 := by
  unfold tailWord_7392267
  simp only [CollatzResearch.WordTrace]
  refine ⟨269618127510086632536055055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179745418340057755024036703 269618127510086632536055055)
  ·
    refine ⟨404427191265129948804082583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269618127510086632536055055 404427191265129948804082583)
    ·
      refine ⟨606640786897694923206123875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404427191265129948804082583 606640786897694923206123875)
      ·
        refine ⟨909961180346542384809185813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606640786897694923206123875 909961180346542384809185813)
        ·
          refine ⟨42654430328744174287930585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 909961180346542384809185813 42654430328744174287930585)
          ·
            refine ⟨31990822746558130715947939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42654430328744174287930585 31990822746558130715947939)
            ·
              refine ⟨47986234119837196073921909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31990822746558130715947939 47986234119837196073921909)
              ·
                refine ⟨4498709448734737131930179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47986234119837196073921909 4498709448734737131930179)
                ·
                  refine ⟨6748064173102105697895269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4498709448734737131930179 6748064173102105697895269)
                  ·
                    refine ⟨1265262032456644818355363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6748064173102105697895269 1265262032456644818355363)
                    ·
                      rfl

theorem cell23_7392267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 1, 4].length) (baseStart_7392267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392267 prefixEnd_7392267 := by exact prefixLift 7392267
  have htrace : WordTrace (prefixWord ++ tailWord_7392267) baseStart_7392267 baseEnd_7392267 := by
    simpa [prefixWord, tailWord_7392267, baseEnd_7392267] using wordTrace_append hprefix tailTrace_7392267
  have hstable : (prefixWord ++ tailWord_7392267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392267).length < 2 ^ (prefixWord ++ tailWord_7392267).sum := by decide
  have hdescent : baseEnd_7392267 < baseStart_7392267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392273 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 3]
def baseStart_7392273 : Nat := 118140960795 + 7392273 * 2 ^ 59
def prefixEnd_7392273 : Nat := 4983230072969 + 3 ^ 40 * 7392273 * 2
def baseEnd_7392273 : Nat := 3795789178253861431591061

theorem tailTrace_7392273 : CollatzResearch.WordTrace tailWord_7392273 prefixEnd_7392273 3795789178253861431591061 := by
  unfold tailWord_7392273
  simp only [CollatzResearch.WordTrace]
  refine ⟨269618346348064895560773473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179745564232043263707182315 269618346348064895560773473)
  ·
    refine ⟨202213759761048671670580105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269618346348064895560773473 202213759761048671670580105)
    ·
      refine ⟨151660319820786503752935079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202213759761048671670580105 151660319820786503752935079)
      ·
        refine ⟨227490479731179755629402619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151660319820786503752935079 227490479731179755629402619)
        ·
          refine ⟨341235719596769633444103929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227490479731179755629402619 341235719596769633444103929)
          ·
            refine ⟨255926789697577225083077947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341235719596769633444103929 255926789697577225083077947)
            ·
              refine ⟨383890184546365837624616921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255926789697577225083077947 383890184546365837624616921)
              ·
                refine ⟨287917638409774378218462691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383890184546365837624616921 287917638409774378218462691)
                ·
                  refine ⟨431876457614661567327694037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287917638409774378218462691 431876457614661567327694037)
                  ·
                    refine ⟨10122104475343630484242829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 431876457614661567327694037 10122104475343630484242829)
                    ·
                      refine ⟨3795789178253861431591061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10122104475343630484242829 3795789178253861431591061)
                      ·
                        rfl

theorem cell23_7392273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_7392273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392273 prefixEnd_7392273 := by exact prefixLift 7392273
  have htrace : WordTrace (prefixWord ++ tailWord_7392273) baseStart_7392273 baseEnd_7392273 := by
    simpa [prefixWord, tailWord_7392273, baseEnd_7392273] using wordTrace_append hprefix tailTrace_7392273
  have hstable : (prefixWord ++ tailWord_7392273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392273).length < 2 ^ (prefixWord ++ tailWord_7392273).sum := by decide
  have hdescent : baseEnd_7392273 < baseStart_7392273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392280 : List Nat := [2, 1, 2, 3, 2, 2, 3, 2, 6]
def baseStart_7392280 : Nat := 118140960795 + 7392280 * 2 ^ 59
def prefixEnd_7392280 : Nat := 4983230072969 + 3 ^ 40 * 7392280 * 2
def baseEnd_7392280 : Nat := 421754752513160322689281

theorem tailTrace_7392280 : CollatzResearch.WordTrace tailWord_7392280 prefixEnd_7392280 421754752513160322689281 := by
  unfold tailWord_7392280
  simp only [CollatzResearch.WordTrace]
  refine ⟨134809300829519767878139147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179745734439359690504185529 134809300829519767878139147)
  ·
    refine ⟨202213951244279651817208721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134809300829519767878139147 202213951244279651817208721)
    ·
      refine ⟨151660463433209738862906541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202213951244279651817208721 151660463433209738862906541)
      ·
        refine ⟨56872673787453652073589953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151660463433209738862906541 56872673787453652073589953)
        ·
          refine ⟨42654505340590239055192465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56872673787453652073589953 42654505340590239055192465)
          ·
            refine ⟨31990879005442679291394349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42654505340590239055192465 31990879005442679291394349)
            ·
              refine ⟨11996579627041004734272881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31990879005442679291394349 11996579627041004734272881)
              ·
                refine ⟨8997434720280753550704661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11996579627041004734272881 8997434720280753550704661)
                ·
                  refine ⟨421754752513160322689281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8997434720280753550704661 421754752513160322689281)
                  ·
                    rfl

theorem cell23_7392280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 6].length) (baseStart_7392280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392280 prefixEnd_7392280 := by exact prefixLift 7392280
  have htrace : WordTrace (prefixWord ++ tailWord_7392280) baseStart_7392280 baseEnd_7392280 := by
    simpa [prefixWord, tailWord_7392280, baseEnd_7392280] using wordTrace_append hprefix tailTrace_7392280
  have hstable : (prefixWord ++ tailWord_7392280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392280).length < 2 ^ (prefixWord ++ tailWord_7392280).sum := by decide
  have hdescent : baseEnd_7392280 < baseStart_7392280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392300 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 3, 5, 2]
def baseStart_7392300 : Nat := 118140960795 + 7392300 * 2 ^ 59
def prefixEnd_7392300 : Nat := 4983230072969 + 3 ^ 40 * 7392300 * 2
def baseEnd_7392300 : Nat := 3795803042231532825953437

theorem tailTrace_7392300 : CollatzResearch.WordTrace tailWord_7392300 prefixEnd_7392300 3795803042231532825953437 := by
  unfold tailWord_7392300
  simp only [CollatzResearch.WordTrace]
  refine ⟨134809665559483539586003177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179746220745978052781337569 134809665559483539586003177)
  ·
    refine ⟨101107249169612654689502383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134809665559483539586003177 101107249169612654689502383)
    ·
      refine ⟨151660873754418982034253575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101107249169612654689502383 151660873754418982034253575)
      ·
        refine ⟨227491310631628473051380363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151660873754418982034253575 227491310631628473051380363)
        ·
          refine ⟨341236965947442709577070545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227491310631628473051380363 341236965947442709577070545)
          ·
            refine ⟨255927724460582032182802909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341236965947442709577070545 255927724460582032182802909)
            ·
              refine ⟨95972896672718262068551091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255927724460582032182802909 95972896672718262068551091)
              ·
                refine ⟨143959345009077393102826637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95972896672718262068551091 143959345009077393102826637)
                ·
                  refine ⟨53984754378404022413559989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143959345009077393102826637 53984754378404022413559989)
                  ·
                    refine ⟨5061070722975377101271249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53984754378404022413559989 5061070722975377101271249)
                    ·
                      refine ⟨3795803042231532825953437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5061070722975377101271249 3795803042231532825953437)
                      ·
                        rfl

theorem cell23_7392300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 5, 2].length) (baseStart_7392300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392300 prefixEnd_7392300 := by exact prefixLift 7392300
  have htrace : WordTrace (prefixWord ++ tailWord_7392300) baseStart_7392300 baseEnd_7392300 := by
    simpa [prefixWord, tailWord_7392300, baseEnd_7392300] using wordTrace_append hprefix tailTrace_7392300
  have hstable : (prefixWord ++ tailWord_7392300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392300).length < 2 ^ (prefixWord ++ tailWord_7392300).sum := by decide
  have hdescent : baseEnd_7392300 < baseStart_7392300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392317 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 1, 5, 2]
def baseStart_7392317 : Nat := 118140960795 + 7392317 * 2 ^ 59
def prefixEnd_7392317 : Nat := 4983230072969 + 3 ^ 40 * 7392317 * 2
def baseEnd_7392317 : Nat := 3795811771402659259440859

theorem tailTrace_7392317 : CollatzResearch.WordTrace tailWord_7392317 prefixEnd_7392317 3795811771402659259440859 := by
  unfold tailWord_7392317
  simp only [CollatzResearch.WordTrace]
  refine ⟨269619951159905491075375205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179746634106603660716916803 269619951159905491075375205)
  ·
    refine ⟨50553740842482279576632851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269619951159905491075375205 50553740842482279576632851)
    ·
      refine ⟨75830611263723419364949277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50553740842482279576632851 75830611263723419364949277)
      ·
        refine ⟨28436479223896282261855979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75830611263723419364949277 28436479223896282261855979)
        ·
          refine ⟨42654718835844423392783969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28436479223896282261855979 42654718835844423392783969)
          ·
            refine ⟨31991039126883317544587977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42654718835844423392783969 31991039126883317544587977)
            ·
              refine ⟨23993279345162488158440983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31991039126883317544587977 23993279345162488158440983)
              ·
                refine ⟨35989919017743732237661475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23993279345162488158440983 35989919017743732237661475)
                ·
                  refine ⟨53984878526615598356492213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35989919017743732237661475 53984878526615598356492213)
                  ·
                    refine ⟨5061082361870212345921145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53984878526615598356492213 5061082361870212345921145)
                    ·
                      refine ⟨3795811771402659259440859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5061082361870212345921145 3795811771402659259440859)
                      ·
                        rfl

theorem cell23_7392317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_7392317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392317 prefixEnd_7392317 := by exact prefixLift 7392317
  have htrace : WordTrace (prefixWord ++ tailWord_7392317) baseStart_7392317 baseEnd_7392317 := by
    simpa [prefixWord, tailWord_7392317, baseEnd_7392317] using wordTrace_append hprefix tailTrace_7392317
  have hstable : (prefixWord ++ tailWord_7392317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392317).length < 2 ^ (prefixWord ++ tailWord_7392317).sum := by decide
  have hdescent : baseEnd_7392317 < baseStart_7392317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392323 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 3, 6]
def baseStart_7392323 : Nat := 118140960795 + 7392323 * 2 ^ 59
def prefixEnd_7392323 : Nat := 4983230072969 + 3 ^ 40 * 7392323 * 2
def baseEnd_7392323 : Nat := 1265271617428862078655277

theorem tailTrace_7392323 : CollatzResearch.WordTrace tailWord_7392323 prefixEnd_7392323 1265271617428862078655277 := by
  unfold tailWord_7392323
  simp only [CollatzResearch.WordTrace]
  refine ⟨269620169997883754100093623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179746779998589169400062415 269620169997883754100093623)
  ·
    refine ⟨404430254996825631150140435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269620169997883754100093623 404430254996825631150140435)
    ·
      refine ⟨606645382495238446725210653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404430254996825631150140435 606645382495238446725210653)
      ·
        refine ⟨227492018435714417521953995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 606645382495238446725210653 227492018435714417521953995)
        ·
          refine ⟨341238027653571626282930993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227492018435714417521953995 341238027653571626282930993)
          ·
            refine ⟨255928520740178719712198245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341238027653571626282930993 255928520740178719712198245)
            ·
              refine ⟨47986597638783509946037171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255928520740178719712198245 47986597638783509946037171)
              ·
                refine ⟨71979896458175264919055757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47986597638783509946037171 71979896458175264919055757)
                ·
                  refine ⟨26992461171815724344645909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71979896458175264919055757 26992461171815724344645909)
                  ·
                    refine ⟨1265271617428862078655277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26992461171815724344645909 1265271617428862078655277)
                    ·
                      rfl

theorem cell23_7392323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 6].length) (baseStart_7392323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392323 prefixEnd_7392323 := by exact prefixLift 7392323
  have htrace : WordTrace (prefixWord ++ tailWord_7392323) baseStart_7392323 baseEnd_7392323 := by
    simpa [prefixWord, tailWord_7392323, baseEnd_7392323] using wordTrace_append hprefix tailTrace_7392323
  have hstable : (prefixWord ++ tailWord_7392323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392323).length < 2 ^ (prefixWord ++ tailWord_7392323).sum := by decide
  have hdescent : baseEnd_7392323 < baseStart_7392323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392341 : List Nat := [1, 3, 2, 2, 1, 2, 5, 2, 1, 1, 3]
def baseStart_7392341 : Nat := 118140960795 + 7392341 * 2 ^ 59
def prefixEnd_7392341 : Nat := 4983230072969 + 3 ^ 40 * 7392341 * 2
def baseEnd_7392341 : Nat := 3795824094938367165540749

theorem tailTrace_7392341 : CollatzResearch.WordTrace tailWord_7392341 prefixEnd_7392341 3795824094938367165540749 := by
  unfold tailWord_7392341
  simp only [CollatzResearch.WordTrace]
  refine ⟨269620826511818543174248877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179747217674545695449499251 269620826511818543174248877)
  ·
    refine ⟨101107809941931953690343329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269620826511818543174248877 101107809941931953690343329)
    ·
      refine ⟨75830857456448965267757497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101107809941931953690343329 75830857456448965267757497)
      ·
        refine ⟨56873143092336723950818123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75830857456448965267757497 56873143092336723950818123)
        ·
          refine ⟨85309714638505085926227185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56873143092336723950818123 85309714638505085926227185)
          ·
            refine ⟨63982285978878814444670389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85309714638505085926227185 63982285978878814444670389)
            ·
              refine ⟨5998339310519888854187849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63982285978878814444670389 5998339310519888854187849)
              ·
                refine ⟨4498754482889916640640887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5998339310519888854187849 4498754482889916640640887)
                ·
                  refine ⟨6748131724334874960961331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4498754482889916640640887 6748131724334874960961331)
                  ·
                    refine ⟨10122197586502312441441997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6748131724334874960961331 10122197586502312441441997)
                    ·
                      refine ⟨3795824094938367165540749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10122197586502312441441997 3795824094938367165540749)
                      ·
                        rfl

theorem cell23_7392341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_7392341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392341 prefixEnd_7392341 := by exact prefixLift 7392341
  have htrace : WordTrace (prefixWord ++ tailWord_7392341) baseStart_7392341 baseEnd_7392341 := by
    simpa [prefixWord, tailWord_7392341, baseEnd_7392341] using wordTrace_append hprefix tailTrace_7392341
  have hstable : (prefixWord ++ tailWord_7392341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392341).length < 2 ^ (prefixWord ++ tailWord_7392341).sum := by decide
  have hdescent : baseEnd_7392341 < baseStart_7392341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392353 : List Nat := [1, 2, 3, 1, 1, 2, 3, 10]
def baseStart_7392353 : Nat := 118140960795 + 7392353 * 2 ^ 59
def prefixEnd_7392353 : Nat := 4983230072969 + 3 ^ 40 * 7392353 * 2
def baseEnd_7392353 : Nat := 140586305803934115503359

theorem tailTrace_7392353 : CollatzResearch.WordTrace tailWord_7392353 prefixEnd_7392353 140586305803934115503359 := by
  unfold tailWord_7392353
  simp only [CollatzResearch.WordTrace]
  refine ⟨269621264187775069223685713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179747509458516712815790475 269621264187775069223685713)
  ·
    refine ⟨202215948140831301917764285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269621264187775069223685713 202215948140831301917764285)
    ·
      refine ⟨75830980552811738219161607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202215948140831301917764285 75830980552811738219161607)
      ·
        refine ⟨113746470829217607328742411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75830980552811738219161607 113746470829217607328742411)
        ·
          refine ⟨170619706243826410993113617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113746470829217607328742411 170619706243826410993113617)
          ·
            refine ⟨127964779682869808244835213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170619706243826410993113617 127964779682869808244835213)
            ·
              refine ⟨47986792381076178091813205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127964779682869808244835213 47986792381076178091813205)
              ·
                refine ⟨140586305803934115503359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47986792381076178091813205 140586305803934115503359)
                ·
                  rfl

theorem cell23_7392353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 10].length) (baseStart_7392353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392353 prefixEnd_7392353 := by exact prefixLift 7392353
  have htrace : WordTrace (prefixWord ++ tailWord_7392353) baseStart_7392353 baseEnd_7392353 := by
    simpa [prefixWord, tailWord_7392353, baseEnd_7392353] using wordTrace_append hprefix tailTrace_7392353
  have hstable : (prefixWord ++ tailWord_7392353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392353).length < 2 ^ (prefixWord ++ tailWord_7392353).sum := by decide
  have hdescent : baseEnd_7392353 < baseStart_7392353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392357 : List Nat := [1, 3, 1, 3, 2, 1, 3, 3, 2, 4]
def baseStart_7392357 : Nat := 118140960795 + 7392357 * 2 ^ 59
def prefixEnd_7392357 : Nat := 4983230072969 + 3 ^ 40 * 7392357 * 2
def baseEnd_7392357 : Nat := 1265277436876279700980225

theorem tailTrace_7392357 : CollatzResearch.WordTrace tailWord_7392357 prefixEnd_7392357 1265277436876279700980225 := by
  unfold tailWord_7392357
  simp only [CollatzResearch.WordTrace]
  refine ⟨269621410079760577906831325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179747606719840385271220883 269621410079760577906831325)
  ·
    refine ⟨101108028779910216715061747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 269621410079760577906831325 101108028779910216715061747)
    ·
      refine ⟨151662043169865325072592621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101108028779910216715061747 151662043169865325072592621)
      ·
        refine ⟨56873266188699496902222233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151662043169865325072592621 56873266188699496902222233)
        ·
          refine ⟨42654949641524622676666675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56873266188699496902222233 42654949641524622676666675)
          ·
            refine ⟨63982424462286934015000013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42654949641524622676666675 63982424462286934015000013)
            ·
              refine ⟨23993409173357600255625005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63982424462286934015000013 23993409173357600255625005)
              ·
                refine ⟨8997528440009100095859377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23993409173357600255625005 8997528440009100095859377)
                ·
                  refine ⟨6748146330006825071894533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8997528440009100095859377 6748146330006825071894533)
                  ·
                    refine ⟨1265277436876279700980225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6748146330006825071894533 1265277436876279700980225)
                    ·
                      rfl

theorem cell23_7392357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_7392357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392357 prefixEnd_7392357 := by exact prefixLift 7392357
  have htrace : WordTrace (prefixWord ++ tailWord_7392357) baseStart_7392357 baseEnd_7392357 := by
    simpa [prefixWord, tailWord_7392357, baseEnd_7392357] using wordTrace_append hprefix tailTrace_7392357
  have hstable : (prefixWord ++ tailWord_7392357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392357).length < 2 ^ (prefixWord ++ tailWord_7392357).sum := by decide
  have hdescent : baseEnd_7392357 < baseStart_7392357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392377 : List Nat := [1, 2, 1, 3, 5, 1, 1, 2, 1, 2, 4]
def baseStart_7392377 : Nat := 118140960795 + 7392377 * 2 ^ 59
def prefixEnd_7392377 : Nat := 4983230072969 + 3 ^ 40 * 7392377 * 2
def baseEnd_7392377 : Nat := 3795842580241929024690583

theorem tailTrace_7392377 : CollatzResearch.WordTrace tailWord_7392377 prefixEnd_7392377 3795842580241929024690583 := by
  unfold tailWord_7392377
  simp only [CollatzResearch.WordTrace]
  refine ⟨269622139539688121322559385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179748093026458747548372923 269622139539688121322559385)
  ·
    refine ⟨202216604654766090991919539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269622139539688121322559385 202216604654766090991919539)
    ·
      refine ⟨303324906982149136487879309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202216604654766090991919539 303324906982149136487879309)
      ·
        refine ⟨113746840118305926182954741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303324906982149136487879309 113746840118305926182954741)
        ·
          refine ⟨10663766261091180579652007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113746840118305926182954741 10663766261091180579652007)
          ·
            refine ⟨15995649391636770869478011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10663766261091180579652007 15995649391636770869478011)
            ·
              refine ⟨23993474087455156304217017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15995649391636770869478011 23993474087455156304217017)
              ·
                refine ⟨17995105565591367228162763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23993474087455156304217017 17995105565591367228162763)
                ·
                  refine ⟨26992658348387050842244145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17995105565591367228162763 26992658348387050842244145)
                  ·
                    refine ⟨20244493761290288131683109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26992658348387050842244145 20244493761290288131683109)
                    ·
                      refine ⟨3795842580241929024690583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20244493761290288131683109 3795842580241929024690583)
                      ·
                        rfl

theorem cell23_7392377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_7392377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392377 prefixEnd_7392377 := by exact prefixLift 7392377
  have htrace : WordTrace (prefixWord ++ tailWord_7392377) baseStart_7392377 baseEnd_7392377 := by
    simpa [prefixWord, tailWord_7392377, baseEnd_7392377] using wordTrace_append hprefix tailTrace_7392377
  have hstable : (prefixWord ++ tailWord_7392377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392377).length < 2 ^ (prefixWord ++ tailWord_7392377).sum := by decide
  have hdescent : baseEnd_7392377 < baseStart_7392377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392381 : List Nat := [1, 4, 1, 1, 3, 1, 2, 5, 1, 2, 2]
def baseStart_7392381 : Nat := 118140960795 + 7392381 * 2 ^ 59
def prefixEnd_7392381 : Nat := 4983230072969 + 3 ^ 40 * 7392381 * 2
def baseEnd_7392381 : Nat := 3795844634164547009040565

theorem tailTrace_7392381 : CollatzResearch.WordTrace tailWord_7392381 prefixEnd_7392381 3795844634164547009040565 := by
  unfold tailWord_7392381
  simp only [CollatzResearch.WordTrace]
  refine ⟨269622285431673630005704997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179748190287782420003803331 269622285431673630005704997)
  ·
    refine ⟨50554178518438805626069687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 269622285431673630005704997 50554178518438805626069687)
    ·
      refine ⟨75831267777658208439104531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50554178518438805626069687 75831267777658208439104531)
      ·
        refine ⟨113746901666487312658656797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75831267777658208439104531 113746901666487312658656797)
        ·
          refine ⟨42655088124932742246996299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113746901666487312658656797 42655088124932742246996299)
          ·
            refine ⟨63982632187399113370494449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42655088124932742246996299 63982632187399113370494449)
            ·
              refine ⟨47986974140549335027870837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63982632187399113370494449 47986974140549335027870837)
              ·
                refine ⟨4498778825676500158862891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47986974140549335027870837 4498778825676500158862891)
                ·
                  refine ⟨6748168238514750238294337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4498778825676500158862891 6748168238514750238294337)
                  ·
                    refine ⟨5061126178886062678720753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6748168238514750238294337 5061126178886062678720753)
                    ·
                      refine ⟨3795844634164547009040565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5061126178886062678720753 3795844634164547009040565)
                      ·
                        rfl

theorem cell23_7392381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 1, 2, 2].length) (baseStart_7392381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392381 prefixEnd_7392381 := by exact prefixLift 7392381
  have htrace : WordTrace (prefixWord ++ tailWord_7392381) baseStart_7392381 baseEnd_7392381 := by
    simpa [prefixWord, tailWord_7392381, baseEnd_7392381] using wordTrace_append hprefix tailTrace_7392381
  have hstable : (prefixWord ++ tailWord_7392381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392381).length < 2 ^ (prefixWord ++ tailWord_7392381).sum := by decide
  have hdescent : baseEnd_7392381 < baseStart_7392381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392383 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 6, 7]
def baseStart_7392383 : Nat := 118140960795 + 7392383 * 2 ^ 59
def prefixEnd_7392383 : Nat := 4983230072969 + 3 ^ 40 * 7392383 * 2
def baseEnd_7392383 : Nat := 1265281887041952000405185

theorem tailTrace_7392383 : CollatzResearch.WordTrace tailWord_7392383 prefixEnd_7392383 1265281887041952000405185 := by
  unfold tailWord_7392383
  simp only [CollatzResearch.WordTrace]
  refine ⟨269622358377666384347277803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179748238918444256231518535 269622358377666384347277803)
  ·
    refine ⟨404433537566499576520916705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269622358377666384347277803 404433537566499576520916705)
    ·
      refine ⟨303325153174874682390687529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404433537566499576520916705 303325153174874682390687529)
      ·
        refine ⟨227493864881156011793015647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303325153174874682390687529 227493864881156011793015647)
        ·
          refine ⟨341240797321734017689523471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227493864881156011793015647 341240797321734017689523471)
          ·
            refine ⟨511861195982601026534285207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341240797321734017689523471 511861195982601026534285207)
            ·
              refine ⟨767791793973901539801427811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511861195982601026534285207 767791793973901539801427811)
              ·
                refine ⟨1151687690960852309702141717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767791793973901539801427811 1151687690960852309702141717)
                ·
                  refine ⟨53985360513789952017287893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1151687690960852309702141717 53985360513789952017287893)
                  ·
                    refine ⟨1265281887041952000405185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53985360513789952017287893 1265281887041952000405185)
                    ·
                      rfl

theorem cell23_7392383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 7].length) (baseStart_7392383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392383 prefixEnd_7392383 := by exact prefixLift 7392383
  have htrace : WordTrace (prefixWord ++ tailWord_7392383) baseStart_7392383 baseEnd_7392383 := by
    simpa [prefixWord, tailWord_7392383, baseEnd_7392383] using wordTrace_append hprefix tailTrace_7392383
  have hstable : (prefixWord ++ tailWord_7392383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392383).length < 2 ^ (prefixWord ++ tailWord_7392383).sum := by decide
  have hdescent : baseEnd_7392383 < baseStart_7392383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392398 : List Nat := [4, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2]
def baseStart_7392398 : Nat := 118140960795 + 7392398 * 2 ^ 59
def prefixEnd_7392398 : Nat := 4983230072969 + 3 ^ 40 * 7392398 * 2
def baseEnd_7392398 : Nat := 3795853363335673442527987

theorem tailTrace_7392398 : CollatzResearch.WordTrace tailWord_7392398 prefixEnd_7392398 3795853363335673442527987 := by
  unfold tailWord_7392398
  simp only [CollatzResearch.WordTrace]
  refine ⟨33702863184076505238634231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179748603648408027939382565 33702863184076505238634231)
  ·
    refine ⟨50554294776114757857951347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33702863184076505238634231 50554294776114757857951347)
    ·
      refine ⟨75831442164172136786927021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50554294776114757857951347 75831442164172136786927021)
      ·
        refine ⟨28436790811564551295097633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75831442164172136786927021 28436790811564551295097633)
        ·
          refine ⟨21327593108673413471323225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28436790811564551295097633 21327593108673413471323225)
          ·
            refine ⟨15995694831505060103492419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21327593108673413471323225 15995694831505060103492419)
            ·
              refine ⟨23993542247257590155238629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15995694831505060103492419 23993542247257590155238629)
              ·
                refine ⟨4498789171360798154107243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23993542247257590155238629 4498789171360798154107243)
                ·
                  refine ⟨6748183757041197231160865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4498789171360798154107243 6748183757041197231160865)
                  ·
                    refine ⟨5061137817780897923370649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6748183757041197231160865 5061137817780897923370649)
                    ·
                      refine ⟨3795853363335673442527987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5061137817780897923370649 3795853363335673442527987)
                      ·
                        rfl

theorem cell23_7392398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_7392398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392398 prefixEnd_7392398 := by exact prefixLift 7392398
  have htrace : WordTrace (prefixWord ++ tailWord_7392398) baseStart_7392398 baseEnd_7392398 := by
    simpa [prefixWord, tailWord_7392398, baseEnd_7392398] using wordTrace_append hprefix tailTrace_7392398
  have hstable : (prefixWord ++ tailWord_7392398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392398).length < 2 ^ (prefixWord ++ tailWord_7392398).sum := by decide
  have hdescent : baseEnd_7392398 < baseStart_7392398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392414 : List Nat := [4, 3, 1, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_7392414 : Nat := 118140960795 + 7392414 * 2 ^ 59
def prefixEnd_7392414 : Nat := 4983230072969 + 3 ^ 40 * 7392414 * 2
def baseEnd_7392414 : Nat := 3795861579026145379927913

theorem tailTrace_7392414 : CollatzResearch.WordTrace tailWord_7392414 prefixEnd_7392414 3795861579026145379927913 := by
  unfold tailWord_7392414
  simp only [CollatzResearch.WordTrace]
  refine ⟨33702936130069259580207037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179748992693702717761104197 33702936130069259580207037)
  ·
    refine ⟨12638601048775972342577639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33702936130069259580207037 12638601048775972342577639)
    ·
      refine ⟨18957901573163958513866459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12638601048775972342577639 18957901573163958513866459)
      ·
        refine ⟨28436852359745937770799689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18957901573163958513866459 28436852359745937770799689)
        ·
          refine ⟨21327639269809453328099767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28436852359745937770799689 21327639269809453328099767)
          ·
            refine ⟨31991458904714179992149651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21327639269809453328099767 31991458904714179992149651)
            ·
              refine ⟨47987188357071269988224477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31991458904714179992149651 47987188357071269988224477)
              ·
                refine ⟨17995195633901726245584179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47987188357071269988224477 17995195633901726245584179)
                ·
                  refine ⟨26992793450852589368376269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17995195633901726245584179 26992793450852589368376269)
                  ·
                    refine ⟨10122297544069721013141101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26992793450852589368376269 10122297544069721013141101)
                    ·
                      refine ⟨3795861579026145379927913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10122297544069721013141101 3795861579026145379927913)
                      ·
                        rfl

theorem cell23_7392414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_7392414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392414 prefixEnd_7392414 := by exact prefixLift 7392414
  have htrace : WordTrace (prefixWord ++ tailWord_7392414) baseStart_7392414 baseEnd_7392414 := by
    simpa [prefixWord, tailWord_7392414, baseEnd_7392414] using wordTrace_append hprefix tailTrace_7392414
  have hstable : (prefixWord ++ tailWord_7392414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392414).length < 2 ^ (prefixWord ++ tailWord_7392414).sum := by decide
  have hdescent : baseEnd_7392414 < baseStart_7392414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392440 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 1, 6, 3]
def baseStart_7392440 : Nat := 118140960795 + 7392440 * 2 ^ 59
def prefixEnd_7392440 : Nat := 4983230072969 + 3 ^ 40 * 7392440 * 2
def baseEnd_7392440 : Nat := 3795874929523162278202793

theorem tailTrace_7392440 : CollatzResearch.WordTrace tailWord_7392440 prefixEnd_7392440 3795874929523162278202793 := by
  unfold tailWord_7392440
  simp only [CollatzResearch.WordTrace]
  refine ⟨134812218669229941541051387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179749624892306588721401849 134812218669229941541051387)
  ·
    refine ⟨202218328003844912311577081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134812218669229941541051387 202218328003844912311577081)
    ·
      refine ⟨151663746002883684233682811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202218328003844912311577081 151663746002883684233682811)
      ·
        refine ⟨227495619004325526350524217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151663746002883684233682811 227495619004325526350524217)
        ·
          refine ⟨170621714253244144762893163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227495619004325526350524217 170621714253244144762893163)
          ·
            refine ⟨255932571379866217144339745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170621714253244144762893163 255932571379866217144339745)
            ·
              refine ⟨191949428534899662858254809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255932571379866217144339745 191949428534899662858254809)
              ·
                refine ⟨143962071401174747143691107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191949428534899662858254809 143962071401174747143691107)
                ·
                  refine ⟨215943107101762120715536661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143962071401174747143691107 215943107101762120715536661)
                  ·
                    refine ⟨10122333145395099408540781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 215943107101762120715536661 10122333145395099408540781)
                    ·
                      refine ⟨3795874929523162278202793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10122333145395099408540781 3795874929523162278202793)
                      ·
                        rfl

theorem cell23_7392440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_7392440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392440 prefixEnd_7392440 := by exact prefixLift 7392440
  have htrace : WordTrace (prefixWord ++ tailWord_7392440) baseStart_7392440 baseEnd_7392440 := by
    simpa [prefixWord, tailWord_7392440, baseEnd_7392440] using wordTrace_append hprefix tailTrace_7392440
  have hstable : (prefixWord ++ tailWord_7392440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392440).length < 2 ^ (prefixWord ++ tailWord_7392440).sum := by decide
  have hdescent : baseEnd_7392440 < baseStart_7392440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392441 : List Nat := [1, 2, 1, 4, 1, 3, 4, 1, 1, 3, 2]
def baseStart_7392441 : Nat := 118140960795 + 7392441 * 2 ^ 59
def prefixEnd_7392441 : Nat := 4983230072969 + 3 ^ 40 * 7392441 * 2
def baseEnd_7392441 : Nat := 3795875443003816774290289

theorem tailTrace_7392441 : CollatzResearch.WordTrace tailWord_7392441 prefixEnd_7392441 3795875443003816774290289 := by
  unfold tailWord_7392441
  simp only [CollatzResearch.WordTrace]
  refine ⟨269624473811456260252889177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179749649207637506835259451 269624473811456260252889177)
  ·
    refine ⟨202218355358592195189666883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269624473811456260252889177 202218355358592195189666883)
    ·
      refine ⟨303327533037888292784500325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202218355358592195189666883 303327533037888292784500325)
      ·
        refine ⟨56873912444604054897093811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303327533037888292784500325 56873912444604054897093811)
        ·
          refine ⟨85310868666906082345640717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56873912444604054897093811 85310868666906082345640717)
          ·
            refine ⟨31991575750089780879615269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85310868666906082345640717 31991575750089780879615269)
            ·
              refine ⟨5998420453141833914927863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31991575750089780879615269 5998420453141833914927863)
              ·
                refine ⟨8997630679712750872391795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5998420453141833914927863 8997630679712750872391795)
                ·
                  refine ⟨13496446019569126308587693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8997630679712750872391795 13496446019569126308587693)
                  ·
                    refine ⟨5061167257338422365720385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13496446019569126308587693 5061167257338422365720385)
                    ·
                      refine ⟨3795875443003816774290289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5061167257338422365720385 3795875443003816774290289)
                      ·
                        rfl

theorem cell23_7392441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_7392441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392441 prefixEnd_7392441 := by exact prefixLift 7392441
  have htrace : WordTrace (prefixWord ++ tailWord_7392441) baseStart_7392441 baseEnd_7392441 := by
    simpa [prefixWord, tailWord_7392441, baseEnd_7392441] using wordTrace_append hprefix tailTrace_7392441
  have hstable : (prefixWord ++ tailWord_7392441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392441).length < 2 ^ (prefixWord ++ tailWord_7392441).sum := by decide
  have hdescent : baseEnd_7392441 < baseStart_7392441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392448 : List Nat := [2, 1, 1, 2, 7, 1, 1, 2, 2, 1, 3]
def baseStart_7392448 : Nat := 118140960795 + 7392448 * 2 ^ 59
def prefixEnd_7392448 : Nat := 4983230072969 + 3 ^ 40 * 7392448 * 2
def baseEnd_7392448 : Nat := 3795879037368398246902757

theorem tailTrace_7392448 : CollatzResearch.WordTrace tailWord_7392448 prefixEnd_7392448 3795879037368398246902757 := by
  unfold tailWord_7392448
  simp only [CollatzResearch.WordTrace]
  refine ⟨134812364561215450224196999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179749819414953933632262665 134812364561215450224196999)
  ·
    refine ⟨202218546841823175336295499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134812364561215450224196999 202218546841823175336295499)
    ·
      refine ⟨303327820262734763004443249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202218546841823175336295499 303327820262734763004443249)
      ·
        refine ⟨227495865197051072253332437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303327820262734763004443249 227495865197051072253332437)
        ·
          refine ⟨5331934340555884505937479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 227495865197051072253332437 5331934340555884505937479)
          ·
            refine ⟨7997901510833826758906219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5331934340555884505937479 7997901510833826758906219)
            ·
              refine ⟨11996852266250740138359329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7997901510833826758906219 11996852266250740138359329)
              ·
                refine ⟨8997639199688055103769497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11996852266250740138359329 8997639199688055103769497)
                ·
                  refine ⟨6748229399766041327827123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8997639199688055103769497 6748229399766041327827123)
                  ·
                    refine ⟨10122344099649061991740685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6748229399766041327827123 10122344099649061991740685)
                    ·
                      refine ⟨3795879037368398246902757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10122344099649061991740685 3795879037368398246902757)
                      ·
                        rfl

theorem cell23_7392448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 2, 1, 3].length) (baseStart_7392448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392448 prefixEnd_7392448 := by exact prefixLift 7392448
  have htrace : WordTrace (prefixWord ++ tailWord_7392448) baseStart_7392448 baseEnd_7392448 := by
    simpa [prefixWord, tailWord_7392448, baseEnd_7392448] using wordTrace_append hprefix tailTrace_7392448
  have hstable : (prefixWord ++ tailWord_7392448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392448).length < 2 ^ (prefixWord ++ tailWord_7392448).sum := by decide
  have hdescent : baseEnd_7392448 < baseStart_7392448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392494 : List Nat := [4, 1, 2, 1, 1, 1, 5, 3, 5]
def baseStart_7392494 : Nat := 118140960795 + 7392494 * 2 ^ 59
def prefixEnd_7392494 : Nat := 4983230072969 + 3 ^ 40 * 7392494 * 2
def baseEnd_7392494 : Nat := 421766961942056118547505

theorem tailTrace_7392494 : CollatzResearch.WordTrace tailWord_7392494 prefixEnd_7392494 421766961942056118547505 := by
  unfold tailWord_7392494
  simp only [CollatzResearch.WordTrace]
  refine ⟨33703300860033031288071067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179750937920176166869712357 33703300860033031288071067)
  ·
    refine ⟨50554951290049546932106601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33703300860033031288071067 50554951290049546932106601)
    ·
      refine ⟨37916213467537160199079951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50554951290049546932106601 37916213467537160199079951)
      ·
        refine ⟨56874320201305740298619927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37916213467537160199079951 56874320201305740298619927)
        ·
          refine ⟨85311480301958610447929891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56874320201305740298619927 85311480301958610447929891)
          ·
            refine ⟨127967220452937915671894837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85311480301958610447929891 127967220452937915671894837)
            ·
              refine ⟨11996926917462929594240141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127967220452937915671894837 11996926917462929594240141)
              ·
                refine ⟨4498847594048598597840053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11996926917462929594240141 4498847594048598597840053)
                ·
                  refine ⟨421766961942056118547505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4498847594048598597840053 421766961942056118547505)
                  ·
                    rfl

theorem cell23_7392494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_7392494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392494 prefixEnd_7392494 := by exact prefixLift 7392494
  have htrace : WordTrace (prefixWord ++ tailWord_7392494) baseStart_7392494 baseEnd_7392494 := by
    simpa [prefixWord, tailWord_7392494, baseEnd_7392494] using wordTrace_append hprefix tailTrace_7392494
  have hstable : (prefixWord ++ tailWord_7392494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392494).length < 2 ^ (prefixWord ++ tailWord_7392494).sum := by decide
  have hdescent : baseEnd_7392494 < baseStart_7392494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392497 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 1, 7, 2]
def baseStart_7392497 : Nat := 118140960795 + 7392497 * 2 ^ 59
def prefixEnd_7392497 : Nat := 4983230072969 + 3 ^ 40 * 7392497 * 2
def baseEnd_7392497 : Nat := 3795904197920468555190031

theorem tailTrace_7392497 : CollatzResearch.WordTrace tailWord_7392497 prefixEnd_7392497 3795904197920468555190031 := by
  unfold tailWord_7392497
  simp only [CollatzResearch.WordTrace]
  refine ⟨269626516299253381816927745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179751010866168921211285163 269626516299253381816927745)
  ·
    refine ⟨202219887224440036362695809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269626516299253381816927745 202219887224440036362695809)
    ·
      refine ⟨151664915418330027272021857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202219887224440036362695809 151664915418330027272021857)
      ·
        refine ⟨113748686563747520454016393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151664915418330027272021857 113748686563747520454016393)
        ·
          refine ⟨85311514922810640340512295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113748686563747520454016393 85311514922810640340512295)
          ·
            refine ⟨127967272384215960510768443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85311514922810640340512295 127967272384215960510768443)
            ·
              refine ⟨191950908576323940766152665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127967272384215960510768443 191950908576323940766152665)
              ·
                refine ⟨143963181432242955574614499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191950908576323940766152665 143963181432242955574614499)
                ·
                  refine ⟨215944772148364433361921749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143963181432242955574614499 215944772148364433361921749)
                  ·
                    refine ⟨5061205597227291406920041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 215944772148364433361921749 5061205597227291406920041)
                    ·
                      refine ⟨3795904197920468555190031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5061205597227291406920041 3795904197920468555190031)
                      ·
                        rfl

theorem cell23_7392497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_7392497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392497 prefixEnd_7392497 := by exact prefixLift 7392497
  have htrace : WordTrace (prefixWord ++ tailWord_7392497) baseStart_7392497 baseEnd_7392497 := by
    simpa [prefixWord, tailWord_7392497, baseEnd_7392497] using wordTrace_append hprefix tailTrace_7392497
  have hstable : (prefixWord ++ tailWord_7392497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392497).length < 2 ^ (prefixWord ++ tailWord_7392497).sum := by decide
  have hdescent : baseEnd_7392497 < baseStart_7392497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392617 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 5, 1, 4]
def baseStart_7392617 : Nat := 118140960795 + 7392617 * 2 ^ 59
def prefixEnd_7392617 : Nat := 4983230072969 + 3 ^ 40 * 7392617 * 2
def baseEnd_7392617 : Nat := 3795965815599008085689479

theorem tailTrace_7392617 : CollatzResearch.WordTrace tailWord_7392617 prefixEnd_7392617 3795965815599008085689479 := by
  unfold tailWord_7392617
  simp only [CollatzResearch.WordTrace]
  refine ⟨269630893058818642311296105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179753928705879094874197403 269630893058818642311296105)
  ·
    refine ⟨202223169794113981733472079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269630893058818642311296105 202223169794113981733472079)
    ·
      refine ⟨303334754691170972600208119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202223169794113981733472079 303334754691170972600208119)
      ·
        refine ⟨455002132036756458900312179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303334754691170972600208119 455002132036756458900312179)
        ·
          refine ⟨682503198055134688350468269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455002132036756458900312179 682503198055134688350468269)
          ·
            refine ⟨255938699270675508131425601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 682503198055134688350468269 255938699270675508131425601)
            ·
              refine ⟨191954024453006631098569201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255938699270675508131425601 191954024453006631098569201)
              ·
                refine ⟨143965518339754973323926901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191954024453006631098569201 143965518339754973323926901)
                ·
                  refine ⟨13496767344352028749118147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143965518339754973323926901 13496767344352028749118147)
                  ·
                    refine ⟨20245151016528043123677221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13496767344352028749118147 20245151016528043123677221)
                    ·
                      refine ⟨3795965815599008085689479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20245151016528043123677221 3795965815599008085689479)
                      ·
                        rfl

theorem cell23_7392617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 1, 4].length) (baseStart_7392617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392617 prefixEnd_7392617 := by exact prefixLift 7392617
  have htrace : WordTrace (prefixWord ++ tailWord_7392617) baseStart_7392617 baseEnd_7392617 := by
    simpa [prefixWord, tailWord_7392617, baseEnd_7392617] using wordTrace_append hprefix tailTrace_7392617
  have hstable : (prefixWord ++ tailWord_7392617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392617).length < 2 ^ (prefixWord ++ tailWord_7392617).sum := by decide
  have hdescent : baseEnd_7392617 < baseStart_7392617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392618 : List Nat := [3, 1, 3, 3, 3, 1, 1, 2, 6]
def baseStart_7392618 : Nat := 118140960795 + 7392618 * 2 ^ 59
def prefixEnd_7392618 : Nat := 4983230072969 + 3 ^ 40 * 7392618 * 2
def baseEnd_7392618 : Nat := 421774036564406953530775

theorem tailTrace_7392618 : CollatzResearch.WordTrace tailWord_7392618 prefixEnd_7392618 421774036564406953530775 := by
  unfold tailWord_7392618
  simp only [CollatzResearch.WordTrace]
  refine ⟨67407732382953754870520627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179753953021210012988055005 67407732382953754870520627)
  ·
    refine ⟨101111598574430632305780941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67407732382953754870520627 101111598574430632305780941)
    ·
      refine ⟨37916849465411487114667853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101111598574430632305780941 37916849465411487114667853)
      ·
        refine ⟨14218818549529307668000445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37916849465411487114667853 14218818549529307668000445)
        ·
          refine ⟨5332056956073490375500167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14218818549529307668000445 5332056956073490375500167)
          ·
            refine ⟨7998085434110235563250251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5332056956073490375500167 7998085434110235563250251)
            ·
              refine ⟨11997128151165353344875377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998085434110235563250251 11997128151165353344875377)
              ·
                refine ⟨8997846113374015008656533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11997128151165353344875377 8997846113374015008656533)
                ·
                  refine ⟨421774036564406953530775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8997846113374015008656533 421774036564406953530775)
                  ·
                    rfl

theorem cell23_7392618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 6].length) (baseStart_7392618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392618 prefixEnd_7392618 := by exact prefixLift 7392618
  have htrace : WordTrace (prefixWord ++ tailWord_7392618) baseStart_7392618 baseEnd_7392618 := by
    simpa [prefixWord, tailWord_7392618, baseEnd_7392618] using wordTrace_append hprefix tailTrace_7392618
  have hstable : (prefixWord ++ tailWord_7392618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392618).length < 2 ^ (prefixWord ++ tailWord_7392618).sum := by decide
  have hdescent : baseEnd_7392618 < baseStart_7392618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7392644 : List Nat := [2, 3, 2, 1, 1, 3, 3, 1, 1, 6]
def baseStart_7392644 : Nat := 118140960795 + 7392644 * 2 ^ 59
def prefixEnd_7392644 : Nat := 4983230072969 + 3 ^ 40 * 7392644 * 2
def baseEnd_7392644 : Nat := 1265326559858893160017285

theorem tailTrace_7392644 : CollatzResearch.WordTrace tailWord_7392644 prefixEnd_7392644 1265326559858893160017285 := by
  unfold tailWord_7392644
  simp only [CollatzResearch.WordTrace]
  refine ⟨134815938914860412961264493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179754585219813883948352657 134815938914860412961264493)
  ·
    refine ⟨50555977093072654860474185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134815938914860412961264493 50555977093072654860474185)
    ·
      refine ⟨37916982819804491145355639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50555977093072654860474185 37916982819804491145355639)
      ·
        refine ⟨56875474229706736718033459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37916982819804491145355639 56875474229706736718033459)
        ·
          refine ⟨85313211344560105077050189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56875474229706736718033459 85313211344560105077050189)
          ·
            refine ⟨31992454254210039403893821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85313211344560105077050189 31992454254210039403893821)
            ·
              refine ⟨11997170345328764776460183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31992454254210039403893821 11997170345328764776460183)
              ·
                refine ⟨17995755517993147164690275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11997170345328764776460183 17995755517993147164690275)
                ·
                  refine ⟨26993633276989720747035413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17995755517993147164690275 26993633276989720747035413)
                  ·
                    refine ⟨1265326559858893160017285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26993633276989720747035413 1265326559858893160017285)
                    ·
                      rfl

theorem cell23_7392644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_7392644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7392644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7392644 prefixEnd_7392644 := by exact prefixLift 7392644
  have htrace : WordTrace (prefixWord ++ tailWord_7392644) baseStart_7392644 baseEnd_7392644 := by
    simpa [prefixWord, tailWord_7392644, baseEnd_7392644] using wordTrace_append hprefix tailTrace_7392644
  have hstable : (prefixWord ++ tailWord_7392644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7392644).length < 2 ^ (prefixWord ++ tailWord_7392644).sum := by decide
  have hdescent : baseEnd_7392644 < baseStart_7392644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7392644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
