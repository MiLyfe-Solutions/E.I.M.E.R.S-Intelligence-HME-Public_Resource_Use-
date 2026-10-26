import V185TrunkScan22Chunk334

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2989315 : List Nat := [1, 1, 1, 3, 2, 5, 1, 3, 1, 4]
def baseStart_2989315 : Nat := 118140960795 + 2989315 * 2 ^ 59
def prefixEnd_2989315 : Nat := 4983230072969 + 3 ^ 40 * 2989315 * 2
def baseEnd_2989315 : Nat := 1023303615130051350009931

theorem tailTrace_2989315 : CollatzResearch.WordTrace tailWord_2989315 prefixEnd_2989315 1023303615130051350009931 := by
  unfold tailWord_2989315
  simp only [CollatzResearch.WordTrace]
  refine ⟨109029275165229764201393399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72686183443486509467595599 109029275165229764201393399)
  ·
    refine ⟨163543912747844646302090099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109029275165229764201393399 163543912747844646302090099)
    ·
      refine ⟨245315869121766969453135149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163543912747844646302090099 245315869121766969453135149)
      ·
        refine ⟨91993450920662613544925681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245315869121766969453135149 91993450920662613544925681)
        ·
          refine ⟨68995088190496960158694261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91993450920662613544925681 68995088190496960158694261)
          ·
            refine ⟨6468289517859090014877587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68995088190496960158694261 6468289517859090014877587)
            ·
              refine ⟨9702434276788635022316381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6468289517859090014877587 9702434276788635022316381)
              ·
                refine ⟨3638412853795738133368643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9702434276788635022316381 3638412853795738133368643)
                ·
                  refine ⟨5457619280693607200052965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3638412853795738133368643 5457619280693607200052965)
                  ·
                    refine ⟨1023303615130051350009931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5457619280693607200052965 1023303615130051350009931)
                    ·
                      rfl

theorem cell22_2989315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 4].length) (baseStart_2989315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989315 prefixEnd_2989315 := by exact prefixLift 2989315
  have htrace : WordTrace (prefixWord ++ tailWord_2989315) baseStart_2989315 baseEnd_2989315 := by
    simpa [prefixWord, tailWord_2989315, baseEnd_2989315] using wordTrace_append hprefix tailTrace_2989315
  have hstable : (prefixWord ++ tailWord_2989315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989315).length < 2 ^ (prefixWord ++ tailWord_2989315).sum := by decide
  have hdescent : baseEnd_2989315 < baseStart_2989315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989377 : List Nat := [1, 2, 5, 2, 1, 2, 1, 2, 2, 4]
def baseStart_2989377 : Nat := 118140960795 + 2989377 * 2 ^ 59
def prefixEnd_2989377 : Nat := 4983230072969 + 3 ^ 40 * 2989377 * 2
def baseEnd_2989377 : Nat := 1023324838997103854959741

theorem tailTrace_2989377 : CollatzResearch.WordTrace tailWord_2989377 prefixEnd_2989377 1023324838997103854959741 := by
  unfold tailWord_2989377
  simp only [CollatzResearch.WordTrace]
  refine ⟨109031536491005148790150385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72687690994003432526766923 109031536491005148790150385)
  ·
    refine ⟨81773652368253861592612789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109031536491005148790150385 81773652368253861592612789)
    ·
      refine ⟨7666279909523799524307449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81773652368253861592612789 7666279909523799524307449)
      ·
        refine ⟨5749709932142849643230587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7666279909523799524307449 5749709932142849643230587)
        ·
          refine ⟨8624564898214274464845881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5749709932142849643230587 8624564898214274464845881)
          ·
            refine ⟨6468423673660705848634411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8624564898214274464845881 6468423673660705848634411)
            ·
              refine ⟨9702635510491058772951617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6468423673660705848634411 9702635510491058772951617)
              ·
                refine ⟨7276976632868294079713713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9702635510491058772951617 7276976632868294079713713)
                ·
                  refine ⟨5457732474651220559785285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7276976632868294079713713 5457732474651220559785285)
                  ·
                    refine ⟨1023324838997103854959741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5457732474651220559785285 1023324838997103854959741)
                    ·
                      rfl

theorem cell22_2989377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_2989377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989377 prefixEnd_2989377 := by exact prefixLift 2989377
  have htrace : WordTrace (prefixWord ++ tailWord_2989377) baseStart_2989377 baseEnd_2989377 := by
    simpa [prefixWord, tailWord_2989377, baseEnd_2989377] using wordTrace_append hprefix tailTrace_2989377
  have hstable : (prefixWord ++ tailWord_2989377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989377).length < 2 ^ (prefixWord ++ tailWord_2989377).sum := by decide
  have hdescent : baseEnd_2989377 < baseStart_2989377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989441 : List Nat := [1, 2, 4, 3, 2, 1, 1, 4, 1, 3]
def baseStart_2989441 : Nat := 118140960795 + 2989441 * 2 ^ 59
def prefixEnd_2989441 : Nat := 4983230072969 + 3 ^ 40 * 2989441 * 2
def baseEnd_2989441 : Nat := 1023346747505029021359545

theorem tailTrace_2989441 : CollatzResearch.WordTrace tailWord_2989441 prefixEnd_2989441 1023346747505029021359545 := by
  unfold tailWord_2989441
  simp only [CollatzResearch.WordTrace]
  refine ⟨109033870762773287720480177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72689247175182191813653451 109033870762773287720480177)
  ·
    refine ⟨81775403072079965790360133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109033870762773287720480177 81775403072079965790360133)
    ·
      refine ⟨15332888076014993585692525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81775403072079965790360133 15332888076014993585692525)
      ·
        refine ⟨5749833028505622594634697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15332888076014993585692525 5749833028505622594634697)
        ·
          refine ⟨4312374771379216945976023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5749833028505622594634697 4312374771379216945976023)
          ·
            refine ⟨6468562157068825418964035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4312374771379216945976023 6468562157068825418964035)
            ·
              refine ⟨9702843235603238128446053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6468562157068825418964035 9702843235603238128446053)
              ·
                refine ⟨1819283106675607149083635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9702843235603238128446053 1819283106675607149083635)
                ·
                  refine ⟨2728924660013410723625453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819283106675607149083635 2728924660013410723625453)
                  ·
                    refine ⟨1023346747505029021359545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2728924660013410723625453 1023346747505029021359545)
                    ·
                      rfl

theorem cell22_2989441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_2989441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989441 prefixEnd_2989441 := by exact prefixLift 2989441
  have htrace : WordTrace (prefixWord ++ tailWord_2989441) baseStart_2989441 baseEnd_2989441 := by
    simpa [prefixWord, tailWord_2989441, baseEnd_2989441] using wordTrace_append hprefix tailTrace_2989441
  have hstable : (prefixWord ++ tailWord_2989441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989441).length < 2 ^ (prefixWord ++ tailWord_2989441).sum := by decide
  have hdescent : baseEnd_2989441 < baseStart_2989441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989465 : List Nat := [1, 2, 1, 2, 1, 6, 1, 2, 6]
def baseStart_2989465 : Nat := 118140960795 + 2989465 * 2 ^ 59
def prefixEnd_2989465 : Nat := 4983230072969 + 3 ^ 40 * 2989465 * 2
def baseEnd_2989465 : Nat := 341118321065166986253157

theorem tailTrace_2989465 : CollatzResearch.WordTrace tailWord_2989465 prefixEnd_2989465 341118321065166986253157 := by
  unfold tailWord_2989465
  simp only [CollatzResearch.WordTrace]
  refine ⟨109034746114686339819353849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72689830743124226546235899 109034746114686339819353849)
  ·
    refine ⟨81776059586014754864515387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109034746114686339819353849 81776059586014754864515387)
    ·
      refine ⟨122664089379022132296773081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81776059586014754864515387 122664089379022132296773081)
      ·
        refine ⟨91998067034266599222579811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122664089379022132296773081 91998067034266599222579811)
        ·
          refine ⟨137997100551399898833869717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91998067034266599222579811 137997100551399898833869717)
          ·
            refine ⟨6468614088346870257837643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 137997100551399898833869717 6468614088346870257837643)
            ·
              refine ⟨9702921132520305386756465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6468614088346870257837643 9702921132520305386756465)
              ·
                refine ⟨7277190849390229040067349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9702921132520305386756465 7277190849390229040067349)
                ·
                  refine ⟨341118321065166986253157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7277190849390229040067349 341118321065166986253157)
                  ·
                    rfl

theorem cell22_2989465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 6].length) (baseStart_2989465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989465 prefixEnd_2989465 := by exact prefixLift 2989465
  have htrace : WordTrace (prefixWord ++ tailWord_2989465) baseStart_2989465 baseEnd_2989465 := by
    simpa [prefixWord, tailWord_2989465, baseEnd_2989465] using wordTrace_append hprefix tailTrace_2989465
  have hstable : (prefixWord ++ tailWord_2989465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989465).length < 2 ^ (prefixWord ++ tailWord_2989465).sum := by decide
  have hdescent : baseEnd_2989465 < baseStart_2989465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989495 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 4, 4]
def baseStart_2989495 : Nat := 118140960795 + 2989495 * 2 ^ 59
def prefixEnd_2989495 : Nat := 4983230072969 + 3 ^ 40 * 2989495 * 2
def baseEnd_2989495 : Nat := 1023365232808590880509379

theorem tailTrace_2989495 : CollatzResearch.WordTrace tailWord_2989495 prefixEnd_2989495 1023365232808590880509379 := by
  unfold tailWord_2989495
  simp only [CollatzResearch.WordTrace]
  refine ⟨109035840304577654942945939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72690560203051769961963959 109035840304577654942945939)
  ·
    refine ⟨163553760456866482414418909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109035840304577654942945939 163553760456866482414418909)
    ·
      refine ⟨61332660171324930905407091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163553760456866482414418909 61332660171324930905407091)
      ·
        refine ⟨91998990256987396358110637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61332660171324930905407091 91998990256987396358110637)
        ·
          refine ⟨34499621346370273634291489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91998990256987396358110637 34499621346370273634291489)
          ·
            refine ⟨25874716009777705225718617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34499621346370273634291489 25874716009777705225718617)
            ·
              refine ⟨19406037007333278919288963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25874716009777705225718617 19406037007333278919288963)
              ·
                refine ⟨29109055510999918378933445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19406037007333278919288963 29109055510999918378933445)
                ·
                  refine ⟨5457947908312484696050021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29109055510999918378933445 5457947908312484696050021)
                  ·
                    refine ⟨1023365232808590880509379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5457947908312484696050021 1023365232808590880509379)
                    ·
                      rfl

theorem cell22_2989495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_2989495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989495 prefixEnd_2989495 := by exact prefixLift 2989495
  have htrace : WordTrace (prefixWord ++ tailWord_2989495) baseStart_2989495 baseEnd_2989495 := by
    simpa [prefixWord, tailWord_2989495, baseEnd_2989495] using wordTrace_append hprefix tailTrace_2989495
  have hstable : (prefixWord ++ tailWord_2989495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989495).length < 2 ^ (prefixWord ++ tailWord_2989495).sum := by decide
  have hdescent : baseEnd_2989495 < baseStart_2989495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989525 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 2, 7]
def baseStart_2989525 : Nat := 118140960795 + 2989525 * 2 ^ 59
def prefixEnd_2989525 : Nat := 4983230072969 + 3 ^ 40 * 2989525 * 2
def baseEnd_2989525 : Nat := 1023375502421680802259287

theorem tailTrace_2989525 : CollatzResearch.WordTrace tailWord_2989525 prefixEnd_2989525 1023375502421680802259287 := by
  unfold tailWord_2989525
  simp only [CollatzResearch.WordTrace]
  refine ⟨109036934494468970066538029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72691289662979313377692019 109036934494468970066538029)
  ·
    refine ⟨40888850435425863774951761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109036934494468970066538029 40888850435425863774951761)
    ·
      refine ⟨30666637826569397831213821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40888850435425863774951761 30666637826569397831213821)
      ·
        refine ⟨11499989184963524186705183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30666637826569397831213821 11499989184963524186705183)
        ·
          refine ⟨17249983777445286280057775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11499989184963524186705183 17249983777445286280057775)
          ·
            refine ⟨25874975666167929420086663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17249983777445286280057775 25874975666167929420086663)
            ·
              refine ⟨38812463499251894130129995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25874975666167929420086663 38812463499251894130129995)
              ·
                refine ⟨58218695248877841195194993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38812463499251894130129995 58218695248877841195194993)
                ·
                  refine ⟨43664021436658380896396245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58218695248877841195194993 43664021436658380896396245)
                  ·
                    refine ⟨1023375502421680802259287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43664021436658380896396245 1023375502421680802259287)
                    ·
                      rfl

theorem cell22_2989525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_2989525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989525 prefixEnd_2989525 := by exact prefixLift 2989525
  have htrace : WordTrace (prefixWord ++ tailWord_2989525) baseStart_2989525 baseEnd_2989525 := by
    simpa [prefixWord, tailWord_2989525, baseEnd_2989525] using wordTrace_append hprefix tailTrace_2989525
  have hstable : (prefixWord ++ tailWord_2989525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989525).length < 2 ^ (prefixWord ++ tailWord_2989525).sum := by decide
  have hdescent : baseEnd_2989525 < baseStart_2989525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989632 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 6, 3]
def baseStart_2989632 : Nat := 118140960795 + 2989632 * 2 ^ 59
def prefixEnd_2989632 : Nat := 4983230072969 + 3 ^ 40 * 2989632 * 2
def baseEnd_2989632 : Nat := 1023412130708368189833959

theorem tailTrace_2989632 : CollatzResearch.WordTrace tailWord_2989632 prefixEnd_2989632 1023412130708368189833959 := by
  unfold tailWord_2989632
  simp only [CollatzResearch.WordTrace]
  refine ⟨54520418552540663670341575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72693891403387551560455433 54520418552540663670341575)
  ·
    refine ⟨81780627828810995505512363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54520418552540663670341575 81780627828810995505512363)
    ·
      refine ⟨122670941743216493258268545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81780627828810995505512363 122670941743216493258268545)
      ·
        refine ⟨92003206307412369943701409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122670941743216493258268545 92003206307412369943701409)
        ·
          refine ⟨69002404730559277457776057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92003206307412369943701409 69002404730559277457776057)
          ·
            refine ⟨51751803547919458093332043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69002404730559277457776057 51751803547919458093332043)
            ·
              refine ⟨77627705321879187139998065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51751803547919458093332043 77627705321879187139998065)
              ·
                refine ⟨58220778991409390354998549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77627705321879187139998065 58220778991409390354998549)
                ·
                  refine ⟨2729099015222315172890557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58220778991409390354998549 2729099015222315172890557)
                  ·
                    refine ⟨1023412130708368189833959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2729099015222315172890557 1023412130708368189833959)
                    ·
                      rfl

theorem cell22_2989632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 6, 3].length) (baseStart_2989632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989632 prefixEnd_2989632 := by exact prefixLift 2989632
  have htrace : WordTrace (prefixWord ++ tailWord_2989632) baseStart_2989632 baseEnd_2989632 := by
    simpa [prefixWord, tailWord_2989632, baseEnd_2989632] using wordTrace_append hprefix tailTrace_2989632
  have hstable : (prefixWord ++ tailWord_2989632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989632).length < 2 ^ (prefixWord ++ tailWord_2989632).sum := by decide
  have hdescent : baseEnd_2989632 < baseStart_2989632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989752 : List Nat := [2, 1, 2, 1, 2, 1, 1, 6, 6]
def baseStart_2989752 : Nat := 118140960795 + 2989752 * 2 ^ 59
def prefixEnd_2989752 : Nat := 4983230072969 + 3 ^ 40 * 2989752 * 2
def baseEnd_2989752 : Nat := 341151069720242625611197

theorem tailTrace_2989752 : CollatzResearch.WordTrace tailWord_2989752 prefixEnd_2989752 341151069720242625611197 := by
  unfold tailWord_2989752
  simp only [CollatzResearch.WordTrace]
  refine ⟨54522606932323293917525755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72696809243097725223367673 54522606932323293917525755)
  ·
    refine ⟨81783910398484940876288633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54522606932323293917525755 81783910398484940876288633)
    ·
      refine ⟨61337932798863705657216475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81783910398484940876288633 61337932798863705657216475)
      ·
        refine ⟨92006899198295558485824713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61337932798863705657216475 92006899198295558485824713)
        ·
          refine ⟨69005174398721668864368535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92006899198295558485824713 69005174398721668864368535)
          ·
            refine ⟨103507761598082503296552803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69005174398721668864368535 103507761598082503296552803)
            ·
              refine ⟨155261642397123754944829205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103507761598082503296552803 155261642397123754944829205)
              ·
                refine ⟨7277889487365176013038869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 155261642397123754944829205 7277889487365176013038869)
                ·
                  refine ⟨341151069720242625611197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7277889487365176013038869 341151069720242625611197)
                  ·
                    rfl

theorem cell22_2989752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 6].length) (baseStart_2989752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989752 prefixEnd_2989752 := by exact prefixLift 2989752
  have htrace : WordTrace (prefixWord ++ tailWord_2989752) baseStart_2989752 baseEnd_2989752 := by
    simpa [prefixWord, tailWord_2989752, baseEnd_2989752] using wordTrace_append hprefix tailTrace_2989752
  have hstable : (prefixWord ++ tailWord_2989752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989752).length < 2 ^ (prefixWord ++ tailWord_2989752).sum := by decide
  have hdescent : baseEnd_2989752 < baseStart_2989752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989754 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 3, 4]
def baseStart_2989754 : Nat := 118140960795 + 2989754 * 2 ^ 59
def prefixEnd_2989754 : Nat := 4983230072969 + 3 ^ 40 * 2989754 * 2
def baseEnd_2989754 : Nat := 1023453893801600538283585

theorem tailTrace_2989754 : CollatzResearch.WordTrace tailWord_2989754 prefixEnd_2989754 1023453893801600538283585 := by
  unfold tailWord_2989754
  simp only [CollatzResearch.WordTrace]
  refine ⟨27261321702659835544156079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72696857873759561451082877 27261321702659835544156079)
  ·
    refine ⟨40891982553989753316234119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27261321702659835544156079 40891982553989753316234119)
    ·
      refine ⟨61337973830984629974351179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40891982553989753316234119 61337973830984629974351179)
      ·
        refine ⟨92006960746476944961526769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61337973830984629974351179 92006960746476944961526769)
        ·
          refine ⟨69005220559857708721145077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92006960746476944961526769 69005220559857708721145077)
          ·
            refine ⟨6469239427486660192607351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69005220559857708721145077 6469239427486660192607351)
            ·
              refine ⟨9703859141229990288911027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6469239427486660192607351 9703859141229990288911027)
              ·
                refine ⟨14555788711844985433366541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9703859141229990288911027 14555788711844985433366541)
                ·
                  refine ⟨5458420766941869537512453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14555788711844985433366541 5458420766941869537512453)
                  ·
                    refine ⟨1023453893801600538283585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5458420766941869537512453 1023453893801600538283585)
                    ·
                      rfl

theorem cell22_2989754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_2989754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989754 prefixEnd_2989754 := by exact prefixLift 2989754
  have htrace : WordTrace (prefixWord ++ tailWord_2989754) baseStart_2989754 baseEnd_2989754 := by
    simpa [prefixWord, tailWord_2989754, baseEnd_2989754] using wordTrace_append hprefix tailTrace_2989754
  have hstable : (prefixWord ++ tailWord_2989754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989754).length < 2 ^ (prefixWord ++ tailWord_2989754).sum := by decide
  have hdescent : baseEnd_2989754 < baseStart_2989754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989786 : List Nat := [3, 1, 1, 2, 2, 4, 1, 4, 4]
def baseStart_2989786 : Nat := 118140960795 + 2989786 * 2 ^ 59
def prefixEnd_2989786 : Nat := 4983230072969 + 3 ^ 40 * 2989786 * 2
def baseEnd_2989786 : Nat := 341154949351854373827829

theorem tailTrace_2989786 : CollatzResearch.WordTrace tailWord_2989786 prefixEnd_2989786 341154949351854373827829 := by
  unfold tailWord_2989786
  simp only [CollatzResearch.WordTrace]
  refine ⟨27261613486630852910447303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72697635964348941094526141 27261613486630852910447303)
  ·
    refine ⟨40892420229946279365670955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27261613486630852910447303 40892420229946279365670955)
    ·
      refine ⟨61338630344919419048506433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40892420229946279365670955 61338630344919419048506433)
      ·
        refine ⟨46003972758689564286379825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61338630344919419048506433 46003972758689564286379825)
        ·
          refine ⟨34502979569017173214784869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46003972758689564286379825 34502979569017173214784869)
          ·
            refine ⟨6469308669190719977772163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34502979569017173214784869 6469308669190719977772163)
            ·
              refine ⟨9703963003786079966658245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6469308669190719977772163 9703963003786079966658245)
              ·
                refine ⟨1819493063209889993748421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9703963003786079966658245 1819493063209889993748421)
                ·
                  refine ⟨341154949351854373827829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1819493063209889993748421 341154949351854373827829)
                  ·
                    rfl

theorem cell22_2989786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_2989786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989786 prefixEnd_2989786 := by exact prefixLift 2989786
  have htrace : WordTrace (prefixWord ++ tailWord_2989786) baseStart_2989786 baseEnd_2989786 := by
    simpa [prefixWord, tailWord_2989786, baseEnd_2989786] using wordTrace_append hprefix tailTrace_2989786
  have hstable : (prefixWord ++ tailWord_2989786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989786).length < 2 ^ (prefixWord ++ tailWord_2989786).sum := by decide
  have hdescent : baseEnd_2989786 < baseStart_2989786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989822 : List Nat := [4, 2, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_2989822 : Nat := 118140960795 + 2989822 * 2 ^ 59
def prefixEnd_2989822 : Nat := 4983230072969 + 3 ^ 40 * 2989822 * 2
def baseEnd_2989822 : Nat := 1023477171591271027583377

theorem tailTrace_2989822 : CollatzResearch.WordTrace tailWord_2989822 prefixEnd_2989822 1023477171591271027583377 := by
  unfold tailWord_2989822
  simp only [CollatzResearch.WordTrace]
  refine ⟨13630970871799123723762465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72698511316261993193399813 13630970871799123723762465)
  ·
    refine ⟨10223228153849342792821849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13630970871799123723762465 10223228153849342792821849)
    ·
      refine ⟨7667421115387007094616387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10223228153849342792821849 7667421115387007094616387)
      ·
        refine ⟨11501131673080510641924581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7667421115387007094616387 11501131673080510641924581)
        ·
          refine ⟨2156462188702595745360859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11501131673080510641924581 2156462188702595745360859)
          ·
            refine ⟨3234693283053893618041289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2156462188702595745360859 3234693283053893618041289)
            ·
              refine ⟨2426019962290420213530967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3234693283053893618041289 2426019962290420213530967)
              ·
                refine ⟨3639029943435630320296451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2426019962290420213530967 3639029943435630320296451)
                ·
                  refine ⟨5458544915153445480444677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3639029943435630320296451 5458544915153445480444677)
                  ·
                    refine ⟨1023477171591271027583377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5458544915153445480444677 1023477171591271027583377)
                    ·
                      rfl

theorem cell22_2989822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_2989822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989822 prefixEnd_2989822 := by exact prefixLift 2989822
  have htrace : WordTrace (prefixWord ++ tailWord_2989822) baseStart_2989822 baseEnd_2989822 := by
    simpa [prefixWord, tailWord_2989822, baseEnd_2989822] using wordTrace_append hprefix tailTrace_2989822
  have hstable : (prefixWord ++ tailWord_2989822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989822).length < 2 ^ (prefixWord ++ tailWord_2989822).sum := by decide
  have hdescent : baseEnd_2989822 < baseStart_2989822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989837 : List Nat := [1, 7, 2, 1, 1, 1, 2, 1, 6]
def baseStart_2989837 : Nat := 118140960795 + 2989837 * 2 ^ 59
def prefixEnd_2989837 : Nat := 4983230072969 + 3 ^ 40 * 2989837 * 2
def baseEnd_2989837 : Nat := 341160768799271996152777

theorem tailTrace_2989837 : CollatzResearch.WordTrace tailWord_2989837 prefixEnd_2989837 341160768799271996152777 := by
  unfold tailWord_2989837
  simp only [CollatzResearch.WordTrace]
  refine ⟨109048314069338647351895765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72698876046225764901263843 109048314069338647351895765)
  ·
    refine ⟨2555819861000124547310057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 109048314069338647351895765 2555819861000124547310057)
    ·
      refine ⟨1916864895750093410482543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2555819861000124547310057 1916864895750093410482543)
      ·
        refine ⟨2875297343625140115723815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1916864895750093410482543 2875297343625140115723815)
        ·
          refine ⟨4312946015437710173585723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2875297343625140115723815 4312946015437710173585723)
          ·
            refine ⟨6469419023156565260378585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4312946015437710173585723 6469419023156565260378585)
            ·
              refine ⟨4852064267367423945283939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6469419023156565260378585 4852064267367423945283939)
              ·
                refine ⟨7278096401051135917925909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4852064267367423945283939 7278096401051135917925909)
                ·
                  refine ⟨341160768799271996152777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7278096401051135917925909 341160768799271996152777)
                  ·
                    rfl

theorem cell22_2989837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_2989837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989837 prefixEnd_2989837 := by exact prefixLift 2989837
  have htrace : WordTrace (prefixWord ++ tailWord_2989837) baseStart_2989837 baseEnd_2989837 := by
    simpa [prefixWord, tailWord_2989837, baseEnd_2989837] using wordTrace_append hprefix tailTrace_2989837
  have hstable : (prefixWord ++ tailWord_2989837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989837).length < 2 ^ (prefixWord ++ tailWord_2989837).sum := by decide
  have hdescent : baseEnd_2989837 < baseStart_2989837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989859 : List Nat := [1, 1, 1, 4, 2, 1, 2, 5, 5]
def baseStart_2989859 : Nat := 118140960795 + 2989859 * 2 ^ 59
def prefixEnd_2989859 : Nat := 4983230072969 + 3 ^ 40 * 2989859 * 2
def baseEnd_2989859 : Nat := 341163279149138421469421

theorem tailTrace_2989859 : CollatzResearch.WordTrace tailWord_2989859 prefixEnd_2989859 341163279149138421469421 := by
  unfold tailWord_2989859
  simp only [CollatzResearch.WordTrace]
  refine ⟨109049116475258945109196631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72699410983505963406131087 109049116475258945109196631)
  ·
    refine ⟨163573674712888417663794947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109049116475258945109196631 163573674712888417663794947)
    ·
      refine ⟨245360512069332626495692421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163573674712888417663794947 245360512069332626495692421)
      ·
        refine ⟨46005096012999867467942329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245360512069332626495692421 46005096012999867467942329)
        ·
          refine ⟨34503822009749900600956747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46005096012999867467942329 34503822009749900600956747)
          ·
            refine ⟨51755733014624850901435121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34503822009749900600956747 51755733014624850901435121)
            ·
              refine ⟨38816799760968638176076341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51755733014624850901435121 38816799760968638176076341)
              ·
                refine ⟨3639074977590809829007157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38816799760968638176076341 3639074977590809829007157)
                ·
                  refine ⟨341163279149138421469421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3639074977590809829007157 341163279149138421469421)
                  ·
                    rfl

theorem cell22_2989859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 5].length) (baseStart_2989859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989859 prefixEnd_2989859 := by exact prefixLift 2989859
  have htrace : WordTrace (prefixWord ++ tailWord_2989859) baseStart_2989859 baseEnd_2989859 := by
    simpa [prefixWord, tailWord_2989859, baseEnd_2989859] using wordTrace_append hprefix tailTrace_2989859
  have hstable : (prefixWord ++ tailWord_2989859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989859).length < 2 ^ (prefixWord ++ tailWord_2989859).sum := by decide
  have hdescent : baseEnd_2989859 < baseStart_2989859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989876 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 7]
def baseStart_2989876 : Nat := 118140960795 + 2989876 * 2 ^ 59
def prefixEnd_2989876 : Nat := 4983230072969 + 3 ^ 40 * 2989876 * 2
def baseEnd_2989876 : Nat := 341165218964944295577737

theorem tailTrace_2989876 : CollatzResearch.WordTrace tailWord_2989876 prefixEnd_2989876 341165218964944295577737 := by
  unfold tailWord_2989876
  simp only [CollatzResearch.WordTrace]
  refine ⟨54524868258098678506282741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72699824344131571341710321 54524868258098678506282741)
  ·
    refine ⟨5111706399196751109964007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54524868258098678506282741 5111706399196751109964007)
    ·
      refine ⟨7667559598795126664946011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5111706399196751109964007 7667559598795126664946011)
      ·
        refine ⟨11501339398192689997419017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7667559598795126664946011 11501339398192689997419017)
        ·
          refine ⟨8626004548644517498064263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11501339398192689997419017 8626004548644517498064263)
          ·
            refine ⟨12939006822966776247096395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8626004548644517498064263 12939006822966776247096395)
            ·
              refine ⟨19408510234450164370644593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12939006822966776247096395 19408510234450164370644593)
              ·
                refine ⟨14556382675837623277983445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19408510234450164370644593 14556382675837623277983445)
                ·
                  refine ⟨341165218964944295577737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14556382675837623277983445 341165218964944295577737)
                  ·
                    rfl

theorem cell22_2989876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_2989876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989876 prefixEnd_2989876 := by exact prefixLift 2989876
  have htrace : WordTrace (prefixWord ++ tailWord_2989876) baseStart_2989876 baseEnd_2989876 := by
    simpa [prefixWord, tailWord_2989876, baseEnd_2989876] using wordTrace_append hprefix tailTrace_2989876
  have hstable : (prefixWord ++ tailWord_2989876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989876).length < 2 ^ (prefixWord ++ tailWord_2989876).sum := by decide
  have hdescent : baseEnd_2989876 < baseStart_2989876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989880 : List Nat := [2, 1, 2, 1, 3, 5, 1, 3, 1, 3]
def baseStart_2989880 : Nat := 118140960795 + 2989880 * 2 ^ 59
def prefixEnd_2989880 : Nat := 4983230072969 + 3 ^ 40 * 2989880 * 2
def baseEnd_2989880 : Nat := 1023497026176578209633199

theorem tailTrace_2989880 : CollatzResearch.WordTrace tailWord_2989880 prefixEnd_2989880 1023497026176578209633199 := by
  unfold tailWord_2989880
  simp only [CollatzResearch.WordTrace]
  refine ⟨54524941204091432847855547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72699921605455243797140729 54524941204091432847855547)
  ·
    refine ⟨81787411806137149271783321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54524941204091432847855547 81787411806137149271783321)
    ·
      refine ⟨61340558854602861953837491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81787411806137149271783321 61340558854602861953837491)
      ·
        refine ⟨92010838281904292930756237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61340558854602861953837491 92010838281904292930756237)
        ·
          refine ⟨34504064355714109849033589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92010838281904292930756237 34504064355714109849033589)
          ·
            refine ⟨3234756033348197798346899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34504064355714109849033589 3234756033348197798346899)
            ·
              refine ⟨4852134050022296697520349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3234756033348197798346899 4852134050022296697520349)
              ·
                refine ⟨1819550268758361261570131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4852134050022296697520349 1819550268758361261570131)
                ·
                  refine ⟨2729325403137541892355197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819550268758361261570131 2729325403137541892355197)
                  ·
                    refine ⟨1023497026176578209633199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2729325403137541892355197 1023497026176578209633199)
                    ·
                      rfl

theorem cell22_2989880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 1, 3].length) (baseStart_2989880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989880 prefixEnd_2989880 := by exact prefixLift 2989880
  have htrace : WordTrace (prefixWord ++ tailWord_2989880) baseStart_2989880 baseEnd_2989880 := by
    simpa [prefixWord, tailWord_2989880, baseEnd_2989880] using wordTrace_append hprefix tailTrace_2989880
  have hstable : (prefixWord ++ tailWord_2989880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989880).length < 2 ^ (prefixWord ++ tailWord_2989880).sum := by decide
  have hdescent : baseEnd_2989880 < baseStart_2989880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989955 : List Nat := [1, 1, 1, 3, 4, 4, 2, 2, 4]
def baseStart_2989955 : Nat := 118140960795 + 2989955 * 2 ^ 59
def prefixEnd_2989955 : Nat := 4983230072969 + 3 ^ 40 * 2989955 * 2
def baseEnd_2989955 : Nat := 341174233403101004669323

theorem tailTrace_2989955 : CollatzResearch.WordTrace tailWord_2989955 prefixEnd_2989955 341174233403101004669323 := by
  unfold tailWord_2989955
  simp only [CollatzResearch.WordTrace]
  refine ⟨109052617882911153504691319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72701745255274102336460879 109052617882911153504691319)
  ·
    refine ⟨163578926824366730257036979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109052617882911153504691319 163578926824366730257036979)
    ·
      refine ⟨245368390236550095385555469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163578926824366730257036979 245368390236550095385555469)
      ·
        refine ⟨92013146338706285769583301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245368390236550095385555469 92013146338706285769583301)
        ·
          refine ⟨17252464938507428581796869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92013146338706285769583301 17252464938507428581796869)
          ·
            refine ⟨3234837175970142859086913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17252464938507428581796869 3234837175970142859086913)
            ·
              refine ⟨2426127881977607144315185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3234837175970142859086913 2426127881977607144315185)
              ·
                refine ⟨1819595911483205358236389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2426127881977607144315185 1819595911483205358236389)
                ·
                  refine ⟨341174233403101004669323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1819595911483205358236389 341174233403101004669323)
                  ·
                    rfl

theorem cell22_2989955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 4].length) (baseStart_2989955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989955 prefixEnd_2989955 := by exact prefixLift 2989955
  have htrace : WordTrace (prefixWord ++ tailWord_2989955) baseStart_2989955 baseEnd_2989955 := by
    simpa [prefixWord, tailWord_2989955, baseEnd_2989955] using wordTrace_append hprefix tailTrace_2989955
  have hstable : (prefixWord ++ tailWord_2989955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989955).length < 2 ^ (prefixWord ++ tailWord_2989955).sum := by decide
  have hdescent : baseEnd_2989955 < baseStart_2989955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989964 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 2, 7]
def baseStart_2989964 : Nat := 118140960795 + 2989964 * 2 ^ 59
def prefixEnd_2989964 : Nat := 4983230072969 + 3 ^ 40 * 2989964 * 2
def baseEnd_2989964 : Nat := 1023525781093229990532941

theorem tailTrace_2989964 : CollatzResearch.WordTrace tailWord_2989964 prefixEnd_2989964 1023525781093229990532941 := by
  unfold tailWord_2989964
  simp only [CollatzResearch.WordTrace]
  refine ⟨54526473069939274020884473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72701964093252365361179297 54526473069939274020884473)
  ·
    refine ⟨40894854802454455515663355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54526473069939274020884473 40894854802454455515663355)
    ·
      refine ⟨61342282203681683273495033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40894854802454455515663355 61342282203681683273495033)
      ·
        refine ⟨46006711652761262455121275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61342282203681683273495033 46006711652761262455121275)
        ·
          refine ⟨69010067479141893682681913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46006711652761262455121275 69010067479141893682681913)
          ·
            refine ⟨51757550609356420262011435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69010067479141893682681913 51757550609356420262011435)
            ·
              refine ⟨77636325914034630393017153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51757550609356420262011435 77636325914034630393017153)
              ·
                refine ⟨58227244435525972794762865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77636325914034630393017153 58227244435525972794762865)
                ·
                  refine ⟨43670433326644479596072149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58227244435525972794762865 43670433326644479596072149)
                  ·
                    refine ⟨1023525781093229990532941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43670433326644479596072149 1023525781093229990532941)
                    ·
                      rfl

theorem cell22_2989964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_2989964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989964 prefixEnd_2989964 := by exact prefixLift 2989964
  have htrace : WordTrace (prefixWord ++ tailWord_2989964) baseStart_2989964 baseEnd_2989964 := by
    simpa [prefixWord, tailWord_2989964, baseEnd_2989964] using wordTrace_append hprefix tailTrace_2989964
  have hstable : (prefixWord ++ tailWord_2989964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989964).length < 2 ^ (prefixWord ++ tailWord_2989964).sum := by decide
  have hdescent : baseEnd_2989964 < baseStart_2989964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989970 : List Nat := [3, 2, 3, 2, 1, 1, 2, 3, 2, 3]
def baseStart_2989970 : Nat := 118140960795 + 2989970 * 2 ^ 59
def prefixEnd_2989970 : Nat := 4983230072969 + 3 ^ 40 * 2989970 * 2
def baseEnd_2989970 : Nat := 1023527835015847974882923

theorem tailTrace_2989970 : CollatzResearch.WordTrace tailWord_2989970 prefixEnd_2989970 1023527835015847974882923 := by
  unfold tailWord_2989970
  simp only [CollatzResearch.WordTrace]
  refine ⟨27263291244464202766621841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72702109985237874044324909 27263291244464202766621841)
  ·
    refine ⟨20447468433348152074966381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27263291244464202766621841 20447468433348152074966381)
    ·
      refine ⟨7667800662505557028112393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20447468433348152074966381 7667800662505557028112393)
      ·
        refine ⟨5750850496879167771084295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7667800662505557028112393 5750850496879167771084295)
        ·
          refine ⟨8626275745318751656626443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5750850496879167771084295 8626275745318751656626443)
          ·
            refine ⟨12939413617978127484939665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8626275745318751656626443 12939413617978127484939665)
            ·
              refine ⟨9704560213483595613704749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12939413617978127484939665 9704560213483595613704749)
              ·
                refine ⟨3639210080056348355139281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9704560213483595613704749 3639210080056348355139281)
                ·
                  refine ⟨2729407560042261266354461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3639210080056348355139281 2729407560042261266354461)
                  ·
                    refine ⟨1023527835015847974882923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2729407560042261266354461 1023527835015847974882923)
                    ·
                      rfl

theorem cell22_2989970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_2989970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989970 prefixEnd_2989970 := by exact prefixLift 2989970
  have htrace : WordTrace (prefixWord ++ tailWord_2989970) baseStart_2989970 baseEnd_2989970 := by
    simpa [prefixWord, tailWord_2989970, baseEnd_2989970] using wordTrace_append hprefix tailTrace_2989970
  have hstable : (prefixWord ++ tailWord_2989970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989970).length < 2 ^ (prefixWord ++ tailWord_2989970).sum := by decide
  have hdescent : baseEnd_2989970 < baseStart_2989970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989983 : List Nat := [1, 1, 2, 5, 3, 1, 3, 6]
def baseStart_2989983 : Nat := 118140960795 + 2989983 * 2 ^ 59
def prefixEnd_2989983 : Nat := 4983230072969 + 3 ^ 40 * 2989983 * 2
def baseEnd_2989983 : Nat := 113725809464613363811987

theorem tailTrace_2989983 : CollatzResearch.WordTrace tailWord_2989983 prefixEnd_2989983 113725809464613363811987 := by
  unfold tailWord_2989983
  simp only [CollatzResearch.WordTrace]
  refine ⟨109053639126809714286710603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72702426084539809524473735 109053639126809714286710603)
  ·
    refine ⟨163580458690214571430065905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109053639126809714286710603 163580458690214571430065905)
    ·
      refine ⟨122685344017660928572549429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163580458690214571430065905 122685344017660928572549429)
      ·
        refine ⟨11501751001655712053676509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122685344017660928572549429 11501751001655712053676509)
        ·
          refine ⟨4313156625620892020128691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11501751001655712053676509 4313156625620892020128691)
          ·
            refine ⟨6469734938431338030193037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4313156625620892020128691 6469734938431338030193037)
            ·
              refine ⟨2426150601911751761322389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6469734938431338030193037 2426150601911751761322389)
              ·
                refine ⟨113725809464613363811987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2426150601911751761322389 113725809464613363811987)
                ·
                  rfl

theorem cell22_2989983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 6].length) (baseStart_2989983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989983 prefixEnd_2989983 := by exact prefixLift 2989983
  have htrace : WordTrace (prefixWord ++ tailWord_2989983) baseStart_2989983 baseEnd_2989983 := by
    simpa [prefixWord, tailWord_2989983, baseEnd_2989983] using wordTrace_append hprefix tailTrace_2989983
  have hstable : (prefixWord ++ tailWord_2989983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989983).length < 2 ^ (prefixWord ++ tailWord_2989983).sum := by decide
  have hdescent : baseEnd_2989983 < baseStart_2989983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2989985 : List Nat := [1, 2, 3, 4, 2, 2, 1, 1, 2, 4]
def baseStart_2989985 : Nat := 118140960795 + 2989985 * 2 ^ 59
def prefixEnd_2989985 : Nat := 4983230072969 + 3 ^ 40 * 2989985 * 2
def baseEnd_2989985 : Nat := 1023532969822392935757877

theorem tailTrace_2989985 : CollatzResearch.WordTrace tailWord_2989985 prefixEnd_2989985 1023532969822392935757877 := by
  unfold tailWord_2989985
  simp only [CollatzResearch.WordTrace]
  refine ⟨109053712072802468628283409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72702474715201645752188939 109053712072802468628283409)
  ·
    refine ⟨81790284054601851471212557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109053712072802468628283409 81790284054601851471212557)
    ·
      refine ⟨30671356520475694301704709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81790284054601851471212557 30671356520475694301704709)
      ·
        refine ⟨5750879347589192681569633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30671356520475694301704709 5750879347589192681569633)
        ·
          refine ⟨4313159510691894511177225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5750879347589192681569633 4313159510691894511177225)
          ·
            refine ⟨3234869633018920883382919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4313159510691894511177225 3234869633018920883382919)
            ·
              refine ⟨4852304449528381325074379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3234869633018920883382919 4852304449528381325074379)
              ·
                refine ⟨7278456674292571987611569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4852304449528381325074379 7278456674292571987611569)
                ·
                  refine ⟨5458842505719428990708677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7278456674292571987611569 5458842505719428990708677)
                  ·
                    refine ⟨1023532969822392935757877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5458842505719428990708677 1023532969822392935757877)
                    ·
                      rfl

theorem cell22_2989985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_2989985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2989985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2989985 prefixEnd_2989985 := by exact prefixLift 2989985
  have htrace : WordTrace (prefixWord ++ tailWord_2989985) baseStart_2989985 baseEnd_2989985 := by
    simpa [prefixWord, tailWord_2989985, baseEnd_2989985] using wordTrace_append hprefix tailTrace_2989985
  have hstable : (prefixWord ++ tailWord_2989985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2989985).length < 2 ^ (prefixWord ++ tailWord_2989985).sum := by decide
  have hdescent : baseEnd_2989985 < baseStart_2989985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2989985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990004 : List Nat := [2, 5, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_2990004 : Nat := 118140960795 + 2990004 * 2 ^ 59
def prefixEnd_2990004 : Nat := 4983230072969 + 3 ^ 40 * 2990004 * 2
def baseEnd_2990004 : Nat := 1023539473910683219532819

theorem tailTrace_2990004 : CollatzResearch.WordTrace tailWord_2990004 prefixEnd_2990004 1023539473910683219532819 := by
  unfold tailWord_2990004
  simp only [CollatzResearch.WordTrace]
  refine ⟨54527202529866817436612533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72702936706489089915483377 54527202529866817436612533)
  ·
    refine ⟨5111925237175014134682425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54527202529866817436612533 5111925237175014134682425)
    ·
      refine ⟨3833943927881260601011819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5111925237175014134682425 3833943927881260601011819)
      ·
        refine ⟨5750915891821890901517729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3833943927881260601011819 5750915891821890901517729)
        ·
          refine ⟨4313186918866418176138297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5750915891821890901517729 4313186918866418176138297)
          ·
            refine ⟨3234890189149813632103723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4313186918866418176138297 3234890189149813632103723)
            ·
              refine ⟨4852335283724720448155585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3234890189149813632103723 4852335283724720448155585)
              ·
                refine ⟨3639251462793540336116689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4852335283724720448155585 3639251462793540336116689)
                ·
                  refine ⟨2729438597095155252087517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3639251462793540336116689 2729438597095155252087517)
                  ·
                    refine ⟨1023539473910683219532819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2729438597095155252087517 1023539473910683219532819)
                    ·
                      rfl

theorem cell22_2990004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_2990004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990004 prefixEnd_2990004 := by exact prefixLift 2990004
  have htrace : WordTrace (prefixWord ++ tailWord_2990004) baseStart_2990004 baseEnd_2990004 := by
    simpa [prefixWord, tailWord_2990004, baseEnd_2990004] using wordTrace_append hprefix tailTrace_2990004
  have hstable : (prefixWord ++ tailWord_2990004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990004).length < 2 ^ (prefixWord ++ tailWord_2990004).sum := by decide
  have hdescent : baseEnd_2990004 < baseStart_2990004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990026 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 2, 5]
def baseStart_2990026 : Nat := 118140960795 + 2990026 * 2 ^ 59
def prefixEnd_2990026 : Nat := 4983230072969 + 3 ^ 40 * 2990026 * 2
def baseEnd_2990026 : Nat := 1023547004960282495482751

theorem tailTrace_2990026 : CollatzResearch.WordTrace tailWord_2990026 prefixEnd_2990026 1023547004960282495482751 := by
  unfold tailWord_2990026
  simp only [CollatzResearch.WordTrace]
  refine ⟨27263801866413483157631483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72703471643769288420350621 27263801866413483157631483)
  ·
    refine ⟨40895702799620224736447225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27263801866413483157631483 40895702799620224736447225)
    ·
      refine ⟨30671777099715168552335419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40895702799620224736447225 30671777099715168552335419)
      ·
        refine ⟨46007665649572752828503129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30671777099715168552335419 46007665649572752828503129)
        ·
          refine ⟨34505749237179564621377347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46007665649572752828503129 34505749237179564621377347)
          ·
            refine ⟨51758623855769346932066021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34505749237179564621377347 51758623855769346932066021)
            ·
              refine ⟨9704741972956752549762379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51758623855769346932066021 9704741972956752549762379)
              ·
                refine ⟨14557112959435128824643569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9704741972956752549762379 14557112959435128824643569)
                ·
                  refine ⟨10917834719576346618482677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14557112959435128824643569 10917834719576346618482677)
                  ·
                    refine ⟨1023547004960282495482751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10917834719576346618482677 1023547004960282495482751)
                    ·
                      rfl

theorem cell22_2990026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_2990026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990026 prefixEnd_2990026 := by exact prefixLift 2990026
  have htrace : WordTrace (prefixWord ++ tailWord_2990026) baseStart_2990026 baseEnd_2990026 := by
    simpa [prefixWord, tailWord_2990026, baseEnd_2990026] using wordTrace_append hprefix tailTrace_2990026
  have hstable : (prefixWord ++ tailWord_2990026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990026).length < 2 ^ (prefixWord ++ tailWord_2990026).sum := by decide
  have hdescent : baseEnd_2990026 < baseStart_2990026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990058 : List Nat := [3, 1, 3, 1, 2, 1, 1, 5, 1, 4]
def baseStart_2990058 : Nat := 118140960795 + 2990058 * 2 ^ 59
def prefixEnd_2990058 : Nat := 4983230072969 + 3 ^ 40 * 2990058 * 2
def baseEnd_2990058 : Nat := 1023557959214245078682653

theorem tailTrace_2990058 : CollatzResearch.WordTrace tailWord_2990058 prefixEnd_2990058 1023557959214245078682653 := by
  unfold tailWord_2990058
  simp only [CollatzResearch.WordTrace]
  refine ⟨27264093650384500523922707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72704249734358668063793885 27264093650384500523922707)
  ·
    refine ⟨40896140475576750785884061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27264093650384500523922707 40896140475576750785884061)
    ·
      refine ⟨15336052678341281544706523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40896140475576750785884061 15336052678341281544706523)
      ·
        refine ⟨23004079017511922317059785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15336052678341281544706523 23004079017511922317059785)
        ·
          refine ⟨17253059263133941737794839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23004079017511922317059785 17253059263133941737794839)
          ·
            refine ⟨25879588894700912606692259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17253059263133941737794839 25879588894700912606692259)
            ·
              refine ⟨38819383342051368910038389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25879588894700912606692259 38819383342051368910038389)
              ·
                refine ⟨3639317188317315835316099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38819383342051368910038389 3639317188317315835316099)
                ·
                  refine ⟨5458975782475973752974149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3639317188317315835316099 5458975782475973752974149)
                  ·
                    refine ⟨1023557959214245078682653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5458975782475973752974149 1023557959214245078682653)
                    ·
                      rfl

theorem cell22_2990058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_2990058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990058 prefixEnd_2990058 := by exact prefixLift 2990058
  have htrace : WordTrace (prefixWord ++ tailWord_2990058) baseStart_2990058 baseEnd_2990058 := by
    simpa [prefixWord, tailWord_2990058, baseEnd_2990058] using wordTrace_append hprefix tailTrace_2990058
  have hstable : (prefixWord ++ tailWord_2990058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990058).length < 2 ^ (prefixWord ++ tailWord_2990058).sum := by decide
  have hdescent : baseEnd_2990058 < baseStart_2990058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990073 : List Nat := [1, 2, 1, 3, 1, 6, 1, 1, 6]
def baseStart_2990073 : Nat := 118140960795 + 2990073 * 2 ^ 59
def prefixEnd_2990073 : Nat := 4983230072969 + 3 ^ 40 * 2990073 * 2
def baseEnd_2990073 : Nat := 341187698006930013185869

theorem tailTrace_2990073 : CollatzResearch.WordTrace tailWord_2990073 prefixEnd_2990073 341187698006930013185869 := by
  unfold tailWord_2990073
  simp only [CollatzResearch.WordTrace]
  refine ⟨109056921696483659657486873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72704614464322439771657915 109056921696483659657486873)
  ·
    refine ⟨81792691272362744743115155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109056921696483659657486873 81792691272362744743115155)
    ·
      refine ⟨122689036908544117114672733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81792691272362744743115155 122689036908544117114672733)
      ·
        refine ⟨46008388840704043918002275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122689036908544117114672733 46008388840704043918002275)
        ·
          refine ⟨69012583261056065877003413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46008388840704043918002275 69012583261056065877003413)
          ·
            refine ⟨3234964840362003087984535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69012583261056065877003413 3234964840362003087984535)
            ·
              refine ⟨4852447260543004631976803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3234964840362003087984535 4852447260543004631976803)
              ·
                refine ⟨7278670890814506947965205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4852447260543004631976803 7278670890814506947965205)
                ·
                  refine ⟨341187698006930013185869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7278670890814506947965205 341187698006930013185869)
                  ·
                    rfl

theorem cell22_2990073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 6].length) (baseStart_2990073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990073 prefixEnd_2990073 := by exact prefixLift 2990073
  have htrace : WordTrace (prefixWord ++ tailWord_2990073) baseStart_2990073 baseEnd_2990073 := by
    simpa [prefixWord, tailWord_2990073, baseEnd_2990073] using wordTrace_append hprefix tailTrace_2990073
  have hstable : (prefixWord ++ tailWord_2990073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990073).length < 2 ^ (prefixWord ++ tailWord_2990073).sum := by decide
  have hdescent : baseEnd_2990073 < baseStart_2990073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990122 : List Nat := [3, 1, 4, 1, 2, 2, 2, 2, 2, 3]
def baseStart_2990122 : Nat := 118140960795 + 2990122 * 2 ^ 59
def prefixEnd_2990122 : Nat := 4983230072969 + 3 ^ 40 * 2990122 * 2
def baseEnd_2990122 : Nat := 1023579867722170245082457

theorem tailTrace_2990122 : CollatzResearch.WordTrace tailWord_2990122 prefixEnd_2990122 1023579867722170245082457 := by
  unfold tailWord_2990122
  simp only [CollatzResearch.WordTrace]
  refine ⟨27264677218326535256505155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72705805915537427350680413 27264677218326535256505155)
  ·
    refine ⟨40897015827489802884757733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27264677218326535256505155 40897015827489802884757733)
    ·
      refine ⟨7668190467654338040892075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40897015827489802884757733 7668190467654338040892075)
      ·
        refine ⟨11502285701481507061338113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7668190467654338040892075 11502285701481507061338113)
        ·
          refine ⟨8626714276111130296003585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11502285701481507061338113 8626714276111130296003585)
          ·
            refine ⟨6470035707083347722002689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8626714276111130296003585 6470035707083347722002689)
            ·
              refine ⟨4852526780312510791502017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6470035707083347722002689 4852526780312510791502017)
              ·
                refine ⟨3639395085234383093626513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4852526780312510791502017 3639395085234383093626513)
                ·
                  refine ⟨2729546313925787320219885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3639395085234383093626513 2729546313925787320219885)
                  ·
                    refine ⟨1023579867722170245082457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2729546313925787320219885 1023579867722170245082457)
                    ·
                      rfl

theorem cell22_2990122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_2990122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990122 prefixEnd_2990122 := by exact prefixLift 2990122
  have htrace : WordTrace (prefixWord ++ tailWord_2990122) baseStart_2990122 baseEnd_2990122 := by
    simpa [prefixWord, tailWord_2990122, baseEnd_2990122] using wordTrace_append hprefix tailTrace_2990122
  have hstable : (prefixWord ++ tailWord_2990122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990122).length < 2 ^ (prefixWord ++ tailWord_2990122).sum := by decide
  have hdescent : baseEnd_2990122 < baseStart_2990122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990131 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 2, 6]
def baseStart_2990131 : Nat := 118140960795 + 2990131 * 2 ^ 59
def prefixEnd_2990131 : Nat := 4983230072969 + 3 ^ 40 * 2990131 * 2
def baseEnd_2990131 : Nat := 1023582948606097221607429

theorem tailTrace_2990131 : CollatzResearch.WordTrace tailWord_2990131 prefixEnd_2990131 1023582948606097221607429 := by
  unfold tailWord_2990131
  simp only [CollatzResearch.WordTrace]
  refine ⟨109059037130273535563098247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72706024753515690375398831 109059037130273535563098247)
  ·
    refine ⟨163588555695410303344647371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109059037130273535563098247 163588555695410303344647371)
    ·
      refine ⟨245382833543115455016971057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163588555695410303344647371 245382833543115455016971057)
      ·
        refine ⟨184037125157336591262728293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245382833543115455016971057 184037125157336591262728293)
        ·
          refine ⟨34506960967000610861761555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184037125157336591262728293 34506960967000610861761555)
          ·
            refine ⟨51760441450500916292642333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34506960967000610861761555 51760441450500916292642333)
            ·
              refine ⟨19410165543937843609740875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51760441450500916292642333 19410165543937843609740875)
              ·
                refine ⟨29115248315906765414611313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19410165543937843609740875 29115248315906765414611313)
                ·
                  refine ⟨21836436236930074060958485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29115248315906765414611313 21836436236930074060958485)
                  ·
                    refine ⟨1023582948606097221607429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21836436236930074060958485 1023582948606097221607429)
                    ·
                      rfl

theorem cell22_2990131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 6].length) (baseStart_2990131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990131 prefixEnd_2990131 := by exact prefixLift 2990131
  have htrace : WordTrace (prefixWord ++ tailWord_2990131) baseStart_2990131 baseEnd_2990131 := by
    simpa [prefixWord, tailWord_2990131, baseEnd_2990131] using wordTrace_append hprefix tailTrace_2990131
  have hstable : (prefixWord ++ tailWord_2990131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990131).length < 2 ^ (prefixWord ++ tailWord_2990131).sum := by decide
  have hdescent : baseEnd_2990131 < baseStart_2990131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990161 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 3, 7]
def baseStart_2990161 : Nat := 118140960795 + 2990161 * 2 ^ 59
def prefixEnd_2990161 : Nat := 4983230072969 + 3 ^ 40 * 2990161 * 2
def baseEnd_2990161 : Nat := 1023593218219187143357337

theorem tailTrace_2990161 : CollatzResearch.WordTrace tailWord_2990161 prefixEnd_2990161 1023593218219187143357337 := by
  unfold tailWord_2990161
  simp only [CollatzResearch.WordTrace]
  refine ⟨109060131320164850686690337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72706754213443233791126891 109060131320164850686690337)
  ·
    refine ⟨81795098490123638015017753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109060131320164850686690337 81795098490123638015017753)
    ·
      refine ⟨61346323867592728511263315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81795098490123638015017753 61346323867592728511263315)
      ·
        refine ⟨92019485801389092766894973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61346323867592728511263315 92019485801389092766894973)
        ·
          refine ⟨34507307175520909787585615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92019485801389092766894973 34507307175520909787585615)
          ·
            refine ⟨51760960763281364681378423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34507307175520909787585615 51760960763281364681378423)
            ·
              refine ⟨77641441144922047022067635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51760960763281364681378423 77641441144922047022067635)
              ·
                refine ⟨116462161717383070533101453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77641441144922047022067635 116462161717383070533101453)
                ·
                  refine ⟨43673310644018651449913045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116462161717383070533101453 43673310644018651449913045)
                  ·
                    refine ⟨1023593218219187143357337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43673310644018651449913045 1023593218219187143357337)
                    ·
                      rfl

theorem cell22_2990161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_2990161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990161 prefixEnd_2990161 := by exact prefixLift 2990161
  have htrace : WordTrace (prefixWord ++ tailWord_2990161) baseStart_2990161 baseEnd_2990161 := by
    simpa [prefixWord, tailWord_2990161, baseEnd_2990161] using wordTrace_append hprefix tailTrace_2990161
  have hstable : (prefixWord ++ tailWord_2990161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990161).length < 2 ^ (prefixWord ++ tailWord_2990161).sum := by decide
  have hdescent : baseEnd_2990161 < baseStart_2990161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990240 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 4, 3]
def baseStart_2990240 : Nat := 118140960795 + 2990240 * 2 ^ 59
def prefixEnd_2990240 : Nat := 4983230072969 + 3 ^ 40 * 2990240 * 2
def baseEnd_2990240 : Nat := 1023620261533657270632095

theorem tailTrace_2990240 : CollatzResearch.WordTrace tailWord_2990240 prefixEnd_2990240 1023620261533657270632095 := by
  unfold tailWord_2990240
  simp only [CollatzResearch.WordTrace]
  refine ⟨54531506343439323589408087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72708675124585764785877449 54531506343439323589408087)
  ·
    refine ⟨81797259515158985384112131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54531506343439323589408087 81797259515158985384112131)
    ·
      refine ⟨122695889272738478076168197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81797259515158985384112131 122695889272738478076168197)
      ·
        refine ⟨23005479238638464639281537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122695889272738478076168197 23005479238638464639281537)
        ·
          refine ⟨17254109428978848479461153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23005479238638464639281537 17254109428978848479461153)
          ·
            refine ⟨12940582071734136359595865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17254109428978848479461153 12940582071734136359595865)
            ·
              refine ⟨9705436553800602269696899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12940582071734136359595865 9705436553800602269696899)
              ·
                refine ⟨14558154830700903404545349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9705436553800602269696899 14558154830700903404545349)
                ·
                  refine ⟨2729654030756419388352253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14558154830700903404545349 2729654030756419388352253)
                  ·
                    refine ⟨1023620261533657270632095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2729654030756419388352253 1023620261533657270632095)
                    ·
                      rfl

theorem cell22_2990240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 4, 3].length) (baseStart_2990240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990240 prefixEnd_2990240 := by exact prefixLift 2990240
  have htrace : WordTrace (prefixWord ++ tailWord_2990240) baseStart_2990240 baseEnd_2990240 := by
    simpa [prefixWord, tailWord_2990240, baseEnd_2990240] using wordTrace_append hprefix tailTrace_2990240
  have hstable : (prefixWord ++ tailWord_2990240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990240).length < 2 ^ (prefixWord ++ tailWord_2990240).sum := by decide
  have hdescent : baseEnd_2990240 < baseStart_2990240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990242 : List Nat := [3, 3, 1, 3, 1, 3, 1, 1, 6]
def baseStart_2990242 : Nat := 118140960795 + 2990242 * 2 ^ 59
def prefixEnd_2990242 : Nat := 4983230072969 + 3 ^ 40 * 2990242 * 2
def baseEnd_2990242 : Nat := 341206982058176644027363

theorem tailTrace_2990242 : CollatzResearch.WordTrace tailWord_2990242 prefixEnd_2990242 341206982058176644027363 := by
  unfold tailWord_2990242
  simp only [CollatzResearch.WordTrace]
  refine ⟨27265771408217850380097245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72708723755247601013592653 27265771408217850380097245)
  ·
    refine ⟨10224664278081693892536467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27265771408217850380097245 10224664278081693892536467)
    ·
      refine ⟨15336996417122540838804701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10224664278081693892536467 15336996417122540838804701)
      ·
        refine ⟨5751373656420952814551763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15336996417122540838804701 5751373656420952814551763)
        ·
          refine ⟨8627060484631429221827645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5751373656420952814551763 8627060484631429221827645)
          ·
            refine ⟨3235147681736785958185367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8627060484631429221827645 3235147681736785958185367)
            ·
              refine ⟨4852721522605178937278051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3235147681736785958185367 4852721522605178937278051)
              ·
                refine ⟨7279082283907768405917077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4852721522605178937278051 7279082283907768405917077)
                ·
                  refine ⟨341206982058176644027363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7279082283907768405917077 341206982058176644027363)
                  ·
                    rfl

theorem cell22_2990242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_2990242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990242 prefixEnd_2990242 := by exact prefixLift 2990242
  have htrace : WordTrace (prefixWord ++ tailWord_2990242) baseStart_2990242 baseEnd_2990242 := by
    simpa [prefixWord, tailWord_2990242, baseEnd_2990242] using wordTrace_append hprefix tailTrace_2990242
  have hstable : (prefixWord ++ tailWord_2990242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990242).length < 2 ^ (prefixWord ++ tailWord_2990242).sum := by decide
  have hdescent : baseEnd_2990242 < baseStart_2990242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990261 : List Nat := [1, 3, 3, 4, 2, 1, 1, 2, 1, 4]
def baseStart_2990261 : Nat := 118140960795 + 2990261 * 2 ^ 59
def prefixEnd_2990261 : Nat := 4983230072969 + 3 ^ 40 * 2990261 * 2
def baseEnd_2990261 : Nat := 1023627450262820215857031

theorem tailTrace_2990261 : CollatzResearch.WordTrace tailWord_2990261 prefixEnd_2990261 1023627450262820215857031 := by
  unfold tailWord_2990261
  simp only [CollatzResearch.WordTrace]
  refine ⟨109063778619802567765330637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72709185746535045176887091 109063778619802567765330637)
  ·
    refine ⟨40898916982425962911998989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109063778619802567765330637 40898916982425962911998989)
    ·
      refine ⟨15337093868409736091999621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40898916982425962911998989 15337093868409736091999621)
      ·
        refine ⟨2875705100326825517249929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15337093868409736091999621 2875705100326825517249929)
        ·
          refine ⟨2156778825245119137937447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2875705100326825517249929 2156778825245119137937447)
          ·
            refine ⟨3235168237867678706906171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2156778825245119137937447 3235168237867678706906171)
            ·
              refine ⟨4852752356801518060359257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3235168237867678706906171 4852752356801518060359257)
              ·
                refine ⟨3639564267601138545269443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4852752356801518060359257 3639564267601138545269443)
                ·
                  refine ⟨5459346401401707817904165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3639564267601138545269443 5459346401401707817904165)
                  ·
                    refine ⟨1023627450262820215857031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5459346401401707817904165 1023627450262820215857031)
                    ·
                      rfl

theorem cell22_2990261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_2990261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990261 prefixEnd_2990261 := by exact prefixLift 2990261
  have htrace : WordTrace (prefixWord ++ tailWord_2990261) baseStart_2990261 baseEnd_2990261 := by
    simpa [prefixWord, tailWord_2990261, baseEnd_2990261] using wordTrace_append hprefix tailTrace_2990261
  have hstable : (prefixWord ++ tailWord_2990261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990261).length < 2 ^ (prefixWord ++ tailWord_2990261).sum := by decide
  have hdescent : baseEnd_2990261 < baseStart_2990261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990274 : List Nat := [3, 5, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_2990274 : Nat := 118140960795 + 2990274 * 2 ^ 59
def prefixEnd_2990274 : Nat := 4983230072969 + 3 ^ 40 * 2990274 * 2
def baseEnd_2990274 : Nat := 1023631900428492515281991

theorem tailTrace_2990274 : CollatzResearch.WordTrace tailWord_2990274 prefixEnd_2990274 1023631900428492515281991 := by
  unfold tailWord_2990274
  simp only [CollatzResearch.WordTrace]
  refine ⟨27266063192188867746388469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72709501845836980657035917 27266063192188867746388469)
  ·
    refine ⟨2556193424267706351223919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27266063192188867746388469 2556193424267706351223919)
    ·
      refine ⟨3834290136401559526835879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2556193424267706351223919 3834290136401559526835879)
      ·
        refine ⟨5751435204602339290253819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3834290136401559526835879 5751435204602339290253819)
        ·
          refine ⟨8627152806903508935380729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5751435204602339290253819 8627152806903508935380729)
          ·
            refine ⟨6470364605177631701535547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8627152806903508935380729 6470364605177631701535547)
            ·
              refine ⟨9705546907766447552303321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6470364605177631701535547 9705546907766447552303321)
              ·
                refine ⟨7279160180824835664227491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9705546907766447552303321 7279160180824835664227491)
                ·
                  refine ⟨10918740271237253496341237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7279160180824835664227491 10918740271237253496341237)
                  ·
                    refine ⟨1023631900428492515281991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10918740271237253496341237 1023631900428492515281991)
                    ·
                      rfl

theorem cell22_2990274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_2990274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990274 prefixEnd_2990274 := by exact prefixLift 2990274
  have htrace : WordTrace (prefixWord ++ tailWord_2990274) baseStart_2990274 baseEnd_2990274 := by
    simpa [prefixWord, tailWord_2990274, baseEnd_2990274] using wordTrace_append hprefix tailTrace_2990274
  have hstable : (prefixWord ++ tailWord_2990274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990274).length < 2 ^ (prefixWord ++ tailWord_2990274).sum := by decide
  have hdescent : baseEnd_2990274 < baseStart_2990274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990298 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 7]
def baseStart_2990298 : Nat := 118140960795 + 2990298 * 2 ^ 59
def prefixEnd_2990298 : Nat := 4983230072969 + 3 ^ 40 * 2990298 * 2
def baseEnd_2990298 : Nat := 341213372039654817560639

theorem tailTrace_2990298 : CollatzResearch.WordTrace tailWord_2990298 prefixEnd_2990298 341213372039654817560639 := by
  unfold tailWord_2990298
  simp only [CollatzResearch.WordTrace]
  refine ⟨27266282030167130771106887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72710085413779015389618365 27266282030167130771106887)
  ·
    refine ⟨40899423045250696156660331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27266282030167130771106887 40899423045250696156660331)
    ·
      refine ⟨61349134567876044234990497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40899423045250696156660331 61349134567876044234990497)
      ·
        refine ⟨46011850925907033176242873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61349134567876044234990497 46011850925907033176242873)
        ·
          refine ⟨34508888194430274882182155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46011850925907033176242873 34508888194430274882182155)
          ·
            refine ⟨51763332291645412323273233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34508888194430274882182155 51763332291645412323273233)
            ·
              refine ⟨38822499218734059242454925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51763332291645412323273233 38822499218734059242454925)
              ·
                refine ⟨14558437207025272215920597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38822499218734059242454925 14558437207025272215920597)
                ·
                  refine ⟨341213372039654817560639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14558437207025272215920597 341213372039654817560639)
                  ·
                    rfl

theorem cell22_2990298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_2990298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990298 prefixEnd_2990298 := by exact prefixLift 2990298
  have htrace : WordTrace (prefixWord ++ tailWord_2990298) baseStart_2990298 baseEnd_2990298 := by
    simpa [prefixWord, tailWord_2990298, baseEnd_2990298] using wordTrace_append hprefix tailTrace_2990298
  have hstable : (prefixWord ++ tailWord_2990298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990298).length < 2 ^ (prefixWord ++ tailWord_2990298).sum := by decide
  have hdescent : baseEnd_2990298 < baseStart_2990298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990313 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 2, 5]
def baseStart_2990313 : Nat := 118140960795 + 2990313 * 2 ^ 59
def prefixEnd_2990313 : Nat := 4983230072969 + 3 ^ 40 * 2990313 * 2
def baseEnd_2990313 : Nat := 1023645250925509413556871

theorem tailTrace_2990313 : CollatzResearch.WordTrace tailWord_2990313 prefixEnd_2990313 1023645250925509413556871 := by
  unfold tailWord_2990313
  simp only [CollatzResearch.WordTrace]
  refine ⟨109065675215614180646223593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72710450143742787097482395 109065675215614180646223593)
  ·
    refine ⟨81799256411710635484667695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109065675215614180646223593 81799256411710635484667695)
    ·
      refine ⟨122698884617565953227001543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81799256411710635484667695 122698884617565953227001543)
      ·
        refine ⟨184048326926348929840502315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122698884617565953227001543 184048326926348929840502315)
        ·
          refine ⟨276072490389523394760753473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184048326926348929840502315 276072490389523394760753473)
          ·
            refine ⟨207054367792142546070565105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276072490389523394760753473 207054367792142546070565105)
            ·
              refine ⟨155290775844106909552923829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207054367792142546070565105 155290775844106909552923829)
              ·
                refine ⟨14558510235385022770586609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 155290775844106909552923829 14558510235385022770586609)
                ·
                  refine ⟨10918882676538767077939957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14558510235385022770586609 10918882676538767077939957)
                  ·
                    refine ⟨1023645250925509413556871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10918882676538767077939957 1023645250925509413556871)
                    ·
                      rfl

theorem cell22_2990313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_2990313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990313 prefixEnd_2990313 := by exact prefixLift 2990313
  have htrace : WordTrace (prefixWord ++ tailWord_2990313) baseStart_2990313 baseEnd_2990313 := by
    simpa [prefixWord, tailWord_2990313, baseEnd_2990313] using wordTrace_append hprefix tailTrace_2990313
  have hstable : (prefixWord ++ tailWord_2990313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990313).length < 2 ^ (prefixWord ++ tailWord_2990313).sum := by decide
  have hdescent : baseEnd_2990313 < baseStart_2990313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990360 : List Nat := [2, 1, 2, 3, 1, 2, 4, 1, 6]
def baseStart_2990360 : Nat := 118140960795 + 2990360 * 2 ^ 59
def prefixEnd_2990360 : Nat := 4983230072969 + 3 ^ 40 * 2990360 * 2
def baseEnd_2990360 : Nat := 341220446662005652543909

theorem tailTrace_2990360 : CollatzResearch.WordTrace tailWord_2990360 prefixEnd_2990360 341220446662005652543909 := by
  unfold tailWord_2990360
  simp only [CollatzResearch.WordTrace]
  refine ⟨54533694723221953836592267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72711592964295938448789689 54533694723221953836592267)
  ·
    refine ⟨81800542084832930754888401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54533694723221953836592267 81800542084832930754888401)
    ·
      refine ⟨61350406563624698066166301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81800542084832930754888401 61350406563624698066166301)
      ·
        refine ⟨23006402461359261774812363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61350406563624698066166301 23006402461359261774812363)
        ·
          refine ⟨34509603692038892662218545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23006402461359261774812363 34509603692038892662218545)
          ·
            refine ⟨25882202769029169496663909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34509603692038892662218545 25882202769029169496663909)
            ·
              refine ⟨4852913019192969280624483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25882202769029169496663909 4852913019192969280624483)
              ·
                refine ⟨7279369528789453920936725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4852913019192969280624483 7279369528789453920936725)
                ·
                  refine ⟨341220446662005652543909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7279369528789453920936725 341220446662005652543909)
                  ·
                    rfl

theorem cell22_2990360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 6].length) (baseStart_2990360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990360 prefixEnd_2990360 := by exact prefixLift 2990360
  have htrace : WordTrace (prefixWord ++ tailWord_2990360) baseStart_2990360 baseEnd_2990360 := by
    simpa [prefixWord, tailWord_2990360, baseEnd_2990360] using wordTrace_append hprefix tailTrace_2990360
  have hstable : (prefixWord ++ tailWord_2990360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990360).length < 2 ^ (prefixWord ++ tailWord_2990360).sum := by decide
  have hdescent : baseEnd_2990360 < baseStart_2990360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990366 : List Nat := [4, 3, 2, 1, 1, 2, 3, 1, 5]
def baseStart_2990366 : Nat := 118140960795 + 2990366 * 2 ^ 59
def prefixEnd_2990366 : Nat := 4983230072969 + 3 ^ 40 * 2990366 * 2
def baseEnd_2990366 : Nat := 341221131302878313993903

theorem tailTrace_2990366 : CollatzResearch.WordTrace tailWord_2990366 prefixEnd_2990366 341221131302878313993903 := by
  unfold tailWord_2990366
  simp only [CollatzResearch.WordTrace]
  refine ⟨13633451035552771337237869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72711738856281447131935301 13633451035552771337237869)
  ·
    refine ⟨5112544138332289251464201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13633451035552771337237869 5112544138332289251464201)
    ·
      refine ⟨3834408103749216938598151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5112544138332289251464201 3834408103749216938598151)
      ·
        refine ⟨5751612155623825407897227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3834408103749216938598151 5751612155623825407897227)
        ·
          refine ⟨8627418233435738111845841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5751612155623825407897227 8627418233435738111845841)
          ·
            refine ⟨6470563675076803583884381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8627418233435738111845841 6470563675076803583884381)
            ·
              refine ⟨2426461378153801343956643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6470563675076803583884381 2426461378153801343956643)
              ·
                refine ⟨3639692067230702015934965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2426461378153801343956643 3639692067230702015934965)
                ·
                  refine ⟨341221131302878313993903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3639692067230702015934965 341221131302878313993903)
                  ·
                    rfl

theorem cell22_2990366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_2990366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990366 prefixEnd_2990366 := by exact prefixLift 2990366
  have htrace : WordTrace (prefixWord ++ tailWord_2990366) baseStart_2990366 baseEnd_2990366 := by
    simpa [prefixWord, tailWord_2990366, baseEnd_2990366] using wordTrace_append hprefix tailTrace_2990366
  have hstable : (prefixWord ++ tailWord_2990366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990366).length < 2 ^ (prefixWord ++ tailWord_2990366).sum := by decide
  have hdescent : baseEnd_2990366 < baseStart_2990366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990394 : List Nat := [3, 1, 1, 1, 4, 4, 1, 3, 4]
def baseStart_2990394 : Nat := 118140960795 + 2990394 * 2 ^ 59
def prefixEnd_2990394 : Nat := 4983230072969 + 3 ^ 40 * 2990394 * 2
def baseEnd_2990394 : Nat := 341224326293617400760541

theorem tailTrace_2990394 : CollatzResearch.WordTrace tailWord_2990394 prefixEnd_2990394 341224326293617400760541 := by
  unfold tailWord_2990394
  simp only [CollatzResearch.WordTrace]
  refine ⟨27267157382080182869980559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72712419685547154319948157 27267157382080182869980559)
  ·
    refine ⟨40900736073120274304970839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27267157382080182869980559 40900736073120274304970839)
    ·
      refine ⟨61351104109680411457456259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40900736073120274304970839 61351104109680411457456259)
      ·
        refine ⟨92026656164520617186184389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61351104109680411457456259 92026656164520617186184389)
        ·
          refine ⟨17254998030847615722409573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92026656164520617186184389 17254998030847615722409573)
          ·
            refine ⟨3235312130783927947951795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17254998030847615722409573 3235312130783927947951795)
            ·
              refine ⟨4852968196175891921927693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3235312130783927947951795 4852968196175891921927693)
              ·
                refine ⟨1819863073565959470722885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4852968196175891921927693 1819863073565959470722885)
                ·
                  refine ⟨341224326293617400760541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1819863073565959470722885 341224326293617400760541)
                  ·
                    rfl

theorem cell22_2990394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_2990394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990394 prefixEnd_2990394 := by exact prefixLift 2990394
  have htrace : WordTrace (prefixWord ++ tailWord_2990394) baseStart_2990394 baseEnd_2990394 := by
    simpa [prefixWord, tailWord_2990394, baseEnd_2990394] using wordTrace_append hprefix tailTrace_2990394
  have hstable : (prefixWord ++ tailWord_2990394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990394).length < 2 ^ (prefixWord ++ tailWord_2990394).sum := by decide
  have hdescent : baseEnd_2990394 < baseStart_2990394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990557 : List Nat := [1, 4, 3, 1, 1, 1, 3, 8]
def baseStart_2990557 : Nat := 118140960795 + 2990557 * 2 ^ 59
def prefixEnd_2990557 : Nat := 4983230072969 + 3 ^ 40 * 2990557 * 2
def baseEnd_2990557 : Nat := 113747641901330456717347

theorem tailTrace_2990557 : CollatzResearch.WordTrace tailWord_2990557 prefixEnd_2990557 113747641901330456717347 := by
  unfold tailWord_2990557
  simp only [CollatzResearch.WordTrace]
  refine ⟨109074574626730210318105925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72716383084486806878737283 109074574626730210318105925)
  ·
    refine ⟨20451482742511914434644861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109074574626730210318105925 20451482742511914434644861)
    ·
      refine ⟨7669306028441967912991823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20451482742511914434644861 7669306028441967912991823)
      ·
        refine ⟨11503959042662951869487735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7669306028441967912991823 11503959042662951869487735)
        ·
          refine ⟨17255938563994427804231603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11503959042662951869487735 17255938563994427804231603)
          ·
            refine ⟨25883907845991641706347405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17255938563994427804231603 25883907845991641706347405)
            ·
              refine ⟨9706465442246865639880277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25883907845991641706347405 9706465442246865639880277)
              ·
                refine ⟨113747641901330456717347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9706465442246865639880277 113747641901330456717347)
                ·
                  rfl

theorem cell22_2990557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 8].length) (baseStart_2990557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990557 prefixEnd_2990557 := by exact prefixLift 2990557
  have htrace : WordTrace (prefixWord ++ tailWord_2990557) baseStart_2990557 baseEnd_2990557 := by
    simpa [prefixWord, tailWord_2990557, baseEnd_2990557] using wordTrace_append hprefix tailTrace_2990557
  have hstable : (prefixWord ++ tailWord_2990557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990557).length < 2 ^ (prefixWord ++ tailWord_2990557).sum := by decide
  have hdescent : baseEnd_2990557 < baseStart_2990557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990563 : List Nat := [1, 1, 1, 6, 4, 1, 1, 3, 4]
def baseStart_2990563 : Nat := 118140960795 + 2990563 * 2 ^ 59
def prefixEnd_2990563 : Nat := 4983230072969 + 3 ^ 40 * 2990563 * 2
def baseEnd_2990563 : Nat := 341243610344864031602035

theorem tailTrace_2990563 : CollatzResearch.WordTrace tailWord_2990563 prefixEnd_2990563 341243610344864031602035 := by
  unfold tailWord_2990563
  simp only [CollatzResearch.WordTrace]
  refine ⟨109074793464708473342824343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72716528976472315561882895 109074793464708473342824343)
  ·
    refine ⟨163612190197062710014236515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109074793464708473342824343 163612190197062710014236515)
    ·
      refine ⟨245418285295594065021354773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163612190197062710014236515 245418285295594065021354773)
      ·
        refine ⟨11503982123230971797876005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 245418285295594065021354773 11503982123230971797876005)
        ·
          refine ⟨2156996648105807212101751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11503982123230971797876005 2156996648105807212101751)
          ·
            refine ⟨3235494972158710818152627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2156996648105807212101751 3235494972158710818152627)
            ·
              refine ⟨4853242458238066227228941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3235494972158710818152627 4853242458238066227228941)
              ·
                refine ⟨1819965921839274835210853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4853242458238066227228941 1819965921839274835210853)
                ·
                  refine ⟨341243610344864031602035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1819965921839274835210853 341243610344864031602035)
                  ·
                    rfl

theorem cell22_2990563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 4].length) (baseStart_2990563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990563 prefixEnd_2990563 := by exact prefixLift 2990563
  have htrace : WordTrace (prefixWord ++ tailWord_2990563) baseStart_2990563 baseEnd_2990563 := by
    simpa [prefixWord, tailWord_2990563, baseEnd_2990563] using wordTrace_append hprefix tailTrace_2990563
  have hstable : (prefixWord ++ tailWord_2990563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990563).length < 2 ^ (prefixWord ++ tailWord_2990563).sum := by decide
  have hdescent : baseEnd_2990563 < baseStart_2990563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990647 : List Nat := [1, 1, 3, 1, 2, 3, 2, 3, 6]
def baseStart_2990647 : Nat := 118140960795 + 2990647 * 2 ^ 59
def prefixEnd_2990647 : Nat := 4983230072969 + 3 ^ 40 * 2990647 * 2
def baseEnd_2990647 : Nat := 341253195317081291901949

theorem tailTrace_2990647 : CollatzResearch.WordTrace tailWord_2990647 prefixEnd_2990647 341253195317081291901949 := by
  unfold tailWord_2990647
  simp only [CollatzResearch.WordTrace]
  refine ⟨109077857196404155688882195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72718571464269437125921463 109077857196404155688882195)
  ·
    refine ⟨163616785794606233533323293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109077857196404155688882195 163616785794606233533323293)
    ·
      refine ⟨61356294672977337574996235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163616785794606233533323293 61356294672977337574996235)
      ·
        refine ⟨92034442009466006362494353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61356294672977337574996235 92034442009466006362494353)
        ·
          refine ⟨69025831507099504771870765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92034442009466006362494353 69025831507099504771870765)
          ·
            refine ⟨25884686815162314289451537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69025831507099504771870765 25884686815162314289451537)
            ·
              refine ⟨19413515111371735717088653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25884686815162314289451537 19413515111371735717088653)
              ·
                refine ⟨7280068166764400893908245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19413515111371735717088653 7280068166764400893908245)
                ·
                  refine ⟨341253195317081291901949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7280068166764400893908245 341253195317081291901949)
                  ·
                    rfl

theorem cell22_2990647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 6].length) (baseStart_2990647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990647 prefixEnd_2990647 := by exact prefixLift 2990647
  have htrace : WordTrace (prefixWord ++ tailWord_2990647) baseStart_2990647 baseEnd_2990647 := by
    simpa [prefixWord, tailWord_2990647, baseEnd_2990647] using wordTrace_append hprefix tailTrace_2990647
  have hstable : (prefixWord ++ tailWord_2990647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990647).length < 2 ^ (prefixWord ++ tailWord_2990647).sum := by decide
  have hdescent : baseEnd_2990647 < baseStart_2990647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990679 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 4, 3]
def baseStart_2990679 : Nat := 118140960795 + 2990679 * 2 ^ 59
def prefixEnd_2990679 : Nat := 4983230072969 + 3 ^ 40 * 2990679 * 2
def baseEnd_2990679 : Nat := 1023770540205206458905749

theorem tailTrace_2990679 : CollatzResearch.WordTrace tailWord_2990679 prefixEnd_2990679 1023770540205206458905749 := by
  unfold tailWord_2990679
  simp only [CollatzResearch.WordTrace]
  refine ⟨109079024332288225154047091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72719349554858816769364727 109079024332288225154047091)
  ·
    refine ⟨163618536498432337731070637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109079024332288225154047091 163618536498432337731070637)
    ·
      refine ⟨61356951186912126649151489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163618536498432337731070637 61356951186912126649151489)
      ·
        refine ⟨46017713390184094986863617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61356951186912126649151489 46017713390184094986863617)
        ·
          refine ⟨34513285042638071240147713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46017713390184094986863617 34513285042638071240147713)
          ·
            refine ⟨25884963781978553430110785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34513285042638071240147713 25884963781978553430110785)
            ·
              refine ⟨19413722836483915072583089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25884963781978553430110785 19413722836483915072583089)
              ·
                refine ⟨14560292127362936304437317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19413722836483915072583089 14560292127362936304437317)
                ·
                  refine ⟨2730054773880550557081997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14560292127362936304437317 2730054773880550557081997)
                  ·
                    refine ⟨1023770540205206458905749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2730054773880550557081997 1023770540205206458905749)
                    ·
                      rfl

theorem cell22_2990679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_2990679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990679 prefixEnd_2990679 := by exact prefixLift 2990679
  have htrace : WordTrace (prefixWord ++ tailWord_2990679) baseStart_2990679 baseEnd_2990679 := by
    simpa [prefixWord, tailWord_2990679, baseEnd_2990679] using wordTrace_append hprefix tailTrace_2990679
  have hstable : (prefixWord ++ tailWord_2990679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990679).length < 2 ^ (prefixWord ++ tailWord_2990679).sum := by decide
  have hdescent : baseEnd_2990679 < baseStart_2990679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990692 : List Nat := [2, 3, 1, 1, 2, 2, 11]
def baseStart_2990692 : Nat := 118140960795 + 2990692 * 2 ^ 59
def prefixEnd_2990692 : Nat := 4983230072969 + 3 ^ 40 * 2990692 * 2
def baseEnd_2990692 : Nat := 37917592235958472530767

theorem tailTrace_2990692 : CollatzResearch.WordTrace tailWord_2990692 prefixEnd_2990692 37917592235958472530767 := by
  unfold tailWord_2990692
  simp only [CollatzResearch.WordTrace]
  refine ⟨54539749240620564187135165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72719665654160752249513553 54539749240620564187135165)
  ·
    refine ⟨20452405965232711570175687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54539749240620564187135165 20452405965232711570175687)
    ·
      refine ⟨30678608947849067355263531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20452405965232711570175687 30678608947849067355263531)
      ·
        refine ⟨46017913421773601032895297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30678608947849067355263531 46017913421773601032895297)
        ·
          refine ⟨34513435066330200774671473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46017913421773601032895297 34513435066330200774671473)
          ·
            refine ⟨25885076299747650581003605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34513435066330200774671473 25885076299747650581003605)
            ·
              refine ⟨37917592235958472530767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25885076299747650581003605 37917592235958472530767)
              ·
                rfl

theorem cell22_2990692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 11].length) (baseStart_2990692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990692 prefixEnd_2990692 := by exact prefixLift 2990692
  have htrace : WordTrace (prefixWord ++ tailWord_2990692) baseStart_2990692 baseEnd_2990692 := by
    simpa [prefixWord, tailWord_2990692, baseEnd_2990692] using wordTrace_append hprefix tailTrace_2990692
  have hstable : (prefixWord ++ tailWord_2990692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990692).length < 2 ^ (prefixWord ++ tailWord_2990692).sum := by decide
  have hdescent : baseEnd_2990692 < baseStart_2990692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990713 : List Nat := [1, 2, 1, 3, 3, 3, 3, 1, 2, 3]
def baseStart_2990713 : Nat := 118140960795 + 2990713 * 2 ^ 59
def prefixEnd_2990713 : Nat := 4983230072969 + 3 ^ 40 * 2990713 * 2
def baseEnd_2990713 : Nat := 1023782179100041703555645

theorem tailTrace_2990713 : CollatzResearch.WordTrace tailWord_2990713 prefixEnd_2990713 1023782179100041703555645 := by
  unfold tailWord_2990713
  simp only [CollatzResearch.WordTrace]
  refine ⟨109080264414165048960784793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72720176276110032640523195 109080264414165048960784793)
  ·
    refine ⟨81810198310623786720588595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109080264414165048960784793 81810198310623786720588595)
    ·
      refine ⟨122715297465935680080882893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81810198310623786720588595 122715297465935680080882893)
      ·
        refine ⟨46018236549725880030331085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122715297465935680080882893 46018236549725880030331085)
        ·
          refine ⟨17256838706147205011374157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46018236549725880030331085 17256838706147205011374157)
          ·
            refine ⟨6471314514805201879265309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17256838706147205011374157 6471314514805201879265309)
            ·
              refine ⟨2426742943051950704724491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6471314514805201879265309 2426742943051950704724491)
              ·
                refine ⟨3640114414577926057086737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2426742943051950704724491 3640114414577926057086737)
                ·
                  refine ⟨2730085810933444542815053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3640114414577926057086737 2730085810933444542815053)
                  ·
                    refine ⟨1023782179100041703555645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2730085810933444542815053 1023782179100041703555645)
                    ·
                      rfl

theorem cell22_2990713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 2, 3].length) (baseStart_2990713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990713 prefixEnd_2990713 := by exact prefixLift 2990713
  have htrace : WordTrace (prefixWord ++ tailWord_2990713) baseStart_2990713 baseEnd_2990713 := by
    simpa [prefixWord, tailWord_2990713, baseEnd_2990713] using wordTrace_append hprefix tailTrace_2990713
  have hstable : (prefixWord ++ tailWord_2990713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990713).length < 2 ^ (prefixWord ++ tailWord_2990713).sum := by decide
  have hdescent : baseEnd_2990713 < baseStart_2990713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990771 : List Nat := [1, 1, 1, 2, 3, 4, 4, 1, 5]
def baseStart_2990771 : Nat := 118140960795 + 2990771 * 2 ^ 59
def prefixEnd_2990771 : Nat := 4983230072969 + 3 ^ 40 * 2990771 * 2
def baseEnd_2990771 : Nat := 341267344561782961868489

theorem tailTrace_2990771 : CollatzResearch.WordTrace tailWord_2990771 prefixEnd_2990771 341267344561782961868489 := by
  unfold tailWord_2990771
  simp only [CollatzResearch.WordTrace]
  refine ⟨109082379847954924866396167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72721586565303283244264111 109082379847954924866396167)
  ·
    refine ⟨163623569771932387299594251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109082379847954924866396167 163623569771932387299594251)
    ·
      refine ⟨245435354657898580949391377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163623569771932387299594251 245435354657898580949391377)
      ·
        refine ⟨184076515993423935712043533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245435354657898580949391377 184076515993423935712043533)
        ·
          refine ⟨69028693497533975892016325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184076515993423935712043533 69028693497533975892016325)
          ·
            refine ⟨12942880030787620479753061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69028693497533975892016325 12942880030787620479753061)
            ·
              refine ⟨2426790005772678839953699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12942880030787620479753061 2426790005772678839953699)
              ·
                refine ⟨3640185008659018259930549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2426790005772678839953699 3640185008659018259930549)
                ·
                  refine ⟨341267344561782961868489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3640185008659018259930549 341267344561782961868489)
                  ·
                    rfl

theorem cell22_2990771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 5].length) (baseStart_2990771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990771 prefixEnd_2990771 := by exact prefixLift 2990771
  have htrace : WordTrace (prefixWord ++ tailWord_2990771) baseStart_2990771 baseEnd_2990771 := by
    simpa [prefixWord, tailWord_2990771, baseEnd_2990771] using wordTrace_append hprefix tailTrace_2990771
  have hstable : (prefixWord ++ tailWord_2990771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990771).length < 2 ^ (prefixWord ++ tailWord_2990771).sum := by decide
  have hdescent : baseEnd_2990771 < baseStart_2990771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990831 : List Nat := [1, 1, 2, 1, 5, 3, 2, 1, 1, 5]
def baseStart_2990831 : Nat := 118140960795 + 2990831 * 2 ^ 59
def prefixEnd_2990831 : Nat := 4983230072969 + 3 ^ 40 * 2990831 * 2
def baseEnd_2990831 : Nat := 1023822572911528729105283

theorem tailTrace_2990831 : CollatzResearch.WordTrace tailWord_2990831 prefixEnd_2990831 1023822572911528729105283 := by
  unfold tailWord_2990831
  simp only [CollatzResearch.WordTrace]
  refine ⟨109084568227737555113580347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72723045485158370075720231 109084568227737555113580347)
  ·
    refine ⟨163626852341606332670370521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109084568227737555113580347 163626852341606332670370521)
    ·
      refine ⟨122720139256204749502777891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163626852341606332670370521 122720139256204749502777891)
      ·
        refine ⟨184080208884307124254166837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122720139256204749502777891 184080208884307124254166837)
        ·
          refine ⟨17257519582903792898828141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184080208884307124254166837 17257519582903792898828141)
          ·
            refine ⟨6471569843588922337060553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17257519582903792898828141 6471569843588922337060553)
            ·
              refine ⟨4853677382691691752795415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6471569843588922337060553 4853677382691691752795415)
              ·
                refine ⟨7280516074037537629193123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4853677382691691752795415 7280516074037537629193123)
                ·
                  refine ⟨10920774111056306443789685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7280516074037537629193123 10920774111056306443789685)
                  ·
                    refine ⟨1023822572911528729105283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10920774111056306443789685 1023822572911528729105283)
                    ·
                      rfl

theorem cell22_2990831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 5].length) (baseStart_2990831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990831 prefixEnd_2990831 := by exact prefixLift 2990831
  have htrace : WordTrace (prefixWord ++ tailWord_2990831) baseStart_2990831 baseEnd_2990831 := by
    simpa [prefixWord, tailWord_2990831, baseEnd_2990831] using wordTrace_append hprefix tailTrace_2990831
  have hstable : (prefixWord ++ tailWord_2990831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990831).length < 2 ^ (prefixWord ++ tailWord_2990831).sum := by decide
  have hdescent : baseEnd_2990831 < baseStart_2990831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990850 : List Nat := [3, 4, 1, 1, 1, 3, 2, 3, 4]
def baseStart_2990850 : Nat := 118140960795 + 2990850 * 2 ^ 59
def prefixEnd_2990850 : Nat := 4983230072969 + 3 ^ 40 * 2990850 * 2
def baseEnd_2990850 : Nat := 341276358999939670960075

theorem tailTrace_2990850 : CollatzResearch.WordTrace tailWord_2990850 prefixEnd_2990850 341276358999939670960075 := by
  unfold tailWord_2990850
  simp only [CollatzResearch.WordTrace]
  refine ⟨27271315303667180339630501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72723507476445814239014669 27271315303667180339630501)
  ·
    refine ⟨5113371619437596313680719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27271315303667180339630501 5113371619437596313680719)
    ·
      refine ⟨7670057429156394470521079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5113371619437596313680719 7670057429156394470521079)
      ·
        refine ⟨11505086143734591705781619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7670057429156394470521079 11505086143734591705781619)
        ·
          refine ⟨17257629215601887558672429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11505086143734591705781619 17257629215601887558672429)
          ·
            refine ⟨6471610955850707834502161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17257629215601887558672429 6471610955850707834502161)
            ·
              refine ⟨4853708216888030875876621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6471610955850707834502161 4853708216888030875876621)
              ·
                refine ⟨1820140581333011578453733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4853708216888030875876621 1820140581333011578453733)
                ·
                  refine ⟨341276358999939670960075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1820140581333011578453733 341276358999939670960075)
                  ·
                    rfl

theorem cell22_2990850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_2990850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990850 prefixEnd_2990850 := by exact prefixLift 2990850
  have htrace : WordTrace (prefixWord ++ tailWord_2990850) baseStart_2990850 baseEnd_2990850 := by
    simpa [prefixWord, tailWord_2990850, baseEnd_2990850] using wordTrace_append hprefix tailTrace_2990850
  have hstable : (prefixWord ++ tailWord_2990850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990850).length < 2 ^ (prefixWord ++ tailWord_2990850).sum := by decide
  have hdescent : baseEnd_2990850 < baseStart_2990850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990940 : List Nat := [2, 2, 4, 2, 1, 1, 4, 1, 5]
def baseStart_2990940 : Nat := 118140960795 + 2990940 * 2 ^ 59
def prefixEnd_2990940 : Nat := 4983230072969 + 3 ^ 40 * 2990940 * 2
def baseEnd_2990940 : Nat := 341286628613029592709983

theorem tailTrace_2990940 : CollatzResearch.WordTrace tailWord_2990940 prefixEnd_2990940 341286628613029592709983 := by
  unfold tailWord_2990940
  simp only [CollatzResearch.WordTrace]
  refine ⟨54544271892171333364649137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72725695856228444486198849 54544271892171333364649137)
  ·
    refine ⟨40908203919128500023486853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54544271892171333364649137 40908203919128500023486853)
    ·
      refine ⟨7670288234836593754403785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40908203919128500023486853 7670288234836593754403785)
      ·
        refine ⟨5752716176127445315802839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7670288234836593754403785 5752716176127445315802839)
        ·
          refine ⟨8629074264191167973704259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5752716176127445315802839 8629074264191167973704259)
          ·
            refine ⟨12943611396286751960556389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8629074264191167973704259 12943611396286751960556389)
            ·
              refine ⟨2426927136803765992604323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12943611396286751960556389 2426927136803765992604323)
              ·
                refine ⟨3640390705205648988906485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2426927136803765992604323 3640390705205648988906485)
                ·
                  refine ⟨341286628613029592709983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3640390705205648988906485 341286628613029592709983)
                  ·
                    rfl

theorem cell22_2990940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_2990940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990940 prefixEnd_2990940 := by exact prefixLift 2990940
  have htrace : WordTrace (prefixWord ++ tailWord_2990940) baseStart_2990940 baseEnd_2990940 := by
    simpa [prefixWord, tailWord_2990940, baseEnd_2990940] using wordTrace_append hprefix tailTrace_2990940
  have hstable : (prefixWord ++ tailWord_2990940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990940).length < 2 ^ (prefixWord ++ tailWord_2990940).sum := by decide
  have hdescent : baseEnd_2990940 < baseStart_2990940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990978 : List Nat := [3, 4, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_2990978 : Nat := 118140960795 + 2990978 * 2 ^ 59
def prefixEnd_2990978 : Nat := 4983230072969 + 3 ^ 40 * 2990978 * 2
def baseEnd_2990978 : Nat := 1023872894015669345679833

theorem tailTrace_2990978 : CollatzResearch.WordTrace tailWord_2990978 prefixEnd_2990978 1023872894015669345679833 := by
  unfold tailWord_2990978
  simp only [CollatzResearch.WordTrace]
  refine ⟨27272482439551249804795397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72726619838803332812787725 27272482439551249804795397)
  ·
    refine ⟨5113590457415859338399137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27272482439551249804795397 5113590457415859338399137)
    ·
      refine ⟨3835192843061894503799353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5113590457415859338399137 3835192843061894503799353)
      ·
        refine ⟨2876394632296420877849515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3835192843061894503799353 2876394632296420877849515)
        ·
          refine ⟨4314591948444631316774273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2876394632296420877849515 4314591948444631316774273)
          ·
            refine ⟨3235943961333473487580705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4314591948444631316774273 3235943961333473487580705)
            ·
              refine ⟨2426957971000105115685529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3235943961333473487580705 2426957971000105115685529)
              ·
                refine ⟨1820218478250078836764147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2426957971000105115685529 1820218478250078836764147)
                ·
                  refine ⟨2730327717375118255146221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1820218478250078836764147 2730327717375118255146221)
                  ·
                    refine ⟨1023872894015669345679833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2730327717375118255146221 1023872894015669345679833)
                    ·
                      rfl

theorem cell22_2990978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_2990978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990978 prefixEnd_2990978 := by exact prefixLift 2990978
  have htrace : WordTrace (prefixWord ++ tailWord_2990978) baseStart_2990978 baseEnd_2990978 := by
    simpa [prefixWord, tailWord_2990978, baseEnd_2990978] using wordTrace_append hprefix tailTrace_2990978
  have hstable : (prefixWord ++ tailWord_2990978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990978).length < 2 ^ (prefixWord ++ tailWord_2990978).sum := by decide
  have hdescent : baseEnd_2990978 < baseStart_2990978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2990985 : List Nat := [1, 2, 1, 1, 5, 2, 4, 2, 4]
def baseStart_2990985 : Nat := 118140960795 + 2990985 * 2 ^ 59
def prefixEnd_2990985 : Nat := 4983230072969 + 3 ^ 40 * 2990985 * 2
def baseEnd_2990985 : Nat := 341291763419574553584937

theorem tailTrace_2990985 : CollatzResearch.WordTrace tailWord_2990985 prefixEnd_2990985 341291763419574553584937 := by
  unfold tailWord_2990985
  simp only [CollatzResearch.WordTrace]
  refine ⟨109090185069179639414686409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72726790046119759609790939 109090185069179639414686409)
  ·
    refine ⟨81817638801884729561014807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109090185069179639414686409 81817638801884729561014807)
    ·
      refine ⟨122726458202827094341522211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81817638801884729561014807 122726458202827094341522211)
      ·
        refine ⟨184089687304240641512283317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122726458202827094341522211 184089687304240641512283317)
        ·
          refine ⟨17258408184772560141776561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184089687304240641512283317 17258408184772560141776561)
          ·
            refine ⟨12943806138579420106332421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17258408184772560141776561 12943806138579420106332421)
            ·
              refine ⟨2426963650983641269937329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12943806138579420106332421 2426963650983641269937329)
              ·
                refine ⟨1820222738237730952452997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2426963650983641269937329 1820222738237730952452997)
                ·
                  refine ⟨341291763419574553584937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1820222738237730952452997 341291763419574553584937)
                  ·
                    rfl

theorem cell22_2990985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 4].length) (baseStart_2990985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2990985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2990985 prefixEnd_2990985 := by exact prefixLift 2990985
  have htrace : WordTrace (prefixWord ++ tailWord_2990985) baseStart_2990985 baseEnd_2990985 := by
    simpa [prefixWord, tailWord_2990985, baseEnd_2990985] using wordTrace_append hprefix tailTrace_2990985
  have hstable : (prefixWord ++ tailWord_2990985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2990985).length < 2 ^ (prefixWord ++ tailWord_2990985).sum := by decide
  have hdescent : baseEnd_2990985 < baseStart_2990985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2990985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991021 : List Nat := [1, 5, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_2991021 : Nat := 118140960795 + 2991021 * 2 ^ 59
def prefixEnd_2991021 : Nat := 4983230072969 + 3 ^ 40 * 2991021 * 2
def baseEnd_2991021 : Nat := 1023887613794431566854701

theorem tailTrace_2991021 : CollatzResearch.WordTrace tailWord_2991021 prefixEnd_2991021 1023887613794431566854701 := by
  unfold tailWord_2991021
  simp only [CollatzResearch.WordTrace]
  refine ⟨109091498097049217562996917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72727665398032811708664611 109091498097049217562996917)
  ·
    refine ⟨10227327946598364146530961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109091498097049217562996917 10227327946598364146530961)
    ·
      refine ⟨7670495959948773109898221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10227327946598364146530961 7670495959948773109898221)
      ·
        refine ⟨2876435984980789916211833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7670495959948773109898221 2876435984980789916211833)
        ·
          refine ⟨2157326988735592437158875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2876435984980789916211833 2157326988735592437158875)
          ·
            refine ⟨3235990483103388655738313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157326988735592437158875 3235990483103388655738313)
            ·
              refine ⟨2426992862327541491803735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3235990483103388655738313 2426992862327541491803735)
              ·
                refine ⟨3640489293491312237705603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2426992862327541491803735 3640489293491312237705603)
                ·
                  refine ⟨5460733940236968356558405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3640489293491312237705603 5460733940236968356558405)
                  ·
                    refine ⟨1023887613794431566854701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5460733940236968356558405 1023887613794431566854701)
                    ·
                      rfl

theorem cell22_2991021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_2991021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991021 prefixEnd_2991021 := by exact prefixLift 2991021
  have htrace : WordTrace (prefixWord ++ tailWord_2991021) baseStart_2991021 baseEnd_2991021 := by
    simpa [prefixWord, tailWord_2991021, baseEnd_2991021] using wordTrace_append hprefix tailTrace_2991021
  have hstable : (prefixWord ++ tailWord_2991021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991021).length < 2 ^ (prefixWord ++ tailWord_2991021).sum := by decide
  have hdescent : baseEnd_2991021 < baseStart_2991021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991062 : List Nat := [5, 2, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_2991062 : Nat := 118140960795 + 2991062 * 2 ^ 59
def prefixEnd_2991062 : Nat := 4983230072969 + 3 ^ 40 * 2991062 * 2
def baseEnd_2991062 : Nat := 1023901648932321126579575

theorem tailTrace_2991062 : CollatzResearch.WordTrace tailWord_2991062 prefixEnd_2991062 1023901648932321126579575 := by
  unfold tailWord_2991062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6818312093118792597827465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72728662326600454376826293 6818312093118792597827465)
  ·
    refine ⟨5113734069839094448370599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6818312093118792597827465 5113734069839094448370599)
    ·
      refine ⟨7670601104758641672555899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5113734069839094448370599 7670601104758641672555899)
      ·
        refine ⟨11505901657137962508833849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7670601104758641672555899 11505901657137962508833849)
        ·
          refine ⟨8629426242853471881625387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11505901657137962508833849 8629426242853471881625387)
          ·
            refine ⟨12944139364280207822438081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8629426242853471881625387 12944139364280207822438081)
            ·
              refine ⟨9708104523210155866828561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12944139364280207822438081 9708104523210155866828561)
              ·
                refine ⟨7281078392407616900121421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9708104523210155866828561 7281078392407616900121421)
                ·
                  refine ⟨2730404397152856337545533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7281078392407616900121421 2730404397152856337545533)
                  ·
                    refine ⟨1023901648932321126579575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2730404397152856337545533 1023901648932321126579575)
                    ·
                      rfl

theorem cell22_2991062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_2991062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991062 prefixEnd_2991062 := by exact prefixLift 2991062
  have htrace : WordTrace (prefixWord ++ tailWord_2991062) baseStart_2991062 baseEnd_2991062 := by
    simpa [prefixWord, tailWord_2991062, baseEnd_2991062] using wordTrace_append hprefix tailTrace_2991062
  have hstable : (prefixWord ++ tailWord_2991062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991062).length < 2 ^ (prefixWord ++ tailWord_2991062).sum := by decide
  have hdescent : baseEnd_2991062 < baseStart_2991062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991079 : List Nat := [1, 1, 5, 2, 2, 3, 1, 3, 1, 3]
def baseStart_2991079 : Nat := 118140960795 + 2991079 * 2 ^ 59
def prefixEnd_2991079 : Nat := 4983230072969 + 3 ^ 40 * 2991079 * 2
def baseEnd_2991079 : Nat := 1023907468379738748904523

theorem tailTrace_2991079 : CollatzResearch.WordTrace tailWord_2991079 prefixEnd_2991079 1023907468379738748904523 := by
  unfold tailWord_2991079
  simp only [CollatzResearch.WordTrace]
  refine ⟨109093613530839093468608291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72729075687226062312405527 109093613530839093468608291)
  ·
    refine ⟨163640420296258640202912437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109093613530839093468608291 163640420296258640202912437)
    ·
      refine ⟨15341289402774247519023041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163640420296258640202912437 15341289402774247519023041)
      ·
        refine ⟨11505967052080685639267281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15341289402774247519023041 11505967052080685639267281)
        ·
          refine ⟨8629475289060514229450461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11505967052080685639267281 8629475289060514229450461)
          ·
            refine ⟨3236053233397692836043923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8629475289060514229450461 3236053233397692836043923)
            ·
              refine ⟨4854079850096539254065885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3236053233397692836043923 4854079850096539254065885)
              ·
                refine ⟨1820279943786202220274707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4854079850096539254065885 1820279943786202220274707)
                ·
                  refine ⟨2730419915679303330412061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1820279943786202220274707 2730419915679303330412061)
                  ·
                    refine ⟨1023907468379738748904523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2730419915679303330412061 1023907468379738748904523)
                    ·
                      rfl

theorem cell22_2991079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_2991079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991079 prefixEnd_2991079 := by exact prefixLift 2991079
  have htrace : WordTrace (prefixWord ++ tailWord_2991079) baseStart_2991079 baseEnd_2991079 := by
    simpa [prefixWord, tailWord_2991079, baseEnd_2991079] using wordTrace_append hprefix tailTrace_2991079
  have hstable : (prefixWord ++ tailWord_2991079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991079).length < 2 ^ (prefixWord ++ tailWord_2991079).sum := by decide
  have hdescent : baseEnd_2991079 < baseStart_2991079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991150 : List Nat := [4, 1, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2991150 : Nat := 118140960795 + 2991150 * 2 ^ 59
def prefixEnd_2991150 : Nat := 4983230072969 + 3 ^ 40 * 2991150 * 2
def baseEnd_2991150 : Nat := 1023931773130718230379305

theorem tailTrace_2991150 : CollatzResearch.WordTrace tailWord_2991150 prefixEnd_2991150 1023931773130718230379305 := by
  unfold tailWord_2991150
  simp only [CollatzResearch.WordTrace]
  refine ⟨13637025389197734074305363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72730802075721248396295269 13637025389197734074305363)
  ·
    refine ⟨20455538083796601111458045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13637025389197734074305363 20455538083796601111458045)
    ·
      refine ⟨7670826781423725416796767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20455538083796601111458045 7670826781423725416796767)
      ·
        refine ⟨11506240172135588125195151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7670826781423725416796767 11506240172135588125195151)
        ·
          refine ⟨17259360258203382187792727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11506240172135588125195151 17259360258203382187792727)
          ·
            refine ⟨25889040387305073281689091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17259360258203382187792727 25889040387305073281689091)
            ·
              refine ⟨38833560580957609922533637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25889040387305073281689091 38833560580957609922533637)
              ·
                refine ⟨7281292608929551860475057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38833560580957609922533637 7281292608929551860475057)
                ·
                  refine ⟨5460969456697163895356293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7281292608929551860475057 5460969456697163895356293)
                  ·
                    refine ⟨1023931773130718230379305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5460969456697163895356293 1023931773130718230379305)
                    ·
                      rfl

theorem cell22_2991150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2991150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991150 prefixEnd_2991150 := by exact prefixLift 2991150
  have htrace : WordTrace (prefixWord ++ tailWord_2991150) baseStart_2991150 baseEnd_2991150 := by
    simpa [prefixWord, tailWord_2991150, baseEnd_2991150] using wordTrace_append hprefix tailTrace_2991150
  have hstable : (prefixWord ++ tailWord_2991150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991150).length < 2 ^ (prefixWord ++ tailWord_2991150).sum := by decide
  have hdescent : baseEnd_2991150 < baseStart_2991150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991165 : List Nat := [1, 4, 1, 3, 1, 4, 1, 7]
def baseStart_2991165 : Nat := 118140960795 + 2991165 * 2 ^ 59
def prefixEnd_2991165 : Nat := 4983230072969 + 3 ^ 40 * 2991165 * 2
def baseEnd_2991165 : Nat := 113770767548584799028251

theorem tailTrace_2991165 : CollatzResearch.WordTrace tailWord_2991165 prefixEnd_2991165 113770767548584799028251 := by
  unfold tailWord_2991165
  simp only [CollatzResearch.WordTrace]
  refine ⟨109096750208527530156238949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72731166805685020104159299 109096750208527530156238949)
  ·
    refine ⟨20455640664098911904294803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109096750208527530156238949 20455640664098911904294803)
    ·
      refine ⟨30683460996148367856442205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20455640664098911904294803 30683460996148367856442205)
      ·
        refine ⟨11506297873555637946165827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30683460996148367856442205 11506297873555637946165827)
        ·
          refine ⟨17259446810333456919248741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11506297873555637946165827 17259446810333456919248741)
          ·
            refine ⟨3236146276937523172359139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17259446810333456919248741 3236146276937523172359139)
            ·
              refine ⟨4854219415406284758538709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3236146276937523172359139 4854219415406284758538709)
              ·
                refine ⟨113770767548584799028251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4854219415406284758538709 113770767548584799028251)
                ·
                  rfl

theorem cell22_2991165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 7].length) (baseStart_2991165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991165 prefixEnd_2991165 := by exact prefixLift 2991165
  have htrace : WordTrace (prefixWord ++ tailWord_2991165) baseStart_2991165 baseEnd_2991165 := by
    simpa [prefixWord, tailWord_2991165, baseEnd_2991165] using wordTrace_append hprefix tailTrace_2991165
  have hstable : (prefixWord ++ tailWord_2991165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991165).length < 2 ^ (prefixWord ++ tailWord_2991165).sum := by decide
  have hdescent : baseEnd_2991165 < baseStart_2991165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991210 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 7]
def baseStart_2991210 : Nat := 118140960795 + 2991210 * 2 ^ 59
def prefixEnd_2991210 : Nat := 4983230072969 + 3 ^ 40 * 2991210 * 2
def baseEnd_2991210 : Nat := 341317437452299357959707

theorem tailTrace_2991210 : CollatzResearch.WordTrace tailWord_2991210 prefixEnd_2991210 341317437452299357959707 := by
  unfold tailWord_2991210
  simp only [CollatzResearch.WordTrace]
  refine ⟨27274597873341125710406771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72732260995576335227751389 27274597873341125710406771)
  ·
    refine ⟨40911896810011688565610157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27274597873341125710406771 40911896810011688565610157)
    ·
      refine ⟨15341961303754383212103809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40911896810011688565610157 15341961303754383212103809)
      ·
        refine ⟨11506470977815787409077857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15341961303754383212103809 11506470977815787409077857)
        ·
          refine ⟨8629853233361840556808393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11506470977815787409077857 8629853233361840556808393)
          ·
            refine ⟨6472389925021380417606295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8629853233361840556808393 6472389925021380417606295)
            ·
              refine ⟨9708584887532070626409443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6472389925021380417606295 9708584887532070626409443)
              ·
                refine ⟨14562877331298105939614165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9708584887532070626409443 14562877331298105939614165)
                ·
                  refine ⟨341317437452299357959707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14562877331298105939614165 341317437452299357959707)
                  ·
                    rfl

theorem cell22_2991210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_2991210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991210 prefixEnd_2991210 := by exact prefixLift 2991210
  have htrace : WordTrace (prefixWord ++ tailWord_2991210) baseStart_2991210 baseEnd_2991210 := by
    simpa [prefixWord, tailWord_2991210, baseEnd_2991210] using wordTrace_append hprefix tailTrace_2991210
  have hstable : (prefixWord ++ tailWord_2991210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991210).length < 2 ^ (prefixWord ++ tailWord_2991210).sum := by decide
  have hdescent : baseEnd_2991210 < baseStart_2991210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991214 : List Nat := [4, 1, 2, 2, 1, 2, 2, 4, 1, 3]
def baseStart_2991214 : Nat := 118140960795 + 2991214 * 2 ^ 59
def prefixEnd_2991214 : Nat := 4983230072969 + 3 ^ 40 * 2991214 * 2
def baseEnd_2991214 : Nat := 1023953681638643396779109

theorem tailTrace_2991214 : CollatzResearch.WordTrace tailWord_2991214 prefixEnd_2991214 1023953681638643396779109 := by
  unfold tailWord_2991214
  simp only [CollatzResearch.WordTrace]
  refine ⟨13637317173168751440596587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72732358256900007683181797 13637317173168751440596587)
  ·
    refine ⟨20455975759753127160894881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13637317173168751440596587 20455975759753127160894881)
    ·
      refine ⟨15341981819814845370671161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20455975759753127160894881 15341981819814845370671161)
      ·
        refine ⟨11506486364861134028003371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15341981819814845370671161 11506486364861134028003371)
        ·
          refine ⟨17259729547291701042005057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11506486364861134028003371 17259729547291701042005057)
          ·
            refine ⟨12944797160468775781503793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17259729547291701042005057 12944797160468775781503793)
            ·
              refine ⟨9708597870351581836127845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12944797160468775781503793 9708597870351581836127845)
              ·
                refine ⟨1820362100690921594273971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9708597870351581836127845 1820362100690921594273971)
                ·
                  refine ⟨2730543151036382391410957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1820362100690921594273971 2730543151036382391410957)
                  ·
                    refine ⟨1023953681638643396779109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2730543151036382391410957 1023953681638643396779109)
                    ·
                      rfl

theorem cell22_2991214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_2991214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991214 prefixEnd_2991214 := by exact prefixLift 2991214
  have htrace : WordTrace (prefixWord ++ tailWord_2991214) baseStart_2991214 baseEnd_2991214 := by
    simpa [prefixWord, tailWord_2991214, baseEnd_2991214] using wordTrace_append hprefix tailTrace_2991214
  have hstable : (prefixWord ++ tailWord_2991214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991214).length < 2 ^ (prefixWord ++ tailWord_2991214).sum := by decide
  have hdescent : baseEnd_2991214 < baseStart_2991214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991283 : List Nat := [1, 1, 1, 2, 3, 2, 3, 9]
def baseStart_2991283 : Nat := 118140960795 + 2991283 * 2 ^ 59
def prefixEnd_2991283 : Nat := 4983230072969 + 3 ^ 40 * 2991283 * 2
def baseEnd_2991283 : Nat := 113775255749861135200433

theorem tailTrace_2991283 : CollatzResearch.WordTrace tailWord_2991283 prefixEnd_2991283 113775255749861135200433 := by
  unfold tailWord_2991283
  simp only [CollatzResearch.WordTrace]
  refine ⟨109101054022100036309034503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72734036014733357539356335 109101054022100036309034503)
  ·
    refine ⟨163651581033150054463551755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109101054022100036309034503 163651581033150054463551755)
    ·
      refine ⟨245477371549725081695327633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163651581033150054463551755 245477371549725081695327633)
      ·
        refine ⟨184108028662293811271495725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245477371549725081695327633 184108028662293811271495725)
        ·
          refine ⟨69040510748360179226810897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184108028662293811271495725 69040510748360179226810897)
          ·
            refine ⟨51780383061270134420108173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69040510748360179226810897 51780383061270134420108173)
            ·
              refine ⟨19417643647976300407540565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51780383061270134420108173 19417643647976300407540565)
              ·
                refine ⟨113775255749861135200433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19417643647976300407540565 113775255749861135200433)
                ·
                  rfl

theorem cell22_2991283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 9].length) (baseStart_2991283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991283 prefixEnd_2991283 := by exact prefixLift 2991283
  have htrace : WordTrace (prefixWord ++ tailWord_2991283) baseStart_2991283 baseEnd_2991283 := by
    simpa [prefixWord, tailWord_2991283, baseEnd_2991283] using wordTrace_append hprefix tailTrace_2991283
  have hstable : (prefixWord ++ tailWord_2991283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991283).length < 2 ^ (prefixWord ++ tailWord_2991283).sum := by decide
  have hdescent : baseEnd_2991283 < baseStart_2991283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991287 : List Nat := [1, 1, 3, 1, 4, 1, 3, 3, 2, 3]
def baseStart_2991287 : Nat := 118140960795 + 2991287 * 2 ^ 59
def prefixEnd_2991287 : Nat := 4983230072969 + 3 ^ 40 * 2991287 * 2
def baseEnd_2991287 : Nat := 1023978671030495539703885

theorem tailTrace_2991287 : CollatzResearch.WordTrace tailWord_2991287 prefixEnd_2991287 1023978671030495539703885 := by
  unfold tailWord_2991287
  simp only [CollatzResearch.WordTrace]
  refine ⟨109101199914085544992180115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72734133276057029994786743 109101199914085544992180115)
  ·
    refine ⟨163651799871128317488270173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109101199914085544992180115 163651799871128317488270173)
    ·
      refine ⟨61369424951673119058101315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163651799871128317488270173 61369424951673119058101315)
      ·
        refine ⟨92054137427509678587151973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61369424951673119058101315 92054137427509678587151973)
        ·
          refine ⟨17260150767658064735090995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92054137427509678587151973 17260150767658064735090995)
          ·
            refine ⟨25890226151487097102636493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17260150767658064735090995 25890226151487097102636493)
            ·
              refine ⟨9708834806807661413488685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25890226151487097102636493 9708834806807661413488685)
              ·
                refine ⟨3640813052552873030058257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9708834806807661413488685 3640813052552873030058257)
                ·
                  refine ⟨2730609789414654772543693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3640813052552873030058257 2730609789414654772543693)
                  ·
                    refine ⟨1023978671030495539703885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2730609789414654772543693 1023978671030495539703885)
                    ·
                      rfl

theorem cell22_2991287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_2991287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991287 prefixEnd_2991287 := by exact prefixLift 2991287
  have htrace : WordTrace (prefixWord ++ tailWord_2991287) baseStart_2991287 baseEnd_2991287 := by
    simpa [prefixWord, tailWord_2991287, baseEnd_2991287] using wordTrace_append hprefix tailTrace_2991287
  have hstable : (prefixWord ++ tailWord_2991287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991287).length < 2 ^ (prefixWord ++ tailWord_2991287).sum := by decide
  have hdescent : baseEnd_2991287 < baseStart_2991287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991315 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 5, 3]
def baseStart_2991315 : Nat := 118140960795 + 2991315 * 2 ^ 59
def prefixEnd_2991315 : Nat := 4983230072969 + 3 ^ 40 * 2991315 * 2
def baseEnd_2991315 : Nat := 1023988256002712800003799

theorem tailTrace_2991315 : CollatzResearch.WordTrace tailWord_2991315 prefixEnd_2991315 1023988256002712800003799 := by
  unfold tailWord_2991315
  simp only [CollatzResearch.WordTrace]
  refine ⟨109102221157984105774199399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72734814105322737182799599 109102221157984105774199399)
  ·
    refine ⟨163653331736976158661299099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109102221157984105774199399 163653331736976158661299099)
    ·
      refine ⟨245479997605464237991948649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163653331736976158661299099 245479997605464237991948649)
      ·
        refine ⟨184109998204098178493961487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245479997605464237991948649 184109998204098178493961487)
        ·
          refine ⟨276164997306147267740942231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184109998204098178493961487 276164997306147267740942231)
          ·
            refine ⟨414247495959220901611413347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276164997306147267740942231 414247495959220901611413347)
            ·
              refine ⟨621371243938831352417120021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414247495959220901611413347 621371243938831352417120021)
              ·
                refine ⟨29126777059632719644552501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 621371243938831352417120021 29126777059632719644552501)
                ·
                  refine ⟨2730635349340567466676797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29126777059632719644552501 2730635349340567466676797)
                  ·
                    refine ⟨1023988256002712800003799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2730635349340567466676797 1023988256002712800003799)
                    ·
                      rfl

theorem cell22_2991315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 3].length) (baseStart_2991315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991315 prefixEnd_2991315 := by exact prefixLift 2991315
  have htrace : WordTrace (prefixWord ++ tailWord_2991315) baseStart_2991315 baseEnd_2991315 := by
    simpa [prefixWord, tailWord_2991315, baseEnd_2991315] using wordTrace_append hprefix tailTrace_2991315
  have hstable : (prefixWord ++ tailWord_2991315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991315).length < 2 ^ (prefixWord ++ tailWord_2991315).sum := by decide
  have hdescent : baseEnd_2991315 < baseStart_2991315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991409 : List Nat := [1, 2, 2, 3, 3, 2, 2, 2, 1, 4]
def baseStart_2991409 : Nat := 118140960795 + 2991409 * 2 ^ 59
def prefixEnd_2991409 : Nat := 4983230072969 + 3 ^ 40 * 2991409 * 2
def baseEnd_2991409 : Nat := 1024020434123727888153511

theorem tailTrace_2991409 : CollatzResearch.WordTrace tailWord_2991409 prefixEnd_2991409 1024020434123727888153511 := by
  unfold tailWord_2991409
  simp only [CollatzResearch.WordTrace]
  refine ⟨109105649619643559828121281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72737099746429039885414187 109105649619643559828121281)
  ·
    refine ⟨81829237214732669871090961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109105649619643559828121281 81829237214732669871090961)
    ·
      refine ⟨61371927911049502403318221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81829237214732669871090961 61371927911049502403318221)
      ·
        refine ⟨23014472966643563401244333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61371927911049502403318221 23014472966643563401244333)
        ·
          refine ⟨8630427362491336275466625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23014472966643563401244333 8630427362491336275466625)
          ·
            refine ⟨6472820521868502206599969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8630427362491336275466625 6472820521868502206599969)
            ·
              refine ⟨4854615391401376654949977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6472820521868502206599969 4854615391401376654949977)
              ·
                refine ⟨3640961543551032491212483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4854615391401376654949977 3640961543551032491212483)
                ·
                  refine ⟨5461442315326548736818725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3640961543551032491212483 5461442315326548736818725)
                  ·
                    refine ⟨1024020434123727888153511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5461442315326548736818725 1024020434123727888153511)
                    ·
                      rfl

theorem cell22_2991409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_2991409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991409 prefixEnd_2991409 := by exact prefixLift 2991409
  have htrace : WordTrace (prefixWord ++ tailWord_2991409) baseStart_2991409 baseEnd_2991409 := by
    simpa [prefixWord, tailWord_2991409, baseEnd_2991409] using wordTrace_append hprefix tailTrace_2991409
  have hstable : (prefixWord ++ tailWord_2991409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991409).length < 2 ^ (prefixWord ++ tailWord_2991409).sum := by decide
  have hdescent : baseEnd_2991409 < baseStart_2991409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991422 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_2991422 : Nat := 118140960795 + 2991422 * 2 ^ 59
def prefixEnd_2991422 : Nat := 4983230072969 + 3 ^ 40 * 2991422 * 2
def baseEnd_2991422 : Nat := 1024024884289400187578471

theorem tailTrace_2991422 : CollatzResearch.WordTrace tailWord_2991422 prefixEnd_2991422 1024024884289400187578471 := by
  unfold tailWord_2991422
  simp only [CollatzResearch.WordTrace]
  refine ⟨13638265471074557881043065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72737415845730975365563013 13638265471074557881043065)
  ·
    refine ⟨10228699103305918410782299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13638265471074557881043065 10228699103305918410782299)
    ·
      refine ⟨15343048654958877616173449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10228699103305918410782299 15343048654958877616173449)
      ·
        refine ⟨11507286491219158212130087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15343048654958877616173449 11507286491219158212130087)
        ·
          refine ⟨17260929736828737318195131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11507286491219158212130087 17260929736828737318195131)
          ·
            refine ⟨25891394605243105977292697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17260929736828737318195131 25891394605243105977292697)
            ·
              refine ⟨19418545953932329482969523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25891394605243105977292697 19418545953932329482969523)
              ·
                refine ⟨29127818930898494224454285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19418545953932329482969523 29127818930898494224454285)
                ·
                  refine ⟨10922932099086935334170357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29127818930898494224454285 10922932099086935334170357)
                  ·
                    refine ⟨1024024884289400187578471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10922932099086935334170357 1024024884289400187578471)
                    ·
                      rfl

theorem cell22_2991422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_2991422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991422 prefixEnd_2991422 := by exact prefixLift 2991422
  have htrace : WordTrace (prefixWord ++ tailWord_2991422) baseStart_2991422 baseEnd_2991422 := by
    simpa [prefixWord, tailWord_2991422, baseEnd_2991422] using wordTrace_append hprefix tailTrace_2991422
  have hstable : (prefixWord ++ tailWord_2991422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991422).length < 2 ^ (prefixWord ++ tailWord_2991422).sum := by decide
  have hdescent : baseEnd_2991422 < baseStart_2991422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991456 : List Nat := [2, 1, 1, 3, 4, 1, 4, 1, 2, 3]
def baseStart_2991456 : Nat := 118140960795 + 2991456 * 2 ^ 59
def prefixEnd_2991456 : Nat := 4983230072969 + 3 ^ 40 * 2991456 * 2
def baseEnd_2991456 : Nat := 1024036523184235432228367

theorem tailTrace_2991456 : CollatzResearch.WordTrace tailWord_2991456 prefixEnd_2991456 1024036523184235432228367 := by
  unfold tailWord_2991456
  simp only [CollatzResearch.WordTrace]
  refine ⟨54553681925236643427541111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72738242566982191236721481 54553681925236643427541111)
  ·
    refine ⟨81830522887854965141311667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54553681925236643427541111 81830522887854965141311667)
    ·
      refine ⟨122745784331782447711967501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81830522887854965141311667 122745784331782447711967501)
      ·
        refine ⟨46029669124418417891987813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122745784331782447711967501 46029669124418417891987813)
        ·
          refine ⟨8630562960828453354747715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46029669124418417891987813 8630562960828453354747715)
          ·
            refine ⟨12945844441242680032121573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8630562960828453354747715 12945844441242680032121573)
            ·
              refine ⟨2427345832733002506022795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12945844441242680032121573 2427345832733002506022795)
              ·
                refine ⟨3641018749099503759034193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2427345832733002506022795 3641018749099503759034193)
                ·
                  refine ⟨2730764061824627819275645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3641018749099503759034193 2730764061824627819275645)
                  ·
                    refine ⟨1024036523184235432228367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2730764061824627819275645 1024036523184235432228367)
                    ·
                      rfl

theorem cell22_2991456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 2, 3].length) (baseStart_2991456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991456 prefixEnd_2991456 := by exact prefixLift 2991456
  have htrace : WordTrace (prefixWord ++ tailWord_2991456) baseStart_2991456 baseEnd_2991456 := by
    simpa [prefixWord, tailWord_2991456, baseEnd_2991456] using wordTrace_append hprefix tailTrace_2991456
  have hstable : (prefixWord ++ tailWord_2991456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991456).length < 2 ^ (prefixWord ++ tailWord_2991456).sum := by decide
  have hdescent : baseEnd_2991456 < baseStart_2991456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991465 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 4, 6]
def baseStart_2991465 : Nat := 118140960795 + 2991465 * 2 ^ 59
def prefixEnd_2991465 : Nat := 4983230072969 + 3 ^ 40 * 2991465 * 2
def baseEnd_2991465 : Nat := 1024039604068162408753339

theorem tailTrace_2991465 : CollatzResearch.WordTrace tailWord_2991465 prefixEnd_2991465 1024039604068162408753339 := by
  unfold tailWord_2991465
  simp only [CollatzResearch.WordTrace]
  refine ⟨109107692107440681392159849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72738461404960454261439899 109107692107440681392159849)
  ·
    refine ⟨81830769080580511044119887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109107692107440681392159849 81830769080580511044119887)
    ·
      refine ⟨122746153620870766566179831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81830769080580511044119887 122746153620870766566179831)
      ·
        refine ⟨184119230431306149849269747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122746153620870766566179831 184119230431306149849269747)
        ·
          refine ⟨276178845646959224773904621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184119230431306149849269747 276178845646959224773904621)
          ·
            refine ⟨103567067117609709290214233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276178845646959224773904621 103567067117609709290214233)
            ·
              refine ⟨77675300338207281967660675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103567067117609709290214233 77675300338207281967660675)
              ·
                refine ⟨116512950507310922951491013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77675300338207281967660675 116512950507310922951491013)
                ·
                  refine ⟨21846178220120798053404565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116512950507310922951491013 21846178220120798053404565)
                  ·
                    refine ⟨1024039604068162408753339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21846178220120798053404565 1024039604068162408753339)
                    ·
                      rfl

theorem cell22_2991465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_2991465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991465 prefixEnd_2991465 := by exact prefixLift 2991465
  have htrace : WordTrace (prefixWord ++ tailWord_2991465) baseStart_2991465 baseEnd_2991465 := by
    simpa [prefixWord, tailWord_2991465, baseEnd_2991465] using wordTrace_append hprefix tailTrace_2991465
  have hstable : (prefixWord ++ tailWord_2991465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991465).length < 2 ^ (prefixWord ++ tailWord_2991465).sum := by decide
  have hdescent : baseEnd_2991465 < baseStart_2991465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991486 : List Nat := [4, 2, 3, 2, 2, 9]
def baseStart_2991486 : Nat := 118140960795 + 2991486 * 2 ^ 59
def prefixEnd_2991486 : Nat := 4983230072969 + 3 ^ 40 * 2991486 * 2
def baseEnd_2991486 : Nat := 12642552997497843876275

theorem tailTrace_2991486 : CollatzResearch.WordTrace tailWord_2991486 prefixEnd_2991486 12642552997497843876275 := by
  unfold tailWord_2991486
  simp only [CollatzResearch.WordTrace]
  refine ⟨13638557255045575247334289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72738972026909734652449541 13638557255045575247334289)
  ·
    refine ⟨10228917941284181435500717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13638557255045575247334289 10228917941284181435500717)
    ·
      refine ⟨3835844227981568038312769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10228917941284181435500717 3835844227981568038312769)
      ·
        refine ⟨2876883170986176028734577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3835844227981568038312769 2876883170986176028734577)
        ·
          refine ⟨2157662378239632021550933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2876883170986176028734577 2157662378239632021550933)
          ·
            refine ⟨12642552997497843876275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2157662378239632021550933 12642552997497843876275)
            ·
              rfl

theorem cell22_2991486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 9].length) (baseStart_2991486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991486 prefixEnd_2991486 := by exact prefixLift 2991486
  have htrace : WordTrace (prefixWord ++ tailWord_2991486) baseStart_2991486 baseEnd_2991486 := by
    simpa [prefixWord, tailWord_2991486, baseEnd_2991486] using wordTrace_append hprefix tailTrace_2991486
  have hstable : (prefixWord ++ tailWord_2991486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991486).length < 2 ^ (prefixWord ++ tailWord_2991486).sum := by decide
  have hdescent : baseEnd_2991486 < baseStart_2991486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991518 : List Nat := [4, 3, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_2991518 : Nat := 118140960795 + 2991518 * 2 ^ 59
def prefixEnd_2991518 : Nat := 4983230072969 + 3 ^ 40 * 2991518 * 2
def baseEnd_2991518 : Nat := 1024057747051287937178177

theorem tailTrace_2991518 : CollatzResearch.WordTrace tailWord_2991518 prefixEnd_2991518 1024057747051287937178177 := by
  unfold tailWord_2991518
  simp only [CollatzResearch.WordTrace]
  refine ⟨13638703147031083930479901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72739750117499114295892805 13638703147031083930479901)
  ·
    refine ⟨5114513680136656473929963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13638703147031083930479901 5114513680136656473929963)
    ·
      refine ⟨7671770520204984710894945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5114513680136656473929963 7671770520204984710894945)
      ·
        refine ⟨5753827890153738533171209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7671770520204984710894945 5753827890153738533171209)
        ·
          refine ⟨4315370917615303899878407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5753827890153738533171209 4315370917615303899878407)
          ·
            refine ⟨6473056376422955849817611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4315370917615303899878407 6473056376422955849817611)
            ·
              refine ⟨9709584564634433774726417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6473056376422955849817611 9709584564634433774726417)
              ·
                refine ⟨7282188423475825331044813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9709584564634433774726417 7282188423475825331044813)
                ·
                  refine ⟨2730820658803434499141805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7282188423475825331044813 2730820658803434499141805)
                  ·
                    refine ⟨1024057747051287937178177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2730820658803434499141805 1024057747051287937178177)
                    ·
                      rfl

theorem cell22_2991518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_2991518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991518 prefixEnd_2991518 := by exact prefixLift 2991518
  have htrace : WordTrace (prefixWord ++ tailWord_2991518) baseStart_2991518 baseEnd_2991518 := by
    simpa [prefixWord, tailWord_2991518, baseEnd_2991518] using wordTrace_append hprefix tailTrace_2991518
  have hstable : (prefixWord ++ tailWord_2991518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991518).length < 2 ^ (prefixWord ++ tailWord_2991518).sum := by decide
  have hdescent : baseEnd_2991518 < baseStart_2991518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991548 : List Nat := [2, 2, 2, 4, 3, 1, 1, 2, 5]
def baseStart_2991548 : Nat := 118140960795 + 2991548 * 2 ^ 59
def prefixEnd_2991548 : Nat := 4983230072969 + 3 ^ 40 * 2991548 * 2
def baseEnd_2991548 : Nat := 341356005554792619642695

theorem tailTrace_2991548 : CollatzResearch.WordTrace tailWord_2991548 prefixEnd_2991548 341356005554792619642695 := by
  unfold tailWord_2991548
  simp only [CollatzResearch.WordTrace]
  refine ⟨54555359683069993283715649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72740479577426657711620865 54555359683069993283715649)
  ·
    refine ⟨40916519762302494962786737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54555359683069993283715649 40916519762302494962786737)
    ·
      refine ⟨30687389821726871222090053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40916519762302494962786737 30687389821726871222090053)
      ·
        refine ⟨5753885591573788354141885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30687389821726871222090053 5753885591573788354141885)
        ·
          refine ⟨2157707096840170632803207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5753885591573788354141885 2157707096840170632803207)
          ·
            refine ⟨3236560645260255949204811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157707096840170632803207 3236560645260255949204811)
            ·
              refine ⟨4854840967890383923807217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3236560645260255949204811 4854840967890383923807217)
              ·
                refine ⟨3641130725917787942855413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4854840967890383923807217 3641130725917787942855413)
                ·
                  refine ⟨341356005554792619642695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3641130725917787942855413 341356005554792619642695)
                  ·
                    rfl

theorem cell22_2991548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_2991548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991548 prefixEnd_2991548 := by exact prefixLift 2991548
  have htrace : WordTrace (prefixWord ++ tailWord_2991548) baseStart_2991548 baseEnd_2991548 := by
    simpa [prefixWord, tailWord_2991548, baseEnd_2991548] using wordTrace_append hprefix tailTrace_2991548
  have hstable : (prefixWord ++ tailWord_2991548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991548).length < 2 ^ (prefixWord ++ tailWord_2991548).sum := by decide
  have hdescent : baseEnd_2991548 < baseStart_2991548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991559 : List Nat := [1, 1, 4, 1, 1, 3, 1, 6, 4]
def baseStart_2991559 : Nat := 118140960795 + 2991559 * 2 ^ 59
def prefixEnd_2991559 : Nat := 4983230072969 + 3 ^ 40 * 2991559 * 2
def baseEnd_2991559 : Nat := 341357260729725832301017

theorem tailTrace_2991559 : CollatzResearch.WordTrace tailWord_2991559 prefixEnd_2991559 341357260729725832301017 := by
  unfold tailWord_2991559
  simp only [CollatzResearch.WordTrace]
  refine ⟨109111120569100135446081731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72740747046066756964054487 109111120569100135446081731)
  ·
    refine ⟨163666680853650203169122597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109111120569100135446081731 163666680853650203169122597)
    ·
      refine ⟨30687502660059413094210487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163666680853650203169122597 30687502660059413094210487)
      ·
        refine ⟨46031253990089119641315731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30687502660059413094210487 46031253990089119641315731)
        ·
          refine ⟨69046880985133679461973597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46031253990089119641315731 69046880985133679461973597)
          ·
            refine ⟨25892580369425129798240099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69046880985133679461973597 25892580369425129798240099)
            ·
              refine ⟨38838870554137694697360149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25892580369425129798240099 38838870554137694697360149)
              ·
                refine ⟨1820572057225204438938757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38838870554137694697360149 1820572057225204438938757)
                ·
                  refine ⟨341357260729725832301017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1820572057225204438938757 341357260729725832301017)
                  ·
                    rfl

theorem cell22_2991559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 4].length) (baseStart_2991559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991559 prefixEnd_2991559 := by exact prefixLift 2991559
  have htrace : WordTrace (prefixWord ++ tailWord_2991559) baseStart_2991559 baseEnd_2991559 := by
    simpa [prefixWord, tailWord_2991559, baseEnd_2991559] using wordTrace_append hprefix tailTrace_2991559
  have hstable : (prefixWord ++ tailWord_2991559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991559).length < 2 ^ (prefixWord ++ tailWord_2991559).sum := by decide
  have hdescent : baseEnd_2991559 < baseStart_2991559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991589 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 1, 6]
def baseStart_2991589 : Nat := 118140960795 + 2991589 * 2 ^ 59
def prefixEnd_2991589 : Nat := 4983230072969 + 3 ^ 40 * 2991589 * 2
def baseEnd_2991589 : Nat := 1024082051802267418652959

theorem tailTrace_2991589 : CollatzResearch.WordTrace tailWord_2991589 prefixEnd_2991589 1024082051802267418652959 := by
  unfold tailWord_2991589
  simp only [CollatzResearch.WordTrace]
  refine ⟨109112214758991450569673821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72741476505994300379782547 109112214758991450569673821)
  ·
    refine ⟨40917080534621793963627683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109112214758991450569673821 40917080534621793963627683)
    ·
      refine ⟨61375620801932690945441525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40917080534621793963627683 61375620801932690945441525)
      ·
        refine ⟨5753964450181189776135143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61375620801932690945441525 5753964450181189776135143)
        ·
          refine ⟨8630946675271784664202715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5753964450181189776135143 8630946675271784664202715)
          ·
            refine ⟨12946420012907676996304073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8630946675271784664202715 12946420012907676996304073)
            ·
              refine ⟨9709815009680757747228055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12946420012907676996304073 9709815009680757747228055)
              ·
                refine ⟨14564722514521136620842083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9709815009680757747228055 14564722514521136620842083)
                ·
                  refine ⟨21847083771781704931263125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14564722514521136620842083 21847083771781704931263125)
                  ·
                    refine ⟨1024082051802267418652959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21847083771781704931263125 1024082051802267418652959)
                    ·
                      rfl

theorem cell22_2991589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_2991589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991589 prefixEnd_2991589 := by exact prefixLift 2991589
  have htrace : WordTrace (prefixWord ++ tailWord_2991589) baseStart_2991589 baseEnd_2991589 := by
    simpa [prefixWord, tailWord_2991589, baseEnd_2991589] using wordTrace_append hprefix tailTrace_2991589
  have hstable : (prefixWord ++ tailWord_2991589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991589).length < 2 ^ (prefixWord ++ tailWord_2991589).sum := by decide
  have hdescent : baseEnd_2991589 < baseStart_2991589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991606 : List Nat := [5, 1, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_2991606 : Nat := 118140960795 + 2991606 * 2 ^ 59
def prefixEnd_2991606 : Nat := 4983230072969 + 3 ^ 40 * 2991606 * 2
def baseEnd_2991606 : Nat := 1024087871249685040977907

theorem tailTrace_2991606 : CollatzResearch.WordTrace tailWord_2991606 prefixEnd_2991606 1024087871249685040977907 := by
  unfold tailWord_2991606
  simp only [CollatzResearch.WordTrace]
  refine ⟨6819552174995616404565167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72741889866619908315361781 6819552174995616404565167)
  ·
    refine ⟨10229328262493424606847751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6819552174995616404565167 10229328262493424606847751)
    ·
      refine ⟨15343992393740136910271627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10229328262493424606847751 15343992393740136910271627)
      ·
        refine ⟨23015988590610205365407441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15343992393740136910271627 23015988590610205365407441)
        ·
          refine ⟨17261991442957654024055581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23015988590610205365407441 17261991442957654024055581)
          ·
            refine ⟨6473246791109120259020843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17261991442957654024055581 6473246791109120259020843)
            ·
              refine ⟨9709870186663680388531265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6473246791109120259020843 9709870186663680388531265)
              ·
                refine ⟨7282402639997760291398449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9709870186663680388531265 7282402639997760291398449)
                ·
                  refine ⟨5461801979998320218548837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7282402639997760291398449 5461801979998320218548837)
                  ·
                    refine ⟨1024087871249685040977907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5461801979998320218548837 1024087871249685040977907)
                    ·
                      rfl

theorem cell22_2991606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_2991606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991606 prefixEnd_2991606 := by exact prefixLift 2991606
  have htrace : WordTrace (prefixWord ++ tailWord_2991606) baseStart_2991606 baseEnd_2991606 := by
    simpa [prefixWord, tailWord_2991606, baseEnd_2991606] using wordTrace_append hprefix tailTrace_2991606
  have hstable : (prefixWord ++ tailWord_2991606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991606).length < 2 ^ (prefixWord ++ tailWord_2991606).sum := by decide
  have hdescent : baseEnd_2991606 < baseStart_2991606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991619 : List Nat := [1, 1, 1, 3, 2, 1, 2, 5, 3, 3]
def baseStart_2991619 : Nat := 118140960795 + 2991619 * 2 ^ 59
def prefixEnd_2991619 : Nat := 4983230072969 + 3 ^ 40 * 2991619 * 2
def baseEnd_2991619 : Nat := 1024092321415357340402867

theorem tailTrace_2991619 : CollatzResearch.WordTrace tailWord_2991619 prefixEnd_2991619 1024092321415357340402867 := by
  unfold tailWord_2991619
  simp only [CollatzResearch.WordTrace]
  refine ⟨109113308948882765693265911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72742205965921843795510607 109113308948882765693265911)
  ·
    refine ⟨163669963423324148539898867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109113308948882765693265911 163669963423324148539898867)
    ·
      refine ⟨245504945134986222809848301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163669963423324148539898867 245504945134986222809848301)
      ·
        refine ⟨92064354425619833553693113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245504945134986222809848301 92064354425619833553693113)
        ·
          refine ⟨69048265819214875165269835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92064354425619833553693113 69048265819214875165269835)
          ·
            refine ⟨103572398728822312747904753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69048265819214875165269835 103572398728822312747904753)
            ·
              refine ⟨77679299046616734560928565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103572398728822312747904753 77679299046616734560928565)
              ·
                refine ⟨7282434285620318865087053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77679299046616734560928565 7282434285620318865087053)
                ·
                  refine ⟨2730912857107619574407645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7282434285620318865087053 2730912857107619574407645)
                  ·
                    refine ⟨1024092321415357340402867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2730912857107619574407645 1024092321415357340402867)
                    ·
                      rfl

theorem cell22_2991619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 3].length) (baseStart_2991619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991619 prefixEnd_2991619 := by exact prefixLift 2991619
  have htrace : WordTrace (prefixWord ++ tailWord_2991619) baseStart_2991619 baseEnd_2991619 := by
    simpa [prefixWord, tailWord_2991619, baseEnd_2991619] using wordTrace_append hprefix tailTrace_2991619
  have hstable : (prefixWord ++ tailWord_2991619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991619).length < 2 ^ (prefixWord ++ tailWord_2991619).sum := by decide
  have hdescent : baseEnd_2991619 < baseStart_2991619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991679 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 3, 4]
def baseStart_2991679 : Nat := 118140960795 + 2991679 * 2 ^ 59
def prefixEnd_2991679 : Nat := 4983230072969 + 3 ^ 40 * 2991679 * 2
def baseEnd_2991679 : Nat := 1024112860641537183902683

theorem tailTrace_2991679 : CollatzResearch.WordTrace tailWord_2991679 prefixEnd_2991679 1024112860641537183902683 := by
  unfold tailWord_2991679
  simp only [CollatzResearch.WordTrace]
  refine ⟨109115497328665395940450091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72743664885776930626966727 109115497328665395940450091)
  ·
    refine ⟨163673245992998093910675137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109115497328665395940450091 163673245992998093910675137)
    ·
      refine ⟨122754934494748570433006353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163673245992998093910675137 122754934494748570433006353)
      ·
        refine ⟨92066200871061427824754765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122754934494748570433006353 92066200871061427824754765)
        ·
          refine ⟨34524825326648035434283037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92066200871061427824754765 34524825326648035434283037)
          ·
            refine ⟨12946809497493013287856139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34524825326648035434283037 12946809497493013287856139)
            ·
              refine ⟨19420214246239519931784209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12946809497493013287856139 19420214246239519931784209)
              ·
                refine ⟨14565160684679639948838157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19420214246239519931784209 14565160684679639948838157)
                ·
                  refine ⟨5461935256754864980814309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14565160684679639948838157 5461935256754864980814309)
                  ·
                    refine ⟨1024112860641537183902683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5461935256754864980814309 1024112860641537183902683)
                    ·
                      rfl

theorem cell22_2991679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_2991679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991679 prefixEnd_2991679 := by exact prefixLift 2991679
  have htrace : WordTrace (prefixWord ++ tailWord_2991679) baseStart_2991679 baseEnd_2991679 := by
    simpa [prefixWord, tailWord_2991679, baseEnd_2991679] using wordTrace_append hprefix tailTrace_2991679
  have hstable : (prefixWord ++ tailWord_2991679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991679).length < 2 ^ (prefixWord ++ tailWord_2991679).sum := by decide
  have hdescent : baseEnd_2991679 < baseStart_2991679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991724 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 4, 4]
def baseStart_2991724 : Nat := 118140960795 + 2991724 * 2 ^ 59
def prefixEnd_2991724 : Nat := 4983230072969 + 3 ^ 40 * 2991724 * 2
def baseEnd_2991724 : Nat := 1024128265061172066527545

theorem tailTrace_2991724 : CollatzResearch.WordTrace tailWord_2991724 prefixEnd_2991724 1024128265061172066527545 := by
  unfold tailWord_2991724
  simp only [CollatzResearch.WordTrace]
  refine ⟨54558569306751184312919113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72744759075668245750558817 54558569306751184312919113)
  ·
    refine ⟨40918926980063388234689335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54558569306751184312919113 40918926980063388234689335)
    ·
      refine ⟨61378390470095082352034003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40918926980063388234689335 61378390470095082352034003)
      ·
        refine ⟨92067585705142623528051005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61378390470095082352034003 92067585705142623528051005)
        ·
          refine ⟨34525344639428483823019127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92067585705142623528051005 34525344639428483823019127)
          ·
            refine ⟨51788016959142725734528691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34525344639428483823019127 51788016959142725734528691)
            ·
              refine ⟨77682025438714088601793037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51788016959142725734528691 77682025438714088601793037)
              ·
                refine ⟨29130759539517783225672389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77682025438714088601793037 29130759539517783225672389)
                ·
                  refine ⟨5462017413659584354813573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29130759539517783225672389 5462017413659584354813573)
                  ·
                    refine ⟨1024128265061172066527545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5462017413659584354813573 1024128265061172066527545)
                    ·
                      rfl

theorem cell22_2991724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_2991724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991724 prefixEnd_2991724 := by exact prefixLift 2991724
  have htrace : WordTrace (prefixWord ++ tailWord_2991724) baseStart_2991724 baseEnd_2991724 := by
    simpa [prefixWord, tailWord_2991724, baseEnd_2991724] using wordTrace_append hprefix tailTrace_2991724
  have hstable : (prefixWord ++ tailWord_2991724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991724).length < 2 ^ (prefixWord ++ tailWord_2991724).sum := by decide
  have hdescent : baseEnd_2991724 < baseStart_2991724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991762 : List Nat := [3, 2, 3, 1, 4, 1, 1, 3, 4]
def baseStart_2991762 : Nat := 118140960795 + 2991762 * 2 ^ 59
def prefixEnd_2991762 : Nat := 4983230072969 + 3 ^ 40 * 2991762 * 2
def baseEnd_2991762 : Nat := 341380424412584211359143

theorem tailTrace_2991762 : CollatzResearch.WordTrace tailWord_2991762 prefixEnd_2991762 341380424412584211359143 := by
  unfold tailWord_2991762
  simp only [CollatzResearch.WordTrace]
  refine ⟨27279631146841175278930385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72745683058243134077147693 27279631146841175278930385)
  ·
    refine ⟨20459723360130881459197789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27279631146841175278930385 20459723360130881459197789)
    ·
      refine ⟨7672396260049080547199171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20459723360130881459197789 7672396260049080547199171)
      ·
        refine ⟨11508594390073620820798757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7672396260049080547199171 11508594390073620820798757)
        ·
          refine ⟨2157861448138803903899767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11508594390073620820798757 2157861448138803903899767)
          ·
            refine ⟨3236792172208205855849651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157861448138803903899767 3236792172208205855849651)
            ·
              refine ⟨4855188258312308783774477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3236792172208205855849651 4855188258312308783774477)
              ·
                refine ⟨1820695596867115793915429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4855188258312308783774477 1820695596867115793915429)
                ·
                  refine ⟨341380424412584211359143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1820695596867115793915429 341380424412584211359143)
                  ·
                    rfl

theorem cell22_2991762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_2991762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991762 prefixEnd_2991762 := by exact prefixLift 2991762
  have htrace : WordTrace (prefixWord ++ tailWord_2991762) baseStart_2991762 baseEnd_2991762 := by
    simpa [prefixWord, tailWord_2991762, baseEnd_2991762] using wordTrace_append hprefix tailTrace_2991762
  have hstable : (prefixWord ++ tailWord_2991762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991762).length < 2 ^ (prefixWord ++ tailWord_2991762).sum := by decide
  have hdescent : baseEnd_2991762 < baseStart_2991762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991895 : List Nat := [1, 1, 3, 4, 2, 1, 3, 2, 2, 3]
def baseStart_2991895 : Nat := 118140960795 + 2991895 * 2 ^ 59
def prefixEnd_2991895 : Nat := 4983230072969 + 3 ^ 40 * 2991895 * 2
def baseEnd_2991895 : Nat := 1024186801855784620502021

theorem tailTrace_2991895 : CollatzResearch.WordTrace tailWord_2991895 prefixEnd_2991895 1024186801855784620502021 := by
  unfold tailWord_2991895
  simp only [CollatzResearch.WordTrace]
  refine ⟨109123375495882864830313139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72748916997255243220208759 109123375495882864830313139)
  ·
    refine ⟨163685063243824297245469709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109123375495882864830313139 163685063243824297245469709)
    ·
      refine ⟨61381898716434111467051141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163685063243824297245469709 61381898716434111467051141)
      ·
        refine ⟨11509106009331395900072089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61381898716434111467051141 11509106009331395900072089)
        ·
          refine ⟨8631829506998546925054067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11509106009331395900072089 8631829506998546925054067)
          ·
            refine ⟨12947744260497820387581101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8631829506998546925054067 12947744260497820387581101)
            ·
              refine ⟨4855404097686682645342913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12947744260497820387581101 4855404097686682645342913)
              ·
                refine ⟨3641553073265011984007185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4855404097686682645342913 3641553073265011984007185)
                ·
                  refine ⟨2731164804948758988005389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3641553073265011984007185 2731164804948758988005389)
                  ·
                    refine ⟨1024186801855784620502021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2731164804948758988005389 1024186801855784620502021)
                    ·
                      rfl

theorem cell22_2991895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_2991895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991895 prefixEnd_2991895 := by exact prefixLift 2991895
  have htrace : WordTrace (prefixWord ++ tailWord_2991895) baseStart_2991895 baseEnd_2991895 := by
    simpa [prefixWord, tailWord_2991895, baseEnd_2991895] using wordTrace_append hprefix tailTrace_2991895
  have hstable : (prefixWord ++ tailWord_2991895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991895).length < 2 ^ (prefixWord ++ tailWord_2991895).sum := by decide
  have hdescent : baseEnd_2991895 < baseStart_2991895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991912 : List Nat := [2, 1, 5, 1, 1, 3, 3, 1, 2, 3]
def baseStart_2991912 : Nat := 118140960795 + 2991912 * 2 ^ 59
def prefixEnd_2991912 : Nat := 4983230072969 + 3 ^ 40 * 2991912 * 2
def baseEnd_2991912 : Nat := 1024192621303202242826969

theorem tailTrace_2991912 : CollatzResearch.WordTrace tailWord_2991912 prefixEnd_2991912 1024192621303202242826969 := by
  unfold tailWord_2991912
  simp only [CollatzResearch.WordTrace]
  refine ⟨54561997768410638366840995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72749330357880851155787993 54561997768410638366840995)
  ·
    refine ⟨81842996652615957550261493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54561997768410638366840995 81842996652615957550261493)
    ·
      refine ⟨7672780936182746020337015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81842996652615957550261493 7672780936182746020337015)
      ·
        refine ⟨11509171404274119030505523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7672780936182746020337015 11509171404274119030505523)
        ·
          refine ⟨17263757106411178545758285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11509171404274119030505523 17263757106411178545758285)
          ·
            refine ⟨6473908914904191954659357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17263757106411178545758285 6473908914904191954659357)
            ·
              refine ⟨2427715843089071982997259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6473908914904191954659357 2427715843089071982997259)
              ·
                refine ⟨3641573764633607974495889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2427715843089071982997259 3641573764633607974495889)
                ·
                  refine ⟨2731180323475205980871917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3641573764633607974495889 2731180323475205980871917)
                  ·
                    refine ⟨1024192621303202242826969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2731180323475205980871917 1024192621303202242826969)
                    ·
                      rfl

theorem cell22_2991912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_2991912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991912 prefixEnd_2991912 := by exact prefixLift 2991912
  have htrace : WordTrace (prefixWord ++ tailWord_2991912) baseStart_2991912 baseEnd_2991912 := by
    simpa [prefixWord, tailWord_2991912, baseEnd_2991912] using wordTrace_append hprefix tailTrace_2991912
  have hstable : (prefixWord ++ tailWord_2991912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991912).length < 2 ^ (prefixWord ++ tailWord_2991912).sum := by decide
  have hdescent : baseEnd_2991912 < baseStart_2991912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991925 : List Nat := [1, 3, 3, 1, 4, 2, 2, 6]
def baseStart_2991925 : Nat := 118140960795 + 2991925 * 2 ^ 59
def prefixEnd_2991925 : Nat := 4983230072969 + 3 ^ 40 * 2991925 * 2
def baseEnd_2991925 : Nat := 113799674607652726916881

theorem tailTrace_2991925 : CollatzResearch.WordTrace tailWord_2991925 prefixEnd_2991925 113799674607652726916881 := by
  unfold tailWord_2991925
  simp only [CollatzResearch.WordTrace]
  refine ⟨109124469685774179953905229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72749646457182786635936819 109124469685774179953905229)
  ·
    refine ⟨40921676132165317482714461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109124469685774179953905229 40921676132165317482714461)
    ·
      refine ⟨15345628549561994056017923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40921676132165317482714461 15345628549561994056017923)
      ·
        refine ⟨23018442824342991084026885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15345628549561994056017923 23018442824342991084026885)
        ·
          refine ⟨4315958029564310828255041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23018442824342991084026885 4315958029564310828255041)
          ·
            refine ⟨3236968522173233121191281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4315958029564310828255041 3236968522173233121191281)
            ·
              refine ⟨2427726391629924840893461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3236968522173233121191281 2427726391629924840893461)
              ·
                refine ⟨113799674607652726916881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2427726391629924840893461 113799674607652726916881)
                ·
                  rfl

theorem cell22_2991925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 6].length) (baseStart_2991925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991925 prefixEnd_2991925 := by exact prefixLift 2991925
  have htrace : WordTrace (prefixWord ++ tailWord_2991925) baseStart_2991925 baseEnd_2991925 := by
    simpa [prefixWord, tailWord_2991925, baseEnd_2991925] using wordTrace_append hprefix tailTrace_2991925
  have hstable : (prefixWord ++ tailWord_2991925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991925).length < 2 ^ (prefixWord ++ tailWord_2991925).sum := by decide
  have hdescent : baseEnd_2991925 < baseStart_2991925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2991970 : List Nat := [3, 3, 2, 1, 2, 2, 1, 3, 5]
def baseStart_2991970 : Nat := 118140960795 + 2991970 * 2 ^ 59
def prefixEnd_2991970 : Nat := 4983230072969 + 3 ^ 40 * 2991970 * 2
def baseEnd_2991970 : Nat := 341404158629503141625597

theorem tailTrace_2991970 : CollatzResearch.WordTrace tailWord_2991970 prefixEnd_2991970 341404158629503141625597 := by
  unfold tailWord_2991970
  simp only [CollatzResearch.WordTrace]
  refine ⟨27281527742652788159823341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72750740647074101759528909 27281527742652788159823341)
  ·
    refine ⟨10230572903494795559933753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27281527742652788159823341 10230572903494795559933753)
    ·
      refine ⟨7672929677621096669950315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10230572903494795559933753 7672929677621096669950315)
      ·
        refine ⟨11509394516431645004925473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7672929677621096669950315 11509394516431645004925473)
        ·
          refine ⟨8632045887323733753694105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11509394516431645004925473 8632045887323733753694105)
          ·
            refine ⟨6474034415492800315270579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8632045887323733753694105 6474034415492800315270579)
            ·
              refine ⟨9711051623239200472905869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6474034415492800315270579 9711051623239200472905869)
              ·
                refine ⟨3641644358714700177339701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9711051623239200472905869 3641644358714700177339701)
                ·
                  refine ⟨341404158629503141625597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3641644358714700177339701 341404158629503141625597)
                  ·
                    rfl

theorem cell22_2991970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_2991970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2991970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2991970 prefixEnd_2991970 := by exact prefixLift 2991970
  have htrace : WordTrace (prefixWord ++ tailWord_2991970) baseStart_2991970 baseEnd_2991970 := by
    simpa [prefixWord, tailWord_2991970, baseEnd_2991970] using wordTrace_append hprefix tailTrace_2991970
  have hstable : (prefixWord ++ tailWord_2991970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2991970).length < 2 ^ (prefixWord ++ tailWord_2991970).sum := by decide
  have hdescent : baseEnd_2991970 < baseStart_2991970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2991970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992000 : List Nat := [2, 1, 1, 2, 1, 2, 7, 1, 1, 4]
def baseStart_2992000 : Nat := 118140960795 + 2992000 * 2 ^ 59
def prefixEnd_2992000 : Nat := 4983230072969 + 3 ^ 40 * 2992000 * 2
def baseEnd_2992000 : Nat := 1024222745501599346626699

theorem tailTrace_2992000 : CollatzResearch.WordTrace tailWord_2992000 prefixEnd_2992000 1024222745501599346626699 := by
  unfold tailWord_2992000
  simp only [CollatzResearch.WordTrace]
  refine ⟨54563602580251233881442727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72751470107001645175256969 54563602580251233881442727)
  ·
    refine ⟨81845403870376850822164091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54563602580251233881442727 81845403870376850822164091)
    ·
      refine ⟨122768105805565276233246137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81845403870376850822164091 122768105805565276233246137)
      ·
        refine ⟨92076079354173957174934603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122768105805565276233246137 92076079354173957174934603)
        ·
          refine ⟨138114119031260935762401905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92076079354173957174934603 138114119031260935762401905)
          ·
            refine ⟨103585589273445701821801429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138114119031260935762401905 103585589273445701821801429)
            ·
              refine ⟨2427787248596383636448471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 103585589273445701821801429 2427787248596383636448471)
              ·
                refine ⟨3641680872894575454672707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2427787248596383636448471 3641680872894575454672707)
                ·
                  refine ⟨5462521309341863182009061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3641680872894575454672707 5462521309341863182009061)
                  ·
                    refine ⟨1024222745501599346626699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5462521309341863182009061 1024222745501599346626699)
                    ·
                      rfl

theorem cell22_2992000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 1, 4].length) (baseStart_2992000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992000 prefixEnd_2992000 := by exact prefixLift 2992000
  have htrace : WordTrace (prefixWord ++ tailWord_2992000) baseStart_2992000 baseEnd_2992000 := by
    simpa [prefixWord, tailWord_2992000, baseEnd_2992000] using wordTrace_append hprefix tailTrace_2992000
  have hstable : (prefixWord ++ tailWord_2992000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992000).length < 2 ^ (prefixWord ++ tailWord_2992000).sum := by decide
  have hdescent : baseEnd_2992000 < baseStart_2992000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992011 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 3, 6]
def baseStart_2992011 : Nat := 118140960795 + 2992011 * 2 ^ 59
def prefixEnd_2992011 : Nat := 4983230072969 + 3 ^ 40 * 2992011 * 2
def baseEnd_2992011 : Nat := 1024226511026398984601665

theorem tailTrace_2992011 : CollatzResearch.WordTrace tailWord_2992011 prefixEnd_2992011 1024226511026398984601665 := by
  unfold tailWord_2992011
  simp only [CollatzResearch.WordTrace]
  refine ⟨109127606363462616641535887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72751737575641744427690591 109127606363462616641535887)
  ·
    refine ⟨163691409545193924962303831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109127606363462616641535887 163691409545193924962303831)
    ·
      refine ⟨245537114317790887443455747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163691409545193924962303831 245537114317790887443455747)
      ·
        refine ⟨368305671476686331165183621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245537114317790887443455747 368305671476686331165183621)
        ·
          refine ⟨69057313401878687093471929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 368305671476686331165183621 69057313401878687093471929)
          ·
            refine ⟨51792985051409015320103947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69057313401878687093471929 51792985051409015320103947)
            ·
              refine ⟨77689477577113522980155921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51792985051409015320103947 77689477577113522980155921)
              ·
                refine ⟨58267108182835142235116941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77689477577113522980155921 58267108182835142235116941)
                ·
                  refine ⟨21850165568563178338168853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58267108182835142235116941 21850165568563178338168853)
                  ·
                    refine ⟨1024226511026398984601665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21850165568563178338168853 1024226511026398984601665)
                    ·
                      rfl

theorem cell22_2992011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 6].length) (baseStart_2992011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992011 prefixEnd_2992011 := by exact prefixLift 2992011
  have htrace : WordTrace (prefixWord ++ tailWord_2992011) baseStart_2992011 baseEnd_2992011 := by
    simpa [prefixWord, tailWord_2992011, baseEnd_2992011] using wordTrace_append hprefix tailTrace_2992011
  have hstable : (prefixWord ++ tailWord_2992011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992011).length < 2 ^ (prefixWord ++ tailWord_2992011).sum := by decide
  have hdescent : baseEnd_2992011 < baseStart_2992011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992041 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 1, 9]
def baseStart_2992041 : Nat := 118140960795 + 2992041 * 2 ^ 59
def prefixEnd_2992041 : Nat := 4983230072969 + 3 ^ 40 * 2992041 * 2
def baseEnd_2992041 : Nat := 1024236780639488906351573

theorem tailTrace_2992041 : CollatzResearch.WordTrace tailWord_2992041 prefixEnd_2992041 1024236780639488906351573 := by
  unfold tailWord_2992041
  simp only [CollatzResearch.WordTrace]
  refine ⟨109128700553353931765127977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72752467035569287843418651 109128700553353931765127977)
  ·
    refine ⟨81846525415015448823845983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109128700553353931765127977 81846525415015448823845983)
    ·
      refine ⟨122769788122523173235768975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81846525415015448823845983 122769788122523173235768975)
      ·
        refine ⟨184154682183784759853653463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122769788122523173235768975 184154682183784759853653463)
        ·
          refine ⟨276232023275677139780480195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184154682183784759853653463 276232023275677139780480195)
          ·
            refine ⟨414348034913515709670720293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276232023275677139780480195 414348034913515709670720293)
            ·
              refine ⟨77690256546284195563260055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 414348034913515709670720293 77690256546284195563260055)
              ·
                refine ⟨116535384819426293344890083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77690256546284195563260055 116535384819426293344890083)
                ·
                  refine ⟨174803077229139440017335125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116535384819426293344890083 174803077229139440017335125)
                  ·
                    refine ⟨1024236780639488906351573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 174803077229139440017335125 1024236780639488906351573)
                    ·
                      rfl

theorem cell22_2992041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_2992041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992041 prefixEnd_2992041 := by exact prefixLift 2992041
  have htrace : WordTrace (prefixWord ++ tailWord_2992041) baseStart_2992041 baseEnd_2992041 := by
    simpa [prefixWord, tailWord_2992041, baseEnd_2992041] using wordTrace_append hprefix tailTrace_2992041
  have hstable : (prefixWord ++ tailWord_2992041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992041).length < 2 ^ (prefixWord ++ tailWord_2992041).sum := by decide
  have hdescent : baseEnd_2992041 < baseStart_2992041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992060 : List Nat := [2, 2, 2, 5, 1, 1, 9]
def baseStart_2992060 : Nat := 118140960795 + 2992060 * 2 ^ 59
def prefixEnd_2992060 : Nat := 4983230072969 + 3 ^ 40 * 2992060 * 2
def baseEnd_2992060 : Nat := 37934936471399229263945

theorem tailTrace_2992060 : CollatzResearch.WordTrace tailWord_2992060 prefixEnd_2992060 37934936471399229263945 := by
  unfold tailWord_2992060
  simp only [CollatzResearch.WordTrace]
  refine ⟨54564696770142549005034817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72752929026856732006713089 54564696770142549005034817)
  ·
    refine ⟨40923522577606911753776113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54564696770142549005034817 40923522577606911753776113)
    ·
      refine ⟨30692641933205183815332085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40923522577606911753776113 30692641933205183815332085)
      ·
        refine ⟨2877435181237985982687383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30692641933205183815332085 2877435181237985982687383)
        ·
          refine ⟨4316152771856978974031075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2877435181237985982687383 4316152771856978974031075)
          ·
            refine ⟨6474229157785468461046613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4316152771856978974031075 6474229157785468461046613)
            ·
              refine ⟨37934936471399229263945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6474229157785468461046613 37934936471399229263945)
              ·
                rfl

theorem cell22_2992060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 9].length) (baseStart_2992060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992060 prefixEnd_2992060 := by exact prefixLift 2992060
  have htrace : WordTrace (prefixWord ++ tailWord_2992060) baseStart_2992060 baseEnd_2992060 := by
    simpa [prefixWord, tailWord_2992060, baseEnd_2992060] using wordTrace_append hprefix tailTrace_2992060
  have hstable : (prefixWord ++ tailWord_2992060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992060).length < 2 ^ (prefixWord ++ tailWord_2992060).sum := by decide
  have hdescent : baseEnd_2992060 < baseStart_2992060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992075 : List Nat := [1, 1, 1, 1, 3, 4, 4, 1, 3, 3]
def baseStart_2992075 : Nat := 118140960795 + 2992075 * 2 ^ 59
def prefixEnd_2992075 : Nat := 4983230072969 + 3 ^ 40 * 2992075 * 2
def baseEnd_2992075 : Nat := 1024248419534324151001469

theorem tailTrace_2992075 : CollatzResearch.WordTrace tailWord_2992075 prefixEnd_2992075 1024248419534324151001469 := by
  unfold tailWord_2992075
  simp only [CollatzResearch.WordTrace]
  refine ⟨109129940635230755571865679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72753293756820503714577119 109129940635230755571865679)
  ·
    refine ⟨163694910952846133357798519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109129940635230755571865679 163694910952846133357798519)
    ·
      refine ⟨245542366429269200036697779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163694910952846133357798519 245542366429269200036697779)
      ·
        refine ⟨368313549643903800055046669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245542366429269200036697779 368313549643903800055046669)
        ·
          refine ⟨138117581116463925020642501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 368313549643903800055046669 138117581116463925020642501)
          ·
            refine ⟨25897046459336985941370469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138117581116463925020642501 25897046459336985941370469)
            ·
              refine ⟨4855696211125684864006963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25897046459336985941370469 4855696211125684864006963)
              ·
                refine ⟨7283544316688527296010445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4855696211125684864006963 7283544316688527296010445)
                ·
                  refine ⟨2731329118758197736003917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7283544316688527296010445 2731329118758197736003917)
                  ·
                    refine ⟨1024248419534324151001469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2731329118758197736003917 1024248419534324151001469)
                    ·
                      rfl

theorem cell22_2992075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 3].length) (baseStart_2992075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992075 prefixEnd_2992075 := by exact prefixLift 2992075
  have htrace : WordTrace (prefixWord ++ tailWord_2992075) baseStart_2992075 baseEnd_2992075 := by
    simpa [prefixWord, tailWord_2992075, baseEnd_2992075] using wordTrace_append hprefix tailTrace_2992075
  have hstable : (prefixWord ++ tailWord_2992075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992075).length < 2 ^ (prefixWord ++ tailWord_2992075).sum := by decide
  have hdescent : baseEnd_2992075 < baseStart_2992075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992165 : List Nat := [1, 3, 1, 2, 2, 4, 1, 2, 1, 5]
def baseStart_2992165 : Nat := 118140960795 + 2992165 * 2 ^ 59
def prefixEnd_2992165 : Nat := 4983230072969 + 3 ^ 40 * 2992165 * 2
def baseEnd_2992165 : Nat := 1024279228373593916251193

theorem tailTrace_2992165 : CollatzResearch.WordTrace tailWord_2992165 prefixEnd_2992165 1024279228373593916251193 := by
  unfold tailWord_2992165
  simp only [CollatzResearch.WordTrace]
  refine ⟨109133223204904700942641949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72755482136603133961761299 109133223204904700942641949)
  ·
    refine ⟨40924958701839262853490731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109133223204904700942641949 40924958701839262853490731)
    ·
      refine ⟨61387438052758894280236097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40924958701839262853490731 61387438052758894280236097)
      ·
        refine ⟨46040578539569170710177073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61387438052758894280236097 46040578539569170710177073)
        ·
          refine ⟨34530433904676878032632805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46040578539569170710177073 34530433904676878032632805)
          ·
            refine ⟨6474456357126914631118651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34530433904676878032632805 6474456357126914631118651)
            ·
              refine ⟨9711684535690371946677977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6474456357126914631118651 9711684535690371946677977)
              ·
                refine ⟨7283763401767778960008483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9711684535690371946677977 7283763401767778960008483)
                ·
                  refine ⟨10925645102651668440012725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7283763401767778960008483 10925645102651668440012725)
                  ·
                    refine ⟨1024279228373593916251193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10925645102651668440012725 1024279228373593916251193)
                    ·
                      rfl

theorem cell22_2992165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_2992165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992165 prefixEnd_2992165 := by exact prefixLift 2992165
  have htrace : WordTrace (prefixWord ++ tailWord_2992165) baseStart_2992165 baseEnd_2992165 := by
    simpa [prefixWord, tailWord_2992165, baseEnd_2992165] using wordTrace_append hprefix tailTrace_2992165
  have hstable : (prefixWord ++ tailWord_2992165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992165).length < 2 ^ (prefixWord ++ tailWord_2992165).sum := by decide
  have hdescent : baseEnd_2992165 < baseStart_2992165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992178 : List Nat := [3, 2, 1, 1, 2, 13]
def baseStart_2992178 : Nat := 118140960795 + 2992178 * 2 ^ 59
def prefixEnd_2992178 : Nat := 4983230072969 + 3 ^ 40 * 2992178 * 2
def baseEnd_2992178 : Nat := 12645477512830447107113

theorem tailTrace_2992178 : CollatzResearch.WordTrace tailWord_2992178 prefixEnd_2992178 12645477512830447107113 := by
  unfold tailWord_2992178
  simp only [CollatzResearch.WordTrace]
  refine ⟨27283424338464401040716297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72755798235905069441910125 27283424338464401040716297)
  ·
    refine ⟨20462568253848300780537223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27283424338464401040716297 20462568253848300780537223)
    ·
      refine ⟨30693852380772451170805835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20462568253848300780537223 30693852380772451170805835)
      ·
        refine ⟨46040778571158676756208753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30693852380772451170805835 46040778571158676756208753)
        ·
          refine ⟨34530583928369007567156565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46040778571158676756208753 34530583928369007567156565)
          ·
            refine ⟨12645477512830447107113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 34530583928369007567156565 12645477512830447107113)
            ·
              rfl

theorem cell22_2992178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 13].length) (baseStart_2992178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992178 prefixEnd_2992178 := by exact prefixLift 2992178
  have htrace : WordTrace (prefixWord ++ tailWord_2992178) baseStart_2992178 baseEnd_2992178 := by
    simpa [prefixWord, tailWord_2992178, baseEnd_2992178] using wordTrace_append hprefix tailTrace_2992178
  have hstable : (prefixWord ++ tailWord_2992178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992178).length < 2 ^ (prefixWord ++ tailWord_2992178).sum := by decide
  have hdescent : baseEnd_2992178 < baseStart_2992178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992214 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_2992214 : Nat := 118140960795 + 2992214 * 2 ^ 59
def prefixEnd_2992214 : Nat := 4983230072969 + 3 ^ 40 * 2992214 * 2
def baseEnd_2992214 : Nat := 1024296002074974121776043

theorem tailTrace_2992214 : CollatzResearch.WordTrace tailWord_2992214 prefixEnd_2992214 1024296002074974121776043 := by
  unfold tailWord_2992214
  simp only [CollatzResearch.WordTrace]
  refine ⟨6820938148857948894448481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72756673587818121540783797 6820938148857948894448481)
  ·
    refine ⟨5115703611643461670836361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6820938148857948894448481 5115703611643461670836361)
    ·
      refine ⟨3836777708732596253127271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5115703611643461670836361 3836777708732596253127271)
      ·
        refine ⟨5755166563098894379690907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3836777708732596253127271 5755166563098894379690907)
        ·
          refine ⟨8632749844648341569536361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5755166563098894379690907 8632749844648341569536361)
          ·
            refine ⟨6474562383486256177152271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8632749844648341569536361 6474562383486256177152271)
            ·
              refine ⟨9711843575229384265728407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6474562383486256177152271 9711843575229384265728407)
              ·
                refine ⟨14567765362844076398592611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9711843575229384265728407 14567765362844076398592611)
                ·
                  refine ⟨21851648044266114597888917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14567765362844076398592611 21851648044266114597888917)
                  ·
                    refine ⟨1024296002074974121776043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21851648044266114597888917 1024296002074974121776043)
                    ·
                      rfl

theorem cell22_2992214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_2992214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992214 prefixEnd_2992214 := by exact prefixLift 2992214
  have htrace : WordTrace (prefixWord ++ tailWord_2992214) baseStart_2992214 baseEnd_2992214 := by
    simpa [prefixWord, tailWord_2992214, baseEnd_2992214] using wordTrace_append hprefix tailTrace_2992214
  have hstable : (prefixWord ++ tailWord_2992214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992214).length < 2 ^ (prefixWord ++ tailWord_2992214).sum := by decide
  have hdescent : baseEnd_2992214 < baseStart_2992214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992240 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 7]
def baseStart_2992240 : Nat := 118140960795 + 2992240 * 2 ^ 59
def prefixEnd_2992240 : Nat := 4983230072969 + 3 ^ 40 * 2992240 * 2
def baseEnd_2992240 : Nat := 341434967468772906875321

theorem tailTrace_2992240 : CollatzResearch.WordTrace tailWord_2992240 prefixEnd_2992240 341434967468772906875321 := by
  unfold tailWord_2992240
  simp only [CollatzResearch.WordTrace]
  refine ⟨54567979339816494375811087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72757305786421992501081449 54567979339816494375811087)
  ·
    refine ⟨81851969009724741563716631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54567979339816494375811087 81851969009724741563716631)
    ·
      refine ⟨122777953514587112345574947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81851969009724741563716631 122777953514587112345574947)
      ·
        refine ⟨184166930271880668518362421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122777953514587112345574947 184166930271880668518362421)
        ·
          refine ⟨17265649712988812673596477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184166930271880668518362421 17265649712988812673596477)
          ·
            refine ⟨6474618642370804752598679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17265649712988812673596477 6474618642370804752598679)
            ·
              refine ⟨9711927963556207128898019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6474618642370804752598679 9711927963556207128898019)
              ·
                refine ⟨14567891945334310693347029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9711927963556207128898019 14567891945334310693347029)
                ·
                  refine ⟨341434967468772906875321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14567891945334310693347029 341434967468772906875321)
                  ·
                    rfl

theorem cell22_2992240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 7].length) (baseStart_2992240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992240 prefixEnd_2992240 := by exact prefixLift 2992240
  have htrace : WordTrace (prefixWord ++ tailWord_2992240) baseStart_2992240 baseEnd_2992240 := by
    simpa [prefixWord, tailWord_2992240, baseEnd_2992240] using wordTrace_append hprefix tailTrace_2992240
  have hstable : (prefixWord ++ tailWord_2992240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992240).length < 2 ^ (prefixWord ++ tailWord_2992240).sum := by decide
  have hdescent : baseEnd_2992240 < baseStart_2992240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992308 : List Nat := [2, 5, 3, 1, 1, 1, 1, 3, 5]
def baseStart_2992308 : Nat := 118140960795 + 2992308 * 2 ^ 59
def prefixEnd_2992308 : Nat := 4983230072969 + 3 ^ 40 * 2992308 * 2
def baseEnd_2992308 : Nat := 341442726731996403308585

theorem tailTrace_2992308 : CollatzResearch.WordTrace tailWord_2992308 prefixEnd_2992308 341442726731996403308585 := by
  unfold tailWord_2992308
  simp only [CollatzResearch.WordTrace]
  refine ⟨54569219421693318182548789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72758959228924424243398385 54569219421693318182548789)
  ·
    refine ⟨5115864320783748579613949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54569219421693318182548789 5115864320783748579613949)
    ·
      refine ⟨1918449120293905717355231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5115864320783748579613949 1918449120293905717355231)
      ·
        refine ⟨2877673680440858576032847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1918449120293905717355231 2877673680440858576032847)
        ·
          refine ⟨4316510520661287864049271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2877673680440858576032847 4316510520661287864049271)
          ·
            refine ⟨6474765780991931796073907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4316510520661287864049271 6474765780991931796073907)
            ·
              refine ⟨9712148671487897694110861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6474765780991931796073907 9712148671487897694110861)
              ·
                refine ⟨3642055751807961635291573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9712148671487897694110861 3642055751807961635291573)
                ·
                  refine ⟨341442726731996403308585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3642055751807961635291573 341442726731996403308585)
                  ·
                    rfl

theorem cell22_2992308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_2992308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992308 prefixEnd_2992308 := by exact prefixLift 2992308
  have htrace : WordTrace (prefixWord ++ tailWord_2992308) baseStart_2992308 baseEnd_2992308 := by
    simpa [prefixWord, tailWord_2992308, baseEnd_2992308] using wordTrace_append hprefix tailTrace_2992308
  have hstable : (prefixWord ++ tailWord_2992308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992308).length < 2 ^ (prefixWord ++ tailWord_2992308).sum := by decide
  have hdescent : baseEnd_2992308 < baseStart_2992308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992315 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 4, 4]
def baseStart_2992315 : Nat := 118140960795 + 2992315 * 2 ^ 59
def prefixEnd_2992315 : Nat := 4983230072969 + 3 ^ 40 * 2992315 * 2
def baseEnd_2992315 : Nat := 1024330576439043525000733

theorem tailTrace_2992315 : CollatzResearch.WordTrace tailWord_2992315 prefixEnd_2992315 1024330576439043525000733 := by
  unfold tailWord_2992315
  simp only [CollatzResearch.WordTrace]
  refine ⟨109138694154361276560602399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72759129436240851040401599 109138694154361276560602399)
  ·
    refine ⟨163708041231541914840903599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109138694154361276560602399 163708041231541914840903599)
    ·
      refine ⟨245562061847312872261355399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163708041231541914840903599 245562061847312872261355399)
      ·
        refine ⟨368343092770969308392033099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245562061847312872261355399 368343092770969308392033099)
        ·
          refine ⟨552514639156453962588049649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368343092770969308392033099 552514639156453962588049649)
          ·
            refine ⟨414385979367340471941037237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552514639156453962588049649 414385979367340471941037237)
            ·
              refine ⟨38848685565688169244472241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 414385979367340471941037237 38848685565688169244472241)
              ·
                refine ⟨29136514174266126933354181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38848685565688169244472241 29136514174266126933354181)
                ·
                  refine ⟨5463096407674898800003909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29136514174266126933354181 5463096407674898800003909)
                  ·
                    refine ⟨1024330576439043525000733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5463096407674898800003909 1024330576439043525000733)
                    ·
                      rfl

theorem cell22_2992315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 4].length) (baseStart_2992315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992315 prefixEnd_2992315 := by exact prefixLift 2992315
  have htrace : WordTrace (prefixWord ++ tailWord_2992315) baseStart_2992315 baseEnd_2992315 := by
    simpa [prefixWord, tailWord_2992315, baseEnd_2992315] using wordTrace_append hprefix tailTrace_2992315
  have hstable : (prefixWord ++ tailWord_2992315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992315).length < 2 ^ (prefixWord ++ tailWord_2992315).sum := by decide
  have hdescent : baseEnd_2992315 < baseStart_2992315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992330 : List Nat := [3, 1, 2, 1, 3, 1, 1, 10]
def baseStart_2992330 : Nat := 118140960795 + 2992330 * 2 ^ 59
def prefixEnd_2992330 : Nat := 4983230072969 + 3 ^ 40 * 2992330 * 2
def baseEnd_2992330 : Nat := 113815079027287609541743

theorem tailTrace_2992330 : CollatzResearch.WordTrace tailWord_2992330 prefixEnd_2992330 113815079027287609541743 := by
  unfold tailWord_2992330
  simp only [CollatzResearch.WordTrace]
  refine ⟨27284810312326733530599611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72759494166204622748265629 27284810312326733530599611)
  ·
    refine ⟨40927215468490100295899417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27284810312326733530599611 40927215468490100295899417)
    ·
      refine ⟨30695411601367575221924563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40927215468490100295899417 30695411601367575221924563)
      ·
        refine ⟨46043117402051362832886845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30695411601367575221924563 46043117402051362832886845)
        ·
          refine ⟨17266169025769261062332567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46043117402051362832886845 17266169025769261062332567)
          ·
            refine ⟨25899253538653891593498851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17266169025769261062332567 25899253538653891593498851)
            ·
              refine ⟨38848880307980837390248277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25899253538653891593498851 38848880307980837390248277)
              ·
                refine ⟨113815079027287609541743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38848880307980837390248277 113815079027287609541743)
                ·
                  rfl

theorem cell22_2992330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 10].length) (baseStart_2992330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992330 prefixEnd_2992330 := by exact prefixLift 2992330
  have htrace : WordTrace (prefixWord ++ tailWord_2992330) baseStart_2992330 baseEnd_2992330 := by
    simpa [prefixWord, tailWord_2992330, baseEnd_2992330] using wordTrace_append hprefix tailTrace_2992330
  have hstable : (prefixWord ++ tailWord_2992330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992330).length < 2 ^ (prefixWord ++ tailWord_2992330).sum := by decide
  have hdescent : baseEnd_2992330 < baseStart_2992330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992349 : List Nat := [1, 4, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_2992349 : Nat := 118140960795 + 2992349 * 2 ^ 59
def prefixEnd_2992349 : Nat := 4983230072969 + 3 ^ 40 * 2992349 * 2
def baseEnd_2992349 : Nat := 1024342215333878769650629

theorem tailTrace_2992349 : CollatzResearch.WordTrace tailWord_2992349 prefixEnd_2992349 1024342215333878769650629 := by
  unfold tailWord_2992349
  simp only [CollatzResearch.WordTrace]
  refine ⟨109139934236238100367340101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72759956157492066911560067 109139934236238100367340101)
  ·
    refine ⟨20463737669294643818876269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109139934236238100367340101 20463737669294643818876269)
    ·
      refine ⟨7673901625985491432078601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20463737669294643818876269 7673901625985491432078601)
      ·
        refine ⟨5755426219489118574058951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7673901625985491432078601 5755426219489118574058951)
        ·
          refine ⟨8633139329233677861088427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5755426219489118574058951 8633139329233677861088427)
          ·
            refine ⟨12949708993850516791632641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8633139329233677861088427 12949708993850516791632641)
            ·
              refine ⟨9712281745387887593724481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12949708993850516791632641 9712281745387887593724481)
              ·
                refine ⟨7284211309040915695293361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9712281745387887593724481 7284211309040915695293361)
                ·
                  refine ⟨5463158481780686771470021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7284211309040915695293361 5463158481780686771470021)
                  ·
                    refine ⟨1024342215333878769650629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5463158481780686771470021 1024342215333878769650629)
                    ·
                      rfl

theorem cell22_2992349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_2992349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992349 prefixEnd_2992349 := by exact prefixLift 2992349
  have htrace : WordTrace (prefixWord ++ tailWord_2992349) baseStart_2992349 baseEnd_2992349 := by
    simpa [prefixWord, tailWord_2992349, baseEnd_2992349] using wordTrace_append hprefix tailTrace_2992349
  have hstable : (prefixWord ++ tailWord_2992349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992349).length < 2 ^ (prefixWord ++ tailWord_2992349).sum := by decide
  have hdescent : baseEnd_2992349 < baseStart_2992349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992396 : List Nat := [2, 2, 1, 2, 2, 2, 4, 3, 1, 3]
def baseStart_2992396 : Nat := 118140960795 + 2992396 * 2 ^ 59
def prefixEnd_2992396 : Nat := 4983230072969 + 3 ^ 40 * 2992396 * 2
def baseEnd_2992396 : Nat := 1024358304394386313725485

theorem tailTrace_2992396 : CollatzResearch.WordTrace tailWord_2992396 prefixEnd_2992396 1024358304394386313725485 := by
  unfold tailWord_2992396
  simp only [CollatzResearch.WordTrace]
  refine ⟨54570824233533913697150521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72761098978045218262867361 54570824233533913697150521)
  ·
    refine ⟨40928118175150435272862891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54570824233533913697150521 40928118175150435272862891)
    ·
      refine ⟨61392177262725652909294337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40928118175150435272862891 61392177262725652909294337)
      ·
        refine ⟨46044132947044239681970753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61392177262725652909294337 46044132947044239681970753)
        ·
          refine ⟨34533099710283179761478065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46044132947044239681970753 34533099710283179761478065)
          ·
            refine ⟨25899824782712384821108549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34533099710283179761478065 25899824782712384821108549)
            ·
              refine ⟨4856217146758572153957853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25899824782712384821108549 4856217146758572153957853)
              ·
                refine ⟨1821081430034464557734195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4856217146758572153957853 1821081430034464557734195)
                ·
                  refine ⟨2731622145051696836601293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1821081430034464557734195 2731622145051696836601293)
                  ·
                    refine ⟨1024358304394386313725485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2731622145051696836601293 1024358304394386313725485)
                    ·
                      rfl

theorem cell22_2992396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 1, 3].length) (baseStart_2992396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992396 prefixEnd_2992396 := by exact prefixLift 2992396
  have htrace : WordTrace (prefixWord ++ tailWord_2992396) baseStart_2992396 baseEnd_2992396 := by
    simpa [prefixWord, tailWord_2992396, baseEnd_2992396] using wordTrace_append hprefix tailTrace_2992396
  have hstable : (prefixWord ++ tailWord_2992396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992396).length < 2 ^ (prefixWord ++ tailWord_2992396).sum := by decide
  have hdescent : baseEnd_2992396 < baseStart_2992396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992407 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 2, 5]
def baseStart_2992407 : Nat := 118140960795 + 2992407 * 2 ^ 59
def prefixEnd_2992407 : Nat := 4983230072969 + 3 ^ 40 * 2992407 * 2
def baseEnd_2992407 : Nat := 1024362069919185951700451

theorem tailTrace_2992407 : CollatzResearch.WordTrace tailWord_2992407 prefixEnd_2992407 1024362069919185951700451 := by
  unfold tailWord_2992407
  simp only [CollatzResearch.WordTrace]
  refine ⟨109142049670027976272951475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72761366446685317515300983 109142049670027976272951475)
  ·
    refine ⟨163713074505041964409427213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109142049670027976272951475 163713074505041964409427213)
    ·
      refine ⟨61392402939390736653535205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163713074505041964409427213 61392402939390736653535205)
      ·
        refine ⟨11511075551135763122537851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61392402939390736653535205 11511075551135763122537851)
        ·
          refine ⟨17266613326703644683806777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11511075551135763122537851 17266613326703644683806777)
          ·
            refine ⟨12949959995027733512855083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17266613326703644683806777 12949959995027733512855083)
            ·
              refine ⟨19424939992541600269282625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12949959995027733512855083 19424939992541600269282625)
              ·
                refine ⟨14568704994406200201961969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19424939992541600269282625 14568704994406200201961969)
                ·
                  refine ⟨10926528745804650151471477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14568704994406200201961969 10926528745804650151471477)
                  ·
                    refine ⟨1024362069919185951700451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10926528745804650151471477 1024362069919185951700451)
                    ·
                      rfl

theorem cell22_2992407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_2992407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992407 prefixEnd_2992407 := by exact prefixLift 2992407
  have htrace : WordTrace (prefixWord ++ tailWord_2992407) baseStart_2992407 baseEnd_2992407 := by
    simpa [prefixWord, tailWord_2992407, baseEnd_2992407] using wordTrace_append hprefix tailTrace_2992407
  have hstable : (prefixWord ++ tailWord_2992407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992407).length < 2 ^ (prefixWord ++ tailWord_2992407).sum := by decide
  have hdescent : baseEnd_2992407 < baseStart_2992407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992437 : List Nat := [1, 3, 3, 1, 2, 1, 1, 4, 6]
def baseStart_2992437 : Nat := 118140960795 + 2992437 * 2 ^ 59
def prefixEnd_2992437 : Nat := 4983230072969 + 3 ^ 40 * 2992437 * 2
def baseEnd_2992437 : Nat := 341457446510758624483453

theorem tailTrace_2992437 : CollatzResearch.WordTrace tailWord_2992437 prefixEnd_2992437 341457446510758624483453 := by
  unfold tailWord_2992437
  simp only [CollatzResearch.WordTrace]
  refine ⟨109143143859919291396543565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72762095906612860931029043 109143143859919291396543565)
  ·
    refine ⟨40928678947469734273703837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109143143859919291396543565 40928678947469734273703837)
    ·
      refine ⟨15348254605301150352638939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40928678947469734273703837 15348254605301150352638939)
      ·
        refine ⟨23022381907951725528958409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15348254605301150352638939 23022381907951725528958409)
        ·
          refine ⟨17266786430963794146718807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23022381907951725528958409 17266786430963794146718807)
          ·
            refine ⟨25900179646445691220078211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17266786430963794146718807 25900179646445691220078211)
            ·
              refine ⟨38850269469668536830117317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25900179646445691220078211 38850269469668536830117317)
              ·
                refine ⟨7284425525562850655646997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38850269469668536830117317 7284425525562850655646997)
                ·
                  refine ⟨341457446510758624483453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7284425525562850655646997 341457446510758624483453)
                  ·
                    rfl

theorem cell22_2992437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_2992437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992437 prefixEnd_2992437 := by exact prefixLift 2992437
  have htrace : WordTrace (prefixWord ++ tailWord_2992437) baseStart_2992437 baseEnd_2992437 := by
    simpa [prefixWord, tailWord_2992437, baseEnd_2992437] using wordTrace_append hprefix tailTrace_2992437
  have hstable : (prefixWord ++ tailWord_2992437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992437).length < 2 ^ (prefixWord ++ tailWord_2992437).sum := by decide
  have hdescent : baseEnd_2992437 < baseStart_2992437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992471 : List Nat := [1, 1, 3, 2, 3, 1, 5, 2, 4]
def baseStart_2992471 : Nat := 118140960795 + 2992471 * 2 ^ 59
def prefixEnd_2992471 : Nat := 4983230072969 + 3 ^ 40 * 2992471 * 2
def baseEnd_2992471 : Nat := 341461326142370372700085

theorem tailTrace_2992471 : CollatzResearch.WordTrace tailWord_2992471 prefixEnd_2992471 341461326142370372700085 := by
  unfold tailWord_2992471
  simp only [CollatzResearch.WordTrace]
  refine ⟨109144383941796115203281267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72762922627864076802187511 109144383941796115203281267)
  ·
    refine ⟨163716575912694172804921901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109144383941796115203281267 163716575912694172804921901)
    ·
      refine ⟨61393715967260314801845713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163716575912694172804921901 61393715967260314801845713)
      ·
        refine ⟨46045286975445236101384285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61393715967260314801845713 46045286975445236101384285)
        ·
          refine ⟨17266982615791963538019107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46045286975445236101384285 17266982615791963538019107)
          ·
            refine ⟨25900473923687945307028661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17266982615791963538019107 25900473923687945307028661)
            ·
              refine ⟨2428169430345744872533937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25900473923687945307028661 2428169430345744872533937)
              ·
                refine ⟨1821127072759308654400453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2428169430345744872533937 1821127072759308654400453)
                ·
                  refine ⟨341461326142370372700085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1821127072759308654400453 341461326142370372700085)
                  ·
                    rfl

theorem cell22_2992471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 4].length) (baseStart_2992471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992471 prefixEnd_2992471 := by exact prefixLift 2992471
  have htrace : WordTrace (prefixWord ++ tailWord_2992471) baseStart_2992471 baseEnd_2992471 := by
    simpa [prefixWord, tailWord_2992471, baseEnd_2992471] using wordTrace_append hprefix tailTrace_2992471
  have hstable : (prefixWord ++ tailWord_2992471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992471).length < 2 ^ (prefixWord ++ tailWord_2992471).sum := by decide
  have hdescent : baseEnd_2992471 < baseStart_2992471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992501 : List Nat := [1, 3, 4, 1, 2, 2, 2, 1, 2, 4]
def baseStart_2992501 : Nat := 118140960795 + 2992501 * 2 ^ 59
def prefixEnd_2992501 : Nat := 4983230072969 + 3 ^ 40 * 2992501 * 2
def baseEnd_2992501 : Nat := 1024394248040201039850163

theorem tailTrace_2992501 : CollatzResearch.WordTrace tailWord_2992501 prefixEnd_2992501 1024394248040201039850163 := by
  unfold tailWord_2992501
  simp only [CollatzResearch.WordTrace]
  refine ⟨109145478131687430326873357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72763652087791620217915571 109145478131687430326873357)
  ·
    refine ⟨40929554299382786372577509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109145478131687430326873357 40929554299382786372577509)
    ·
      refine ⟨7674291431134272444858283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40929554299382786372577509 7674291431134272444858283)
      ·
        refine ⟨11511437146701408667287425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7674291431134272444858283 11511437146701408667287425)
        ·
          refine ⟨8633577860026056500465569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11511437146701408667287425 8633577860026056500465569)
          ·
            refine ⟨6475183395019542375349177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8633577860026056500465569 6475183395019542375349177)
            ·
              refine ⟨4856387546264656781511883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6475183395019542375349177 4856387546264656781511883)
              ·
                refine ⟨7284581319396985172267825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4856387546264656781511883 7284581319396985172267825)
                ·
                  refine ⟨5463435989547738879200869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7284581319396985172267825 5463435989547738879200869)
                  ·
                    refine ⟨1024394248040201039850163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5463435989547738879200869 1024394248040201039850163)
                    ·
                      rfl

theorem cell22_2992501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_2992501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992501 prefixEnd_2992501 := by exact prefixLift 2992501
  have htrace : WordTrace (prefixWord ++ tailWord_2992501) baseStart_2992501 baseEnd_2992501 := by
    simpa [prefixWord, tailWord_2992501, baseEnd_2992501] using wordTrace_append hprefix tailTrace_2992501
  have hstable : (prefixWord ++ tailWord_2992501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992501).length < 2 ^ (prefixWord ++ tailWord_2992501).sum := by decide
  have hdescent : baseEnd_2992501 < baseStart_2992501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992522 : List Nat := [3, 1, 2, 5, 2, 1, 2, 2, 4]
def baseStart_2992522 : Nat := 118140960795 + 2992522 * 2 ^ 59
def prefixEnd_2992522 : Nat := 4983230072969 + 3 ^ 40 * 2992522 * 2
def baseEnd_2992522 : Nat := 341467145589787995025033

theorem tailTrace_2992522 : CollatzResearch.WordTrace tailWord_2992522 prefixEnd_2992522 341467145589787995025033 := by
  unfold tailWord_2992522
  simp only [CollatzResearch.WordTrace]
  refine ⟨27286561016152837728346955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72764162709740900608925213 27286561016152837728346955)
  ·
    refine ⟨40929841524229256592520433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27286561016152837728346955 40929841524229256592520433)
    ·
      refine ⟨30697381143171942444390325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40929841524229256592520433 30697381143171942444390325)
      ·
        refine ⟨2877879482172369604161593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30697381143171942444390325 2877879482172369604161593)
        ·
          refine ⟨2158409611629277203121195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2877879482172369604161593 2158409611629277203121195)
          ·
            refine ⟨3237614417443915804681793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158409611629277203121195 3237614417443915804681793)
            ·
              refine ⟨2428210813082936853511345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3237614417443915804681793 2428210813082936853511345)
              ·
                refine ⟨1821158109812202640133509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2428210813082936853511345 1821158109812202640133509)
                ·
                  refine ⟨341467145589787995025033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1821158109812202640133509 341467145589787995025033)
                  ·
                    rfl

theorem cell22_2992522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_2992522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992522 prefixEnd_2992522 := by exact prefixLift 2992522
  have htrace : WordTrace (prefixWord ++ tailWord_2992522) baseStart_2992522 baseEnd_2992522 := by
    simpa [prefixWord, tailWord_2992522, baseEnd_2992522] using wordTrace_append hprefix tailTrace_2992522
  have hstable : (prefixWord ++ tailWord_2992522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992522).length < 2 ^ (prefixWord ++ tailWord_2992522).sum := by decide
  have hdescent : baseEnd_2992522 < baseStart_2992522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992544 : List Nat := [2, 1, 1, 4, 1, 3, 2, 3, 5]
def baseStart_2992544 : Nat := 118140960795 + 2992544 * 2 ^ 59
def prefixEnd_2992544 : Nat := 4983230072969 + 3 ^ 40 * 2992544 * 2
def baseEnd_2992544 : Nat := 341469655939654420341677

theorem tailTrace_2992544 : CollatzResearch.WordTrace tailWord_2992544 prefixEnd_2992544 341469655939654420341677 := by
  unfold tailWord_2992544
  simp only [CollatzResearch.WordTrace]
  refine ⟨54573523235265824335344343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72764697647021099113792457 54573523235265824335344343)
  ·
    refine ⟨81860284852898736503016515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54573523235265824335344343 81860284852898736503016515)
    ·
      refine ⟨122790427279348104754524773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81860284852898736503016515 122790427279348104754524773)
      ·
        refine ⟨23023205114877769641473395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122790427279348104754524773 23023205114877769641473395)
        ·
          refine ⟨34534807672316654462210093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23023205114877769641473395 34534807672316654462210093)
          ·
            refine ⟨12950552877118745423328785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34534807672316654462210093 12950552877118745423328785)
            ·
              refine ⟨9712914657839059067496589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12950552877118745423328785 9712914657839059067496589)
              ·
                refine ⟨3642342996689647150311221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9712914657839059067496589 3642342996689647150311221)
                ·
                  refine ⟨341469655939654420341677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3642342996689647150311221 341469655939654420341677)
                  ·
                    rfl

theorem cell22_2992544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 5].length) (baseStart_2992544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992544 prefixEnd_2992544 := by exact prefixLift 2992544
  have htrace : WordTrace (prefixWord ++ tailWord_2992544) baseStart_2992544 baseEnd_2992544 := by
    simpa [prefixWord, tailWord_2992544, baseEnd_2992544] using wordTrace_append hprefix tailTrace_2992544
  have hstable : (prefixWord ++ tailWord_2992544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992544).length < 2 ^ (prefixWord ++ tailWord_2992544).sum := by decide
  have hdescent : baseEnd_2992544 < baseStart_2992544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992565 : List Nat := [1, 3, 3, 2, 3, 1, 2, 3, 1, 3]
def baseStart_2992565 : Nat := 118140960795 + 2992565 * 2 ^ 59
def prefixEnd_2992565 : Nat := 4983230072969 + 3 ^ 40 * 2992565 * 2
def baseEnd_2992565 : Nat := 1024416156548126206249967

theorem tailTrace_2992565 : CollatzResearch.WordTrace tailWord_2992565 prefixEnd_2992565 1024416156548126206249967 := by
  unfold tailWord_2992565
  simp only [CollatzResearch.WordTrace]
  refine ⟨109147812403455569257203149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72765208268970379504802099 109147812403455569257203149)
  ·
    refine ⟨40930429651295838471451181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109147812403455569257203149 40930429651295838471451181)
    ·
      refine ⟨15348911119235939426794193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40930429651295838471451181 15348911119235939426794193)
      ·
        refine ⟨11511683339426954570095645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15348911119235939426794193 11511683339426954570095645)
        ·
          refine ⟨4316881252285107963785867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11511683339426954570095645 4316881252285107963785867)
          ·
            refine ⟨6475321878427661945678801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4316881252285107963785867 6475321878427661945678801)
            ·
              refine ⟨4856491408820746459259101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6475321878427661945678801 4856491408820746459259101)
              ·
                refine ⟨1821184278307779922222163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4856491408820746459259101 1821184278307779922222163)
                ·
                  refine ⟨2731776417461669883333245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1821184278307779922222163 2731776417461669883333245)
                  ·
                    refine ⟨1024416156548126206249967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2731776417461669883333245 1024416156548126206249967)
                    ·
                      rfl

theorem cell22_2992565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_2992565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992565 prefixEnd_2992565 := by exact prefixLift 2992565
  have htrace : WordTrace (prefixWord ++ tailWord_2992565) baseStart_2992565 baseEnd_2992565 := by
    simpa [prefixWord, tailWord_2992565, baseEnd_2992565] using wordTrace_append hprefix tailTrace_2992565
  have hstable : (prefixWord ++ tailWord_2992565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992565).length < 2 ^ (prefixWord ++ tailWord_2992565).sum := by decide
  have hdescent : baseEnd_2992565 < baseStart_2992565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992619 : List Nat := [1, 1, 1, 1, 2, 3, 4, 3, 2, 4]
def baseStart_2992619 : Nat := 118140960795 + 2992619 * 2 ^ 59
def prefixEnd_2992619 : Nat := 4983230072969 + 3 ^ 40 * 2992619 * 2
def baseEnd_2992619 : Nat := 1024434641851688065399801

theorem tailTrace_2992619 : CollatzResearch.WordTrace tailWord_2992619 prefixEnd_2992619 1024434641851688065399801 := by
  unfold tailWord_2992619
  simp only [CollatzResearch.WordTrace]
  refine ⟨109149781945259936479668911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72766521296839957653112607 109149781945259936479668911)
  ·
    refine ⟨163724672917889904719503367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109149781945259936479668911 163724672917889904719503367)
    ·
      refine ⟨245587009376834857079255051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163724672917889904719503367 245587009376834857079255051)
      ·
        refine ⟨368380514065252285618882577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245587009376834857079255051 368380514065252285618882577)
        ·
          refine ⟨276285385548939214214161933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368380514065252285618882577 276285385548939214214161933)
          ·
            refine ⟨103607019580852205330310725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276285385548939214214161933 103607019580852205330310725)
            ·
              refine ⟨19426316171409788499433261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103607019580852205330310725 19426316171409788499433261)
              ·
                refine ⟨7284868564278670687287473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19426316171409788499433261 7284868564278670687287473)
                ·
                  refine ⟨5463651423209003015465605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7284868564278670687287473 5463651423209003015465605)
                  ·
                    refine ⟨1024434641851688065399801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5463651423209003015465605 1024434641851688065399801)
                    ·
                      rfl

theorem cell22_2992619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 4].length) (baseStart_2992619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992619 prefixEnd_2992619 := by exact prefixLift 2992619
  have htrace : WordTrace (prefixWord ++ tailWord_2992619) baseStart_2992619 baseEnd_2992619 := by
    simpa [prefixWord, tailWord_2992619, baseEnd_2992619] using wordTrace_append hprefix tailTrace_2992619
  have hstable : (prefixWord ++ tailWord_2992619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992619).length < 2 ^ (prefixWord ++ tailWord_2992619).sum := by decide
  have hdescent : baseEnd_2992619 < baseStart_2992619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992666 : List Nat := [3, 1, 1, 3, 1, 1, 2, 4, 3, 3]
def baseStart_2992666 : Nat := 118140960795 + 2992666 * 2 ^ 59
def prefixEnd_2992666 : Nat := 4983230072969 + 3 ^ 40 * 2992666 * 2
def baseEnd_2992666 : Nat := 1024450730912195609474657

theorem tailTrace_2992666 : CollatzResearch.WordTrace tailWord_2992666 prefixEnd_2992666 1024450730912195609474657 := by
  unfold tailWord_2992666
  simp only [CollatzResearch.WordTrace]
  refine ⟨27287874044022415876657463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72767664117393109004419901 27287874044022415876657463)
  ·
    refine ⟨40931811066033623814986195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27287874044022415876657463 40931811066033623814986195)
    ·
      refine ⟨61397716599050435722479293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40931811066033623814986195 61397716599050435722479293)
      ·
        refine ⟨23024143724643913395929735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61397716599050435722479293 23024143724643913395929735)
        ·
          refine ⟨34536215586965870093894603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23024143724643913395929735 34536215586965870093894603)
          ·
            refine ⟨51804323380448805140841905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34536215586965870093894603 51804323380448805140841905)
            ·
              refine ⟨38853242535336603855631429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51804323380448805140841905 38853242535336603855631429)
              ·
                refine ⟨7284982975375613222930893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38853242535336603855631429 7284982975375613222930893)
                ·
                  refine ⟨2731868615765854958599085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7284982975375613222930893 2731868615765854958599085)
                  ·
                    refine ⟨1024450730912195609474657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2731868615765854958599085 1024450730912195609474657)
                    ·
                      rfl

theorem cell22_2992666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_2992666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992666 prefixEnd_2992666 := by exact prefixLift 2992666
  have htrace : WordTrace (prefixWord ++ tailWord_2992666) baseStart_2992666 baseEnd_2992666 := by
    simpa [prefixWord, tailWord_2992666, baseEnd_2992666] using wordTrace_append hprefix tailTrace_2992666
  have hstable : (prefixWord ++ tailWord_2992666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992666).length < 2 ^ (prefixWord ++ tailWord_2992666).sum := by decide
  have hdescent : baseEnd_2992666 < baseStart_2992666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992685 : List Nat := [1, 5, 4, 1, 2, 9]
def baseStart_2992685 : Nat := 118140960795 + 2992685 * 2 ^ 59
def prefixEnd_2992685 : Nat := 4983230072969 + 3 ^ 40 * 2992685 * 2
def baseEnd_2992685 : Nat := 12647620185191183867279

theorem tailTrace_2992685 : CollatzResearch.WordTrace tailWord_2992685 prefixEnd_2992685 12647620185191183867279 := by
  unfold tailWord_2992685
  simp only [CollatzResearch.WordTrace]
  refine ⟨109152189163020829751571509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72768126108680553167714339 109152189163020829751571509)
  ·
    refine ⟨10233017734033202789209829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109152189163020829751571509 10233017734033202789209829)
    ·
      refine ⟨1918690825131225522976843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10233017734033202789209829 1918690825131225522976843)
      ·
        refine ⟨2878036237696838284465265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1918690825131225522976843 2878036237696838284465265)
        ·
          refine ⟨2158527178272628713348949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2878036237696838284465265 2158527178272628713348949)
          ·
            refine ⟨12647620185191183867279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2158527178272628713348949 12647620185191183867279)
            ·
              rfl

theorem cell22_2992685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 9].length) (baseStart_2992685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992685 prefixEnd_2992685 := by exact prefixLift 2992685
  have htrace : WordTrace (prefixWord ++ tailWord_2992685) baseStart_2992685 baseEnd_2992685 := by
    simpa [prefixWord, tailWord_2992685, baseEnd_2992685] using wordTrace_append hprefix tailTrace_2992685
  have hstable : (prefixWord ++ tailWord_2992685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992685).length < 2 ^ (prefixWord ++ tailWord_2992685).sum := by decide
  have hdescent : baseEnd_2992685 < baseStart_2992685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992696 : List Nat := [2, 1, 2, 1, 4, 1, 4, 2, 5]
def baseStart_2992696 : Nat := 118140960795 + 2992696 * 2 ^ 59
def prefixEnd_2992696 : Nat := 4983230072969 + 3 ^ 40 * 2992696 * 2
def baseEnd_2992696 : Nat := 341487000175095177074855

theorem tailTrace_2992696 : CollatzResearch.WordTrace tailWord_2992696 prefixEnd_2992696 341487000175095177074855 := by
  unfold tailWord_2992696
  simp only [CollatzResearch.WordTrace]
  refine ⟨54576295182990489315110971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72768393577320652420147961 54576295182990489315110971)
  ·
    refine ⟨81864442774485733972666457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54576295182990489315110971 81864442774485733972666457)
    ·
      refine ⟨61398332080864300479499843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81864442774485733972666457 61398332080864300479499843)
      ·
        refine ⟨92097498121296450719249765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61398332080864300479499843 92097498121296450719249765)
        ·
          refine ⟨17268280897743084509859331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92097498121296450719249765 17268280897743084509859331)
          ·
            refine ⟨25902421346614626764788997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17268280897743084509859331 25902421346614626764788997)
            ·
              refine ⟨4856704002490242518397937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25902421346614626764788997 4856704002490242518397937)
              ·
                refine ⟨3642528001867681888798453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4856704002490242518397937 3642528001867681888798453)
                ·
                  refine ⟨341487000175095177074855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3642528001867681888798453 341487000175095177074855)
                  ·
                    rfl

theorem cell22_2992696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 5].length) (baseStart_2992696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992696 prefixEnd_2992696 := by exact prefixLift 2992696
  have htrace : WordTrace (prefixWord ++ tailWord_2992696) baseStart_2992696 baseEnd_2992696 := by
    simpa [prefixWord, tailWord_2992696, baseEnd_2992696] using wordTrace_append hprefix tailTrace_2992696
  have hstable : (prefixWord ++ tailWord_2992696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992696).length < 2 ^ (prefixWord ++ tailWord_2992696).sum := by decide
  have hdescent : baseEnd_2992696 < baseStart_2992696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992700 : List Nat := [2, 2, 2, 2, 3, 2, 1, 4, 1, 3]
def baseStart_2992700 : Nat := 118140960795 + 2992700 * 2 ^ 59
def prefixEnd_2992700 : Nat := 4983230072969 + 3 ^ 40 * 2992700 * 2
def baseEnd_2992700 : Nat := 1024462369807030854124553

theorem tailTrace_2992700 : CollatzResearch.WordTrace tailWord_2992700 prefixEnd_2992700 1024462369807030854124553 := by
  unfold tailWord_2992700
  simp only [CollatzResearch.WordTrace]
  refine ⟨54576368128983243656683777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72768490838644324875578369 54576368128983243656683777)
  ·
    refine ⟨40932276096737432742512833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54576368128983243656683777 40932276096737432742512833)
    ·
      refine ⟨30699207072553074556884625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40932276096737432742512833 30699207072553074556884625)
      ·
        refine ⟨23024405304414805917663469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30699207072553074556884625 23024405304414805917663469)
        ·
          refine ⟨8634151989155552219123801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23024405304414805917663469 8634151989155552219123801)
          ·
            refine ⟨6475613991866664164342851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8634151989155552219123801 6475613991866664164342851)
            ·
              refine ⟨9713420987799996246514277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6475613991866664164342851 9713420987799996246514277)
              ·
                refine ⟨1821266435212499296221427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9713420987799996246514277 1821266435212499296221427)
                ·
                  refine ⟨2731899652818748944332141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1821266435212499296221427 2731899652818748944332141)
                  ·
                    refine ⟨1024462369807030854124553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2731899652818748944332141 1024462369807030854124553)
                    ·
                      rfl

theorem cell22_2992700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_2992700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992700 prefixEnd_2992700 := by exact prefixLift 2992700
  have htrace : WordTrace (prefixWord ++ tailWord_2992700) baseStart_2992700 baseEnd_2992700 := by
    simpa [prefixWord, tailWord_2992700, baseEnd_2992700] using wordTrace_append hprefix tailTrace_2992700
  have hstable : (prefixWord ++ tailWord_2992700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992700).length < 2 ^ (prefixWord ++ tailWord_2992700).sum := by decide
  have hdescent : baseEnd_2992700 < baseStart_2992700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992711 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 2, 5]
def baseStart_2992711 : Nat := 118140960795 + 2992711 * 2 ^ 59
def prefixEnd_2992711 : Nat := 4983230072969 + 3 ^ 40 * 2992711 * 2
def baseEnd_2992711 : Nat := 1024466135331830492099519

theorem tailTrace_2992711 : CollatzResearch.WordTrace tailWord_2992711 prefixEnd_2992711 1024466135331830492099519 := by
  unfold tailWord_2992711
  simp only [CollatzResearch.WordTrace]
  refine ⟨109153137460926636192017987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72768758307284424128011991 109153137460926636192017987)
  ·
    refine ⟨163729706191389954288026981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109153137460926636192017987 163729706191389954288026981)
    ·
      refine ⟨30699319910885616429005059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163729706191389954288026981 30699319910885616429005059)
      ·
        refine ⟨46048979866328424643507589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30699319910885616429005059 46048979866328424643507589)
        ·
          refine ⟨8634183724936579620657673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46048979866328424643507589 8634183724936579620657673)
          ·
            refine ⟨6475637793702434715493255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8634183724936579620657673 6475637793702434715493255)
            ·
              refine ⟨9713456690553652073239883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6475637793702434715493255 9713456690553652073239883)
              ·
                refine ⟨14570185035830478109859825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9713456690553652073239883 14570185035830478109859825)
                ·
                  refine ⟨10927638776872858582394869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14570185035830478109859825 10927638776872858582394869)
                  ·
                    refine ⟨1024466135331830492099519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10927638776872858582394869 1024466135331830492099519)
                    ·
                      rfl

theorem cell22_2992711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_2992711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992711 prefixEnd_2992711 := by exact prefixLift 2992711
  have htrace : WordTrace (prefixWord ++ tailWord_2992711) baseStart_2992711 baseEnd_2992711 := by
    simpa [prefixWord, tailWord_2992711, baseEnd_2992711] using wordTrace_append hprefix tailTrace_2992711
  have hstable : (prefixWord ++ tailWord_2992711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992711).length < 2 ^ (prefixWord ++ tailWord_2992711).sum := by decide
  have hdescent : baseEnd_2992711 < baseStart_2992711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992773 : List Nat := [1, 3, 1, 1, 4, 4, 1, 1, 1, 5]
def baseStart_2992773 : Nat := 118140960795 + 2992773 * 2 ^ 59
def prefixEnd_2992773 : Nat := 4983230072969 + 3 ^ 40 * 2992773 * 2
def baseEnd_2992773 : Nat := 1024487359198882997049329

theorem tailTrace_2992773 : CollatzResearch.WordTrace tailWord_2992773 prefixEnd_2992773 1024487359198882997049329 := by
  unfold tailWord_2992773
  simp only [CollatzResearch.WordTrace]
  refine ⟨109155398786702020780774973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72770265857801347187183315 109155398786702020780774973)
  ·
    refine ⟨40933274545013257792790615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109155398786702020780774973 40933274545013257792790615)
    ·
      refine ⟨61399911817519886689185923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40933274545013257792790615 61399911817519886689185923)
      ·
        refine ⟨92099867726279830033778885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61399911817519886689185923 92099867726279830033778885)
        ·
          refine ⟨17268725198677468131333541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92099867726279830033778885 17268725198677468131333541)
          ·
            refine ⟨3237885974752025274625039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17268725198677468131333541 3237885974752025274625039)
            ·
              refine ⟨4856828962128037911937559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3237885974752025274625039 4856828962128037911937559)
              ·
                refine ⟨7285243443192056867906339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4856828962128037911937559 7285243443192056867906339)
                ·
                  refine ⟨10927865164788085301859509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7285243443192056867906339 10927865164788085301859509)
                  ·
                    refine ⟨1024487359198882997049329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10927865164788085301859509 1024487359198882997049329)
                    ·
                      rfl

theorem cell22_2992773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_2992773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992773 prefixEnd_2992773 := by exact prefixLift 2992773
  have htrace : WordTrace (prefixWord ++ tailWord_2992773) baseStart_2992773 baseEnd_2992773 := by
    simpa [prefixWord, tailWord_2992773, baseEnd_2992773] using wordTrace_append hprefix tailTrace_2992773
  have hstable : (prefixWord ++ tailWord_2992773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992773).length < 2 ^ (prefixWord ++ tailWord_2992773).sum := by decide
  have hdescent : baseEnd_2992773 < baseStart_2992773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992788 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_2992788 : Nat := 118140960795 + 2992788 * 2 ^ 59
def prefixEnd_2992788 : Nat := 4983230072969 + 3 ^ 40 * 2992788 * 2
def baseEnd_2992788 : Nat := 1024492494005427957924283

theorem tailTrace_2992788 : CollatzResearch.WordTrace tailWord_2992788 prefixEnd_2992788 1024492494005427957924283 := by
  unfold tailWord_2992788
  simp only [CollatzResearch.WordTrace]
  refine ⟨54577972940823839171285509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72770630587765118895047345 54577972940823839171285509)
  ·
    refine ⟨10233369926404469844616033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54577972940823839171285509 10233369926404469844616033)
    ·
      refine ⟨7675027444803352383462025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10233369926404469844616033 7675027444803352383462025)
      ·
        refine ⟨5756270583602514287596519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7675027444803352383462025 5756270583602514287596519)
        ·
          refine ⟨8634405875403771431394779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5756270583602514287596519 8634405875403771431394779)
          ·
            refine ⟨12951608813105657147092169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8634405875403771431394779 12951608813105657147092169)
            ·
              refine ⟨9713706609829242860319127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12951608813105657147092169 9713706609829242860319127)
              ·
                refine ⟨14570559914743864290478691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9713706609829242860319127 14570559914743864290478691)
                ·
                  refine ⟨21855839872115796435718037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14570559914743864290478691 21855839872115796435718037)
                  ·
                    refine ⟨1024492494005427957924283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21855839872115796435718037 1024492494005427957924283)
                    ·
                      rfl

theorem cell22_2992788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_2992788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992788 prefixEnd_2992788 := by exact prefixLift 2992788
  have htrace : WordTrace (prefixWord ++ tailWord_2992788) baseStart_2992788 baseEnd_2992788 := by
    simpa [prefixWord, tailWord_2992788, baseEnd_2992788] using wordTrace_append hprefix tailTrace_2992788
  have hstable : (prefixWord ++ tailWord_2992788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992788).length < 2 ^ (prefixWord ++ tailWord_2992788).sum := by decide
  have hdescent : baseEnd_2992788 < baseStart_2992788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992869 : List Nat := [1, 3, 1, 4, 1, 4, 2, 2, 1, 3]
def baseStart_2992869 : Nat := 118140960795 + 2992869 * 2 ^ 59
def prefixEnd_2992869 : Nat := 4983230072969 + 3 ^ 40 * 2992869 * 2
def baseEnd_2992869 : Nat := 1024520221960770746649035

theorem tailTrace_2992869 : CollatzResearch.WordTrace tailWord_2992869 prefixEnd_2992869 1024520221960770746649035 := by
  unfold tailWord_2992869
  simp only [CollatzResearch.WordTrace]
  refine ⟨109158900194354229176269661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72772600129569486117513107 109158900194354229176269661)
  ·
    refine ⟨40934587572882835941101123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109158900194354229176269661 40934587572882835941101123)
    ·
      refine ⟨61401881359324253911651685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40934587572882835941101123 61401881359324253911651685)
      ·
        refine ⟨11512852754873297608434691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61401881359324253911651685 11512852754873297608434691)
        ·
          refine ⟨17269279132309946412652037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11512852754873297608434691 17269279132309946412652037)
          ·
            refine ⟨3237989837308114952372257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17269279132309946412652037 3237989837308114952372257)
            ·
              refine ⟨2428492377981086214279193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3237989837308114952372257 2428492377981086214279193)
              ·
                refine ⟨1821369283485814660709395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2428492377981086214279193 1821369283485814660709395)
                ·
                  refine ⟨2732053925228721991064093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1821369283485814660709395 2732053925228721991064093)
                  ·
                    refine ⟨1024520221960770746649035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2732053925228721991064093 1024520221960770746649035)
                    ·
                      rfl

theorem cell22_2992869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 1, 3].length) (baseStart_2992869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992869 prefixEnd_2992869 := by exact prefixLift 2992869
  have htrace : WordTrace (prefixWord ++ tailWord_2992869) baseStart_2992869 baseEnd_2992869 := by
    simpa [prefixWord, tailWord_2992869, baseEnd_2992869] using wordTrace_append hprefix tailTrace_2992869
  have hstable : (prefixWord ++ tailWord_2992869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992869).length < 2 ^ (prefixWord ++ tailWord_2992869).sum := by decide
  have hdescent : baseEnd_2992869 < baseStart_2992869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992876 : List Nat := [2, 2, 1, 1, 2, 2, 1, 5, 6]
def baseStart_2992876 : Nat := 118140960795 + 2992876 * 2 ^ 59
def prefixEnd_2992876 : Nat := 4983230072969 + 3 ^ 40 * 2992876 * 2
def baseEnd_2992876 : Nat := 341507539401275020574671

theorem tailTrace_2992876 : CollatzResearch.WordTrace tailWord_2992876 prefixEnd_2992876 341507539401275020574671 := by
  unfold tailWord_2992876
  simp only [CollatzResearch.WordTrace]
  refine ⟨54579577752664434685887241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72772770336885912914516321 54579577752664434685887241)
  ·
    refine ⟨40934683314498326014415431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54579577752664434685887241 40934683314498326014415431)
    ·
      refine ⟨61402024971747489021623147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40934683314498326014415431 61402024971747489021623147)
      ·
        refine ⟨92103037457621233532434721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61402024971747489021623147 92103037457621233532434721)
        ·
          refine ⟨69077278093215925149326041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92103037457621233532434721 69077278093215925149326041)
          ·
            refine ⟨51807958569911943861994531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69077278093215925149326041 51807958569911943861994531)
            ·
              refine ⟨77711937854867915792991797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51807958569911943861994531 77711937854867915792991797)
              ·
                refine ⟨7285494173893867105592981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77711937854867915792991797 7285494173893867105592981)
                ·
                  refine ⟨341507539401275020574671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7285494173893867105592981 341507539401275020574671)
                  ·
                    rfl

theorem cell22_2992876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_2992876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992876 prefixEnd_2992876 := by exact prefixLift 2992876
  have htrace : WordTrace (prefixWord ++ tailWord_2992876) baseStart_2992876 baseEnd_2992876 := by
    simpa [prefixWord, tailWord_2992876, baseEnd_2992876] using wordTrace_append hprefix tailTrace_2992876
  have hstable : (prefixWord ++ tailWord_2992876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992876).length < 2 ^ (prefixWord ++ tailWord_2992876).sum := by decide
  have hdescent : baseEnd_2992876 < baseStart_2992876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992878 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_2992878 : Nat := 118140960795 + 2992878 * 2 ^ 59
def prefixEnd_2992878 : Nat := 4983230072969 + 3 ^ 40 * 2992878 * 2
def baseEnd_2992878 : Nat := 1024523302844697723174007

theorem tailTrace_2992878 : CollatzResearch.WordTrace tailWord_2992878 prefixEnd_2992878 1024523302844697723174007 := by
  unfold tailWord_2992878
  simp only [CollatzResearch.WordTrace]
  refine ⟨13644903556415202964168411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72772818967547749142231525 13644903556415202964168411)
  ·
    refine ⟨20467355334622804446252617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13644903556415202964168411 20467355334622804446252617)
    ·
      refine ⟨15350516500967103334689463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20467355334622804446252617 15350516500967103334689463)
      ·
        refine ⟨23025774751450655002034195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15350516500967103334689463 23025774751450655002034195)
        ·
          refine ⟨34538662127175982503051293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23025774751450655002034195 34538662127175982503051293)
          ·
            refine ⟨12951998297690993438644235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34538662127175982503051293 12951998297690993438644235)
            ·
              refine ⟨19427997446536490157966353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12951998297690993438644235 19427997446536490157966353)
              ·
                refine ⟨14570998084902367618474765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19427997446536490157966353 14570998084902367618474765)
                ·
                  refine ⟨5464124281838387856928037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14570998084902367618474765 5464124281838387856928037)
                  ·
                    refine ⟨1024523302844697723174007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5464124281838387856928037 1024523302844697723174007)
                    ·
                      rfl

theorem cell22_2992878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_2992878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992878 prefixEnd_2992878 := by exact prefixLift 2992878
  have htrace : WordTrace (prefixWord ++ tailWord_2992878) baseStart_2992878 baseEnd_2992878 := by
    simpa [prefixWord, tailWord_2992878, baseEnd_2992878] using wordTrace_append hprefix tailTrace_2992878
  have hstable : (prefixWord ++ tailWord_2992878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992878).length < 2 ^ (prefixWord ++ tailWord_2992878).sum := by decide
  have hdescent : baseEnd_2992878 < baseStart_2992878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992908 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 4, 3]
def baseStart_2992908 : Nat := 118140960795 + 2992908 * 2 ^ 59
def prefixEnd_2992908 : Nat := 4983230072969 + 3 ^ 40 * 2992908 * 2
def baseEnd_2992908 : Nat := 1024533572457787644923915

theorem tailTrace_2992908 : CollatzResearch.WordTrace tailWord_2992908 prefixEnd_2992908 1024533572457787644923915 := by
  unfold tailWord_2992908
  simp only [CollatzResearch.WordTrace]
  refine ⟨54580161320606469418469689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72773548427475292557959585 54580161320606469418469689)
  ·
    refine ⟨40935120990454852063852267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54580161320606469418469689 40935120990454852063852267)
    ·
      refine ⟨61402681485682278095778401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40935120990454852063852267 61402681485682278095778401)
      ·
        refine ⟨46052011114261708571833801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61402681485682278095778401 46052011114261708571833801)
        ·
          refine ⟨34539008335696281428875351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46052011114261708571833801 34539008335696281428875351)
          ·
            refine ⟨51808512503544422143313027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34539008335696281428875351 51808512503544422143313027)
            ·
              refine ⟨77712768755316633214969541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51808512503544422143313027 77712768755316633214969541)
              ·
                refine ⟨14571144141621868727806789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77712768755316633214969541 14571144141621868727806789)
                ·
                  refine ⟨2732089526554100386463773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14571144141621868727806789 2732089526554100386463773)
                  ·
                    refine ⟨1024533572457787644923915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2732089526554100386463773 1024533572457787644923915)
                    ·
                      rfl

theorem cell22_2992908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_2992908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992908 prefixEnd_2992908 := by exact prefixLift 2992908
  have htrace : WordTrace (prefixWord ++ tailWord_2992908) baseStart_2992908 baseEnd_2992908 := by
    simpa [prefixWord, tailWord_2992908, baseEnd_2992908] using wordTrace_append hprefix tailTrace_2992908
  have hstable : (prefixWord ++ tailWord_2992908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992908).length < 2 ^ (prefixWord ++ tailWord_2992908).sum := by decide
  have hdescent : baseEnd_2992908 < baseStart_2992908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992942 : List Nat := [4, 1, 3, 2, 1, 3, 1, 1, 1, 5]
def baseStart_2992942 : Nat := 118140960795 + 2992942 * 2 ^ 59
def prefixEnd_2992942 : Nat := 4983230072969 + 3 ^ 40 * 2992942 * 2
def baseEnd_2992942 : Nat := 1024545211352622889573811

theorem tailTrace_2992942 : CollatzResearch.WordTrace tailWord_2992942 prefixEnd_2992942 1024545211352622889573811 := by
  unfold tailWord_2992942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13645195340386220330459635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72774375148726508429118053 13645195340386220330459635)
  ·
    refine ⟨20467793010579330495689453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13645195340386220330459635 20467793010579330495689453)
    ·
      refine ⟨7675422378967248935883545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20467793010579330495689453 7675422378967248935883545)
      ·
        refine ⟨5756566784225436701912659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7675422378967248935883545 5756566784225436701912659)
        ·
          refine ⟨8634850176338155052868989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5756566784225436701912659 8634850176338155052868989)
          ·
            refine ⟨3238068816126808144825871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8634850176338155052868989 3238068816126808144825871)
            ·
              refine ⟨4857103224190212217238807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3238068816126808144825871 4857103224190212217238807)
              ·
                refine ⟨7285654836285318325858211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4857103224190212217238807 7285654836285318325858211)
                ·
                  refine ⟨10928482254427977488787317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7285654836285318325858211 10928482254427977488787317)
                  ·
                    refine ⟨1024545211352622889573811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10928482254427977488787317 1024545211352622889573811)
                    ·
                      rfl

theorem cell22_2992942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_2992942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992942 prefixEnd_2992942 := by exact prefixLift 2992942
  have htrace : WordTrace (prefixWord ++ tailWord_2992942) baseStart_2992942 baseEnd_2992942 := by
    simpa [prefixWord, tailWord_2992942, baseEnd_2992942] using wordTrace_append hprefix tailTrace_2992942
  have hstable : (prefixWord ++ tailWord_2992942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992942).length < 2 ^ (prefixWord ++ tailWord_2992942).sum := by decide
  have hdescent : baseEnd_2992942 < baseStart_2992942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992961 : List Nat := [1, 2, 5, 3, 2, 1, 1, 3, 4]
def baseStart_2992961 : Nat := 118140960795 + 2992961 * 2 ^ 59
def prefixEnd_2992961 : Nat := 4983230072969 + 3 ^ 40 * 2992961 * 2
def baseEnd_2992961 : Nat := 341517238480304391116251

theorem tailTrace_2992961 : CollatzResearch.WordTrace tailWord_2992961 prefixEnd_2992961 341517238480304391116251 := by
  unfold tailWord_2992961
  simp only [CollatzResearch.WordTrace]
  refine ⟨109162255710020928888618737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72774837140013952592412491 109162255710020928888618737)
  ·
    refine ⟨81871691782515696666464053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109162255710020928888618737 81871691782515696666464053)
    ·
      refine ⟨7675471104610846562481005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81871691782515696666464053 7675471104610846562481005)
      ·
        refine ⟨2878301664229067460930377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7675471104610846562481005 2878301664229067460930377)
        ·
          refine ⟨2158726248171800595697783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2878301664229067460930377 2158726248171800595697783)
          ·
            refine ⟨3238089372257700893546675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158726248171800595697783 3238089372257700893546675)
            ·
              refine ⟨4857134058386551340320013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3238089372257700893546675 4857134058386551340320013)
              ·
                refine ⟨1821425271894956752620005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4857134058386551340320013 1821425271894956752620005)
                ·
                  refine ⟨341517238480304391116251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1821425271894956752620005 341517238480304391116251)
                  ·
                    rfl

theorem cell22_2992961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 4].length) (baseStart_2992961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992961 prefixEnd_2992961 := by exact prefixLift 2992961
  have htrace : WordTrace (prefixWord ++ tailWord_2992961) baseStart_2992961 baseEnd_2992961 := by
    simpa [prefixWord, tailWord_2992961, baseEnd_2992961] using wordTrace_append hprefix tailTrace_2992961
  have hstable : (prefixWord ++ tailWord_2992961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992961).length < 2 ^ (prefixWord ++ tailWord_2992961).sum := by decide
  have hdescent : baseEnd_2992961 < baseStart_2992961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2992983 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 7]
def baseStart_2992983 : Nat := 118140960795 + 2992983 * 2 ^ 59
def prefixEnd_2992983 : Nat := 4983230072969 + 3 ^ 40 * 2992983 * 2
def baseEnd_2992983 : Nat := 341519748830170816432895

theorem tailTrace_2992983 : CollatzResearch.WordTrace tailWord_2992983 prefixEnd_2992983 341519748830170816432895 := by
  unfold tailWord_2992983
  simp only [CollatzResearch.WordTrace]
  refine ⟨109163058115941226645919603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72775372077294151097279735 109163058115941226645919603)
  ·
    refine ⟨163744587173911839968879405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109163058115941226645919603 163744587173911839968879405)
    ·
      refine ⟨61404220190216939988329777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163744587173911839968879405 61404220190216939988329777)
      ·
        refine ⟨46053165142662704991247333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61404220190216939988329777 46053165142662704991247333)
        ·
          refine ⟨8634968464249257185858875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46053165142662704991247333 8634968464249257185858875)
          ·
            refine ⟨12952452696373885778788313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8634968464249257185858875 12952452696373885778788313)
            ·
              refine ⟨9714339522280414334091235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12952452696373885778788313 9714339522280414334091235)
              ·
                refine ⟨14571509283420621501136853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9714339522280414334091235 14571509283420621501136853)
                ·
                  refine ⟨341519748830170816432895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14571509283420621501136853 341519748830170816432895)
                  ·
                    rfl

theorem cell22_2992983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 7].length) (baseStart_2992983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2992983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2992983 prefixEnd_2992983 := by exact prefixLift 2992983
  have htrace : WordTrace (prefixWord ++ tailWord_2992983) baseStart_2992983 baseEnd_2992983 := by
    simpa [prefixWord, tailWord_2992983, baseEnd_2992983] using wordTrace_append hprefix tailTrace_2992983
  have hstable : (prefixWord ++ tailWord_2992983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2992983).length < 2 ^ (prefixWord ++ tailWord_2992983).sum := by decide
  have hdescent : baseEnd_2992983 < baseStart_2992983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2992983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993000 : List Nat := [2, 1, 4, 2, 1, 3, 1, 3, 5]
def baseStart_2993000 : Nat := 118140960795 + 2993000 * 2 ^ 59
def prefixEnd_2993000 : Nat := 4983230072969 + 3 ^ 40 * 2993000 * 2
def baseEnd_2993000 : Nat := 341521688645976690541211

theorem tailTrace_2993000 : CollatzResearch.WordTrace tailWord_2993000 prefixEnd_2993000 341521688645976690541211 := by
  unfold tailWord_2993000
  simp only [CollatzResearch.WordTrace]
  refine ⟨54581839078439819274644227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72775785437919759032858969 54581839078439819274644227)
  ·
    refine ⟨81872758617659728911966341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54581839078439819274644227 81872758617659728911966341)
    ·
      refine ⟨15351142240811199170993689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81872758617659728911966341 15351142240811199170993689)
      ·
        refine ⟨11513356680608399378245267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15351142240811199170993689 11513356680608399378245267)
        ·
          refine ⟨17270035020912599067367901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11513356680608399378245267 17270035020912599067367901)
          ·
            refine ⟨6476263132842224650262963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17270035020912599067367901 6476263132842224650262963)
            ·
              refine ⟨9714394699263336975394445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6476263132842224650262963 9714394699263336975394445)
              ·
                refine ⟨3642898012223751365772917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9714394699263336975394445 3642898012223751365772917)
                ·
                  refine ⟨341521688645976690541211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3642898012223751365772917 341521688645976690541211)
                  ·
                    rfl

theorem cell22_2993000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 5].length) (baseStart_2993000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993000 prefixEnd_2993000 := by exact prefixLift 2993000
  have htrace : WordTrace (prefixWord ++ tailWord_2993000) baseStart_2993000 baseEnd_2993000 := by
    simpa [prefixWord, tailWord_2993000, baseEnd_2993000] using wordTrace_append hprefix tailTrace_2993000
  have hstable : (prefixWord ++ tailWord_2993000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993000).length < 2 ^ (prefixWord ++ tailWord_2993000).sum := by decide
  have hdescent : baseEnd_2993000 < baseStart_2993000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993060 : List Nat := [2, 3, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_2993060 : Nat := 118140960795 + 2993060 * 2 ^ 59
def prefixEnd_2993060 : Nat := 4983230072969 + 3 ^ 40 * 2993060 * 2
def baseEnd_2993060 : Nat := 1024585605164109915123449

theorem tailTrace_2993060 : CollatzResearch.WordTrace tailWord_2993060 prefixEnd_2993060 1024585605164109915123449 := by
  unfold tailWord_2993060
  simp only [CollatzResearch.WordTrace]
  refine ⟨54582933268331134398236317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72777244357774845864315089 54582933268331134398236317)
  ·
    refine ⟨20468599975624175399338619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54582933268331134398236317 20468599975624175399338619)
    ·
      refine ⟨30702899963436263099007929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20468599975624175399338619 30702899963436263099007929)
      ·
        refine ⟨23027174972577197324255947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30702899963436263099007929 23027174972577197324255947)
        ·
          refine ⟨34540762458865795986383921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23027174972577197324255947 34540762458865795986383921)
          ·
            refine ⟨25905571844149346989787941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34540762458865795986383921 25905571844149346989787941)
            ·
              refine ⟨4857294720778002560585239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25905571844149346989787941 4857294720778002560585239)
              ·
                refine ⟨7285942081167003840877859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4857294720778002560585239 7285942081167003840877859)
                ·
                  refine ⟨10928913121750505761316789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7285942081167003840877859 10928913121750505761316789)
                  ·
                    refine ⟨1024585605164109915123449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10928913121750505761316789 1024585605164109915123449)
                    ·
                      rfl

theorem cell22_2993060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_2993060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993060 prefixEnd_2993060 := by exact prefixLift 2993060
  have htrace : WordTrace (prefixWord ++ tailWord_2993060) baseStart_2993060 baseEnd_2993060 := by
    simpa [prefixWord, tailWord_2993060, baseEnd_2993060] using wordTrace_append hprefix tailTrace_2993060
  have hstable : (prefixWord ++ tailWord_2993060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993060).length < 2 ^ (prefixWord ++ tailWord_2993060).sum := by decide
  have hdescent : baseEnd_2993060 < baseStart_2993060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993195 : List Nat := [1, 1, 1, 1, 2, 1, 7, 2, 1, 5]
def baseStart_2993195 : Nat := 118140960795 + 2993195 * 2 ^ 59
def prefixEnd_2993195 : Nat := 4983230072969 + 3 ^ 40 * 2993195 * 2
def baseEnd_2993195 : Nat := 1024631818423014562998035

theorem tailTrace_2993195 : CollatzResearch.WordTrace tailWord_2993195 prefixEnd_2993195 1024631818423014562998035 := by
  unfold tailWord_2993195
  simp only [CollatzResearch.WordTrace]
  refine ⟨109170790391173186852637039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72780526927448791235091359 109170790391173186852637039)
  ·
    refine ⟨163756185586759780278955559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109170790391173186852637039 163756185586759780278955559)
    ·
      refine ⟨245634278380139670418433339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163756185586759780278955559 245634278380139670418433339)
      ·
        refine ⟨368451417570209505627650009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245634278380139670418433339 368451417570209505627650009)
        ·
          refine ⟨276338563177657129220737507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368451417570209505627650009 276338563177657129220737507)
          ·
            refine ⟨414507844766485693831106261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276338563177657129220737507 414507844766485693831106261)
            ·
              refine ⟨9715027611714508449166553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 414507844766485693831106261 9715027611714508449166553)
              ·
                refine ⟨7286270708785881336874915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9715027611714508449166553 7286270708785881336874915)
                ·
                  refine ⟨10929406063178822005312373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7286270708785881336874915 10929406063178822005312373)
                  ·
                    refine ⟨1024631818423014562998035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10929406063178822005312373 1024631818423014562998035)
                    ·
                      rfl

theorem cell22_2993195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 5].length) (baseStart_2993195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993195 prefixEnd_2993195 := by exact prefixLift 2993195
  have htrace : WordTrace (prefixWord ++ tailWord_2993195) baseStart_2993195 baseEnd_2993195 := by
    simpa [prefixWord, tailWord_2993195, baseEnd_2993195] using wordTrace_append hprefix tailTrace_2993195
  have hstable : (prefixWord ++ tailWord_2993195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993195).length < 2 ^ (prefixWord ++ tailWord_2993195).sum := by decide
  have hdescent : baseEnd_2993195 < baseStart_2993195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993229 : List Nat := [1, 6, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_2993229 : Nat := 118140960795 + 2993229 * 2 ^ 59
def prefixEnd_2993229 : Nat := 4983230072969 + 3 ^ 40 * 2993229 * 2
def baseEnd_2993229 : Nat := 1024643457317849807647931

theorem tailTrace_2993229 : CollatzResearch.WordTrace tailWord_2993229 prefixEnd_2993229 1024643457317849807647931 := by
  unfold tailWord_2993229
  simp only [CollatzResearch.WordTrace]
  refine ⟨109172030473050010659374741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72781353648700007106249827 109172030473050010659374741)
  ·
    refine ⟨5117438928424219249658191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109172030473050010659374741 5117438928424219249658191)
    ·
      refine ⟨7676158392636328874487287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5117438928424219249658191 7676158392636328874487287)
      ·
        refine ⟨11514237588954493311730931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7676158392636328874487287 11514237588954493311730931)
        ·
          refine ⟨17271356383431739967596397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11514237588954493311730931 17271356383431739967596397)
          ·
            refine ⟨6476758643786902487848649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17271356383431739967596397 6476758643786902487848649)
            ·
              refine ⟨4857568982840176865886487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6476758643786902487848649 4857568982840176865886487)
              ·
                refine ⟨7286353474260265298829731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4857568982840176865886487 7286353474260265298829731)
                ·
                  refine ⟨10929530211390397948244597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7286353474260265298829731 10929530211390397948244597)
                  ·
                    refine ⟨1024643457317849807647931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10929530211390397948244597 1024643457317849807647931)
                    ·
                      rfl

theorem cell22_2993229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_2993229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993229 prefixEnd_2993229 := by exact prefixLift 2993229
  have htrace : WordTrace (prefixWord ++ tailWord_2993229) baseStart_2993229 baseEnd_2993229 := by
    simpa [prefixWord, tailWord_2993229, baseEnd_2993229] using wordTrace_append hprefix tailTrace_2993229
  have hstable : (prefixWord ++ tailWord_2993229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993229).length < 2 ^ (prefixWord ++ tailWord_2993229).sum := by decide
  have hdescent : baseEnd_2993229 < baseStart_2993229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993246 : List Nat := [4, 4, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_2993246 : Nat := 118140960795 + 2993246 * 2 ^ 59
def prefixEnd_2993246 : Nat := 4983230072969 + 3 ^ 40 * 2993246 * 2
def baseEnd_2993246 : Nat := 1024649276765267429972879

theorem tailTrace_2993246 : CollatzResearch.WordTrace tailWord_2993246 prefixEnd_2993246 1024649276765267429972879 := by
  unfold tailWord_2993246
  simp only [CollatzResearch.WordTrace]
  refine ⟨13646581314248552820342949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72781767009325615041829061 13646581314248552820342949)
  ·
    refine ⟨2558733996421603653814303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13646581314248552820342949 2558733996421603653814303)
    ·
      refine ⟨3838100994632405480721455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2558733996421603653814303 3838100994632405480721455)
      ·
        refine ⟨5757151491948608221082183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3838100994632405480721455 5757151491948608221082183)
        ·
          refine ⟨8635727237922912331623275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5757151491948608221082183 8635727237922912331623275)
          ·
            refine ⟨12953590856884368497434913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8635727237922912331623275 12953590856884368497434913)
            ·
              refine ⟨9715193142663276373076185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12953590856884368497434913 9715193142663276373076185)
              ·
                refine ⟨7286394856997457279807139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9715193142663276373076185 7286394856997457279807139)
                ·
                  refine ⟨10929592285496185919710709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7286394856997457279807139 10929592285496185919710709)
                  ·
                    refine ⟨1024649276765267429972879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10929592285496185919710709 1024649276765267429972879)
                    ·
                      rfl

theorem cell22_2993246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_2993246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993246 prefixEnd_2993246 := by exact prefixLift 2993246
  have htrace : WordTrace (prefixWord ++ tailWord_2993246) baseStart_2993246 baseEnd_2993246 := by
    simpa [prefixWord, tailWord_2993246, baseEnd_2993246] using wordTrace_append hprefix tailTrace_2993246
  have hstable : (prefixWord ++ tailWord_2993246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993246).length < 2 ^ (prefixWord ++ tailWord_2993246).sum := by decide
  have hdescent : baseEnd_2993246 < baseStart_2993246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993308 : List Nat := [2, 2, 3, 2, 1, 4, 1, 3, 1, 3]
def baseStart_2993308 : Nat := 118140960795 + 2993308 * 2 ^ 59
def prefixEnd_2993308 : Nat := 4983230072969 + 3 ^ 40 * 2993308 * 2
def baseEnd_2993308 : Nat := 1024670500632319934922689

theorem tailTrace_2993308 : CollatzResearch.WordTrace tailWord_2993308 prefixEnd_2993308 1024670500632319934922689 := by
  unfold tailWord_2993308
  simp only [CollatzResearch.WordTrace]
  refine ⟨54587455919881903575750289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72783274559842538101000385 54587455919881903575750289)
  ·
    refine ⟨40940591939911427681812717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54587455919881903575750289 40940591939911427681812717)
    ·
      refine ⟨15352721977466785380679769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40940591939911427681812717 15352721977466785380679769)
      ·
        refine ⟨11514541483100089035509827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15352721977466785380679769 11514541483100089035509827)
        ·
          refine ⟨17271812224650133553264741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11514541483100089035509827 17271812224650133553264741)
          ·
            refine ⟨3238464792121900041237139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17271812224650133553264741 3238464792121900041237139)
            ·
              refine ⟨4857697188182850061855709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3238464792121900041237139 4857697188182850061855709)
              ·
                refine ⟨1821636445568568773195891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4857697188182850061855709 1821636445568568773195891)
                ·
                  refine ⟨2732454668352853159793837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1821636445568568773195891 2732454668352853159793837)
                  ·
                    refine ⟨1024670500632319934922689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2732454668352853159793837 1024670500632319934922689)
                    ·
                      rfl

theorem cell22_2993308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_2993308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993308 prefixEnd_2993308 := by exact prefixLift 2993308
  have htrace : WordTrace (prefixWord ++ tailWord_2993308) baseStart_2993308 baseEnd_2993308 := by
    simpa [prefixWord, tailWord_2993308, baseEnd_2993308] using wordTrace_append hprefix tailTrace_2993308
  have hstable : (prefixWord ++ tailWord_2993308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993308).length < 2 ^ (prefixWord ++ tailWord_2993308).sum := by decide
  have hdescent : baseEnd_2993308 < baseStart_2993308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993315 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 8]
def baseStart_2993315 : Nat := 118140960795 + 2993315 * 2 ^ 59
def prefixEnd_2993315 : Nat := 4983230072969 + 3 ^ 40 * 2993315 * 2
def baseEnd_2993315 : Nat := 341557632291791416665889

theorem tailTrace_2993315 : CollatzResearch.WordTrace tailWord_2993315 prefixEnd_2993315 341557632291791416665889 := by
  unfold tailWord_2993315
  simp only [CollatzResearch.WordTrace]
  refine ⟨109175167150738447347005399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72783444767158964898003599 109175167150738447347005399)
  ·
    refine ⟨163762750726107671020508099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109175167150738447347005399 163762750726107671020508099)
    ·
      refine ⟨245644126089161506530762149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163762750726107671020508099 245644126089161506530762149)
      ·
        refine ⟨46058273641717782474517903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245644126089161506530762149 46058273641717782474517903)
        ·
          refine ⟨69087410462576673711776855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46058273641717782474517903 69087410462576673711776855)
          ·
            refine ⟨103631115693865010567665283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69087410462576673711776855 103631115693865010567665283)
            ·
              refine ⟨155446673540797515851497925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103631115693865010567665283 155446673540797515851497925)
              ·
                refine ⟨29146251288899534222155861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155446673540797515851497925 29146251288899534222155861)
                ·
                  refine ⟨341557632291791416665889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29146251288899534222155861 341557632291791416665889)
                  ·
                    rfl

theorem cell22_2993315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 8].length) (baseStart_2993315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993315 prefixEnd_2993315 := by exact prefixLift 2993315
  have htrace : WordTrace (prefixWord ++ tailWord_2993315) baseStart_2993315 baseEnd_2993315 := by
    simpa [prefixWord, tailWord_2993315, baseEnd_2993315] using wordTrace_append hprefix tailTrace_2993315
  have hstable : (prefixWord ++ tailWord_2993315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993315).length < 2 ^ (prefixWord ++ tailWord_2993315).sum := by decide
  have hdescent : baseEnd_2993315 < baseStart_2993315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993325 : List Nat := [1, 5, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_2993325 : Nat := 118140960795 + 2993325 * 2 ^ 59
def prefixEnd_2993325 : Nat := 4983230072969 + 3 ^ 40 * 2993325 * 2
def baseEnd_2993325 : Nat := 1024676320079737557247637

theorem tailTrace_2993325 : CollatzResearch.WordTrace tailWord_2993325 prefixEnd_2993325 1024676320079737557247637 := by
  unfold tailWord_2993325
  simp only [CollatzResearch.WordTrace]
  refine ⟨109175531880702219054869429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72783687920468146036579619 109175531880702219054869429)
  ·
    refine ⟨10235206113815833036394009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109175531880702219054869429 10235206113815833036394009)
    ·
      refine ⟨7676404585361874777295507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10235206113815833036394009 7676404585361874777295507)
      ·
        refine ⟨11514606878042812165943261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7676404585361874777295507 11514606878042812165943261)
        ·
          refine ⟨4317977579266054562228723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11514606878042812165943261 4317977579266054562228723)
          ·
            refine ⟨6476966368899081843343085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4317977579266054562228723 6476966368899081843343085)
            ·
              refine ⟨2428862388337155691253657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6476966368899081843343085 2428862388337155691253657)
              ·
                refine ⟨1821646791252866768440243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2428862388337155691253657 1821646791252866768440243)
                ·
                  refine ⟨2732470186879300152660365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1821646791252866768440243 2732470186879300152660365)
                  ·
                    refine ⟨1024676320079737557247637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2732470186879300152660365 1024676320079737557247637)
                    ·
                      rfl

theorem cell22_2993325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_2993325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993325 prefixEnd_2993325 := by exact prefixLift 2993325
  have htrace : WordTrace (prefixWord ++ tailWord_2993325) baseStart_2993325 baseEnd_2993325 := by
    simpa [prefixWord, tailWord_2993325, baseEnd_2993325] using wordTrace_append hprefix tailTrace_2993325
  have hstable : (prefixWord ++ tailWord_2993325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993325).length < 2 ^ (prefixWord ++ tailWord_2993325).sum := by decide
  have hdescent : baseEnd_2993325 < baseStart_2993325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993347 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 6, 3]
def baseStart_2993347 : Nat := 118140960795 + 2993347 * 2 ^ 59
def prefixEnd_2993347 : Nat := 4983230072969 + 3 ^ 40 * 2993347 * 2
def baseEnd_2993347 : Nat := 1024683851129336833197569

theorem tailTrace_2993347 : CollatzResearch.WordTrace tailWord_2993347 prefixEnd_2993347 1024683851129336833197569 := by
  unfold tailWord_2993347
  simp only [CollatzResearch.WordTrace]
  refine ⟨109176334286622516812170295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72784222857748344541446863 109176334286622516812170295)
  ·
    refine ⟨163764501429933775218255443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109176334286622516812170295 163764501429933775218255443)
    ·
      refine ⟨245646752144900662827383165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163764501429933775218255443 245646752144900662827383165)
      ·
        refine ⟨92117532054337748560268687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245646752144900662827383165 92117532054337748560268687)
        ·
          refine ⟨138176298081506622840403031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92117532054337748560268687 138176298081506622840403031)
          ·
            refine ⟨207264447122259934260604547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138176298081506622840403031 207264447122259934260604547)
            ·
              refine ⟨310896670683389901390906821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207264447122259934260604547 310896670683389901390906821)
              ·
                refine ⟨58293125753135606510795029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 310896670683389901390906821 58293125753135606510795029)
                ·
                  refine ⟨2732490269678231555193517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58293125753135606510795029 2732490269678231555193517)
                  ·
                    refine ⟨1024683851129336833197569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2732490269678231555193517 1024683851129336833197569)
                    ·
                      rfl

theorem cell22_2993347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 3].length) (baseStart_2993347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993347 prefixEnd_2993347 := by exact prefixLift 2993347
  have htrace : WordTrace (prefixWord ++ tailWord_2993347) baseStart_2993347 baseEnd_2993347 := by
    simpa [prefixWord, tailWord_2993347, baseEnd_2993347] using wordTrace_append hprefix tailTrace_2993347
  have hstable : (prefixWord ++ tailWord_2993347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993347).length < 2 ^ (prefixWord ++ tailWord_2993347).sum := by decide
  have hdescent : baseEnd_2993347 < baseStart_2993347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993409 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 5, 3]
def baseStart_2993409 : Nat := 118140960795 + 2993409 * 2 ^ 59
def prefixEnd_2993409 : Nat := 4983230072969 + 3 ^ 40 * 2993409 * 2
def baseEnd_2993409 : Nat := 1024705074996389338147379

theorem tailTrace_2993409 : CollatzResearch.WordTrace tailWord_2993409 prefixEnd_2993409 1024705074996389338147379 := by
  unfold tailWord_2993409
  simp only [CollatzResearch.WordTrace]
  refine ⟨109178595612397901400927281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72785730408265267600618187 109178595612397901400927281)
  ·
    refine ⟨81883946709298426050695461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109178595612397901400927281 81883946709298426050695461)
    ·
      refine ⟨15353240007993454884505399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81883946709298426050695461 15353240007993454884505399)
      ·
        refine ⟨23029860011990182326758099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15353240007993454884505399 23029860011990182326758099)
        ·
          refine ⟨34544790017985273490137149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23029860011990182326758099 34544790017985273490137149)
          ·
            refine ⟨12954296256744477558801431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34544790017985273490137149 12954296256744477558801431)
            ·
              refine ⟨19431444385116716338202147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12954296256744477558801431 19431444385116716338202147)
              ·
                refine ⟨29147166577675074507303221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19431444385116716338202147 29147166577675074507303221)
                ·
                  refine ⟨2732546866657038235059677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29147166577675074507303221 2732546866657038235059677)
                  ·
                    refine ⟨1024705074996389338147379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2732546866657038235059677 1024705074996389338147379)
                    ·
                      rfl

theorem cell22_2993409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_2993409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993409 prefixEnd_2993409 := by exact prefixLift 2993409
  have htrace : WordTrace (prefixWord ++ tailWord_2993409) baseStart_2993409 baseEnd_2993409 := by
    simpa [prefixWord, tailWord_2993409, baseEnd_2993409] using wordTrace_append hprefix tailTrace_2993409
  have hstable : (prefixWord ++ tailWord_2993409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993409).length < 2 ^ (prefixWord ++ tailWord_2993409).sum := by decide
  have hdescent : baseEnd_2993409 < baseStart_2993409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993439 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 7]
def baseStart_2993439 : Nat := 118140960795 + 2993439 * 2 ^ 59
def prefixEnd_2993439 : Nat := 4983230072969 + 3 ^ 40 * 2993439 * 2
def baseEnd_2993439 : Nat := 341571781536493086632429

theorem tailTrace_2993439 : CollatzResearch.WordTrace tailWord_2993439 prefixEnd_2993439 341571781536493086632429 := by
  unfold tailWord_2993439
  simp only [CollatzResearch.WordTrace]
  refine ⟨109179689802289216524519371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72786459868192811016346247 109179689802289216524519371)
  ·
    refine ⟨163769534703433824786779057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109179689802289216524519371 163769534703433824786779057)
    ·
      refine ⟨122827151027575368590084293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163769534703433824786779057 122827151027575368590084293)
      ·
        refine ⟨23030090817670381610640805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122827151027575368590084293 23030090817670381610640805)
        ·
          refine ⟨4318142028313196551995151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23030090817670381610640805 4318142028313196551995151)
          ·
            refine ⟨6477213042469794827992727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4318142028313196551995151 6477213042469794827992727)
            ·
              refine ⟨9715819563704692241989091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6477213042469794827992727 9715819563704692241989091)
              ·
                refine ⟨14573729345557038362983637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9715819563704692241989091 14573729345557038362983637)
                ·
                  refine ⟨341571781536493086632429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14573729345557038362983637 341571781536493086632429)
                  ·
                    rfl

theorem cell22_2993439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 7].length) (baseStart_2993439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993439 prefixEnd_2993439 := by exact prefixLift 2993439
  have htrace : WordTrace (prefixWord ++ tailWord_2993439) baseStart_2993439 baseEnd_2993439 := by
    simpa [prefixWord, tailWord_2993439, baseEnd_2993439] using wordTrace_append hprefix tailTrace_2993439
  have hstable : (prefixWord ++ tailWord_2993439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993439).length < 2 ^ (prefixWord ++ tailWord_2993439).sum := by decide
  have hdescent : baseEnd_2993439 < baseStart_2993439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993494 : List Nat := [5, 2, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2993494 : Nat := 118140960795 + 2993494 * 2 ^ 59
def prefixEnd_2993494 : Nat := 4983230072969 + 3 ^ 40 * 2993494 * 2
def baseEnd_2993494 : Nat := 1024734172233477449772119

theorem tailTrace_2993494 : CollatzResearch.WordTrace tailWord_2993494 prefixEnd_2993494 1024734172233477449772119 := by
  unfold tailWord_2993494
  simp only [CollatzResearch.WordTrace]
  refine ⟨6823855988568122557360721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72787797211393307278514357 6823855988568122557360721)
  ·
    refine ⟨5117891991426091918020541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6823855988568122557360721 5117891991426091918020541)
    ·
      refine ⟨1919209496784784469257703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5117891991426091918020541 1919209496784784469257703)
      ·
        refine ⟨2878814245177176703886555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1919209496784784469257703 2878814245177176703886555)
        ·
          refine ⟨4318221367765765055829833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2878814245177176703886555 4318221367765765055829833)
          ·
            refine ⟨3238666025824323791872375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4318221367765765055829833 3238666025824323791872375)
            ·
              refine ⟨4857999038736485687808563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3238666025824323791872375 4857999038736485687808563)
              ·
                refine ⟨7286998558104728531712845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4857999038736485687808563 7286998558104728531712845)
                ·
                  refine ⟨2732624459289273199392317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7286998558104728531712845 2732624459289273199392317)
                  ·
                    refine ⟨1024734172233477449772119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2732624459289273199392317 1024734172233477449772119)
                    ·
                      rfl

theorem cell22_2993494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2993494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993494 prefixEnd_2993494 := by exact prefixLift 2993494
  have htrace : WordTrace (prefixWord ++ tailWord_2993494) baseStart_2993494 baseEnd_2993494 := by
    simpa [prefixWord, tailWord_2993494, baseEnd_2993494] using wordTrace_append hprefix tailTrace_2993494
  have hstable : (prefixWord ++ tailWord_2993494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993494).length < 2 ^ (prefixWord ++ tailWord_2993494).sum := by decide
  have hdescent : baseEnd_2993494 < baseStart_2993494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993550 : List Nat := [4, 1, 1, 4, 2, 1, 2, 2, 2, 3]
def baseStart_2993550 : Nat := 118140960795 + 2993550 * 2 ^ 59
def prefixEnd_2993550 : Nat := 4983230072969 + 3 ^ 40 * 2993550 * 2
def baseEnd_2993550 : Nat := 1024753342177911970371947

theorem tailTrace_2993550 : CollatzResearch.WordTrace tailWord_2993550 prefixEnd_2993550 1024753342177911970371947 := by
  unfold tailWord_2993550
  simp only [CollatzResearch.WordTrace]
  refine ⟨13647967288110885310226263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72789158869924721654540069 13647967288110885310226263)
  ·
    refine ⟨20471950932166327965339395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13647967288110885310226263 20471950932166327965339395)
    ·
      refine ⟨30707926398249491948009093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20471950932166327965339395 30707926398249491948009093)
      ·
        refine ⟨5757736199671779740251705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30707926398249491948009093 5757736199671779740251705)
        ·
          refine ⟨4318302149753834805188779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5757736199671779740251705 4318302149753834805188779)
          ·
            refine ⟨6477453224630752207783169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4318302149753834805188779 6477453224630752207783169)
            ·
              refine ⟨4858089918473064155837377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6477453224630752207783169 4858089918473064155837377)
              ·
                refine ⟨3643567438854798116878033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4858089918473064155837377 3643567438854798116878033)
                ·
                  refine ⟨2732675579141098587658525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3643567438854798116878033 2732675579141098587658525)
                  ·
                    refine ⟨1024753342177911970371947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2732675579141098587658525 1024753342177911970371947)
                    ·
                      rfl

theorem cell22_2993550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_2993550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993550 prefixEnd_2993550 := by exact prefixLift 2993550
  have htrace : WordTrace (prefixWord ++ tailWord_2993550) baseStart_2993550 baseEnd_2993550 := by
    simpa [prefixWord, tailWord_2993550, baseEnd_2993550] using wordTrace_append hprefix tailTrace_2993550
  have hstable : (prefixWord ++ tailWord_2993550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993550).length < 2 ^ (prefixWord ++ tailWord_2993550).sum := by decide
  have hdescent : baseEnd_2993550 < baseStart_2993550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993685 : List Nat := [1, 3, 2, 1, 3, 2, 4, 1, 2, 3]
def baseStart_2993685 : Nat := 118140960795 + 2993685 * 2 ^ 59
def prefixEnd_2993685 : Nat := 4983230072969 + 3 ^ 40 * 2993685 * 2
def baseEnd_2993685 : Nat := 1024799555436816618246533

theorem tailTrace_2993685 : CollatzResearch.WordTrace tailWord_2993685 prefixEnd_2993685 1024799555436816618246533 := by
  unfold tailWord_2993685
  simp only [CollatzResearch.WordTrace]
  refine ⟨109188662159398000537974509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72792441439598667025316339 109188662159398000537974509)
  ·
    refine ⟨40945748309774250201740441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109188662159398000537974509 40945748309774250201740441)
    ·
      refine ⟨30709311232330687651305331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40945748309774250201740441 30709311232330687651305331)
      ·
        refine ⟨46063966848496031476957997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30709311232330687651305331 46063966848496031476957997)
        ·
          refine ⟨17273987568186011803859249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46063966848496031476957997 17273987568186011803859249)
          ·
            refine ⟨12955490676139508852894437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17273987568186011803859249 12955490676139508852894437)
            ·
              refine ⟨2429154501776157909917707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12955490676139508852894437 2429154501776157909917707)
              ·
                refine ⟨3643731752664236864876561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429154501776157909917707 3643731752664236864876561)
                ·
                  refine ⟨2732798814498177648657421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3643731752664236864876561 2732798814498177648657421)
                  ·
                    refine ⟨1024799555436816618246533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2732798814498177648657421 1024799555436816618246533)
                    ·
                      rfl

theorem cell22_2993685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_2993685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993685 prefixEnd_2993685 := by exact prefixLift 2993685
  have htrace : WordTrace (prefixWord ++ tailWord_2993685) baseStart_2993685 baseEnd_2993685 := by
    simpa [prefixWord, tailWord_2993685, baseEnd_2993685] using wordTrace_append hprefix tailTrace_2993685
  have hstable : (prefixWord ++ tailWord_2993685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993685).length < 2 ^ (prefixWord ++ tailWord_2993685).sum := by decide
  have hdescent : baseEnd_2993685 < baseStart_2993685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993801 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 1, 6]
def baseStart_2993801 : Nat := 118140960795 + 2993801 * 2 ^ 59
def prefixEnd_2993801 : Nat := 4983230072969 + 3 ^ 40 * 2993801 * 2
def baseEnd_2993801 : Nat := 1024839264607430982346177

theorem tailTrace_2993801 : CollatzResearch.WordTrace tailWord_2993801 prefixEnd_2993801 1024839264607430982346177 := by
  unfold tailWord_2993801
  simp only [CollatzResearch.WordTrace]
  refine ⟨109192893026977752349197257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72795262017985168232798171 109192893026977752349197257)
  ·
    refine ⟨81894669770233314261897943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109192893026977752349197257 81894669770233314261897943)
    ·
      refine ⟨122842004655349971392846915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81894669770233314261897943 122842004655349971392846915)
      ·
        refine ⟨184263006983024957089270373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122842004655349971392846915 184263006983024957089270373)
        ·
          refine ⟨34549313809317179454238195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184263006983024957089270373 34549313809317179454238195)
          ·
            refine ⟨51823970713975769181357293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34549313809317179454238195 51823970713975769181357293)
            ·
              refine ⟨19433989017740913443008985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51823970713975769181357293 19433989017740913443008985)
              ·
                refine ⟨14575491763305685082256739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19433989017740913443008985 14575491763305685082256739)
                ·
                  refine ⟨21863237644958527623385109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14575491763305685082256739 21863237644958527623385109)
                  ·
                    refine ⟨1024839264607430982346177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21863237644958527623385109 1024839264607430982346177)
                    ·
                      rfl

theorem cell22_2993801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_2993801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993801 prefixEnd_2993801 := by exact prefixLift 2993801
  have htrace : WordTrace (prefixWord ++ tailWord_2993801) baseStart_2993801 baseEnd_2993801 := by
    simpa [prefixWord, tailWord_2993801, baseEnd_2993801] using wordTrace_append hprefix tailTrace_2993801
  have hstable : (prefixWord ++ tailWord_2993801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993801).length < 2 ^ (prefixWord ++ tailWord_2993801).sum := by decide
  have hdescent : baseEnd_2993801 < baseStart_2993801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993822 : List Nat := [4, 3, 1, 1, 1, 2, 3, 3, 4]
def baseStart_2993822 : Nat := 118140960795 + 2993822 * 2 ^ 59
def prefixEnd_2993822 : Nat := 4983230072969 + 3 ^ 40 * 2993822 * 2
def baseEnd_2993822 : Nat := 341615484445531309190371

theorem tailTrace_2993822 : CollatzResearch.WordTrace tailWord_2993822 prefixEnd_2993822 341615484445531309190371 := by
  unfold tailWord_2993822
  simp only [CollatzResearch.WordTrace]
  refine ⟨13649207369987709116963965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72795772639934448623807813 13649207369987709116963965)
  ·
    refine ⟨5118452763745390918861487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13649207369987709116963965 5118452763745390918861487)
    ·
      refine ⟨7677679145618086378292231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5118452763745390918861487 7677679145618086378292231)
      ·
        refine ⟨11516518718427129567438347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7677679145618086378292231 11516518718427129567438347)
        ·
          refine ⟨17274778077640694351157521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11516518718427129567438347 17274778077640694351157521)
          ·
            refine ⟨12956083558230520763368141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17274778077640694351157521 12956083558230520763368141)
            ·
              refine ⟨4858531334336445286263053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12956083558230520763368141 4858531334336445286263053)
              ·
                refine ⟨1821949250376166982348645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4858531334336445286263053 1821949250376166982348645)
                ·
                  refine ⟨341615484445531309190371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1821949250376166982348645 341615484445531309190371)
                  ·
                    rfl

theorem cell22_2993822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_2993822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993822 prefixEnd_2993822 := by exact prefixLift 2993822
  have htrace : WordTrace (prefixWord ++ tailWord_2993822) baseStart_2993822 baseEnd_2993822 := by
    simpa [prefixWord, tailWord_2993822, baseEnd_2993822] using wordTrace_append hprefix tailTrace_2993822
  have hstable : (prefixWord ++ tailWord_2993822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993822).length < 2 ^ (prefixWord ++ tailWord_2993822).sum := by decide
  have hdescent : baseEnd_2993822 < baseStart_2993822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993854 : List Nat := [4, 2, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_2993854 : Nat := 118140960795 + 2993854 * 2 ^ 59
def prefixEnd_2993854 : Nat := 4983230072969 + 3 ^ 40 * 2993854 * 2
def baseEnd_2993854 : Nat := 1024857407590556510771015

theorem tailTrace_2993854 : CollatzResearch.WordTrace tailWord_2993854 prefixEnd_2993854 1024857407590556510771015 := by
  unfold tailWord_2993854
  simp only [CollatzResearch.WordTrace]
  refine ⟨13649353261973217800109577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72796550730523828267251077 13649353261973217800109577)
  ·
    refine ⟨10237014946479913350082183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13649353261973217800109577 10237014946479913350082183)
    ·
      refine ⟨15355522419719870025123275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10237014946479913350082183 15355522419719870025123275)
      ·
        refine ⟨23033283629579805037684913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15355522419719870025123275 23033283629579805037684913)
        ·
          refine ⟨17274962722184853778263685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23033283629579805037684913 17274962722184853778263685)
          ·
            refine ⟨3239055510409660083424441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17274962722184853778263685 3239055510409660083424441)
            ·
              refine ⟨2429291632807245062568331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3239055510409660083424441 2429291632807245062568331)
              ·
                refine ⟨3643937449210867593852497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429291632807245062568331 3643937449210867593852497)
                ·
                  refine ⟨2732953086908150695389373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3643937449210867593852497 2732953086908150695389373)
                  ·
                    refine ⟨1024857407590556510771015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2732953086908150695389373 1024857407590556510771015)
                    ·
                      rfl

theorem cell22_2993854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_2993854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993854 prefixEnd_2993854 := by exact prefixLift 2993854
  have htrace : WordTrace (prefixWord ++ tailWord_2993854) baseStart_2993854 baseEnd_2993854 := by
    simpa [prefixWord, tailWord_2993854, baseEnd_2993854] using wordTrace_append hprefix tailTrace_2993854
  have hstable : (prefixWord ++ tailWord_2993854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993854).length < 2 ^ (prefixWord ++ tailWord_2993854).sum := by decide
  have hdescent : baseEnd_2993854 < baseStart_2993854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993858 : List Nat := [3, 5, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_2993858 : Nat := 118140960795 + 2993858 * 2 ^ 59
def prefixEnd_2993858 : Nat := 4983230072969 + 3 ^ 40 * 2993858 * 2
def baseEnd_2993858 : Nat := 1024858776872301833671003

theorem tailTrace_2993858 : CollatzResearch.WordTrace tailWord_2993858 prefixEnd_2993858 1024858776872301833671003 := by
  unfold tailWord_2993858
  simp only [CollatzResearch.WordTrace]
  refine ⟨27298742996942812771005557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72796647991847500722681485 27298742996942812771005557)
  ·
    refine ⟨2559257155963388697281771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27298742996942812771005557 2559257155963388697281771)
    ·
      refine ⟨3838885733945083045922657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2559257155963388697281771 3838885733945083045922657)
      ·
        refine ⟨2879164300458812284441993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3838885733945083045922657 2879164300458812284441993)
        ·
          refine ⟨2159373225344109213331495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2879164300458812284441993 2159373225344109213331495)
          ·
            refine ⟨3239059838016163819997243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2159373225344109213331495 3239059838016163819997243)
            ·
              refine ⟨4858589757024245729995865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3239059838016163819997243 4858589757024245729995865)
              ·
                refine ⟨3643942317768184297496899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4858589757024245729995865 3643942317768184297496899)
                ·
                  refine ⟨5465913476652276446245349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3643942317768184297496899 5465913476652276446245349)
                  ·
                    refine ⟨1024858776872301833671003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5465913476652276446245349 1024858776872301833671003)
                    ·
                      rfl

theorem cell22_2993858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_2993858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993858 prefixEnd_2993858 := by exact prefixLift 2993858
  have htrace : WordTrace (prefixWord ++ tailWord_2993858) baseStart_2993858 baseEnd_2993858 := by
    simpa [prefixWord, tailWord_2993858, baseEnd_2993858] using wordTrace_append hprefix tailTrace_2993858
  have hstable : (prefixWord ++ tailWord_2993858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993858).length < 2 ^ (prefixWord ++ tailWord_2993858).sum := by decide
  have hdescent : baseEnd_2993858 < baseStart_2993858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993893 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 2, 5]
def baseStart_2993893 : Nat := 118140960795 + 2993893 * 2 ^ 59
def prefixEnd_2993893 : Nat := 4983230072969 + 3 ^ 40 * 2993893 * 2
def baseEnd_2993893 : Nat := 1024870758087573409045895

theorem tailTrace_2993893 : CollatzResearch.WordTrace tailWord_2993893 prefixEnd_2993893 1024870758087573409045895 := by
  unfold tailWord_2993893
  simp only [CollatzResearch.WordTrace]
  refine ⟨109196248542644452061546333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72797499028429634707697555 109196248542644452061546333)
  ·
    refine ⟨40948593203491669523079875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109196248542644452061546333 40948593203491669523079875)
    ·
      refine ⟨61422889805237504284619813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40948593203491669523079875 61422889805237504284619813)
      ·
        refine ⟨11516791838482032053366215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61422889805237504284619813 11516791838482032053366215)
        ·
          refine ⟨17275187757723048080049323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11516791838482032053366215 17275187757723048080049323)
          ·
            refine ⟨25912781636584572120073985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17275187757723048080049323 25912781636584572120073985)
            ·
              refine ⟨19434586227438429090055489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25912781636584572120073985 19434586227438429090055489)
              ·
                refine ⟨14575939670578821817541617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19434586227438429090055489 14575939670578821817541617)
                ·
                  refine ⟨10931954752934116363156213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14575939670578821817541617 10931954752934116363156213)
                  ·
                    refine ⟨1024870758087573409045895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10931954752934116363156213 1024870758087573409045895)
                    ·
                      rfl

theorem cell22_2993893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_2993893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993893 prefixEnd_2993893 := by exact prefixLift 2993893
  have htrace : WordTrace (prefixWord ++ tailWord_2993893) baseStart_2993893 baseEnd_2993893 := by
    simpa [prefixWord, tailWord_2993893, baseEnd_2993893] using wordTrace_append hprefix tailTrace_2993893
  have hstable : (prefixWord ++ tailWord_2993893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993893).length < 2 ^ (prefixWord ++ tailWord_2993893).sum := by decide
  have hdescent : baseEnd_2993893 < baseStart_2993893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993910 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_2993910 : Nat := 118140960795 + 2993910 * 2 ^ 59
def prefixEnd_2993910 : Nat := 4983230072969 + 3 ^ 40 * 2993910 * 2
def baseEnd_2993910 : Nat := 1024876577534991031370843

theorem tailTrace_2993910 : CollatzResearch.WordTrace tailWord_2993910 prefixEnd_2993910 1024876577534991031370843 := by
  unfold tailWord_2993910
  simp only [CollatzResearch.WordTrace]
  refine ⟨6824804286473928997807199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72797912389055242643276789 6824804286473928997807199)
  ·
    refine ⟨10237206429710893496710799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6824804286473928997807199 10237206429710893496710799)
    ·
      refine ⟨15355809644566340245066199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10237206429710893496710799 15355809644566340245066199)
      ·
        refine ⟨23033714466849510367599299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15355809644566340245066199 23033714466849510367599299)
        ·
          refine ⟨34550571700274265551398949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23033714466849510367599299 34550571700274265551398949)
          ·
            refine ⟨6478232193801424790887303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34550571700274265551398949 6478232193801424790887303)
            ·
              refine ⟨9717348290702137186330955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6478232193801424790887303 9717348290702137186330955)
              ·
                refine ⟨14576022436053205779496433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9717348290702137186330955 14576022436053205779496433)
                ·
                  refine ⟨10932016827039904334622325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14576022436053205779496433 10932016827039904334622325)
                  ·
                    refine ⟨1024876577534991031370843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10932016827039904334622325 1024876577534991031370843)
                    ·
                      rfl

theorem cell22_2993910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_2993910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993910 prefixEnd_2993910 := by exact prefixLift 2993910
  have htrace : WordTrace (prefixWord ++ tailWord_2993910) baseStart_2993910 baseEnd_2993910 := by
    simpa [prefixWord, tailWord_2993910, baseEnd_2993910] using wordTrace_append hprefix tailTrace_2993910
  have hstable : (prefixWord ++ tailWord_2993910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993910).length < 2 ^ (prefixWord ++ tailWord_2993910).sum := by decide
  have hdescent : baseEnd_2993910 < baseStart_2993910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993972 : List Nat := [2, 5, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_2993972 : Nat := 118140960795 + 2993972 * 2 ^ 59
def prefixEnd_2993972 : Nat := 4983230072969 + 3 ^ 40 * 2993972 * 2
def baseEnd_2993972 : Nat := 1024897801402043536320653

theorem tailTrace_2993972 : CollatzResearch.WordTrace tailWord_2993972 prefixEnd_2993972 1024897801402043536320653 := by
  unfold tailWord_2993972
  simp only [CollatzResearch.WordTrace]
  refine ⟨54599564954679124276836085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72799419939572165702448113 54599564954679124276836085)
  ·
    refine ⟨5118709214501167900953383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54599564954679124276836085 5118709214501167900953383)
    ·
      refine ⟨7678063821751751851430075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5118709214501167900953383 7678063821751751851430075)
      ·
        refine ⟨11517095732627627777145113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7678063821751751851430075 11517095732627627777145113)
        ·
          refine ⟨8637821799470720832858835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11517095732627627777145113 8637821799470720832858835)
          ·
            refine ⟨12956732699206081249288253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8637821799470720832858835 12956732699206081249288253)
            ·
              refine ⟨4858774762202280468483095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12956732699206081249288253 4858774762202280468483095)
              ·
                refine ⟨7288162143303420702724643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4858774762202280468483095 7288162143303420702724643)
                ·
                  refine ⟨10932243214955131054086965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7288162143303420702724643 10932243214955131054086965)
                  ·
                    refine ⟨1024897801402043536320653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10932243214955131054086965 1024897801402043536320653)
                    ·
                      rfl

theorem cell22_2993972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_2993972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993972 prefixEnd_2993972 := by exact prefixLift 2993972
  have htrace : WordTrace (prefixWord ++ tailWord_2993972) baseStart_2993972 baseEnd_2993972 := by
    simpa [prefixWord, tailWord_2993972, baseEnd_2993972] using wordTrace_append hprefix tailTrace_2993972
  have hstable : (prefixWord ++ tailWord_2993972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993972).length < 2 ^ (prefixWord ++ tailWord_2993972).sum := by decide
  have hdescent : baseEnd_2993972 < baseStart_2993972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2993998 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_2993998 : Nat := 118140960795 + 2993998 * 2 ^ 59
def prefixEnd_2993998 : Nat := 4983230072969 + 3 ^ 40 * 2993998 * 2
def baseEnd_2993998 : Nat := 1024906701733388135170573

theorem tailTrace_2993998 : CollatzResearch.WordTrace tailWord_2993998 prefixEnd_2993998 1024906701733388135170573 := by
  unfold tailWord_2993998
  simp only [CollatzResearch.WordTrace]
  refine ⟨13650009775908006874264831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72800052138176036662745765 13650009775908006874264831)
  ·
    refine ⟨20475014663862010311397247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13650009775908006874264831 20475014663862010311397247)
    ·
      refine ⟨30712521995793015467095871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20475014663862010311397247 30712521995793015467095871)
      ·
        refine ⟨46068782993689523200643807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30712521995793015467095871 46068782993689523200643807)
        ·
          refine ⟨69103174490534284800965711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46068782993689523200643807 69103174490534284800965711)
          ·
            refine ⟨103654761735801427201448567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69103174490534284800965711 103654761735801427201448567)
            ·
              refine ⟨155482142603702140802172851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103654761735801427201448567 155482142603702140802172851)
              ·
                refine ⟨233223213905553211203259277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155482142603702140802172851 233223213905553211203259277)
                ·
                  refine ⟨87458705214582454201222229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233223213905553211203259277 87458705214582454201222229)
                  ·
                    refine ⟨1024906701733388135170573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87458705214582454201222229 1024906701733388135170573)
                    ·
                      rfl

theorem cell22_2993998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_2993998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2993998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2993998 prefixEnd_2993998 := by exact prefixLift 2993998
  have htrace : WordTrace (prefixWord ++ tailWord_2993998) baseStart_2993998 baseEnd_2993998 := by
    simpa [prefixWord, tailWord_2993998, baseEnd_2993998] using wordTrace_append hprefix tailTrace_2993998
  have hstable : (prefixWord ++ tailWord_2993998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2993998).length < 2 ^ (prefixWord ++ tailWord_2993998).sum := by decide
  have hdescent : baseEnd_2993998 < baseStart_2993998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2993998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994068 : List Nat := [2, 4, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_2994068 : Nat := 118140960795 + 2994068 * 2 ^ 59
def prefixEnd_2994068 : Nat := 4983230072969 + 3 ^ 40 * 2994068 * 2
def baseEnd_2994068 : Nat := 1024930664163931285920359

theorem tailTrace_2994068 : CollatzResearch.WordTrace tailWord_2994068 prefixEnd_2994068 1024930664163931285920359 := by
  unfold tailWord_2994068
  simp only [CollatzResearch.WordTrace]
  refine ⟨54601315658505228474583429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72801754211340304632777905 54601315658505228474583429)
  ·
    refine ⟨10237746685969730338984393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54601315658505228474583429 10237746685969730338984393)
    ·
      refine ⟨7678310014477297754238295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10237746685969730338984393 7678310014477297754238295)
      ·
        refine ⟨11517465021715946631357443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7678310014477297754238295 11517465021715946631357443)
        ·
          refine ⟨17276197532573919947036165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11517465021715946631357443 17276197532573919947036165)
          ·
            refine ⟨3239287037357609990069281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17276197532573919947036165 3239287037357609990069281)
            ·
              refine ⟨2429465278018207492551961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3239287037357609990069281 2429465278018207492551961)
              ·
                refine ⟨1822098958513655619413971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2429465278018207492551961 1822098958513655619413971)
                ·
                  refine ⟨2733148437770483429120957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1822098958513655619413971 2733148437770483429120957)
                  ·
                    refine ⟨1024930664163931285920359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2733148437770483429120957 1024930664163931285920359)
                    ·
                      rfl

theorem cell22_2994068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_2994068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994068 prefixEnd_2994068 := by exact prefixLift 2994068
  have htrace : WordTrace (prefixWord ++ tailWord_2994068) baseStart_2994068 baseEnd_2994068 := by
    simpa [prefixWord, tailWord_2994068, baseEnd_2994068] using wordTrace_append hprefix tailTrace_2994068
  have hstable : (prefixWord ++ tailWord_2994068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994068).length < 2 ^ (prefixWord ++ tailWord_2994068).sum := by decide
  have hdescent : baseEnd_2994068 < baseStart_2994068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994105 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 1, 6]
def baseStart_2994105 : Nat := 118140960795 + 2994105 * 2 ^ 59
def prefixEnd_2994105 : Nat := 4983230072969 + 3 ^ 40 * 2994105 * 2
def baseEnd_2994105 : Nat := 1024943330020075522745245

theorem tailTrace_2994105 : CollatzResearch.WordTrace tailWord_2994105 prefixEnd_2994105 1024943330020075522745245 := by
  unfold tailWord_2994105
  simp only [CollatzResearch.WordTrace]
  refine ⟨109203980817876412268263769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72802653878584274845509179 109203980817876412268263769)
  ·
    refine ⟨81902985613407309201197827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109203980817876412268263769 81902985613407309201197827)
    ·
      refine ⟨122854478420110963801796741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81902985613407309201197827 122854478420110963801796741)
      ·
        refine ⟨23035214703770805712836889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122854478420110963801796741 23035214703770805712836889)
        ·
          refine ⟨17276411027828104284627667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23035214703770805712836889 17276411027828104284627667)
          ·
            refine ⟨25914616541742156426941501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17276411027828104284627667 25914616541742156426941501)
            ·
              refine ⟨9717981203153308660103063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25914616541742156426941501 9717981203153308660103063)
              ·
                refine ⟨14576971804729962990154595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9717981203153308660103063 14576971804729962990154595)
                ·
                  refine ⟨21865457707094944485231893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14576971804729962990154595 21865457707094944485231893)
                  ·
                    refine ⟨1024943330020075522745245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21865457707094944485231893 1024943330020075522745245)
                    ·
                      rfl

theorem cell22_2994105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_2994105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994105 prefixEnd_2994105 := by exact prefixLift 2994105
  have htrace : WordTrace (prefixWord ++ tailWord_2994105) baseStart_2994105 baseEnd_2994105 := by
    simpa [prefixWord, tailWord_2994105, baseEnd_2994105] using wordTrace_append hprefix tailTrace_2994105
  have hstable : (prefixWord ++ tailWord_2994105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994105).length < 2 ^ (prefixWord ++ tailWord_2994105).sum := by decide
  have hdescent : baseEnd_2994105 < baseStart_2994105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994109 : List Nat := [1, 4, 1, 2, 3, 2, 2, 3, 4]
def baseStart_2994109 : Nat := 118140960795 + 2994109 * 2 ^ 59
def prefixEnd_2994109 : Nat := 4983230072969 + 3 ^ 40 * 2994109 * 2
def baseEnd_2994109 : Nat := 341648233100606948548411

theorem tailTrace_2994109 : CollatzResearch.WordTrace tailWord_2994109 prefixEnd_2994109 341648233100606948548411 := by
  unfold tailWord_2994109
  simp only [CollatzResearch.WordTrace]
  refine ⟨109204126709861920951409381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72802751139907947300939587 109204126709861920951409381)
  ·
    refine ⟨20475773758099110178389259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109204126709861920951409381 20475773758099110178389259)
    ·
      refine ⟨30713660637148665267583889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20475773758099110178389259 30713660637148665267583889)
      ·
        refine ⟨23035245477861498950687917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30713660637148665267583889 23035245477861498950687917)
        ·
          refine ⟨8638217054198062106507969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23035245477861498950687917 8638217054198062106507969)
          ·
            refine ⟨6478662790648546579880977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8638217054198062106507969 6478662790648546579880977)
            ·
              refine ⟨4858997092986409934910733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6478662790648546579880977 4858997092986409934910733)
              ·
                refine ⟨1822123909869903725591525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4858997092986409934910733 1822123909869903725591525)
                ·
                  refine ⟨341648233100606948548411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1822123909869903725591525 341648233100606948548411)
                  ·
                    rfl

theorem cell22_2994109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_2994109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994109 prefixEnd_2994109 := by exact prefixLift 2994109
  have htrace : WordTrace (prefixWord ++ tailWord_2994109) baseStart_2994109 baseEnd_2994109 := by
    simpa [prefixWord, tailWord_2994109, baseEnd_2994109] using wordTrace_append hprefix tailTrace_2994109
  have hstable : (prefixWord ++ tailWord_2994109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994109).length < 2 ^ (prefixWord ++ tailWord_2994109).sum := by decide
  have hdescent : baseEnd_2994109 < baseStart_2994109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994120 : List Nat := [2, 1, 3, 1, 4, 2, 9]
def baseStart_2994120 : Nat := 118140960795 + 2994120 * 2 ^ 59
def prefixEnd_2994120 : Nat := 4983230072969 + 3 ^ 40 * 2994120 * 2
def baseEnd_2994120 : Nat := 37961054252837795689637

theorem tailTrace_2994120 : CollatzResearch.WordTrace tailWord_2994120 prefixEnd_2994120 37961054252837795689637 := by
  unfold tailWord_2994120
  simp only [CollatzResearch.WordTrace]
  refine ⟨54602263956411034915029907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72803018608548046553373209 54602263956411034915029907)
  ·
    refine ⟨81903395934616552372544861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54602263956411034915029907 81903395934616552372544861)
    ·
      refine ⟨30713773475481207139704323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81903395934616552372544861 30713773475481207139704323)
      ·
        refine ⟨46070660213221810709556485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30713773475481207139704323 46070660213221810709556485)
        ·
          refine ⟨8638248789979089508041841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46070660213221810709556485 8638248789979089508041841)
          ·
            refine ⟨6478686592484317131031381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8638248789979089508041841 6478686592484317131031381)
            ·
              refine ⟨37961054252837795689637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6478686592484317131031381 37961054252837795689637)
              ·
                rfl

theorem cell22_2994120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 9].length) (baseStart_2994120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994120 prefixEnd_2994120 := by exact prefixLift 2994120
  have htrace : WordTrace (prefixWord ++ tailWord_2994120) baseStart_2994120 baseEnd_2994120 := by
    simpa [prefixWord, tailWord_2994120, baseEnd_2994120] using wordTrace_append hprefix tailTrace_2994120
  have hstable : (prefixWord ++ tailWord_2994120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994120).length < 2 ^ (prefixWord ++ tailWord_2994120).sum := by decide
  have hdescent : baseEnd_2994120 < baseStart_2994120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994124 : List Nat := [2, 2, 1, 4, 1, 2, 3, 2, 2, 3]
def baseStart_2994124 : Nat := 118140960795 + 2994124 * 2 ^ 59
def prefixEnd_2994124 : Nat := 4983230072969 + 3 ^ 40 * 2994124 * 2
def baseEnd_2994124 : Nat := 1024949834108365806520187

theorem tailTrace_2994124 : CollatzResearch.WordTrace tailWord_2994124 prefixEnd_2994124 1024949834108365806520187 := by
  unfold tailWord_2994124
  simp only [CollatzResearch.WordTrace]
  refine ⟨54602336902403789256602713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72803115869871719008803617 54602336902403789256602713)
  ·
    refine ⟨40951752676802841942452035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54602336902403789256602713 40951752676802841942452035)
    ·
      refine ⟨61427629015204262913678053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40951752676802841942452035 61427629015204262913678053)
      ·
        refine ⟨11517680440350799296314635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61427629015204262913678053 11517680440350799296314635)
        ·
          refine ⟨17276520660526198944471953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11517680440350799296314635 17276520660526198944471953)
          ·
            refine ⟨12957390495394649208353965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17276520660526198944471953 12957390495394649208353965)
            ·
              refine ⟨4859021435772993453132737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12957390495394649208353965 4859021435772993453132737)
              ·
                refine ⟨3644266076829745089849553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4859021435772993453132737 3644266076829745089849553)
                ·
                  refine ⟨2733199557622308817387165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3644266076829745089849553 2733199557622308817387165)
                  ·
                    refine ⟨1024949834108365806520187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2733199557622308817387165 1024949834108365806520187)
                    ·
                      rfl

theorem cell22_2994124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_2994124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994124 prefixEnd_2994124 := by exact prefixLift 2994124
  have htrace : WordTrace (prefixWord ++ tailWord_2994124) baseStart_2994124 baseEnd_2994124 := by
    simpa [prefixWord, tailWord_2994124, baseEnd_2994124] using wordTrace_append hprefix tailTrace_2994124
  have hstable : (prefixWord ++ tailWord_2994124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994124).length < 2 ^ (prefixWord ++ tailWord_2994124).sum := by decide
  have hdescent : baseEnd_2994124 < baseStart_2994124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994141 : List Nat := [1, 4, 3, 1, 4, 1, 1, 1, 1, 5]
def baseStart_2994141 : Nat := 118140960795 + 2994141 * 2 ^ 59
def prefixEnd_2994141 : Nat := 4983230072969 + 3 ^ 40 * 2994141 * 2
def baseEnd_2994141 : Nat := 1024955653555783428845135

theorem tailTrace_2994141 : CollatzResearch.WordTrace tailWord_2994141 prefixEnd_2994141 1024955653555783428845135 := by
  unfold tailWord_2994141
  simp only [CollatzResearch.WordTrace]
  refine ⟨109205293845745990416574277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72803529230497326944382851 109205293845745990416574277)
  ·
    refine ⟨20475992596077373203107677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109205293845745990416574277 20475992596077373203107677)
    ·
      refine ⟨7678497223529014951165379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20475992596077373203107677 7678497223529014951165379)
      ·
        refine ⟨11517745835293522426748069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7678497223529014951165379 11517745835293522426748069)
        ·
          refine ⟨2159577344117535455015263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11517745835293522426748069 2159577344117535455015263)
          ·
            refine ⟨3239366016176303182522895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2159577344117535455015263 3239366016176303182522895)
            ·
              refine ⟨4859049024264454773784343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3239366016176303182522895 4859049024264454773784343)
              ·
                refine ⟨7288573536396682160676515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4859049024264454773784343 7288573536396682160676515)
                ·
                  refine ⟨10932860304595023241014773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7288573536396682160676515 10932860304595023241014773)
                  ·
                    refine ⟨1024955653555783428845135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10932860304595023241014773 1024955653555783428845135)
                    ·
                      rfl

theorem cell22_2994141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_2994141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994141 prefixEnd_2994141 := by exact prefixLift 2994141
  have htrace : WordTrace (prefixWord ++ tailWord_2994141) baseStart_2994141 baseEnd_2994141 := by
    simpa [prefixWord, tailWord_2994141, baseEnd_2994141] using wordTrace_append hprefix tailTrace_2994141
  have hstable : (prefixWord ++ tailWord_2994141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994141).length < 2 ^ (prefixWord ++ tailWord_2994141).sum := by decide
  have hdescent : baseEnd_2994141 < baseStart_2994141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994186 : List Nat := [3, 1, 2, 2, 4, 2, 1, 1, 3, 3]
def baseStart_2994186 : Nat := 118140960795 + 2994186 * 2 ^ 59
def prefixEnd_2994186 : Nat := 4983230072969 + 3 ^ 40 * 2994186 * 2
def baseEnd_2994186 : Nat := 1024971057975418311469997

theorem tailTrace_2994186 : CollatzResearch.WordTrace tailWord_2994186 prefixEnd_2994186 1024971057975418311469997 := by
  unfold tailWord_2994186
  simp only [CollatzResearch.WordTrace]
  refine ⟨27301733782645740775490603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72804623420388642067974941 27301733782645740775490603)
  ·
    refine ⟨40952600673968611163235905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27301733782645740775490603 40952600673968611163235905)
    ·
      refine ⟨30714450505476458372426929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40952600673968611163235905 30714450505476458372426929)
      ·
        refine ⟨23035837879107343779320197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30714450505476458372426929 23035837879107343779320197)
        ·
          refine ⟨4319219602332626958622537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23035837879107343779320197 4319219602332626958622537)
          ·
            refine ⟨3239414701749470218966903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4319219602332626958622537 3239414701749470218966903)
            ·
              refine ⟨4859122052624205328450355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3239414701749470218966903 4859122052624205328450355)
              ·
                refine ⟨7288683078936307992675533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4859122052624205328450355 7288683078936307992675533)
                ·
                  refine ⟨2733256154601115497253325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7288683078936307992675533 2733256154601115497253325)
                  ·
                    refine ⟨1024971057975418311469997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2733256154601115497253325 1024971057975418311469997)
                    ·
                      rfl

theorem cell22_2994186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_2994186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994186 prefixEnd_2994186 := by exact prefixLift 2994186
  have htrace : WordTrace (prefixWord ++ tailWord_2994186) baseStart_2994186 baseEnd_2994186 := by
    simpa [prefixWord, tailWord_2994186, baseEnd_2994186] using wordTrace_append hprefix tailTrace_2994186
  have hstable : (prefixWord ++ tailWord_2994186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994186).length < 2 ^ (prefixWord ++ tailWord_2994186).sum := by decide
  have hdescent : baseEnd_2994186 < baseStart_2994186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994199 : List Nat := [1, 1, 3, 5, 2, 1, 1, 3, 5]
def baseStart_2994199 : Nat := 118140960795 + 2994199 * 2 ^ 59
def prefixEnd_2994199 : Nat := 4983230072969 + 3 ^ 40 * 2994199 * 2
def baseEnd_2994199 : Nat := 341658502713696870298319

theorem tailTrace_2994199 : CollatzResearch.WordTrace tailWord_2994199 prefixEnd_2994199 341658502713696870298319 := by
  unfold tailWord_2994199
  simp only [CollatzResearch.WordTrace]
  refine ⟨109207409279535866322185651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72804939519690577548123767 109207409279535866322185651)
  ·
    refine ⟨163811113919303799483278477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109207409279535866322185651 163811113919303799483278477)
    ·
      refine ⟨61429167719738924806229429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163811113919303799483278477 61429167719738924806229429)
      ·
        refine ⟨5758984473725524200584009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61429167719738924806229429 5758984473725524200584009)
        ·
          refine ⟨4319238355294143150438007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5758984473725524200584009 4319238355294143150438007)
          ·
            refine ⟨6478857532941214725657011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4319238355294143150438007 6478857532941214725657011)
            ·
              refine ⟨9718286299411822088485517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6478857532941214725657011 9718286299411822088485517)
              ·
                refine ⟨3644357362279433283182069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9718286299411822088485517 3644357362279433283182069)
                ·
                  refine ⟨341658502713696870298319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3644357362279433283182069 341658502713696870298319)
                  ·
                    rfl

theorem cell22_2994199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 5].length) (baseStart_2994199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994199 prefixEnd_2994199 := by exact prefixLift 2994199
  have htrace : WordTrace (prefixWord ++ tailWord_2994199) baseStart_2994199 baseEnd_2994199 := by
    simpa [prefixWord, tailWord_2994199, baseEnd_2994199] using wordTrace_append hprefix tailTrace_2994199
  have hstable : (prefixWord ++ tailWord_2994199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994199).length < 2 ^ (prefixWord ++ tailWord_2994199).sum := by decide
  have hdescent : baseEnd_2994199 < baseStart_2994199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994394 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 6, 3]
def baseStart_2994394 : Nat := 118140960795 + 2994394 * 2 ^ 59
def prefixEnd_2994394 : Nat := 4983230072969 + 3 ^ 40 * 2994394 * 2
def baseEnd_2994394 : Nat := 1025042260626175102269359

theorem tailTrace_2994394 : CollatzResearch.WordTrace tailWord_2994394 prefixEnd_2994394 1025042260626175102269359 := by
  unfold tailWord_2994394
  simp only [CollatzResearch.WordTrace]
  refine ⟨27303630378457353656383559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72809681009219609750356157 27303630378457353656383559)
  ·
    refine ⟨40955445567686030484575339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27303630378457353656383559 40955445567686030484575339)
    ·
      refine ⟨61433168351529045726863009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40955445567686030484575339 61433168351529045726863009)
      ·
        refine ⟨46074876263646784295147257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61433168351529045726863009 46074876263646784295147257)
        ·
          refine ⟨34556157197735088221360443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46074876263646784295147257 34556157197735088221360443)
          ·
            refine ⟨51834235796602632332040665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34556157197735088221360443 51834235796602632332040665)
            ·
              refine ⟨38875676847451974249030499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51834235796602632332040665 38875676847451974249030499)
              ·
                refine ⟨58313515271177961373545749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38875676847451974249030499 58313515271177961373545749)
                ·
                  refine ⟨2733446028336466939384957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58313515271177961373545749 2733446028336466939384957)
                  ·
                    refine ⟨1025042260626175102269359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2733446028336466939384957 1025042260626175102269359)
                    ·
                      rfl

theorem cell22_2994394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_2994394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994394 prefixEnd_2994394 := by exact prefixLift 2994394
  have htrace : WordTrace (prefixWord ++ tailWord_2994394) baseStart_2994394 baseEnd_2994394 := by
    simpa [prefixWord, tailWord_2994394, baseEnd_2994394] using wordTrace_append hprefix tailTrace_2994394
  have hstable : (prefixWord ++ tailWord_2994394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994394).length < 2 ^ (prefixWord ++ tailWord_2994394).sum := by decide
  have hdescent : baseEnd_2994394 < baseStart_2994394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994411 : List Nat := [1, 1, 1, 1, 2, 5, 4, 2, 2, 3]
def baseStart_2994411 : Nat := 118140960795 + 2994411 * 2 ^ 59
def prefixEnd_2994411 : Nat := 4983230072969 + 3 ^ 40 * 2994411 * 2
def baseEnd_2994411 : Nat := 1025048080073592724594307

theorem tailTrace_2994411 : CollatzResearch.WordTrace tailWord_2994411 prefixEnd_2994411 1025048080073592724594307 := by
  unfold tailWord_2994411
  simp only [CollatzResearch.WordTrace]
  refine ⟨109215141554767826528903087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72810094369845217685935391 109215141554767826528903087)
  ·
    refine ⟨163822712332151739793354631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109215141554767826528903087 163822712332151739793354631)
    ·
      refine ⟨245734068498227609690031947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163822712332151739793354631 245734068498227609690031947)
      ·
        refine ⟨368601102747341414535047921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245734068498227609690031947 368601102747341414535047921)
        ·
          refine ⟨276450827060506060901285941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368601102747341414535047921 276450827060506060901285941)
          ·
            refine ⟨25917265036922443209495557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 276450827060506060901285941 25917265036922443209495557)
            ·
              refine ⟨4859487194422958101780417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25917265036922443209495557 4859487194422958101780417)
              ·
                refine ⟨3644615395817218576335313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4859487194422958101780417 3644615395817218576335313)
                ·
                  refine ⟨2733461546862913932251485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3644615395817218576335313 2733461546862913932251485)
                  ·
                    refine ⟨1025048080073592724594307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2733461546862913932251485 1025048080073592724594307)
                    ·
                      rfl

theorem cell22_2994411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 3].length) (baseStart_2994411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994411 prefixEnd_2994411 := by exact prefixLift 2994411
  have htrace : WordTrace (prefixWord ++ tailWord_2994411) baseStart_2994411 baseEnd_2994411 := by
    simpa [prefixWord, tailWord_2994411, baseEnd_2994411] using wordTrace_append hprefix tailTrace_2994411
  have hstable : (prefixWord ++ tailWord_2994411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994411).length < 2 ^ (prefixWord ++ tailWord_2994411).sum := by decide
  have hdescent : baseEnd_2994411 < baseStart_2994411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994413 : List Nat := [1, 5, 1, 2, 3, 1, 1, 4, 4]
def baseStart_2994413 : Nat := 118140960795 + 2994413 * 2 ^ 59
def prefixEnd_2994413 : Nat := 4983230072969 + 3 ^ 40 * 2994413 * 2
def baseEnd_2994413 : Nat := 341682921571488462014767

theorem tailTrace_2994413 : CollatzResearch.WordTrace tailWord_2994413 prefixEnd_2994413 341682921571488462014767 := by
  unfold tailWord_2994413
  simp only [CollatzResearch.WordTrace]
  refine ⟨109215214500760580870475893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72810143000507053913650595 109215214500760580870475893)
  ·
    refine ⟨10238926359446304456607115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109215214500760580870475893 10238926359446304456607115)
    ·
      refine ⟨15358389539169456684910673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10238926359446304456607115 15358389539169456684910673)
      ·
        refine ⟨11518792154377092513683005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15358389539169456684910673 11518792154377092513683005)
        ·
          refine ⟨4319547057891409692631127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11518792154377092513683005 4319547057891409692631127)
          ·
            refine ⟨6479320586837114538946691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4319547057891409692631127 6479320586837114538946691)
            ·
              refine ⟨9718980880255671808420037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6479320586837114538946691 9718980880255671808420037)
              ·
                refine ⟨1822308915047938464078757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9718980880255671808420037 1822308915047938464078757)
                ·
                  refine ⟨341682921571488462014767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1822308915047938464078757 341682921571488462014767)
                  ·
                    rfl

theorem cell22_2994413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_2994413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994413 prefixEnd_2994413 := by exact prefixLift 2994413
  have htrace : WordTrace (prefixWord ++ tailWord_2994413) baseStart_2994413 baseEnd_2994413 := by
    simpa [prefixWord, tailWord_2994413, baseEnd_2994413] using wordTrace_append hprefix tailTrace_2994413
  have hstable : (prefixWord ++ tailWord_2994413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994413).length < 2 ^ (prefixWord ++ tailWord_2994413).sum := by decide
  have hdescent : baseEnd_2994413 < baseStart_2994413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994462 : List Nat := [4, 3, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_2994462 : Nat := 118140960795 + 2994462 * 2 ^ 59
def prefixEnd_2994462 : Nat := 4983230072969 + 3 ^ 40 * 2994462 * 2
def baseEnd_2994462 : Nat := 1025065538415845591569151

theorem tailTrace_2994462 : CollatzResearch.WordTrace tailWord_2994462 prefixEnd_2994462 1025065538415845591569151 := by
  unfold tailWord_2994462
  simp only [CollatzResearch.WordTrace]
  refine ⟨13652125209697882779876205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72811334451722041492673093 13652125209697882779876205)
  ·
    refine ⟨5119546953636706042453577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13652125209697882779876205 5119546953636706042453577)
    ·
      refine ⟨3839660215227529531840183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5119546953636706042453577 3839660215227529531840183)
      ·
        refine ⟨5759490322841294297760275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3839660215227529531840183 5759490322841294297760275)
        ·
          refine ⟨8639235484261941446640413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5759490322841294297760275 8639235484261941446640413)
          ·
            refine ⟨3239713306598228042490155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8639235484261941446640413 3239713306598228042490155)
            ·
              refine ⟨4859569959897342063735233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3239713306598228042490155 4859569959897342063735233)
              ·
                refine ⟨3644677469923006547801425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4859569959897342063735233 3644677469923006547801425)
                ·
                  refine ⟨2733508102442254910851069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3644677469923006547801425 2733508102442254910851069)
                  ·
                    refine ⟨1025065538415845591569151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2733508102442254910851069 1025065538415845591569151)
                    ·
                      rfl

theorem cell22_2994462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_2994462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994462 prefixEnd_2994462 := by exact prefixLift 2994462
  have htrace : WordTrace (prefixWord ++ tailWord_2994462) baseStart_2994462 baseEnd_2994462 := by
    simpa [prefixWord, tailWord_2994462, baseEnd_2994462] using wordTrace_append hprefix tailTrace_2994462
  have hstable : (prefixWord ++ tailWord_2994462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994462).length < 2 ^ (prefixWord ++ tailWord_2994462).sum := by decide
  have hdescent : baseEnd_2994462 < baseStart_2994462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994499 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 3, 4]
def baseStart_2994499 : Nat := 118140960795 + 2994499 * 2 ^ 59
def prefixEnd_2994499 : Nat := 4983230072969 + 3 ^ 40 * 2994499 * 2
def baseEnd_2994499 : Nat := 1025078204271989828394037

theorem tailTrace_2994499 : CollatzResearch.WordTrace tailWord_2994499 prefixEnd_2994499 1025078204271989828394037 := by
  unfold tailWord_2994499
  simp only [CollatzResearch.WordTrace]
  refine ⟨109218351178449017558106551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72812234118966011705404367 109218351178449017558106551)
  ·
    refine ⟨163827526767673526337159827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109218351178449017558106551 163827526767673526337159827)
    ·
      refine ⟨245741290151510289505739741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163827526767673526337159827 245741290151510289505739741)
      ·
        refine ⟨92152983806816358564652403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245741290151510289505739741 92152983806816358564652403)
        ·
          refine ⟨138229475710224537846978605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92152983806816358564652403 138229475710224537846978605)
          ·
            refine ⟨51836053391334201692616977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138229475710224537846978605 51836053391334201692616977)
            ·
              refine ⟨38877040043500651269462733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51836053391334201692616977 38877040043500651269462733)
              ·
                refine ⟨14578890016312744226048525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38877040043500651269462733 14578890016312744226048525)
                ·
                  refine ⟨5467083756117279084768197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14578890016312744226048525 5467083756117279084768197)
                  ·
                    refine ⟨1025078204271989828394037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5467083756117279084768197 1025078204271989828394037)
                    ·
                      rfl

theorem cell22_2994499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 4].length) (baseStart_2994499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994499 prefixEnd_2994499 := by exact prefixLift 2994499
  have htrace : WordTrace (prefixWord ++ tailWord_2994499) baseStart_2994499 baseEnd_2994499 := by
    simpa [prefixWord, tailWord_2994499, baseEnd_2994499] using wordTrace_append hprefix tailTrace_2994499
  have hstable : (prefixWord ++ tailWord_2994499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994499).length < 2 ^ (prefixWord ++ tailWord_2994499).sum := by decide
  have hdescent : baseEnd_2994499 < baseStart_2994499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994514 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 8]
def baseStart_2994514 : Nat := 118140960795 + 2994514 * 2 ^ 59
def prefixEnd_2994514 : Nat := 4983230072969 + 3 ^ 40 * 2994514 * 2
def baseEnd_2994514 : Nat := 341694446359511596422997

theorem tailTrace_2994514 : CollatzResearch.WordTrace tailWord_2994514 prefixEnd_2994514 341694446359511596422997 := by
  unfold tailWord_2994514
  simp only [CollatzResearch.WordTrace]
  refine ⟨27304724568348668779975649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72812598848929783413268397 27304724568348668779975649)
  ·
    refine ⟨20478543426261501584981737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27304724568348668779975649 20478543426261501584981737)
    ·
      refine ⟨15358907569696126188736303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20478543426261501584981737 15358907569696126188736303)
      ·
        refine ⟨23038361354544189283104455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15358907569696126188736303 23038361354544189283104455)
        ·
          refine ⟨34557542031816283924656683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23038361354544189283104455 34557542031816283924656683)
          ·
            refine ⟨51836313047724425886985025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34557542031816283924656683 51836313047724425886985025)
            ·
              refine ⟨38877234785793319415238769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51836313047724425886985025 38877234785793319415238769)
              ·
                refine ⟨29157926089344989561429077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38877234785793319415238769 29157926089344989561429077)
                ·
                  refine ⟨341694446359511596422997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29157926089344989561429077 341694446359511596422997)
                  ·
                    rfl

theorem cell22_2994514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_2994514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994514 prefixEnd_2994514 := by exact prefixLift 2994514
  have htrace : WordTrace (prefixWord ++ tailWord_2994514) baseStart_2994514 baseEnd_2994514 := by
    simpa [prefixWord, tailWord_2994514, baseEnd_2994514] using wordTrace_append hprefix tailTrace_2994514
  have hstable : (prefixWord ++ tailWord_2994514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994514).length < 2 ^ (prefixWord ++ tailWord_2994514).sum := by decide
  have hdescent : baseEnd_2994514 < baseStart_2994514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994524 : List Nat := [2, 2, 4, 3, 1, 1, 3, 2, 1, 3]
def baseStart_2994524 : Nat := 118140960795 + 2994524 * 2 ^ 59
def prefixEnd_2994524 : Nat := 4983230072969 + 3 ^ 40 * 2994524 * 2
def baseEnd_2994524 : Nat := 1025086762282898096518961

theorem tailTrace_2994524 : CollatzResearch.WordTrace tailWord_2994524 prefixEnd_2994524 1025086762282898096518961 := by
  unfold tailWord_2994524
  simp only [CollatzResearch.WordTrace]
  refine ⟨54609631501679223413883313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72812842002238964551844417 54609631501679223413883313)
  ·
    refine ⟨40957223626259417560412485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54609631501679223413883313 40957223626259417560412485)
    ·
      refine ⟨7679479429923640792577341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40957223626259417560412485 7679479429923640792577341)
      ·
        refine ⟨2879804786221365297216503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7679479429923640792577341 2879804786221365297216503)
        ·
          refine ⟨4319707179332047945824755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2879804786221365297216503 4319707179332047945824755)
          ·
            refine ⟨6479560768998071918737133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4319707179332047945824755 6479560768998071918737133)
            ·
              refine ⟨2429835288374276969526425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6479560768998071918737133 2429835288374276969526425)
              ·
                refine ⟨1822376466280707727144819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2429835288374276969526425 1822376466280707727144819)
                ·
                  refine ⟨2733564699421061590717229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1822376466280707727144819 2733564699421061590717229)
                  ·
                    refine ⟨1025086762282898096518961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2733564699421061590717229 1025086762282898096518961)
                    ·
                      rfl

theorem cell22_2994524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_2994524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994524 prefixEnd_2994524 := by exact prefixLift 2994524
  have htrace : WordTrace (prefixWord ++ tailWord_2994524) baseStart_2994524 baseEnd_2994524 := by
    simpa [prefixWord, tailWord_2994524, baseEnd_2994524] using wordTrace_append hprefix tailTrace_2994524
  have hstable : (prefixWord ++ tailWord_2994524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994524).length < 2 ^ (prefixWord ++ tailWord_2994524).sum := by decide
  have hdescent : baseEnd_2994524 < baseStart_2994524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994550 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_2994550 : Nat := 118140960795 + 2994550 * 2 ^ 59
def prefixEnd_2994550 : Nat := 4983230072969 + 3 ^ 40 * 2994550 * 2
def baseEnd_2994550 : Nat := 1025095662614242695368881

theorem tailTrace_2994550 : CollatzResearch.WordTrace tailWord_2994550 prefixEnd_2994550 1025095662614242695368881 := by
  unfold tailWord_2994550
  simp only [CollatzResearch.WordTrace]
  refine ⟨6826263206329015829263319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72813474200842835512142069 6826263206329015829263319)
  ·
    refine ⟨10239394809493523743894979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6826263206329015829263319 10239394809493523743894979)
    ·
      refine ⟨15359092214240285615842469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10239394809493523743894979 15359092214240285615842469)
      ·
        refine ⟨2879829790170053552970463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15359092214240285615842469 2879829790170053552970463)
        ·
          refine ⟨4319744685255080329455695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2879829790170053552970463 4319744685255080329455695)
          ·
            refine ⟨6479617027882620494183543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4319744685255080329455695 6479617027882620494183543)
            ·
              refine ⟨9719425541823930741275315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6479617027882620494183543 9719425541823930741275315)
              ·
                refine ⟨14579138312735896111912973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9719425541823930741275315 14579138312735896111912973)
                ·
                  refine ⟨5467176867275961041967365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14579138312735896111912973 5467176867275961041967365)
                  ·
                    refine ⟨1025095662614242695368881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5467176867275961041967365 1025095662614242695368881)
                    ·
                      rfl

theorem cell22_2994550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_2994550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994550 prefixEnd_2994550 := by exact prefixLift 2994550
  have htrace : WordTrace (prefixWord ++ tailWord_2994550) baseStart_2994550 baseEnd_2994550 := by
    simpa [prefixWord, tailWord_2994550, baseEnd_2994550] using wordTrace_append hprefix tailTrace_2994550
  have hstable : (prefixWord ++ tailWord_2994550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994550).length < 2 ^ (prefixWord ++ tailWord_2994550).sum := by decide
  have hdescent : baseEnd_2994550 < baseStart_2994550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994604 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 9]
def baseStart_2994604 : Nat := 118140960795 + 2994604 * 2 ^ 59
def prefixEnd_2994604 : Nat := 4983230072969 + 3 ^ 40 * 2994604 * 2
def baseEnd_2994604 : Nat := 341704715972601518172905

theorem tailTrace_2994604 : CollatzResearch.WordTrace tailWord_2994604 prefixEnd_2994604 341704715972601518172905 := by
  unfold tailWord_2994604
  simp only [CollatzResearch.WordTrace]
  refine ⟨54611090421534310245339433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72814787228712413660452577 54611090421534310245339433)
  ·
    refine ⟨40958317816150732684004575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54611090421534310245339433 40958317816150732684004575)
    ·
      refine ⟨61437476724226099026006863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40958317816150732684004575 61437476724226099026006863)
      ·
        refine ⟨92156215086339148539010295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61437476724226099026006863 92156215086339148539010295)
        ·
          refine ⟨138234322629508722808515443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92156215086339148539010295 138234322629508722808515443)
          ·
            refine ⟨207351483944263084212773165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138234322629508722808515443 207351483944263084212773165)
            ·
              refine ⟨77756806479098656579789937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207351483944263084212773165 77756806479098656579789937)
              ·
                refine ⟨58317604859323992434842453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77756806479098656579789937 58317604859323992434842453)
                ·
                  refine ⟨341704715972601518172905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58317604859323992434842453 341704715972601518172905)
                  ·
                    rfl

theorem cell22_2994604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_2994604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994604 prefixEnd_2994604 := by exact prefixLift 2994604
  have htrace : WordTrace (prefixWord ++ tailWord_2994604) baseStart_2994604 baseEnd_2994604 := by
    simpa [prefixWord, tailWord_2994604, baseEnd_2994604] using wordTrace_append hprefix tailTrace_2994604
  have hstable : (prefixWord ++ tailWord_2994604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994604).length < 2 ^ (prefixWord ++ tailWord_2994604).sum := by decide
  have hdescent : baseEnd_2994604 < baseStart_2994604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994642 : List Nat := [3, 2, 2, 4, 1, 1, 2, 1, 3, 3]
def baseStart_2994642 : Nat := 118140960795 + 2994642 * 2 ^ 59
def prefixEnd_2994642 : Nat := 4983230072969 + 3 ^ 40 * 2994642 * 2
def baseEnd_2994642 : Nat := 1025127156094385122068599

theorem tailTrace_2994642 : CollatzResearch.WordTrace tailWord_2994642 prefixEnd_2994642 1025127156094385122068599 := by
  unfold tailWord_2994642
  simp only [CollatzResearch.WordTrace]
  refine ⟨27305891704232738245140545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72815711211287301987041453 27305891704232738245140545)
  ·
    refine ⟨20479418778174553683855409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27305891704232738245140545 20479418778174553683855409)
    ·
      refine ⟨15359564083630915262891557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20479418778174553683855409 15359564083630915262891557)
      ·
        refine ⟨2879918265680796611792167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15359564083630915262891557 2879918265680796611792167)
        ·
          refine ⟨4319877398521194917688251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2879918265680796611792167 4319877398521194917688251)
          ·
            refine ⟨6479816097781792376532377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4319877398521194917688251 6479816097781792376532377)
            ·
              refine ⟨4859862073336344282399283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6479816097781792376532377 4859862073336344282399283)
              ·
                refine ⟨7289793110004516423598925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4859862073336344282399283 7289793110004516423598925)
                ·
                  refine ⟨2733672416251693658849597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7289793110004516423598925 2733672416251693658849597)
                  ·
                    refine ⟨1025127156094385122068599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2733672416251693658849597 1025127156094385122068599)
                    ·
                      rfl

theorem cell22_2994642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_2994642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994642 prefixEnd_2994642 := by exact prefixLift 2994642
  have htrace : WordTrace (prefixWord ++ tailWord_2994642) baseStart_2994642 baseEnd_2994642 := by
    simpa [prefixWord, tailWord_2994642, baseEnd_2994642] using wordTrace_append hprefix tailTrace_2994642
  have hstable : (prefixWord ++ tailWord_2994642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994642).length < 2 ^ (prefixWord ++ tailWord_2994642).sum := by decide
  have hdescent : baseEnd_2994642 < baseStart_2994642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994668 : List Nat := [2, 2, 1, 1, 2, 1, 6, 2, 1, 4]
def baseStart_2994668 : Nat := 118140960795 + 2994668 * 2 ^ 59
def prefixEnd_2994668 : Nat := 4983230072969 + 3 ^ 40 * 2994668 * 2
def baseEnd_2994668 : Nat := 1025136056425729720918519

theorem tailTrace_2994668 : CollatzResearch.WordTrace tailWord_2994668 prefixEnd_2994668 1025136056425729720918519 := by
  unfold tailWord_2994668
  simp only [CollatzResearch.WordTrace]
  refine ⟨54612257557418379710504329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72816343409891172947339105 54612257557418379710504329)
  ·
    refine ⟨40959193168063784782878247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54612257557418379710504329 40959193168063784782878247)
    ·
      refine ⟨61438789752095677174317371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40959193168063784782878247 61438789752095677174317371)
      ·
        refine ⟨92158184628143515761476057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61438789752095677174317371 92158184628143515761476057)
        ·
          refine ⟨69118638471107636821107043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92158184628143515761476057 69118638471107636821107043)
          ·
            refine ⟨103677957706661455231660565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69118638471107636821107043 103677957706661455231660565)
            ·
              refine ⟨4859904267499755713984089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 103677957706661455231660565 4859904267499755713984089)
              ·
                refine ⟨3644928200624816785488067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4859904267499755713984089 3644928200624816785488067)
                ·
                  refine ⟨5467392300937225178232101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3644928200624816785488067 5467392300937225178232101)
                  ·
                    refine ⟨1025136056425729720918519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5467392300937225178232101 1025136056425729720918519)
                    ·
                      rfl

theorem cell22_2994668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_2994668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994668 prefixEnd_2994668 := by exact prefixLift 2994668
  have htrace : WordTrace (prefixWord ++ tailWord_2994668) baseStart_2994668 baseEnd_2994668 := by
    simpa [prefixWord, tailWord_2994668, baseEnd_2994668] using wordTrace_append hprefix tailTrace_2994668
  have hstable : (prefixWord ++ tailWord_2994668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994668).length < 2 ^ (prefixWord ++ tailWord_2994668).sum := by decide
  have hdescent : baseEnd_2994668 < baseStart_2994668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994681 : List Nat := [1, 2, 1, 3, 1, 2, 2, 4, 1, 5]
def baseStart_2994681 : Nat := 118140960795 + 2994681 * 2 ^ 59
def prefixEnd_2994681 : Nat := 4983230072969 + 3 ^ 40 * 2994681 * 2
def baseEnd_2994681 : Nat := 1025140506591402020343479

theorem tailTrace_2994681 : CollatzResearch.WordTrace tailWord_2994681 prefixEnd_2994681 1025140506591402020343479 := by
  unfold tailWord_2994681
  simp only [CollatzResearch.WordTrace]
  refine ⟨109224989263789662641231897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72816659509193108427487931 109224989263789662641231897)
  ·
    refine ⟨81918741947842246980923923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109224989263789662641231897 81918741947842246980923923)
    ·
      refine ⟨122878112921763370471385885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81918741947842246980923923 122878112921763370471385885)
      ·
        refine ⟨46079292345661263926769707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122878112921763370471385885 46079292345661263926769707)
        ·
          refine ⟨69118938518491895890154561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46079292345661263926769707 69118938518491895890154561)
          ·
            refine ⟨51839203888868921917615921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69118938518491895890154561 51839203888868921917615921)
            ·
              refine ⟨38879402916651691438211941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51839203888868921917615921 38879402916651691438211941)
              ·
                refine ⟨7289888046872192144664739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38879402916651691438211941 7289888046872192144664739)
                ·
                  refine ⟨10934832070308288216997109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7289888046872192144664739 10934832070308288216997109)
                  ·
                    refine ⟨1025140506591402020343479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10934832070308288216997109 1025140506591402020343479)
                    ·
                      rfl

theorem cell22_2994681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_2994681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994681 prefixEnd_2994681 := by exact prefixLift 2994681
  have htrace : WordTrace (prefixWord ++ tailWord_2994681) baseStart_2994681 baseEnd_2994681 := by
    simpa [prefixWord, tailWord_2994681, baseEnd_2994681] using wordTrace_append hprefix tailTrace_2994681
  have hstable : (prefixWord ++ tailWord_2994681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994681).length < 2 ^ (prefixWord ++ tailWord_2994681).sum := by decide
  have hdescent : baseEnd_2994681 < baseStart_2994681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994698 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 4, 3]
def baseStart_2994698 : Nat := 118140960795 + 2994698 * 2 ^ 59
def prefixEnd_2994698 : Nat := 4983230072969 + 3 ^ 40 * 2994698 * 2
def baseEnd_2994698 : Nat := 1025146326038819642668427

theorem tailTrace_2994698 : CollatzResearch.WordTrace tailWord_2994698 prefixEnd_2994698 1025146326038819642668427 := by
  unfold tailWord_2994698
  simp only [CollatzResearch.WordTrace]
  refine ⟨27306402326182018636150187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72817072869818716363067165 27306402326182018636150187)
  ·
    refine ⟨40959603489273027954225281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27306402326182018636150187 40959603489273027954225281)
    ·
      refine ⟨30719702616954770965668961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40959603489273027954225281 30719702616954770965668961)
      ·
        refine ⟨23039776962716078224251721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30719702616954770965668961 23039776962716078224251721)
        ·
          refine ⟨17279832722037058668188791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23039776962716078224251721 17279832722037058668188791)
          ·
            refine ⟨25919749083055588002283187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17279832722037058668188791 25919749083055588002283187)
            ·
              refine ⟨38879623624583382003424781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25919749083055588002283187 38879623624583382003424781)
              ·
                refine ⟨14579858859218768251284293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38879623624583382003424781 14579858859218768251284293)
                ·
                  refine ⟨2733723536103519047115805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14579858859218768251284293 2733723536103519047115805)
                  ·
                    refine ⟨1025146326038819642668427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2733723536103519047115805 1025146326038819642668427)
                    ·
                      rfl

theorem cell22_2994698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_2994698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994698 prefixEnd_2994698 := by exact prefixLift 2994698
  have htrace : WordTrace (prefixWord ++ tailWord_2994698) baseStart_2994698 baseEnd_2994698 := by
    simpa [prefixWord, tailWord_2994698, baseEnd_2994698] using wordTrace_append hprefix tailTrace_2994698
  have hstable : (prefixWord ++ tailWord_2994698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994698).length < 2 ^ (prefixWord ++ tailWord_2994698).sum := by decide
  have hdescent : baseEnd_2994698 < baseStart_2994698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994728 : List Nat := [2, 1, 5, 2, 1, 1, 2, 8]
def baseStart_2994728 : Nat := 118140960795 + 2994728 * 2 ^ 59
def prefixEnd_2994728 : Nat := 4983230072969 + 3 ^ 40 * 2994728 * 2
def baseEnd_2994728 : Nat := 113906288405767729379815

theorem tailTrace_2994728 : CollatzResearch.WordTrace tailWord_2994728 prefixEnd_2994728 113906288405767729379815 := by
  unfold tailWord_2994728
  simp only [CollatzResearch.WordTrace]
  refine ⟨54613351747309694834096419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72817802329746259778795225 54613351747309694834096419)
  ·
    refine ⟨81920027620964542251144629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54613351747309694834096419 81920027620964542251144629)
    ·
      refine ⟨7680002589465425836044809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81920027620964542251144629 7680002589465425836044809)
      ·
        refine ⟨5760001942099069377033607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7680002589465425836044809 5760001942099069377033607)
        ·
          refine ⟨8640002913148604065550411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5760001942099069377033607 8640002913148604065550411)
          ·
            refine ⟨12960004369722906098325617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8640002913148604065550411 12960004369722906098325617)
            ·
              refine ⟨9720003277292179573744213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12960004369722906098325617 9720003277292179573744213)
              ·
                refine ⟨113906288405767729379815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9720003277292179573744213 113906288405767729379815)
                ·
                  rfl

theorem cell22_2994728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 8].length) (baseStart_2994728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994728 prefixEnd_2994728 := by exact prefixLift 2994728
  have htrace : WordTrace (prefixWord ++ tailWord_2994728) baseStart_2994728 baseEnd_2994728 := by
    simpa [prefixWord, tailWord_2994728, baseEnd_2994728] using wordTrace_append hprefix tailTrace_2994728
  have hstable : (prefixWord ++ tailWord_2994728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994728).length < 2 ^ (prefixWord ++ tailWord_2994728).sum := by decide
  have hdescent : baseEnd_2994728 < baseStart_2994728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994730 : List Nat := [3, 1, 4, 1, 1, 3, 2, 1, 2, 4]
def baseStart_2994730 : Nat := 118140960795 + 2994730 * 2 ^ 59
def prefixEnd_2994730 : Nat := 4983230072969 + 3 ^ 40 * 2994730 * 2
def baseEnd_2994730 : Nat := 1025157280292782225868329

theorem tailTrace_2994730 : CollatzResearch.WordTrace tailWord_2994730 prefixEnd_2994730 1025157280292782225868329 := by
  unfold tailWord_2994730
  simp only [CollatzResearch.WordTrace]
  refine ⟨27306694110153036002441411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72817850960408096006510429 27306694110153036002441411)
  ·
    refine ⟨40960041165229554003662117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27306694110153036002441411 40960041165229554003662117)
    ·
      refine ⟨7680007718480541375686647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40960041165229554003662117 7680007718480541375686647)
      ·
        refine ⟨11520011577720812063529971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7680007718480541375686647 11520011577720812063529971)
        ·
          refine ⟨17280017366581218095294957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11520011577720812063529971 17280017366581218095294957)
          ·
            refine ⟨6480006512467956785735609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17280017366581218095294957 6480006512467956785735609)
            ·
              refine ⟨4860004884350967589301707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6480006512467956785735609 4860004884350967589301707)
              ·
                refine ⟨7290007326526451383952561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4860004884350967589301707 7290007326526451383952561)
                ·
                  refine ⟨5467505494894838537964421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7290007326526451383952561 5467505494894838537964421)
                  ·
                    refine ⟨1025157280292782225868329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5467505494894838537964421 1025157280292782225868329)
                    ·
                      rfl

theorem cell22_2994730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_2994730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994730 prefixEnd_2994730 := by exact prefixLift 2994730
  have htrace : WordTrace (prefixWord ++ tailWord_2994730) baseStart_2994730 baseEnd_2994730 := by
    simpa [prefixWord, tailWord_2994730, baseEnd_2994730] using wordTrace_append hprefix tailTrace_2994730
  have hstable : (prefixWord ++ tailWord_2994730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994730).length < 2 ^ (prefixWord ++ tailWord_2994730).sum := by decide
  have hdescent : baseEnd_2994730 < baseStart_2994730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994773 : List Nat := [1, 3, 2, 2, 1, 1, 4, 3, 5]
def baseStart_2994773 : Nat := 118140960795 + 2994773 * 2 ^ 59
def prefixEnd_2994773 : Nat := 4983230072969 + 3 ^ 40 * 2994773 * 2
def baseEnd_2994773 : Nat := 341724000023848149014399

theorem tailTrace_2994773 : CollatzResearch.WordTrace tailWord_2994773 prefixEnd_2994773 341724000023848149014399 := by
  unfold tailWord_2994773
  simp only [CollatzResearch.WordTrace]
  refine ⟨109228344779456362353580973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72818896519637574902387315 109228344779456362353580973)
  ·
    refine ⟨40960629292296135882592865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109228344779456362353580973 40960629292296135882592865)
    ·
      refine ⟨30720471969222101911944649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40960629292296135882592865 30720471969222101911944649)
      ·
        refine ⟨23040353976916576433958487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30720471969222101911944649 23040353976916576433958487)
        ·
          refine ⟨34560530965374864650937731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23040353976916576433958487 34560530965374864650937731)
          ·
            refine ⟨51840796448062296976406597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34560530965374864650937731 51840796448062296976406597)
            ·
              refine ⟨9720149334011680683076237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51840796448062296976406597 9720149334011680683076237)
              ·
                refine ⟨3645056000254380256153589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9720149334011680683076237 3645056000254380256153589)
                ·
                  refine ⟨341724000023848149014399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3645056000254380256153589 341724000023848149014399)
                  ·
                    rfl

theorem cell22_2994773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_2994773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994773 prefixEnd_2994773 := by exact prefixLift 2994773
  have htrace : WordTrace (prefixWord ++ tailWord_2994773) baseStart_2994773 baseEnd_2994773 := by
    simpa [prefixWord, tailWord_2994773, baseEnd_2994773] using wordTrace_append hprefix tailTrace_2994773
  have hstable : (prefixWord ++ tailWord_2994773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994773).length < 2 ^ (prefixWord ++ tailWord_2994773).sum := by decide
  have hdescent : baseEnd_2994773 < baseStart_2994773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994863 : List Nat := [1, 1, 2, 1, 2, 7, 8]
def baseStart_2994863 : Nat := 118140960795 + 2994863 * 2 ^ 59
def prefixEnd_2994863 : Nat := 4983230072969 + 3 ^ 40 * 2994863 * 2
def baseEnd_2994863 : Nat := 37970474404104230084923

theorem tailTrace_2994863 : CollatzResearch.WordTrace tailWord_2994863 prefixEnd_2994863 37970474404104230084923 := by
  unfold tailWord_2994863
  simp only [CollatzResearch.WordTrace]
  refine ⟨109231627349130307724357243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72821084899420205149571495 109231627349130307724357243)
  ·
    refine ⟨163847441023695461586535865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109231627349130307724357243 163847441023695461586535865)
    ·
      refine ⟨122885580767771596189901899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163847441023695461586535865 122885580767771596189901899)
      ·
        refine ⟨184328371151657394284852849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122885580767771596189901899 184328371151657394284852849)
        ·
          refine ⟨138246278363743045713639637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184328371151657394284852849 138246278363743045713639637)
          ·
            refine ⟨3240147149150227633913429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 138246278363743045713639637 3240147149150227633913429)
            ·
              refine ⟨37970474404104230084923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3240147149150227633913429 37970474404104230084923)
              ·
                rfl

theorem cell22_2994863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 8].length) (baseStart_2994863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994863 prefixEnd_2994863 := by exact prefixLift 2994863
  have htrace : WordTrace (prefixWord ++ tailWord_2994863) baseStart_2994863 baseEnd_2994863 := by
    simpa [prefixWord, tailWord_2994863, baseEnd_2994863] using wordTrace_append hprefix tailTrace_2994863
  have hstable : (prefixWord ++ tailWord_2994863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994863).length < 2 ^ (prefixWord ++ tailWord_2994863).sum := by decide
  have hdescent : baseEnd_2994863 < baseStart_2994863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994869 : List Nat := [1, 3, 3, 3, 1, 2, 3, 2, 4]
def baseStart_2994869 : Nat := 118140960795 + 2994869 * 2 ^ 59
def prefixEnd_2994869 : Nat := 4983230072969 + 3 ^ 40 * 2994869 * 2
def baseEnd_2994869 : Nat := 341734954277810732214301

theorem tailTrace_2994869 : CollatzResearch.WordTrace tailWord_2994869 prefixEnd_2994869 341734954277810732214301 := by
  unfold tailWord_2994869
  simp only [CollatzResearch.WordTrace]
  refine ⟨109231846187108570749075661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72821230791405713832717107 109231846187108570749075661)
  ·
    refine ⟨40961942320165714030903373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109231846187108570749075661 40961942320165714030903373)
    ·
      refine ⟨15360728370062142761588765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40961942320165714030903373 15360728370062142761588765)
      ·
        refine ⟨5760273138773303535595787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15360728370062142761588765 5760273138773303535595787)
        ·
          refine ⟨8640409708159955303393681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5760273138773303535595787 8640409708159955303393681)
          ·
            refine ⟨6480307281119966477545261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8640409708159955303393681 6480307281119966477545261)
            ·
              refine ⟨2430115230419987429079473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6480307281119966477545261 2430115230419987429079473)
              ·
                refine ⟨1822586422814990571809605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2430115230419987429079473 1822586422814990571809605)
                ·
                  refine ⟨341734954277810732214301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1822586422814990571809605 341734954277810732214301)
                  ·
                    rfl

theorem cell22_2994869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_2994869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994869 prefixEnd_2994869 := by exact prefixLift 2994869
  have htrace : WordTrace (prefixWord ++ tailWord_2994869) baseStart_2994869 baseEnd_2994869 := by
    simpa [prefixWord, tailWord_2994869, baseEnd_2994869] using wordTrace_append hprefix tailTrace_2994869
  have hstable : (prefixWord ++ tailWord_2994869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994869).length < 2 ^ (prefixWord ++ tailWord_2994869).sum := by decide
  have hdescent : baseEnd_2994869 < baseStart_2994869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994884 : List Nat := [2, 3, 3, 1, 1, 2, 4, 1, 2, 3]
def baseStart_2994884 : Nat := 118140960795 + 2994884 * 2 ^ 59
def prefixEnd_2994884 : Nat := 4983230072969 + 3 ^ 40 * 2994884 * 2
def baseEnd_2994884 : Nat := 1025209997639977157517857

theorem tailTrace_2994884 : CollatzResearch.WordTrace tailWord_2994884 prefixEnd_2994884 1025209997639977157517857 := by
  unfold tailWord_2994884
  simp only [CollatzResearch.WordTrace]
  refine ⟨54616196641027114155435853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72821595521369485540581137 54616196641027114155435853)
  ·
    refine ⟨20481073740385167808288445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54616196641027114155435853 20481073740385167808288445)
    ·
      refine ⟨7680402652644437928108167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20481073740385167808288445 7680402652644437928108167)
      ·
        refine ⟨11520603978966656892162251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7680402652644437928108167 11520603978966656892162251)
        ·
          refine ⟨17280905968449985338243377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11520603978966656892162251 17280905968449985338243377)
          ·
            refine ⟨12960679476337489003682533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17280905968449985338243377 12960679476337489003682533)
            ·
              refine ⟨2430127401813279188190475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12960679476337489003682533 2430127401813279188190475)
              ·
                refine ⟨3645191102719918782285713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2430127401813279188190475 3645191102719918782285713)
                ·
                  refine ⟨2733893327039939086714285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3645191102719918782285713 2733893327039939086714285)
                  ·
                    refine ⟨1025209997639977157517857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2733893327039939086714285 1025209997639977157517857)
                    ·
                      rfl

theorem cell22_2994884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_2994884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994884 prefixEnd_2994884 := by exact prefixLift 2994884
  have htrace : WordTrace (prefixWord ++ tailWord_2994884) baseStart_2994884 baseEnd_2994884 := by
    simpa [prefixWord, tailWord_2994884, baseEnd_2994884] using wordTrace_append hprefix tailTrace_2994884
  have hstable : (prefixWord ++ tailWord_2994884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994884).length < 2 ^ (prefixWord ++ tailWord_2994884).sum := by decide
  have hdescent : baseEnd_2994884 < baseStart_2994884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994912 : List Nat := [2, 1, 1, 3, 1, 2, 1, 7, 1, 3]
def baseStart_2994912 : Nat := 118140960795 + 2994912 * 2 ^ 59
def prefixEnd_2994912 : Nat := 4983230072969 + 3 ^ 40 * 2994912 * 2
def baseEnd_2994912 : Nat := 1025219582612194417817771

theorem tailTrace_2994912 : CollatzResearch.WordTrace tailWord_2994912 prefixEnd_2994912 1025219582612194417817771 := by
  unfold tailWord_2994912
  simp only [CollatzResearch.WordTrace]
  refine ⟨54616707262976394546445495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72822276350635192728593993 54616707262976394546445495)
  ·
    refine ⟨81925060894464591819668243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54616707262976394546445495 81925060894464591819668243)
    ·
      refine ⟨122887591341696887729502365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81925060894464591819668243 122887591341696887729502365)
      ·
        refine ⟨46082846753136332898563387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122887591341696887729502365 46082846753136332898563387)
        ·
          refine ⟨69124270129704499347845081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46082846753136332898563387 69124270129704499347845081)
          ·
            refine ⟨51843202597278374510883811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69124270129704499347845081 51843202597278374510883811)
            ·
              refine ⟨77764803895917561766325717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51843202597278374510883811 77764803895917561766325717)
              ·
                refine ⟨1822612591310567853898259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 77764803895917561766325717 1822612591310567853898259)
                ·
                  refine ⟨2733918886965851780847389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1822612591310567853898259 2733918886965851780847389)
                  ·
                    refine ⟨1025219582612194417817771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2733918886965851780847389 1025219582612194417817771)
                    ·
                      rfl

theorem cell22_2994912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 1, 3].length) (baseStart_2994912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994912 prefixEnd_2994912 := by exact prefixLift 2994912
  have htrace : WordTrace (prefixWord ++ tailWord_2994912) baseStart_2994912 baseEnd_2994912 := by
    simpa [prefixWord, tailWord_2994912, baseEnd_2994912] using wordTrace_append hprefix tailTrace_2994912
  have hstable : (prefixWord ++ tailWord_2994912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994912).length < 2 ^ (prefixWord ++ tailWord_2994912).sum := by decide
  have hdescent : baseEnd_2994912 < baseStart_2994912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994923 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 2, 5]
def baseStart_2994923 : Nat := 118140960795 + 2994923 * 2 ^ 59
def prefixEnd_2994923 : Nat := 4983230072969 + 3 ^ 40 * 2994923 * 2
def baseEnd_2994923 : Nat := 1025223348136994055792737

theorem tailTrace_2994923 : CollatzResearch.WordTrace tailWord_2994923 prefixEnd_2994923 1025223348136994055792737 := by
  unfold tailWord_2994923
  simp only [CollatzResearch.WordTrace]
  refine ⟨109233815728912937971541423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72822543819275291981027615 109233815728912937971541423)
  ·
    refine ⟨163850723593369406957312135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109233815728912937971541423 163850723593369406957312135)
    ·
      refine ⟨245776085390054110435968203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163850723593369406957312135 245776085390054110435968203)
      ·
        refine ⟨368664128085081165653952305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245776085390054110435968203 368664128085081165653952305)
        ·
          refine ⟨276498096063810874240464229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368664128085081165653952305 276498096063810874240464229)
          ·
            refine ⟨51843393011964538920087043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 276498096063810874240464229 51843393011964538920087043)
            ·
              refine ⟨77765089517946808380130565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51843393011964538920087043 77765089517946808380130565)
              ·
                refine ⟨14580954284615026571274481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77765089517946808380130565 14580954284615026571274481)
                ·
                  refine ⟨10935715713461269928455861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14580954284615026571274481 10935715713461269928455861)
                  ·
                    refine ⟨1025223348136994055792737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10935715713461269928455861 1025223348136994055792737)
                    ·
                      rfl

theorem cell22_2994923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 5].length) (baseStart_2994923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994923 prefixEnd_2994923 := by exact prefixLift 2994923
  have htrace : WordTrace (prefixWord ++ tailWord_2994923) baseStart_2994923 baseEnd_2994923 := by
    simpa [prefixWord, tailWord_2994923, baseEnd_2994923] using wordTrace_append hprefix tailTrace_2994923
  have hstable : (prefixWord ++ tailWord_2994923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994923).length < 2 ^ (prefixWord ++ tailWord_2994923).sum := by decide
  have hdescent : baseEnd_2994923 < baseStart_2994923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994940 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 2, 5]
def baseStart_2994940 : Nat := 118140960795 + 2994940 * 2 ^ 59
def prefixEnd_2994940 : Nat := 4983230072969 + 3 ^ 40 * 2994940 * 2
def baseEnd_2994940 : Nat := 1025229167584411678117685

theorem tailTrace_2994940 : CollatzResearch.WordTrace tailWord_2994940 prefixEnd_2994940 1025229167584411678117685 := by
  unfold tailWord_2994940
  simp only [CollatzResearch.WordTrace]
  refine ⟨54617217884925674937455137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72822957179900899916606849 54617217884925674937455137)
  ·
    refine ⟨40962913413694256203091353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54617217884925674937455137 40962913413694256203091353)
    ·
      refine ⟨30722185060270692152318515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40962913413694256203091353 30722185060270692152318515)
      ·
        refine ⟨46083277590406038228477773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30722185060270692152318515 46083277590406038228477773)
        ·
          refine ⟨17281229096402264335679165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46083277590406038228477773 17281229096402264335679165)
          ·
            refine ⟨6480460911150849125879687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17281229096402264335679165 6480460911150849125879687)
            ·
              refine ⟨9720691366726273688819531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6480460911150849125879687 9720691366726273688819531)
              ·
                refine ⟨14581037050089410533229297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9720691366726273688819531 14581037050089410533229297)
                ·
                  refine ⟨10935777787567057899921973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14581037050089410533229297 10935777787567057899921973)
                  ·
                    refine ⟨1025229167584411678117685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10935777787567057899921973 1025229167584411678117685)
                    ·
                      rfl

theorem cell22_2994940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_2994940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994940 prefixEnd_2994940 := by exact prefixLift 2994940
  have htrace : WordTrace (prefixWord ++ tailWord_2994940) baseStart_2994940 baseEnd_2994940 := by
    simpa [prefixWord, tailWord_2994940, baseEnd_2994940] using wordTrace_append hprefix tailTrace_2994940
  have hstable : (prefixWord ++ tailWord_2994940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994940).length < 2 ^ (prefixWord ++ tailWord_2994940).sum := by decide
  have hdescent : baseEnd_2994940 < baseStart_2994940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994942 : List Nat := [4, 2, 2, 1, 2, 1, 2, 3, 5]
def baseStart_2994942 : Nat := 118140960795 + 2994942 * 2 ^ 59
def prefixEnd_2994942 : Nat := 4983230072969 + 3 ^ 40 * 2994942 * 2
def baseEnd_2994942 : Nat := 341743284075094779855893

theorem tailTrace_2994942 : CollatzResearch.WordTrace tailWord_2994942 prefixEnd_2994942 341743284075094779855893 := by
  unfold tailWord_2994942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13654313589480513027060385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72823005810562736144322053 13654313589480513027060385)
  ·
    refine ⟨10240735192110384770295289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13654313589480513027060385 10240735192110384770295289)
    ·
      refine ⟨7680551394082788577721467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10240735192110384770295289 7680551394082788577721467)
      ·
        refine ⟨11520827091124182866582201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7680551394082788577721467 11520827091124182866582201)
        ·
          refine ⟨8640620318343137149936651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11520827091124182866582201 8640620318343137149936651)
          ·
            refine ⟨12960930477514705724904977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8640620318343137149936651 12960930477514705724904977)
            ·
              refine ⟨9720697858136029293678733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12960930477514705724904977 9720697858136029293678733)
              ·
                refine ⟨3645261696801010985129525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9720697858136029293678733 3645261696801010985129525)
                ·
                  refine ⟨341743284075094779855893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3645261696801010985129525 341743284075094779855893)
                  ·
                    rfl

theorem cell22_2994942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_2994942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994942 prefixEnd_2994942 := by exact prefixLift 2994942
  have htrace : WordTrace (prefixWord ++ tailWord_2994942) baseStart_2994942 baseEnd_2994942 := by
    simpa [prefixWord, tailWord_2994942, baseEnd_2994942] using wordTrace_append hprefix tailTrace_2994942
  have hstable : (prefixWord ++ tailWord_2994942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994942).length < 2 ^ (prefixWord ++ tailWord_2994942).sum := by decide
  have hdescent : baseEnd_2994942 < baseStart_2994942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994953 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 8]
def baseStart_2994953 : Nat := 118140960795 + 2994953 * 2 ^ 59
def prefixEnd_2994953 : Nat := 4983230072969 + 3 ^ 40 * 2994953 * 2
def baseEnd_2994953 : Nat := 341744539250027992514215

theorem tailTrace_2994953 : CollatzResearch.WordTrace tailWord_2994953 prefixEnd_2994953 341744539250027992514215 := by
  unfold tailWord_2994953
  simp only [CollatzResearch.WordTrace]
  refine ⟨109234909918804253095133513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72823273279202835396755675 109234909918804253095133513)
  ·
    refine ⟨81926182439103189821350135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109234909918804253095133513 81926182439103189821350135)
    ·
      refine ⟨122889273658654784732025203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81926182439103189821350135 122889273658654784732025203)
      ·
        refine ⟨184333910487982177098037805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122889273658654784732025203 184333910487982177098037805)
        ·
          refine ⟨69125216432993316411764177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184333910487982177098037805 69125216432993316411764177)
          ·
            refine ⟨51843912324744987308823133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69125216432993316411764177 51843912324744987308823133)
            ·
              refine ⟨19441467121779370240808675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51843912324744987308823133 19441467121779370240808675)
              ·
                refine ⟨29162200682669055361213013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19441467121779370240808675 29162200682669055361213013)
                ·
                  refine ⟨341744539250027992514215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29162200682669055361213013 341744539250027992514215)
                  ·
                    rfl

theorem cell22_2994953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 8].length) (baseStart_2994953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994953 prefixEnd_2994953 := by exact prefixLift 2994953
  have htrace : WordTrace (prefixWord ++ tailWord_2994953) baseStart_2994953 baseEnd_2994953 := by
    simpa [prefixWord, tailWord_2994953, baseEnd_2994953] using wordTrace_append hprefix tailTrace_2994953
  have hstable : (prefixWord ++ tailWord_2994953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994953).length < 2 ^ (prefixWord ++ tailWord_2994953).sum := by decide
  have hdescent : baseEnd_2994953 < baseStart_2994953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994955 : List Nat := [1, 1, 1, 1, 5, 1, 1, 6, 1, 4]
def baseStart_2994955 : Nat := 118140960795 + 2994955 * 2 ^ 59
def prefixEnd_2994955 : Nat := 4983230072969 + 3 ^ 40 * 2994955 * 2
def baseEnd_2994955 : Nat := 1025234302390956638992639

theorem tailTrace_2994955 : CollatzResearch.WordTrace tailWord_2994955 prefixEnd_2994955 1025234302390956638992639 := by
  unfold tailWord_2994955
  simp only [CollatzResearch.WordTrace]
  refine ⟨109234982864797007436706319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72823321909864671624470879 109234982864797007436706319)
  ·
    refine ⟨163852474297195511155059479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109234982864797007436706319 163852474297195511155059479)
    ·
      refine ⟨245778711445793266732589219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163852474297195511155059479 245778711445793266732589219)
      ·
        refine ⟨368668067168689900098883829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245778711445793266732589219 368668067168689900098883829)
        ·
          refine ⟨34562631297064678134270359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 368668067168689900098883829 34562631297064678134270359)
          ·
            refine ⟨51843946945597017201405539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34562631297064678134270359 51843946945597017201405539)
            ·
              refine ⟨77765920418395525802108309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51843946945597017201405539 77765920418395525802108309)
              ·
                refine ⟨3645277519612290271973827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77765920418395525802108309 3645277519612290271973827)
                ·
                  refine ⟨5467916279418435407960741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3645277519612290271973827 5467916279418435407960741)
                  ·
                    refine ⟨1025234302390956638992639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5467916279418435407960741 1025234302390956638992639)
                    ·
                      rfl

theorem cell22_2994955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 4].length) (baseStart_2994955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994955 prefixEnd_2994955 := by exact prefixLift 2994955
  have htrace : WordTrace (prefixWord ++ tailWord_2994955) baseStart_2994955 baseEnd_2994955 := by
    simpa [prefixWord, tailWord_2994955, baseEnd_2994955] using wordTrace_append hprefix tailTrace_2994955
  have hstable : (prefixWord ++ tailWord_2994955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994955).length < 2 ^ (prefixWord ++ tailWord_2994955).sum := by decide
  have hdescent : baseEnd_2994955 < baseStart_2994955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994972 : List Nat := [2, 2, 3, 1, 1, 4, 1, 3, 1, 4]
def baseStart_2994972 : Nat := 118140960795 + 2994972 * 2 ^ 59
def prefixEnd_2994972 : Nat := 4983230072969 + 3 ^ 40 * 2994972 * 2
def baseEnd_2994972 : Nat := 1025240121838374261317587

theorem tailTrace_2994972 : CollatzResearch.WordTrace tailWord_2994972 prefixEnd_2994972 1025240121838374261317587 := by
  unfold tailWord_2994972
  simp only [CollatzResearch.WordTrace]
  refine ⟨54617801452867709670037585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72823735270490279560050113 54617801452867709670037585)
  ·
    refine ⟨40963351089650782252528189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54617801452867709670037585 40963351089650782252528189)
    ·
      refine ⟨15361256658619043344698071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40963351089650782252528189 15361256658619043344698071)
      ·
        refine ⟨23041884987928565017047107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15361256658619043344698071 23041884987928565017047107)
        ·
          refine ⟨34562827481892847525570661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23041884987928565017047107 34562827481892847525570661)
          ·
            refine ⟨6480530152854908911044499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34562827481892847525570661 6480530152854908911044499)
            ·
              refine ⟨9720795229282363366566749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6480530152854908911044499 9720795229282363366566749)
              ·
                refine ⟨3645298210980886262462531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9720795229282363366566749 3645298210980886262462531)
                ·
                  refine ⟨5467947316471329393693797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3645298210980886262462531 5467947316471329393693797)
                  ·
                    refine ⟨1025240121838374261317587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5467947316471329393693797 1025240121838374261317587)
                    ·
                      rfl

theorem cell22_2994972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_2994972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994972 prefixEnd_2994972 := by exact prefixLift 2994972
  have htrace : WordTrace (prefixWord ++ tailWord_2994972) baseStart_2994972 baseEnd_2994972 := by
    simpa [prefixWord, tailWord_2994972, baseEnd_2994972] using wordTrace_append hprefix tailTrace_2994972
  have hstable : (prefixWord ++ tailWord_2994972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994972).length < 2 ^ (prefixWord ++ tailWord_2994972).sum := by decide
  have hdescent : baseEnd_2994972 < baseStart_2994972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2994985 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 4, 3]
def baseStart_2994985 : Nat := 118140960795 + 2994985 * 2 ^ 59
def prefixEnd_2994985 : Nat := 4983230072969 + 3 ^ 40 * 2994985 * 2
def baseEnd_2994985 : Nat := 1025244572004046560742547

theorem tailTrace_2994985 : CollatzResearch.WordTrace tailWord_2994985 prefixEnd_2994985 1025244572004046560742547 := by
  unfold tailWord_2994985
  simp only [CollatzResearch.WordTrace]
  refine ⟨109236077054688322560298409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72824051369792215040198939 109236077054688322560298409)
  ·
    refine ⟨81927057791016241920223807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109236077054688322560298409 81927057791016241920223807)
    ·
      refine ⟨122890586686524362880335711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81927057791016241920223807 122890586686524362880335711)
      ·
        refine ⟨184335880029786544320503567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122890586686524362880335711 184335880029786544320503567)
        ·
          refine ⟨276503820044679816480755351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184335880029786544320503567 276503820044679816480755351)
          ·
            refine ⟨414755730067019724721133027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276503820044679816480755351 414755730067019724721133027)
            ·
              refine ⟨622133595100529587081699541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414755730067019724721133027 622133595100529587081699541)
              ·
                refine ⟨14581256135168662197227333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 622133595100529587081699541 14581256135168662197227333)
                ·
                  refine ⟨2733985525344124161980125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14581256135168662197227333 2733985525344124161980125)
                  ·
                    refine ⟨1025244572004046560742547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2733985525344124161980125 1025244572004046560742547)
                    ·
                      rfl

theorem cell22_2994985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 3].length) (baseStart_2994985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2994985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2994985 prefixEnd_2994985 := by exact prefixLift 2994985
  have htrace : WordTrace (prefixWord ++ tailWord_2994985) baseStart_2994985 baseEnd_2994985 := by
    simpa [prefixWord, tailWord_2994985, baseEnd_2994985] using wordTrace_append hprefix tailTrace_2994985
  have hstable : (prefixWord ++ tailWord_2994985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2994985).length < 2 ^ (prefixWord ++ tailWord_2994985).sum := by decide
  have hdescent : baseEnd_2994985 < baseStart_2994985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2994985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995092 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_2995092 : Nat := 118140960795 + 2995092 * 2 ^ 59
def prefixEnd_2995092 : Nat := 4983230072969 + 3 ^ 40 * 2995092 * 2
def baseEnd_2995092 : Nat := 1025281200290733948317219

theorem tailTrace_2995092 : CollatzResearch.WordTrace tailWord_2995092 prefixEnd_2995092 1025281200290733948317219 := by
  unfold tailWord_2995092
  simp only [CollatzResearch.WordTrace]
  refine ⟨54619989832650339917221765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72826653110200453222962353 54619989832650339917221765)
  ·
    refine ⟨10241248093621938734479081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54619989832650339917221765 10241248093621938734479081)
    ·
      refine ⟨7680936070216454050859311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10241248093621938734479081 7680936070216454050859311)
      ·
        refine ⟨11521404105324681076288967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7680936070216454050859311 11521404105324681076288967)
        ·
          refine ⟨17282106157987021614433451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11521404105324681076288967 17282106157987021614433451)
          ·
            refine ⟨25923159236980532421650177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17282106157987021614433451 25923159236980532421650177)
            ·
              refine ⟨19442369427735399316237633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25923159236980532421650177 19442369427735399316237633)
              ·
                refine ⟨14581777070801549487178225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19442369427735399316237633 14581777070801549487178225)
                ·
                  refine ⟨10936332803101162115383669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14581777070801549487178225 10936332803101162115383669)
                  ·
                    refine ⟨1025281200290733948317219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10936332803101162115383669 1025281200290733948317219)
                    ·
                      rfl

theorem cell22_2995092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_2995092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995092 prefixEnd_2995092 := by exact prefixLift 2995092
  have htrace : WordTrace (prefixWord ++ tailWord_2995092) baseStart_2995092 baseEnd_2995092 := by
    simpa [prefixWord, tailWord_2995092, baseEnd_2995092] using wordTrace_append hprefix tailTrace_2995092
  have hstable : (prefixWord ++ tailWord_2995092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995092).length < 2 ^ (prefixWord ++ tailWord_2995092).sum := by decide
  have hdescent : baseEnd_2995092 < baseStart_2995092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995171 : List Nat := [1, 1, 1, 6, 1, 1, 5, 1, 2, 3]
def baseStart_2995171 : Nat := 118140960795 + 2995171 * 2 ^ 59
def prefixEnd_2995171 : Nat := 4983230072969 + 3 ^ 40 * 2995171 * 2
def baseEnd_2995171 : Nat := 1025308243605204075591977

theorem tailTrace_2995171 : CollatzResearch.WordTrace tailWord_2995171 prefixEnd_2995171 1025308243605204075591977 := by
  unfold tailWord_2995171
  simp only [CollatzResearch.WordTrace]
  refine ⟨109242861032014476326569367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72828574021342984217712911 109242861032014476326569367)
  ·
    refine ⟨163864291548021714489854051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109242861032014476326569367 163864291548021714489854051)
    ·
      refine ⟨245796437322032571734781077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163864291548021714489854051 245796437322032571734781077)
      ·
        refine ⟨11521707999470276800067863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 245796437322032571734781077 11521707999470276800067863)
        ·
          refine ⟨17282561999205415200101795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11521707999470276800067863 17282561999205415200101795)
          ·
            refine ⟨25923842998808122800152693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17282561999205415200101795 25923842998808122800152693)
            ·
              refine ⟨2430360281138261512514315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25923842998808122800152693 2430360281138261512514315)
              ·
                refine ⟨3645540421707392268771473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2430360281138261512514315 3645540421707392268771473)
                ·
                  refine ⟨2734155316280544201578605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3645540421707392268771473 2734155316280544201578605)
                  ·
                    refine ⟨1025308243605204075591977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2734155316280544201578605 1025308243605204075591977)
                    ·
                      rfl

theorem cell22_2995171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 2, 3].length) (baseStart_2995171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995171 prefixEnd_2995171 := by exact prefixLift 2995171
  have htrace : WordTrace (prefixWord ++ tailWord_2995171) baseStart_2995171 baseEnd_2995171 := by
    simpa [prefixWord, tailWord_2995171, baseEnd_2995171] using wordTrace_append hprefix tailTrace_2995171
  have hstable : (prefixWord ++ tailWord_2995171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995171).length < 2 ^ (prefixWord ++ tailWord_2995171).sum := by decide
  have hdescent : baseEnd_2995171 < baseStart_2995171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995212 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 7]
def baseStart_2995212 : Nat := 118140960795 + 2995212 * 2 ^ 59
def prefixEnd_2995212 : Nat := 4983230072969 + 3 ^ 40 * 2995212 * 2
def baseEnd_2995212 : Nat := 341774092914364545105617

theorem tailTrace_2995212 : CollatzResearch.WordTrace tailWord_2995212 prefixEnd_2995212 341774092914364545105617 := by
  unfold tailWord_2995212
  simp only [CollatzResearch.WordTrace]
  refine ⟨54622178212432970164405945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72829570949910626885874593 54622178212432970164405945)
  ·
    refine ⟨40966633659324727623304459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54622178212432970164405945 40966633659324727623304459)
    ·
      refine ⟨61449950488987091434956689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40966633659324727623304459 61449950488987091434956689)
      ·
        refine ⟨46087462866740318576217517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61449950488987091434956689 46087462866740318576217517)
        ·
          refine ⟨17282798575027619466081569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46087462866740318576217517 17282798575027619466081569)
          ·
            refine ⟨12962098931270714599561177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17282798575027619466081569 12962098931270714599561177)
            ·
              refine ⟨9721574198453035949670883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12962098931270714599561177 9721574198453035949670883)
              ·
                refine ⟨14582361297679553924506325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9721574198453035949670883 14582361297679553924506325)
                ·
                  refine ⟨341774092914364545105617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14582361297679553924506325 341774092914364545105617)
                  ·
                    rfl

theorem cell22_2995212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_2995212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995212 prefixEnd_2995212 := by exact prefixLift 2995212
  have htrace : WordTrace (prefixWord ++ tailWord_2995212) baseStart_2995212 baseEnd_2995212 := by
    simpa [prefixWord, tailWord_2995212, baseEnd_2995212] using wordTrace_append hprefix tailTrace_2995212
  have hstable : (prefixWord ++ tailWord_2995212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995212).length < 2 ^ (prefixWord ++ tailWord_2995212).sum := by decide
  have hdescent : baseEnd_2995212 < baseStart_2995212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995218 : List Nat := [3, 2, 5, 1, 1, 1, 2, 7]
def baseStart_2995218 : Nat := 118140960795 + 2995218 * 2 ^ 59
def prefixEnd_2995218 : Nat := 4983230072969 + 3 ^ 40 * 2995218 * 2
def baseEnd_2995218 : Nat := 113924925851745735518537

theorem tailTrace_2995218 : CollatzResearch.WordTrace tailWord_2995218 prefixEnd_2995218 113924925851745735518537 := by
  unfold tailWord_2995218
  simp only [CollatzResearch.WordTrace]
  refine ⟨27311143815711050838382577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72829716841896135569020205 27311143815711050838382577)
  ·
    refine ⟨20483357861783288128786933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27311143815711050838382577 20483357861783288128786933)
    ·
      refine ⟨1920314799542183262073775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20483357861783288128786933 1920314799542183262073775)
      ·
        refine ⟨2880472199313274893110663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1920314799542183262073775 2880472199313274893110663)
        ·
          refine ⟨4320708298969912339665995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2880472199313274893110663 4320708298969912339665995)
          ·
            refine ⟨6481062448454868509498993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4320708298969912339665995 6481062448454868509498993)
            ·
              refine ⟨4860796836341151382124245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6481062448454868509498993 4860796836341151382124245)
              ·
                refine ⟨113924925851745735518537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4860796836341151382124245 113924925851745735518537)
                ·
                  rfl

theorem cell22_2995218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 7].length) (baseStart_2995218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995218 prefixEnd_2995218 := by exact prefixLift 2995218
  have htrace : WordTrace (prefixWord ++ tailWord_2995218) baseStart_2995218 baseEnd_2995218 := by
    simpa [prefixWord, tailWord_2995218, baseEnd_2995218] using wordTrace_append hprefix tailTrace_2995218
  have hstable : (prefixWord ++ tailWord_2995218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995218).length < 2 ^ (prefixWord ++ tailWord_2995218).sum := by decide
  have hdescent : baseEnd_2995218 < baseStart_2995218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995272 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 3, 5]
def baseStart_2995272 : Nat := 118140960795 + 2995272 * 2 ^ 59
def prefixEnd_2995272 : Nat := 4983230072969 + 3 ^ 40 * 2995272 * 2
def baseEnd_2995272 : Nat := 1025342817969273478816667

theorem tailTrace_2995272 : CollatzResearch.WordTrace tailWord_2995272 prefixEnd_2995272 1025342817969273478816667 := by
  unfold tailWord_2995272
  simp only [CollatzResearch.WordTrace]
  refine ⟨54623272402324285287998035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72831029869765713717330713 54623272402324285287998035)
  ·
    refine ⟨81934908603486427931997053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54623272402324285287998035 81934908603486427931997053)
    ·
      refine ⟨30725590726307410474498895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81934908603486427931997053 30725590726307410474498895)
      ·
        refine ⟨46088386089461115711748343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30725590726307410474498895 46088386089461115711748343)
        ·
          refine ⟨69132579134191673567622515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46088386089461115711748343 69132579134191673567622515)
          ·
            refine ⟨103698868701287510351433773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69132579134191673567622515 103698868701287510351433773)
            ·
              refine ⟨38887075762982816381787665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103698868701287510351433773 38887075762982816381787665)
              ·
                refine ⟨29165306822237112286340749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38887075762982816381787665 29165306822237112286340749)
                ·
                  refine ⟨10936990058338917107377781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29165306822237112286340749 10936990058338917107377781)
                  ·
                    refine ⟨1025342817969273478816667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10936990058338917107377781 1025342817969273478816667)
                    ·
                      rfl

theorem cell22_2995272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_2995272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995272 prefixEnd_2995272 := by exact prefixLift 2995272
  have htrace : WordTrace (prefixWord ++ tailWord_2995272) baseStart_2995272 baseEnd_2995272 := by
    simpa [prefixWord, tailWord_2995272, baseEnd_2995272] using wordTrace_append hprefix tailTrace_2995272
  have hstable : (prefixWord ++ tailWord_2995272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995272).length < 2 ^ (prefixWord ++ tailWord_2995272).sum := by decide
  have hdescent : baseEnd_2995272 < baseStart_2995272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995287 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 1, 6]
def baseStart_2995287 : Nat := 118140960795 + 2995287 * 2 ^ 59
def prefixEnd_2995287 : Nat := 4983230072969 + 3 ^ 40 * 2995287 * 2
def baseEnd_2995287 : Nat := 1025347952775818439691621

theorem tailTrace_2995287 : CollatzResearch.WordTrace tailWord_2995287 prefixEnd_2995287 1025347952775818439691621 := by
  unfold tailWord_2995287
  simp only [CollatzResearch.WordTrace]
  refine ⟨109247091899594228137792115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72831394599729485425194743 109247091899594228137792115)
  ·
    refine ⟨163870637849391342206688173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109247091899594228137792115 163870637849391342206688173)
    ·
      refine ⟨61451489193521753327508065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163870637849391342206688173 61451489193521753327508065)
      ·
        refine ⟨46088616895141314995631049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61451489193521753327508065 46088616895141314995631049)
        ·
          refine ⟨34566462671355986246723287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46088616895141314995631049 34566462671355986246723287)
          ·
            refine ⟨51849694007033979370084931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34566462671355986246723287 51849694007033979370084931)
            ·
              refine ⟨77774541010550969055127397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51849694007033979370084931 77774541010550969055127397)
              ·
                refine ⟨14582726439478306697836387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77774541010550969055127397 14582726439478306697836387)
                ·
                  refine ⟨21874089659217460046754581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14582726439478306697836387 21874089659217460046754581)
                  ·
                    refine ⟨1025347952775818439691621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21874089659217460046754581 1025347952775818439691621)
                    ·
                      rfl

theorem cell22_2995287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_2995287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995287 prefixEnd_2995287 := by exact prefixLift 2995287
  have htrace : WordTrace (prefixWord ++ tailWord_2995287) baseStart_2995287 baseEnd_2995287 := by
    simpa [prefixWord, tailWord_2995287, baseEnd_2995287] using wordTrace_append hprefix tailTrace_2995287
  have hstable : (prefixWord ++ tailWord_2995287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995287).length < 2 ^ (prefixWord ++ tailWord_2995287).sum := by decide
  have hdescent : baseEnd_2995287 < baseStart_2995287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995351 : List Nat := [1, 1, 3, 3, 3, 1, 2, 2, 3, 3]
def baseStart_2995351 : Nat := 118140960795 + 2995351 * 2 ^ 59
def prefixEnd_2995351 : Nat := 4983230072969 + 3 ^ 40 * 2995351 * 2
def baseEnd_2995351 : Nat := 1025369861283743606091425

theorem tailTrace_2995351 : CollatzResearch.WordTrace tailWord_2995351 prefixEnd_2995351 1025369861283743606091425 := by
  unfold tailWord_2995351
  simp only [CollatzResearch.WordTrace]
  refine ⟨109249426171362367068121907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72832950780908244712081271 109249426171362367068121907)
  ·
    refine ⟨163874139257043550602182861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109249426171362367068121907 163874139257043550602182861)
    ·
      refine ⟨61452802221391331475818573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163874139257043550602182861 61452802221391331475818573)
      ·
        refine ⟨23044800833021749303431965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61452802221391331475818573 23044800833021749303431965)
        ·
          refine ⟨8641800312383155988786987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23044800833021749303431965 8641800312383155988786987)
          ·
            refine ⟨12962700468574733983180481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8641800312383155988786987 12962700468574733983180481)
            ·
              refine ⟨9722025351431050487385361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12962700468574733983180481 9722025351431050487385361)
              ·
                refine ⟨7291519013573287865539021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9722025351431050487385361 7291519013573287865539021)
                ·
                  refine ⟨2734319630089982949577133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7291519013573287865539021 2734319630089982949577133)
                  ·
                    refine ⟨1025369861283743606091425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2734319630089982949577133 1025369861283743606091425)
                    ·
                      rfl

theorem cell22_2995351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_2995351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995351 prefixEnd_2995351 := by exact prefixLift 2995351
  have htrace : WordTrace (prefixWord ++ tailWord_2995351) baseStart_2995351 baseEnd_2995351 := by
    simpa [prefixWord, tailWord_2995351, baseEnd_2995351] using wordTrace_append hprefix tailTrace_2995351
  have hstable : (prefixWord ++ tailWord_2995351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995351).length < 2 ^ (prefixWord ++ tailWord_2995351).sum := by decide
  have hdescent : baseEnd_2995351 < baseStart_2995351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995364 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 7]
def baseStart_2995364 : Nat := 118140960795 + 2995364 * 2 ^ 59
def prefixEnd_2995364 : Nat := 4983230072969 + 3 ^ 40 * 2995364 * 2
def baseEnd_2995364 : Nat := 341791437149805301838795

theorem tailTrace_2995364 : CollatzResearch.WordTrace tailWord_2995364 prefixEnd_2995364 341791437149805301838795 := by
  unfold tailWord_2995364
  simp only [CollatzResearch.WordTrace]
  refine ⟨54624950160157635144172573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72833266880210180192230097 54624950160157635144172573)
  ·
    refine ⟨20484356310059113179064715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54624950160157635144172573 20484356310059113179064715)
    ·
      refine ⟨30726534465088669768597073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20484356310059113179064715 30726534465088669768597073)
      ·
        refine ⟨23044900848816502326447805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30726534465088669768597073 23044900848816502326447805)
        ·
          refine ⟨8641837818306188372417927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23044900848816502326447805 8641837818306188372417927)
          ·
            refine ⟨12962756727459282558626891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8641837818306188372417927 12962756727459282558626891)
            ·
              refine ⟨19444135091188923837940337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12962756727459282558626891 19444135091188923837940337)
              ·
                refine ⟨14583101318391692878455253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19444135091188923837940337 14583101318391692878455253)
                ·
                  refine ⟨341791437149805301838795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14583101318391692878455253 341791437149805301838795)
                  ·
                    rfl

theorem cell22_2995364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_2995364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995364 prefixEnd_2995364 := by exact prefixLift 2995364
  have htrace : WordTrace (prefixWord ++ tailWord_2995364) baseStart_2995364 baseEnd_2995364 := by
    simpa [prefixWord, tailWord_2995364, baseEnd_2995364] using wordTrace_append hprefix tailTrace_2995364
  have hstable : (prefixWord ++ tailWord_2995364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995364).length < 2 ^ (prefixWord ++ tailWord_2995364).sum := by decide
  have hdescent : baseEnd_2995364 < baseStart_2995364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995385 : List Nat := [1, 2, 1, 4, 1, 4, 3, 2, 1, 3]
def baseStart_2995385 : Nat := 118140960795 + 2995385 * 2 ^ 59
def prefixEnd_2995385 : Nat := 4983230072969 + 3 ^ 40 * 2995385 * 2
def baseEnd_2995385 : Nat := 1025381500178578850741321

theorem tailTrace_2995385 : CollatzResearch.WordTrace tailWord_2995385 prefixEnd_2995385 1025381500178578850741321 := by
  unfold tailWord_2995385
  simp only [CollatzResearch.WordTrace]
  refine ⟨109250666253239190874859609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72833777502159460583239739 109250666253239190874859609)
  ·
    refine ⟨81937999689929393156144707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109250666253239190874859609 81937999689929393156144707)
    ·
      refine ⟨122906999534894089734217061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81937999689929393156144707 122906999534894089734217061)
      ·
        refine ⟨23045062412792641825165699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122906999534894089734217061 23045062412792641825165699)
        ·
          refine ⟨34567593619188962737748549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23045062412792641825165699 34567593619188962737748549)
          ·
            refine ⟨6481423803597930513327853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34567593619188962737748549 6481423803597930513327853)
            ·
              refine ⟨2430533926349223942497945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6481423803597930513327853 2430533926349223942497945)
              ·
                refine ⟨1822900444761917956873459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2430533926349223942497945 1822900444761917956873459)
                ·
                  refine ⟨2734350667142876935310189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1822900444761917956873459 2734350667142876935310189)
                  ·
                    refine ⟨1025381500178578850741321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2734350667142876935310189 1025381500178578850741321)
                    ·
                      rfl

theorem cell22_2995385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 1, 3].length) (baseStart_2995385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995385 prefixEnd_2995385 := by exact prefixLift 2995385
  have htrace : WordTrace (prefixWord ++ tailWord_2995385) baseStart_2995385 baseEnd_2995385 := by
    simpa [prefixWord, tailWord_2995385, baseEnd_2995385] using wordTrace_append hprefix tailTrace_2995385
  have hstable : (prefixWord ++ tailWord_2995385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995385).length < 2 ^ (prefixWord ++ tailWord_2995385).sum := by decide
  have hdescent : baseEnd_2995385 < baseStart_2995385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995424 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 3, 5]
def baseStart_2995424 : Nat := 118140960795 + 2995424 * 2 ^ 59
def prefixEnd_2995424 : Nat := 4983230072969 + 3 ^ 40 * 2995424 * 2
def baseEnd_2995424 : Nat := 1025394850675595749016201

theorem tailTrace_2995424 : CollatzResearch.WordTrace tailWord_2995424 prefixEnd_2995424 1025394850675595749016201 := by
  unfold tailWord_2995424
  simp only [CollatzResearch.WordTrace]
  refine ⟨54626044350048950267764663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72834725800065267023686217 54626044350048950267764663)
  ·
    refine ⟨81939066525073425401646995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54626044350048950267764663 81939066525073425401646995)
    ·
      refine ⟨122908599787610138102470493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81939066525073425401646995 122908599787610138102470493)
      ·
        refine ⟨46090724920353801788426435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122908599787610138102470493 46090724920353801788426435)
        ·
          refine ⟨69136087380530702682639653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46090724920353801788426435 69136087380530702682639653)
          ·
            refine ⟨12963016383849506752994935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69136087380530702682639653 12963016383849506752994935)
            ·
              refine ⟨19444524575774260129492403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12963016383849506752994935 19444524575774260129492403)
              ·
                refine ⟨29166786863661390194238605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19444524575774260129492403 29166786863661390194238605)
                ·
                  refine ⟨10937545073873021322839477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29166786863661390194238605 10937545073873021322839477)
                  ·
                    refine ⟨1025394850675595749016201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10937545073873021322839477 1025394850675595749016201)
                    ·
                      rfl

theorem cell22_2995424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_2995424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995424 prefixEnd_2995424 := by exact prefixLift 2995424
  have htrace : WordTrace (prefixWord ++ tailWord_2995424) baseStart_2995424 baseEnd_2995424 := by
    simpa [prefixWord, tailWord_2995424, baseEnd_2995424] using wordTrace_append hprefix tailTrace_2995424
  have hstable : (prefixWord ++ tailWord_2995424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995424).length < 2 ^ (prefixWord ++ tailWord_2995424).sum := by decide
  have hdescent : baseEnd_2995424 < baseStart_2995424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995443 : List Nat := [1, 1, 1, 2, 2, 5, 4, 2, 4]
def baseStart_2995443 : Nat := 118140960795 + 2995443 * 2 ^ 59
def prefixEnd_2995443 : Nat := 4983230072969 + 3 ^ 40 * 2995443 * 2
def baseEnd_2995443 : Nat := 341800451587962010930381

theorem tailTrace_2995443 : CollatzResearch.WordTrace tailWord_2995443 prefixEnd_2995443 341800451587962010930381 := by
  unfold tailWord_2995443
  simp only [CollatzResearch.WordTrace]
  refine ⟨109252781687029066780470983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72835187791352711186980655 109252781687029066780470983)
  ·
    refine ⟨163879172530543600170706475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109252781687029066780470983 163879172530543600170706475)
    ·
      refine ⟨245818758795815400256059713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163879172530543600170706475 245818758795815400256059713)
      ·
        refine ⟨184364069096861550192044785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245818758795815400256059713 184364069096861550192044785)
        ·
          refine ⟨138273051822646162644033589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184364069096861550192044785 138273051822646162644033589)
          ·
            refine ⟨12963098608373077747878149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138273051822646162644033589 12963098608373077747878149)
            ·
              refine ⟨2430580989069952077727153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12963098608373077747878149 2430580989069952077727153)
              ·
                refine ⟨1822935741802464058295365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2430580989069952077727153 1822935741802464058295365)
                ·
                  refine ⟨341800451587962010930381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1822935741802464058295365 341800451587962010930381)
                  ·
                    rfl

theorem cell22_2995443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 4].length) (baseStart_2995443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995443 prefixEnd_2995443 := by exact prefixLift 2995443
  have htrace : WordTrace (prefixWord ++ tailWord_2995443) baseStart_2995443 baseEnd_2995443 := by
    simpa [prefixWord, tailWord_2995443, baseEnd_2995443] using wordTrace_append hprefix tailTrace_2995443
  have hstable : (prefixWord ++ tailWord_2995443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995443).length < 2 ^ (prefixWord ++ tailWord_2995443).sum := by decide
  have hdescent : baseEnd_2995443 < baseStart_2995443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995593 : List Nat := [1, 2, 1, 1, 7, 1, 1, 2, 1, 5]
def baseStart_2995593 : Nat := 118140960795 + 2995593 * 2 ^ 59
def prefixEnd_2995593 : Nat := 4983230072969 + 3 ^ 40 * 2995593 * 2
def baseEnd_2995593 : Nat := 1025452702829335641540683

theorem tailTrace_2995593 : CollatzResearch.WordTrace tailWord_2995593 prefixEnd_2995593 1025452702829335641540683 := by
  unfold tailWord_2995593
  simp only [CollatzResearch.WordTrace]
  refine ⟨109258252636485642398431433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72838835090990428265620955 109258252636485642398431433)
  ·
    refine ⟨81943689477364231798823575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109258252636485642398431433 81943689477364231798823575)
    ·
      refine ⟨122915534216046347698235363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81943689477364231798823575 122915534216046347698235363)
      ·
        refine ⟨184373301324069521547353045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122915534216046347698235363 184373301324069521547353045)
        ·
          refine ⟨4321249249782879411266087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 184373301324069521547353045 4321249249782879411266087)
          ·
            refine ⟨6481873874674319116899131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4321249249782879411266087 6481873874674319116899131)
            ·
              refine ⟨9722810812011478675348697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6481873874674319116899131 9722810812011478675348697)
              ·
                refine ⟨7292108109008609006511523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9722810812011478675348697 7292108109008609006511523)
                ·
                  refine ⟨10938162163512913509767285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7292108109008609006511523 10938162163512913509767285)
                  ·
                    refine ⟨1025452702829335641540683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10938162163512913509767285 1025452702829335641540683)
                    ·
                      rfl

theorem cell22_2995593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 5].length) (baseStart_2995593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995593 prefixEnd_2995593 := by exact prefixLift 2995593
  have htrace : WordTrace (prefixWord ++ tailWord_2995593) baseStart_2995593 baseEnd_2995593 := by
    simpa [prefixWord, tailWord_2995593, baseEnd_2995593] using wordTrace_append hprefix tailTrace_2995593
  have hstable : (prefixWord ++ tailWord_2995593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995593).length < 2 ^ (prefixWord ++ tailWord_2995593).sum := by decide
  have hdescent : baseEnd_2995593 < baseStart_2995593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995610 : List Nat := [3, 1, 1, 4, 1, 1, 4, 2, 2, 3]
def baseStart_2995610 : Nat := 118140960795 + 2995610 * 2 ^ 59
def prefixEnd_2995610 : Nat := 4983230072969 + 3 ^ 40 * 2995610 * 2
def baseEnd_2995610 : Nat := 1025458522276753263865631

theorem tailTrace_2995610 : CollatzResearch.WordTrace tailWord_2995610 prefixEnd_2995610 1025458522276753263865631 := by
  unfold tailWord_2995610
  simp only [CollatzResearch.WordTrace]
  refine ⟨27314718169356013575450071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72839248451616036201200189 27314718169356013575450071)
  ·
    refine ⟨40972077254034020363175107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27314718169356013575450071 40972077254034020363175107)
    ·
      refine ⟨61458115881051030544762661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40972077254034020363175107 61458115881051030544762661)
      ·
        refine ⟨11523396727697068227142999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61458115881051030544762661 11523396727697068227142999)
        ·
          refine ⟨17285095091545602340714499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11523396727697068227142999 17285095091545602340714499)
          ·
            refine ⟨25927642637318403511071749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17285095091545602340714499 25927642637318403511071749)
            ·
              refine ⟨4861432994497200658325953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25927642637318403511071749 4861432994497200658325953)
              ·
                refine ⟨3646074745872900493744465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4861432994497200658325953 3646074745872900493744465)
                ·
                  refine ⟨2734556059404675370308349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3646074745872900493744465 2734556059404675370308349)
                  ·
                    refine ⟨1025458522276753263865631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2734556059404675370308349 1025458522276753263865631)
                    ·
                      rfl

theorem cell22_2995610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_2995610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995610 prefixEnd_2995610 := by exact prefixLift 2995610
  have htrace : WordTrace (prefixWord ++ tailWord_2995610) baseStart_2995610 baseEnd_2995610 := by
    simpa [prefixWord, tailWord_2995610, baseEnd_2995610] using wordTrace_append hprefix tailTrace_2995610
  have hstable : (prefixWord ++ tailWord_2995610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995610).length < 2 ^ (prefixWord ++ tailWord_2995610).sum := by decide
  have hdescent : baseEnd_2995610 < baseStart_2995610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995612 : List Nat := [2, 2, 3, 4, 1, 1, 1, 4, 4]
def baseStart_2995612 : Nat := 118140960795 + 2995612 * 2 ^ 59
def prefixEnd_2995612 : Nat := 4983230072969 + 3 ^ 40 * 2995612 * 2
def baseEnd_2995612 : Nat := 341819735639208641771875

theorem tailTrace_2995612 : CollatzResearch.WordTrace tailWord_2995612 prefixEnd_2995612 341819735639208641771875 := by
  unfold tailWord_2995612
  simp only [CollatzResearch.WordTrace]
  refine ⟨54629472811708404321686545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72839297082277872428915393 54629472811708404321686545)
  ·
    refine ⟨40972104608781303241264909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54629472811708404321686545 40972104608781303241264909)
    ·
      refine ⟨15364539228292988715474341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40972104608781303241264909 15364539228292988715474341)
      ·
        refine ⟨2880851105304935384151439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15364539228292988715474341 2880851105304935384151439)
        ·
          refine ⟨4321276657957403076227159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2880851105304935384151439 4321276657957403076227159)
          ·
            refine ⟨6481914986936104614340739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4321276657957403076227159 6481914986936104614340739)
            ·
              refine ⟨9722872480404156921511109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6481914986936104614340739 9722872480404156921511109)
              ·
                refine ⟨1823038590075779422783333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9722872480404156921511109 1823038590075779422783333)
                ·
                  refine ⟨341819735639208641771875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1823038590075779422783333 341819735639208641771875)
                  ·
                    rfl

theorem cell22_2995612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_2995612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995612 prefixEnd_2995612 := by exact prefixLift 2995612
  have htrace : WordTrace (prefixWord ++ tailWord_2995612) baseStart_2995612 baseEnd_2995612 := by
    simpa [prefixWord, tailWord_2995612, baseEnd_2995612] using wordTrace_append hprefix tailTrace_2995612
  have hstable : (prefixWord ++ tailWord_2995612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995612).length < 2 ^ (prefixWord ++ tailWord_2995612).sum := by decide
  have hdescent : baseEnd_2995612 < baseStart_2995612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995683 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 2, 5]
def baseStart_2995683 : Nat := 118140960795 + 2995683 * 2 ^ 59
def prefixEnd_2995683 : Nat := 4983230072969 + 3 ^ 40 * 2995683 * 2
def baseEnd_2995683 : Nat := 1025483511668605406790407

theorem tailTrace_2995683 : CollatzResearch.WordTrace tailWord_2995683 prefixEnd_2995683 1025483511668605406790407 := by
  unfold tailWord_2995683
  simp only [CollatzResearch.WordTrace]
  refine ⟨109261535206159587769207703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72841023470773058512805135 109261535206159587769207703)
  ·
    refine ⟨163892302809239381653811555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109261535206159587769207703 163892302809239381653811555)
    ·
      refine ⟨245838454213859072480717333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163892302809239381653811555 245838454213859072480717333)
      ·
        refine ⟨11523677541274644022533625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 245838454213859072480717333 11523677541274644022533625)
        ·
          refine ⟨8642758155955983016900219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11523677541274644022533625 8642758155955983016900219)
          ·
            refine ⟨12964137233933974525350329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8642758155955983016900219 12964137233933974525350329)
            ·
              refine ⟨9723102925450480894012747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12964137233933974525350329 9723102925450480894012747)
              ·
                refine ⟨14584654388175721341019121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9723102925450480894012747 14584654388175721341019121)
                ·
                  refine ⟨10938490791131791005764341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14584654388175721341019121 10938490791131791005764341)
                  ·
                    refine ⟨1025483511668605406790407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10938490791131791005764341 1025483511668605406790407)
                    ·
                      rfl

theorem cell22_2995683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 5].length) (baseStart_2995683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995683 prefixEnd_2995683 := by exact prefixLift 2995683
  have htrace : WordTrace (prefixWord ++ tailWord_2995683) baseStart_2995683 baseEnd_2995683 := by
    simpa [prefixWord, tailWord_2995683, baseEnd_2995683] using wordTrace_append hprefix tailTrace_2995683
  have hstable : (prefixWord ++ tailWord_2995683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995683).length < 2 ^ (prefixWord ++ tailWord_2995683).sum := by decide
  have hdescent : baseEnd_2995683 < baseStart_2995683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995788 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 2, 6]
def baseStart_2995788 : Nat := 118140960795 + 2995788 * 2 ^ 59
def prefixEnd_2995788 : Nat := 4983230072969 + 3 ^ 40 * 2995788 * 2
def baseEnd_2995788 : Nat := 1025519455314420132915085

theorem tailTrace_2995788 : CollatzResearch.WordTrace tailWord_2995788 prefixEnd_2995788 1025519455314420132915085 := by
  unfold tailWord_2995788
  simp only [CollatzResearch.WordTrace]
  refine ⟨54632682435389595350890009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72843576580519460467853345 54632682435389595350890009)
  ·
    refine ⟨40974511826542196513167507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54632682435389595350890009 40974511826542196513167507)
    ·
      refine ⟨61461767739813294769751261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40974511826542196513167507 61461767739813294769751261)
      ·
        refine ⟨23048162902429985538656723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61461767739813294769751261 23048162902429985538656723)
        ·
          refine ⟨34572244353644978307985085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23048162902429985538656723 34572244353644978307985085)
          ·
            refine ⟨12964591632616866865494407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34572244353644978307985085 12964591632616866865494407)
            ·
              refine ⟨19446887448925300298241611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12964591632616866865494407 19446887448925300298241611)
              ·
                refine ⟨29170331173387950447362417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19446887448925300298241611 29170331173387950447362417)
                ·
                  refine ⟨21877748380040962835521813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29170331173387950447362417 21877748380040962835521813)
                  ·
                    refine ⟨1025519455314420132915085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21877748380040962835521813 1025519455314420132915085)
                    ·
                      rfl

theorem cell22_2995788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_2995788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995788 prefixEnd_2995788 := by exact prefixLift 2995788
  have htrace : WordTrace (prefixWord ++ tailWord_2995788) baseStart_2995788 baseEnd_2995788 := by
    simpa [prefixWord, tailWord_2995788, baseEnd_2995788] using wordTrace_append hprefix tailTrace_2995788
  have hstable : (prefixWord ++ tailWord_2995788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995788).length < 2 ^ (prefixWord ++ tailWord_2995788).sum := by decide
  have hdescent : baseEnd_2995788 < baseStart_2995788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995790 : List Nat := [4, 1, 1, 1, 1, 2, 1, 5, 3, 3]
def baseStart_2995790 : Nat := 118140960795 + 2995790 * 2 ^ 59
def prefixEnd_2995790 : Nat := 4983230072969 + 3 ^ 40 * 2995790 * 2
def baseEnd_2995790 : Nat := 1025520139955292794365079

theorem tailTrace_2995790 : CollatzResearch.WordTrace tailWord_2995790 prefixEnd_2995790 1025520139955292794365079 := by
  unfold tailWord_2995790
  simp only [CollatzResearch.WordTrace]
  refine ⟨13658179727096493130419103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72843625211181296695568549 13658179727096493130419103)
  ·
    refine ⟨20487269590644739695628655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13658179727096493130419103 20487269590644739695628655)
    ·
      refine ⟨30730904385967109543442983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20487269590644739695628655 30730904385967109543442983)
      ·
        refine ⟨46096356578950664315164475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30730904385967109543442983 46096356578950664315164475)
        ·
          refine ⟨69144534868425996472746713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46096356578950664315164475 69144534868425996472746713)
          ·
            refine ⟨51858401151319497354560035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69144534868425996472746713 51858401151319497354560035)
            ·
              refine ⟨77787601726979246031840053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51858401151319497354560035 77787601726979246031840053)
              ·
                refine ⟨7292587661904304315485005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77787601726979246031840053 7292587661904304315485005)
                ·
                  refine ⟨2734720373214114118306877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7292587661904304315485005 2734720373214114118306877)
                  ·
                    refine ⟨1025520139955292794365079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2734720373214114118306877 1025520139955292794365079)
                    ·
                      rfl

theorem cell22_2995790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_2995790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995790 prefixEnd_2995790 := by exact prefixLift 2995790
  have htrace : WordTrace (prefixWord ++ tailWord_2995790) baseStart_2995790 baseEnd_2995790 := by
    simpa [prefixWord, tailWord_2995790, baseEnd_2995790] using wordTrace_append hprefix tailTrace_2995790
  have hstable : (prefixWord ++ tailWord_2995790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995790).length < 2 ^ (prefixWord ++ tailWord_2995790).sum := by decide
  have hdescent : baseEnd_2995790 < baseStart_2995790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995824 : List Nat := [2, 1, 1, 1, 6, 2, 2, 3, 1, 3]
def baseStart_2995824 : Nat := 118140960795 + 2995824 * 2 ^ 59
def prefixEnd_2995824 : Nat := 4983230072969 + 3 ^ 40 * 2995824 * 2
def baseEnd_2995824 : Nat := 1025531778850128039014975

theorem tailTrace_2995824 : CollatzResearch.WordTrace tailWord_2995824 prefixEnd_2995824 1025531778850128039014975 := by
  unfold tailWord_2995824
  simp only [CollatzResearch.WordTrace]
  refine ⟨54633338949324384425045263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72844451932432512566727017 54633338949324384425045263)
  ·
    refine ⟨81950008423986576637567895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54633338949324384425045263 81950008423986576637567895)
    ·
      refine ⟨122925012635979864956351843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81950008423986576637567895 122925012635979864956351843)
      ·
        refine ⟨184387518953969797434527765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122925012635979864956351843 184387518953969797434527765)
        ·
          refine ⟨8643164950967334254743489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 184387518953969797434527765 8643164950967334254743489)
          ·
            refine ⟨6482373713225500691057617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8643164950967334254743489 6482373713225500691057617)
            ·
              refine ⟨4861780284919125518293213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6482373713225500691057617 4861780284919125518293213)
              ·
                refine ⟨1823167606844672069359955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4861780284919125518293213 1823167606844672069359955)
                ·
                  refine ⟨2734751410267008104039933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823167606844672069359955 2734751410267008104039933)
                  ·
                    refine ⟨1025531778850128039014975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2734751410267008104039933 1025531778850128039014975)
                    ·
                      rfl

theorem cell22_2995824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 1, 3].length) (baseStart_2995824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995824 prefixEnd_2995824 := by exact prefixLift 2995824
  have htrace : WordTrace (prefixWord ++ tailWord_2995824) baseStart_2995824 baseEnd_2995824 := by
    simpa [prefixWord, tailWord_2995824, baseEnd_2995824] using wordTrace_append hprefix tailTrace_2995824
  have hstable : (prefixWord ++ tailWord_2995824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995824).length < 2 ^ (prefixWord ++ tailWord_2995824).sum := by decide
  have hdescent : baseEnd_2995824 < baseStart_2995824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995837 : List Nat := [1, 4, 1, 1, 4, 3, 1, 2, 5]
def baseStart_2995837 : Nat := 118140960795 + 2995837 * 2 ^ 59
def prefixEnd_2995837 : Nat := 4983230072969 + 3 ^ 40 * 2995837 * 2
def baseEnd_2995837 : Nat := 341845409671933446146645

theorem tailTrace_2995837 : CollatzResearch.WordTrace tailWord_2995837 prefixEnd_2995837 341845409671933446146645 := by
  unfold tailWord_2995837
  simp only [CollatzResearch.WordTrace]
  refine ⟨109267152047601672070313765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72844768031734448046875843 109267152047601672070313765)
  ·
    refine ⟨20487591008925313513183831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109267152047601672070313765 20487591008925313513183831)
    ·
      refine ⟨30731386513387970269775747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20487591008925313513183831 30731386513387970269775747)
      ·
        refine ⟨46097079770081955404663621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30731386513387970269775747 46097079770081955404663621)
        ·
          refine ⟨8643202456890366638374429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46097079770081955404663621 8643202456890366638374429)
          ·
            refine ⟨3241200921333887489390411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8643202456890366638374429 3241200921333887489390411)
            ·
              refine ⟨4861801382000831234085617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3241200921333887489390411 4861801382000831234085617)
              ·
                refine ⟨3646351036500623425564213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4861801382000831234085617 3646351036500623425564213)
                ·
                  refine ⟨341845409671933446146645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3646351036500623425564213 341845409671933446146645)
                  ·
                    rfl

theorem cell22_2995837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_2995837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995837 prefixEnd_2995837 := by exact prefixLift 2995837
  have htrace : WordTrace (prefixWord ++ tailWord_2995837) baseStart_2995837 baseEnd_2995837 := by
    simpa [prefixWord, tailWord_2995837, baseEnd_2995837] using wordTrace_append hprefix tailTrace_2995837
  have hstable : (prefixWord ++ tailWord_2995837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995837).length < 2 ^ (prefixWord ++ tailWord_2995837).sum := by decide
  have hdescent : baseEnd_2995837 < baseStart_2995837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995895 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 4, 4]
def baseStart_2995895 : Nat := 118140960795 + 2995895 * 2 ^ 59
def prefixEnd_2995895 : Nat := 4983230072969 + 3 ^ 40 * 2995895 * 2
def baseEnd_2995895 : Nat := 1025556083601107520489757

theorem tailTrace_2995895 : CollatzResearch.WordTrace tailWord_2995895 prefixEnd_2995895 1025556083601107520489757 := by
  unfold tailWord_2995895
  simp only [CollatzResearch.WordTrace]
  refine ⟨109269267481391547975925139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72846178320927698650616759 109269267481391547975925139)
  ·
    refine ⟨163903901222087321963887709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109269267481391547975925139 163903901222087321963887709)
    ·
      refine ⟨61463962958282745736457891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163903901222087321963887709 61463962958282745736457891)
      ·
        refine ⟨92195944437424118604686837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61463962958282745736457891 92195944437424118604686837)
        ·
          refine ⟨8643369791008511119189391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92195944437424118604686837 8643369791008511119189391)
          ·
            refine ⟨12965054686512766678784087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8643369791008511119189391 12965054686512766678784087)
            ·
              refine ⟨19447582029769150018176131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12965054686512766678784087 19447582029769150018176131)
              ·
                refine ⟨29171373044653725027264197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19447582029769150018176131 29171373044653725027264197)
                ·
                  refine ⟨5469632445872573442612037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29171373044653725027264197 5469632445872573442612037)
                  ·
                    refine ⟨1025556083601107520489757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5469632445872573442612037 1025556083601107520489757)
                    ·
                      rfl

theorem cell22_2995895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_2995895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995895 prefixEnd_2995895 := by exact prefixLift 2995895
  have htrace : WordTrace (prefixWord ++ tailWord_2995895) baseStart_2995895 baseEnd_2995895 := by
    simpa [prefixWord, tailWord_2995895, baseEnd_2995895] using wordTrace_append hprefix tailTrace_2995895
  have hstable : (prefixWord ++ tailWord_2995895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995895).length < 2 ^ (prefixWord ++ tailWord_2995895).sum := by decide
  have hdescent : baseEnd_2995895 < baseStart_2995895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995914 : List Nat := [3, 1, 2, 1, 5, 1, 1, 3, 2, 3]
def baseStart_2995914 : Nat := 118140960795 + 2995914 * 2 ^ 59
def prefixEnd_2995914 : Nat := 4983230072969 + 3 ^ 40 * 2995914 * 2
def baseEnd_2995914 : Nat := 1025562587689397804264699

theorem tailTrace_2995914 : CollatzResearch.WordTrace tailWord_2995914 prefixEnd_2995914 1025562587689397804264699 := by
  unfold tailWord_2995914
  simp only [CollatzResearch.WordTrace]
  refine ⟨27317490117080678555216699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72846640312215142813911197 27317490117080678555216699)
  ·
    refine ⟨40976235175621017832825049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27317490117080678555216699 40976235175621017832825049)
    ·
      refine ⟨30732176381715763374618787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40976235175621017832825049 30732176381715763374618787)
      ·
        refine ⟨46098264572573645061928181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30732176381715763374618787 46098264572573645061928181)
        ·
          refine ⟨4321712303678779224555767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46098264572573645061928181 4321712303678779224555767)
          ·
            refine ⟨6482568455518168836833651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4321712303678779224555767 6482568455518168836833651)
            ·
              refine ⟨9723852683277253255250477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6482568455518168836833651 9723852683277253255250477)
              ·
                refine ⟨3646444756228969970718929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9723852683277253255250477 3646444756228969970718929)
                ·
                  refine ⟨2734833567171727478039197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3646444756228969970718929 2734833567171727478039197)
                  ·
                    refine ⟨1025562587689397804264699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2734833567171727478039197 1025562587689397804264699)
                    ·
                      rfl

theorem cell22_2995914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_2995914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995914 prefixEnd_2995914 := by exact prefixLift 2995914
  have htrace : WordTrace (prefixWord ++ tailWord_2995914) baseStart_2995914 baseEnd_2995914 := by
    simpa [prefixWord, tailWord_2995914, baseEnd_2995914] using wordTrace_append hprefix tailTrace_2995914
  have hstable : (prefixWord ++ tailWord_2995914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995914).length < 2 ^ (prefixWord ++ tailWord_2995914).sum := by decide
  have hdescent : baseEnd_2995914 < baseStart_2995914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995955 : List Nat := [1, 1, 1, 2, 2, 3, 3, 4, 5]
def baseStart_2995955 : Nat := 118140960795 + 2995955 * 2 ^ 59
def prefixEnd_2995955 : Nat := 4983230072969 + 3 ^ 40 * 2995955 * 2
def baseEnd_2995955 : Nat := 341858874275762454663191

theorem tailTrace_2995955 : CollatzResearch.WordTrace tailWord_2995955 prefixEnd_2995955 341858874275762454663191 := by
  unfold tailWord_2995955
  simp only [CollatzResearch.WordTrace]
  refine ⟨109271455861174178223109319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72847637240782785482072879 109271455861174178223109319)
  ·
    refine ⟨163907183791761267334663979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109271455861174178223109319 163907183791761267334663979)
    ·
      refine ⟨245860775687641901001995969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163907183791761267334663979 245860775687641901001995969)
      ·
        refine ⟨184395581765731425751496977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245860775687641901001995969 184395581765731425751496977)
        ·
          refine ⟨138296686324298569313622733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184395581765731425751496977 138296686324298569313622733)
          ·
            refine ⟨51861257371611963492608525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138296686324298569313622733 51861257371611963492608525)
            ·
              refine ⟨19447971514354486309728197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51861257371611963492608525 19447971514354486309728197)
              ·
                refine ⟨3646494658941466183074037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19447971514354486309728197 3646494658941466183074037)
                ·
                  refine ⟨341858874275762454663191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3646494658941466183074037 341858874275762454663191)
                  ·
                    rfl

theorem cell22_2995955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 5].length) (baseStart_2995955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995955 prefixEnd_2995955 := by exact prefixLift 2995955
  have htrace : WordTrace (prefixWord ++ tailWord_2995955) baseStart_2995955 baseEnd_2995955 := by
    simpa [prefixWord, tailWord_2995955, baseEnd_2995955] using wordTrace_append hprefix tailTrace_2995955
  have hstable : (prefixWord ++ tailWord_2995955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995955).length < 2 ^ (prefixWord ++ tailWord_2995955).sum := by decide
  have hdescent : baseEnd_2995955 < baseStart_2995955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2995972 : List Nat := [2, 3, 2, 2, 1, 2, 2, 3, 5]
def baseStart_2995972 : Nat := 118140960795 + 2995972 * 2 ^ 59
def prefixEnd_2995972 : Nat := 4983230072969 + 3 ^ 40 * 2995972 * 2
def baseEnd_2995972 : Nat := 341860814091568328771507

theorem tailTrace_2995972 : CollatzResearch.WordTrace tailWord_2995972 prefixEnd_2995972 341860814091568328771507 := by
  unfold tailWord_2995972
  simp only [CollatzResearch.WordTrace]
  refine ⟨54636037951056295063239085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72848050601408393417652113 54636037951056295063239085)
  ·
    refine ⟨20488514231646110648714657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54636037951056295063239085 20488514231646110648714657)
    ·
      refine ⟨15366385673734582986535993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20488514231646110648714657 15366385673734582986535993)
      ·
        refine ⟨11524789255300937239901995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15366385673734582986535993 11524789255300937239901995)
        ·
          refine ⟨17287183882951405859852993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11524789255300937239901995 17287183882951405859852993)
          ·
            refine ⟨12965387912213554394889745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17287183882951405859852993 12965387912213554394889745)
            ·
              refine ⟨9724040934160165796167309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12965387912213554394889745 9724040934160165796167309)
              ·
                refine ⟨3646515350310062173562741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9724040934160165796167309 3646515350310062173562741)
                ·
                  refine ⟨341860814091568328771507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3646515350310062173562741 341860814091568328771507)
                  ·
                    rfl

theorem cell22_2995972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_2995972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2995972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2995972 prefixEnd_2995972 := by exact prefixLift 2995972
  have htrace : WordTrace (prefixWord ++ tailWord_2995972) baseStart_2995972 baseEnd_2995972 := by
    simpa [prefixWord, tailWord_2995972, baseEnd_2995972] using wordTrace_append hprefix tailTrace_2995972
  have hstable : (prefixWord ++ tailWord_2995972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2995972).length < 2 ^ (prefixWord ++ tailWord_2995972).sum := by decide
  have hdescent : baseEnd_2995972 < baseStart_2995972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2995972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996000 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 8]
def baseStart_2996000 : Nat := 118140960795 + 2996000 * 2 ^ 59
def prefixEnd_2996000 : Nat := 4983230072969 + 3 ^ 40 * 2996000 * 2
def baseEnd_2996000 : Nat := 341864009082307415538145

theorem tailTrace_2996000 : CollatzResearch.WordTrace tailWord_2996000 prefixEnd_2996000 341864009082307415538145 := by
  unfold tailWord_2996000
  simp only [CollatzResearch.WordTrace]
  refine ⟨54636548573005575454248727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72848731430674100605664969 54636548573005575454248727)
  ·
    refine ⟨81954822859508363181373091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54636548573005575454248727 81954822859508363181373091)
    ·
      refine ⟨122932234289262544772059637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81954822859508363181373091 122932234289262544772059637)
      ·
        refine ⟨11524896964618363572380591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122932234289262544772059637 11524896964618363572380591)
        ·
          refine ⟨17287345446927545358570887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11524896964618363572380591 17287345446927545358570887)
          ·
            refine ⟨25931018170391318037856331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17287345446927545358570887 25931018170391318037856331)
            ·
              refine ⟨38896527255586977056784497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25931018170391318037856331 38896527255586977056784497)
              ·
                refine ⟨29172395441690232792588373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38896527255586977056784497 29172395441690232792588373)
                ·
                  refine ⟨341864009082307415538145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29172395441690232792588373 341864009082307415538145)
                  ·
                    rfl

theorem cell22_2996000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 8].length) (baseStart_2996000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996000 prefixEnd_2996000 := by exact prefixLift 2996000
  have htrace : WordTrace (prefixWord ++ tailWord_2996000) baseStart_2996000 baseEnd_2996000 := by
    simpa [prefixWord, tailWord_2996000, baseEnd_2996000] using wordTrace_append hprefix tailTrace_2996000
  have hstable : (prefixWord ++ tailWord_2996000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996000).length < 2 ^ (prefixWord ++ tailWord_2996000).sum := by decide
  have hdescent : baseEnd_2996000 < baseStart_2996000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996017 : List Nat := [1, 2, 2, 3, 2, 3, 2, 1, 6]
def baseStart_2996017 : Nat := 118140960795 + 2996017 * 2 ^ 59
def prefixEnd_2996017 : Nat := 4983230072969 + 3 ^ 40 * 2996017 * 2
def baseEnd_2996017 : Nat := 341865948898113289646461

theorem tailTrace_2996017 : CollatzResearch.WordTrace tailWord_2996017 prefixEnd_2996017 341865948898113289646461 := by
  unfold tailWord_2996017
  simp only [CollatzResearch.WordTrace]
  refine ⟨109273717186949562811866305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72849144791299708541244203 109273717186949562811866305)
  ·
    refine ⟨81955287890212172108899729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109273717186949562811866305 81955287890212172108899729)
    ·
      refine ⟨61466465917659129081674797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81955287890212172108899729 61466465917659129081674797)
      ·
        refine ⟨23049924719122173405628049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61466465917659129081674797 23049924719122173405628049)
        ·
          refine ⟨17287443539341630054221037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23049924719122173405628049 17287443539341630054221037)
          ·
            refine ⟨6482791327253111270332889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17287443539341630054221037 6482791327253111270332889)
            ·
              refine ⟨4862093495439833452749667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6482791327253111270332889 4862093495439833452749667)
              ·
                refine ⟨7293140243159750179124501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4862093495439833452749667 7293140243159750179124501)
                ·
                  refine ⟨341865948898113289646461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7293140243159750179124501 341865948898113289646461)
                  ·
                    rfl

theorem cell22_2996017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 6].length) (baseStart_2996017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996017 prefixEnd_2996017 := by exact prefixLift 2996017
  have htrace : WordTrace (prefixWord ++ tailWord_2996017) baseStart_2996017 baseEnd_2996017 := by
    simpa [prefixWord, tailWord_2996017, baseEnd_2996017] using wordTrace_append hprefix tailTrace_2996017
  have hstable : (prefixWord ++ tailWord_2996017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996017).length < 2 ^ (prefixWord ++ tailWord_2996017).sum := by decide
  have hdescent : baseEnd_2996017 < baseStart_2996017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996075 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 2, 6]
def baseStart_2996075 : Nat := 118140960795 + 2996075 * 2 ^ 59
def prefixEnd_2996075 : Nat := 4983230072969 + 3 ^ 40 * 2996075 * 2
def baseEnd_2996075 : Nat := 1025617701279647050989205

theorem tailTrace_2996075 : CollatzResearch.WordTrace tailWord_2996075 prefixEnd_2996075 1025617701279647050989205 := by
  unfold tailWord_2996075
  simp only [CollatzResearch.WordTrace]
  refine ⟨109275832620739438717477679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72850555080492959144985119 109275832620739438717477679)
  ·
    refine ⟨163913748931109158076216519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109275832620739438717477679 163913748931109158076216519)
    ·
      refine ⟨245870623396663737114324779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163913748931109158076216519 245870623396663737114324779)
      ·
        refine ⟨368805935094995605671487169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245870623396663737114324779 368805935094995605671487169)
        ·
          refine ⟨276604451321246704253615377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368805935094995605671487169 276604451321246704253615377)
          ·
            refine ⟨207453338490935028190211533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276604451321246704253615377 207453338490935028190211533)
            ·
              refine ⟨77795001934100635571329325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207453338490935028190211533 77795001934100635571329325)
              ·
                refine ⟨29173125725287738339248497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77795001934100635571329325 29173125725287738339248497)
                ·
                  refine ⟨21879844293965803754436373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29173125725287738339248497 21879844293965803754436373)
                  ·
                    refine ⟨1025617701279647050989205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21879844293965803754436373 1025617701279647050989205)
                    ·
                      rfl

theorem cell22_2996075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 6].length) (baseStart_2996075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996075 prefixEnd_2996075 := by exact prefixLift 2996075
  have htrace : WordTrace (prefixWord ++ tailWord_2996075) baseStart_2996075 baseEnd_2996075 := by
    simpa [prefixWord, tailWord_2996075, baseEnd_2996075] using wordTrace_append hprefix tailTrace_2996075
  have hstable : (prefixWord ++ tailWord_2996075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996075).length < 2 ^ (prefixWord ++ tailWord_2996075).sum := by decide
  have hdescent : baseEnd_2996075 < baseStart_2996075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996124 : List Nat := [2, 2, 3, 3, 1, 1, 1, 4, 5]
def baseStart_2996124 : Nat := 118140960795 + 2996124 * 2 ^ 59
def prefixEnd_2996124 : Nat := 4983230072969 + 3 ^ 40 * 2996124 * 2
def baseEnd_2996124 : Nat := 341878158327009085504685

theorem tailTrace_2996124 : CollatzResearch.WordTrace tailWord_2996124 prefixEnd_2996124 341878158327009085504685 := by
  unfold tailWord_2996124
  simp only [CollatzResearch.WordTrace]
  refine ⟨54638809898780960043005713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72851746531707946724007617 54638809898780960043005713)
  ·
    refine ⟨40979107424085720032254285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54638809898780960043005713 40979107424085720032254285)
    ·
      refine ⟨15367165284032145012095357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40979107424085720032254285 15367165284032145012095357)
      ·
        refine ⟨5762686981512054379535759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15367165284032145012095357 5762686981512054379535759)
        ·
          refine ⟨8644030472268081569303639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5762686981512054379535759 8644030472268081569303639)
          ·
            refine ⟨12966045708402122353955459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8644030472268081569303639 12966045708402122353955459)
            ·
              refine ⟨19449068562603183530933189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12966045708402122353955459 19449068562603183530933189)
              ·
                refine ⟨3646700355488096912049973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19449068562603183530933189 3646700355488096912049973)
                ·
                  refine ⟨341878158327009085504685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3646700355488096912049973 341878158327009085504685)
                  ·
                    rfl

theorem cell22_2996124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_2996124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996124 prefixEnd_2996124 := by exact prefixLift 2996124
  have htrace : WordTrace (prefixWord ++ tailWord_2996124) baseStart_2996124 baseEnd_2996124 := by
    simpa [prefixWord, tailWord_2996124, baseEnd_2996124] using wordTrace_append hprefix tailTrace_2996124
  have hstable : (prefixWord ++ tailWord_2996124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996124).length < 2 ^ (prefixWord ++ tailWord_2996124).sum := by decide
  have hdescent : baseEnd_2996124 < baseStart_2996124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996152 : List Nat := [2, 1, 2, 1, 2, 3, 3, 2, 6]
def baseStart_2996152 : Nat := 118140960795 + 2996152 * 2 ^ 59
def prefixEnd_2996152 : Nat := 4983230072969 + 3 ^ 40 * 2996152 * 2
def baseEnd_2996152 : Nat := 341881353317748172271323

theorem tailTrace_2996152 : CollatzResearch.WordTrace tailWord_2996152 prefixEnd_2996152 341881353317748172271323 := by
  unfold tailWord_2996152
  simp only [CollatzResearch.WordTrace]
  refine ⟨54639320520730240434015355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72852427360973653912020473 54639320520730240434015355)
  ·
    refine ⟨81958980781095360651023033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54639320520730240434015355 81958980781095360651023033)
    ·
      refine ⟨61469235585821520488267275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81958980781095360651023033 61469235585821520488267275)
      ·
        refine ⟨92203853378732280732400913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61469235585821520488267275 92203853378732280732400913)
        ·
          refine ⟨69152890034049210549300685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92203853378732280732400913 69152890034049210549300685)
          ·
            refine ⟨25932333762768453955987757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69152890034049210549300685 25932333762768453955987757)
            ·
              refine ⟨9724625161038170233495409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25932333762768453955987757 9724625161038170233495409)
              ·
                refine ⟨7293468870778627675121557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9724625161038170233495409 7293468870778627675121557)
                ·
                  refine ⟨341881353317748172271323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7293468870778627675121557 341881353317748172271323)
                  ·
                    rfl

theorem cell22_2996152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 6].length) (baseStart_2996152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996152 prefixEnd_2996152 := by exact prefixLift 2996152
  have htrace : WordTrace (prefixWord ++ tailWord_2996152) baseStart_2996152 baseEnd_2996152 := by
    simpa [prefixWord, tailWord_2996152, baseEnd_2996152] using wordTrace_append hprefix tailTrace_2996152
  have hstable : (prefixWord ++ tailWord_2996152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996152).length < 2 ^ (prefixWord ++ tailWord_2996152).sum := by decide
  have hdescent : baseEnd_2996152 < baseStart_2996152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996184 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 4, 3]
def baseStart_2996184 : Nat := 118140960795 + 2996184 * 2 ^ 59
def prefixEnd_2996184 : Nat := 4983230072969 + 3 ^ 40 * 2996184 * 2
def baseEnd_2996184 : Nat := 1025655014207207100013871

theorem tailTrace_2996184 : CollatzResearch.WordTrace tailWord_2996184 prefixEnd_2996184 1025655014207207100013871 := by
  unfold tailWord_2996184
  simp only [CollatzResearch.WordTrace]
  refine ⟨54639904088672275166597803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72853205451563033555463737 54639904088672275166597803)
  ·
    refine ⟨81959856133008412749896705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54639904088672275166597803 81959856133008412749896705)
    ·
      refine ⟨61469892099756309562422529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81959856133008412749896705 61469892099756309562422529)
      ·
        refine ⟨46102419074817232171816897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61469892099756309562422529 46102419074817232171816897)
        ·
          refine ⟨34576814306112924128862673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46102419074817232171816897 34576814306112924128862673)
          ·
            refine ⟨25932610729584693096647005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34576814306112924128862673 25932610729584693096647005)
            ·
              refine ⟨9724729023594259911242627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25932610729584693096647005 9724729023594259911242627)
              ·
                refine ⟨14587093535391389866863941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9724729023594259911242627 14587093535391389866863941)
                ·
                  refine ⟨2735080037885885600036989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14587093535391389866863941 2735080037885885600036989)
                  ·
                    refine ⟨1025655014207207100013871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2735080037885885600036989 1025655014207207100013871)
                    ·
                      rfl

theorem cell22_2996184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_2996184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996184 prefixEnd_2996184 := by exact prefixLift 2996184
  have htrace : WordTrace (prefixWord ++ tailWord_2996184) baseStart_2996184 baseEnd_2996184 := by
    simpa [prefixWord, tailWord_2996184, baseEnd_2996184] using wordTrace_append hprefix tailTrace_2996184
  have hstable : (prefixWord ++ tailWord_2996184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996184).length < 2 ^ (prefixWord ++ tailWord_2996184).sum := by decide
  have hdescent : baseEnd_2996184 < baseStart_2996184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996237 : List Nat := [1, 7, 1, 2, 2, 1, 1, 1, 6]
def baseStart_2996237 : Nat := 118140960795 + 2996237 * 2 ^ 59
def prefixEnd_2996237 : Nat := 4983230072969 + 3 ^ 40 * 2996237 * 2
def baseEnd_2996237 : Nat := 341891052396777542812903

theorem tailTrace_2996237 : CollatzResearch.WordTrace tailWord_2996237 prefixEnd_2996237 341891052396777542812903 := by
  unfold tailWord_2996237
  simp only [CollatzResearch.WordTrace]
  refine ⟨109281741246152540384874965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72854494164101693589916643 109281741246152540384874965)
  ·
    refine ⟨2561290810456700165270507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 109281741246152540384874965 2561290810456700165270507)
    ·
      refine ⟨3841936215685050247905761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2561290810456700165270507 3841936215685050247905761)
      ·
        refine ⟨2881452161763787685929321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3841936215685050247905761 2881452161763787685929321)
        ·
          refine ⟨2161089121322840764446991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2881452161763787685929321 2161089121322840764446991)
          ·
            refine ⟨3241633681984261146670487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2161089121322840764446991 3241633681984261146670487)
            ·
              refine ⟨4862450522976391720005731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3241633681984261146670487 4862450522976391720005731)
              ·
                refine ⟨7293675784464587580008597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4862450522976391720005731 7293675784464587580008597)
                ·
                  refine ⟨341891052396777542812903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7293675784464587580008597 341891052396777542812903)
                  ·
                    rfl

theorem cell22_2996237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_2996237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996237 prefixEnd_2996237 := by exact prefixLift 2996237
  have htrace : WordTrace (prefixWord ++ tailWord_2996237) baseStart_2996237 baseEnd_2996237 := by
    simpa [prefixWord, tailWord_2996237, baseEnd_2996237] using wordTrace_append hprefix tailTrace_2996237
  have hstable : (prefixWord ++ tailWord_2996237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996237).length < 2 ^ (prefixWord ++ tailWord_2996237).sum := by decide
  have hdescent : baseEnd_2996237 < baseStart_2996237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996259 : List Nat := [1, 1, 1, 4, 3, 1, 3, 3, 5]
def baseStart_2996259 : Nat := 118140960795 + 2996259 * 2 ^ 59
def prefixEnd_2996259 : Nat := 4983230072969 + 3 ^ 40 * 2996259 * 2
def baseEnd_2996259 : Nat := 341893562746643968129547

theorem tailTrace_2996259 : CollatzResearch.WordTrace tailWord_2996259 prefixEnd_2996259 341893562746643968129547 := by
  unfold tailWord_2996259
  simp only [CollatzResearch.WordTrace]
  refine ⟨109282543652072838142175831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72855029101381892094783887 109282543652072838142175831)
  ·
    refine ⟨163923815478109257213263747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109282543652072838142175831 163923815478109257213263747)
    ·
      refine ⟨245885723217163885819895621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163923815478109257213263747 245885723217163885819895621)
      ·
        refine ⟨46103573103218228591230429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 245885723217163885819895621 46103573103218228591230429)
        ·
          refine ⟨17288839913706835721711411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46103573103218228591230429 17288839913706835721711411)
          ·
            refine ⟨25933259870560253582567117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17288839913706835721711411 25933259870560253582567117)
            ·
              refine ⟨9724972451460095093462669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25933259870560253582567117 9724972451460095093462669)
              ·
                refine ⟨3646864669297535660048501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9724972451460095093462669 3646864669297535660048501)
                ·
                  refine ⟨341893562746643968129547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3646864669297535660048501 341893562746643968129547)
                  ·
                    rfl

theorem cell22_2996259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 5].length) (baseStart_2996259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996259 prefixEnd_2996259 := by exact prefixLift 2996259
  have htrace : WordTrace (prefixWord ++ tailWord_2996259) baseStart_2996259 baseEnd_2996259 := by
    simpa [prefixWord, tailWord_2996259, baseEnd_2996259] using wordTrace_append hprefix tailTrace_2996259
  have hstable : (prefixWord ++ tailWord_2996259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996259).length < 2 ^ (prefixWord ++ tailWord_2996259).sum := by decide
  have hdescent : baseEnd_2996259 < baseStart_2996259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996338 : List Nat := [3, 2, 1, 2, 2, 3, 2, 3, 4]
def baseStart_2996338 : Nat := 118140960795 + 2996338 * 2 ^ 59
def prefixEnd_2996338 : Nat := 4983230072969 + 3 ^ 40 * 2996338 * 2
def baseEnd_2996338 : Nat := 341902577184800677221133

theorem tailTrace_2996338 : CollatzResearch.WordTrace tailWord_2996338 prefixEnd_2996338 341902577184800677221133 := by
  unfold tailWord_2996338
  simp only [CollatzResearch.WordTrace]
  refine ⟨27321356254696658658575417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72856950012524423089534445 27321356254696658658575417)
  ·
    refine ⟨20491017191022493993931563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27321356254696658658575417 20491017191022493993931563)
    ·
      refine ⟨30736525786533740990897345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20491017191022493993931563 30736525786533740990897345)
      ·
        refine ⟨23052394339900305743173009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30736525786533740990897345 23052394339900305743173009)
        ·
          refine ⟨17289295754925229307379757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23052394339900305743173009 17289295754925229307379757)
          ·
            refine ⟨6483485908096960990267409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17289295754925229307379757 6483485908096960990267409)
            ·
              refine ⟨4862614431072720742700557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6483485908096960990267409 4862614431072720742700557)
              ·
                refine ⟨1823480411652270278512709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4862614431072720742700557 1823480411652270278512709)
                ·
                  refine ⟨341902577184800677221133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1823480411652270278512709 341902577184800677221133)
                  ·
                    rfl

theorem cell22_2996338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_2996338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996338 prefixEnd_2996338 := by exact prefixLift 2996338
  have htrace : WordTrace (prefixWord ++ tailWord_2996338) baseStart_2996338 baseEnd_2996338 := by
    simpa [prefixWord, tailWord_2996338, baseEnd_2996338] using wordTrace_append hprefix tailTrace_2996338
  have hstable : (prefixWord ++ tailWord_2996338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996338).length < 2 ^ (prefixWord ++ tailWord_2996338).sum := by decide
  have hdescent : baseEnd_2996338 < baseStart_2996338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996349 : List Nat := [1, 4, 1, 1, 3, 3, 9]
def baseStart_2996349 : Nat := 118140960795 + 2996349 * 2 ^ 59
def prefixEnd_2996349 : Nat := 4983230072969 + 3 ^ 40 * 2996349 * 2
def baseEnd_2996349 : Nat := 37989314706637098875495

theorem tailTrace_2996349 : CollatzResearch.WordTrace tailWord_2996349 prefixEnd_2996349 37989314706637098875495 := by
  unfold tailWord_2996349
  simp only [CollatzResearch.WordTrace]
  refine ⟨109285826221746783512952101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72857217481164522341968067 109285826221746783512952101)
  ·
    refine ⟨20491092416577521908678519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109285826221746783512952101 20491092416577521908678519)
    ·
      refine ⟨30736638624866282863017779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20491092416577521908678519 30736638624866282863017779)
      ·
        refine ⟨46104957937299424294526669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30736638624866282863017779 46104957937299424294526669)
        ·
          refine ⟨17289359226487284110447501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46104957937299424294526669 17289359226487284110447501)
          ·
            refine ⟨6483509709932731541417813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17289359226487284110447501 6483509709932731541417813)
            ·
              refine ⟨37989314706637098875495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6483509709932731541417813 37989314706637098875495)
              ·
                rfl

theorem cell22_2996349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 9].length) (baseStart_2996349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996349 prefixEnd_2996349 := by exact prefixLift 2996349
  have htrace : WordTrace (prefixWord ++ tailWord_2996349) baseStart_2996349 baseEnd_2996349 := by
    simpa [prefixWord, tailWord_2996349, baseEnd_2996349] using wordTrace_append hprefix tailTrace_2996349
  have hstable : (prefixWord ++ tailWord_2996349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996349).length < 2 ^ (prefixWord ++ tailWord_2996349).sum := by decide
  have hdescent : baseEnd_2996349 < baseStart_2996349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996353 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 4, 3]
def baseStart_2996353 : Nat := 118140960795 + 2996353 * 2 ^ 59
def prefixEnd_2996353 : Nat := 4983230072969 + 3 ^ 40 * 2996353 * 2
def baseEnd_2996353 : Nat := 1025712866360946992538353

theorem tailTrace_2996353 : CollatzResearch.WordTrace tailWord_2996353 prefixEnd_2996353 1025712866360946992538353 := by
  unfold tailWord_2996353
  simp only [CollatzResearch.WordTrace]
  refine ⟨109285972113732292196097713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72857314742488194797398475 109285972113732292196097713)
  ·
    refine ⟨81964479085299219147073285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109285972113732292196097713 81964479085299219147073285)
    ·
      refine ⟨15368339828493603590076241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81964479085299219147073285 15368339828493603590076241)
      ·
        refine ⟨11526254871370202692557181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15368339828493603590076241 11526254871370202692557181)
        ·
          refine ⟨4322345576763826009708943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11526254871370202692557181 4322345576763826009708943)
          ·
            refine ⟨6483518365145739014563415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4322345576763826009708943 6483518365145739014563415)
            ·
              refine ⟨9725277547718608521845123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6483518365145739014563415 9725277547718608521845123)
              ·
                refine ⟨14587916321577912782767685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9725277547718608521845123 14587916321577912782767685)
                ·
                  refine ⟨2735234310295858646768941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14587916321577912782767685 2735234310295858646768941)
                  ·
                    refine ⟨1025712866360946992538353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2735234310295858646768941 1025712866360946992538353)
                    ·
                      rfl

theorem cell22_2996353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_2996353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996353 prefixEnd_2996353 := by exact prefixLift 2996353
  have htrace : WordTrace (prefixWord ++ tailWord_2996353) baseStart_2996353 baseEnd_2996353 := by
    simpa [prefixWord, tailWord_2996353, baseEnd_2996353] using wordTrace_append hprefix tailTrace_2996353
  have hstable : (prefixWord ++ tailWord_2996353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996353).length < 2 ^ (prefixWord ++ tailWord_2996353).sum := by decide
  have hdescent : baseEnd_2996353 < baseStart_2996353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996370 : List Nat := [3, 2, 3, 1, 1, 1, 5, 1, 2, 3]
def baseStart_2996370 : Nat := 118140960795 + 2996370 * 2 ^ 59
def prefixEnd_2996370 : Nat := 4983230072969 + 3 ^ 40 * 2996370 * 2
def baseEnd_2996370 : Nat := 1025718685808364614863301

theorem tailTrace_2996370 : CollatzResearch.WordTrace tailWord_2996370 prefixEnd_2996370 1025718685808364614863301 := by
  unfold tailWord_2996370
  simp only [CollatzResearch.WordTrace]
  refine ⟨27321648038667676024866641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72857728103113802732977709 27321648038667676024866641)
  ·
    refine ⟨20491236029000757018649981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27321648038667676024866641 20491236029000757018649981)
    ·
      refine ⟨7684213510875283881993743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20491236029000757018649981 7684213510875283881993743)
      ·
        refine ⟨11526320266312925822990615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7684213510875283881993743 11526320266312925822990615)
        ·
          refine ⟨17289480399469388734485923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11526320266312925822990615 17289480399469388734485923)
          ·
            refine ⟨25934220599204083101728885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17289480399469388734485923 25934220599204083101728885)
            ·
              refine ⟨2431333181175382790787083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25934220599204083101728885 2431333181175382790787083)
              ·
                refine ⟨3646999771763074186180625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2431333181175382790787083 3646999771763074186180625)
                ·
                  refine ⟨2735249828822305639635469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3646999771763074186180625 2735249828822305639635469)
                  ·
                    refine ⟨1025718685808364614863301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2735249828822305639635469 1025718685808364614863301)
                    ·
                      rfl

theorem cell22_2996370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_2996370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996370 prefixEnd_2996370 := by exact prefixLift 2996370
  have htrace : WordTrace (prefixWord ++ tailWord_2996370) baseStart_2996370 baseEnd_2996370 := by
    simpa [prefixWord, tailWord_2996370, baseEnd_2996370] using wordTrace_append hprefix tailTrace_2996370
  have hstable : (prefixWord ++ tailWord_2996370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996370).length < 2 ^ (prefixWord ++ tailWord_2996370).sum := by decide
  have hdescent : baseEnd_2996370 < baseStart_2996370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996383 : List Nat := [1, 1, 2, 6, 1, 3, 2, 6]
def baseStart_2996383 : Nat := 118140960795 + 2996383 * 2 ^ 59
def prefixEnd_2996383 : Nat := 4983230072969 + 3 ^ 40 * 2996383 * 2
def baseEnd_2996383 : Nat := 113969237330448546032029

theorem tailTrace_2996383 : CollatzResearch.WordTrace tailWord_2996383 prefixEnd_2996383 113969237330448546032029 := by
  unfold tailWord_2996383
  simp only [CollatzResearch.WordTrace]
  refine ⟨109287066303623607319689803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72858044202415738213126535 109287066303623607319689803)
  ·
    refine ⟨163930599455435410979534705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109287066303623607319689803 163930599455435410979534705)
    ·
      refine ⟨122947949591576558234651029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163930599455435410979534705 122947949591576558234651029)
      ·
        refine ⟨5763185137105151167249267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122947949591576558234651029 5763185137105151167249267)
        ·
          refine ⟨8644777705657726750873901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5763185137105151167249267 8644777705657726750873901)
          ·
            refine ⟨3241791639621647531577713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8644777705657726750873901 3241791639621647531577713)
            ·
              refine ⟨2431343729716235648683285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3241791639621647531577713 2431343729716235648683285)
              ·
                refine ⟨113969237330448546032029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2431343729716235648683285 113969237330448546032029)
                ·
                  rfl

theorem cell22_2996383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 6].length) (baseStart_2996383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996383 prefixEnd_2996383 := by exact prefixLift 2996383
  have htrace : WordTrace (prefixWord ++ tailWord_2996383) baseStart_2996383 baseEnd_2996383 := by
    simpa [prefixWord, tailWord_2996383, baseEnd_2996383] using wordTrace_append hprefix tailTrace_2996383
  have hstable : (prefixWord ++ tailWord_2996383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996383).length < 2 ^ (prefixWord ++ tailWord_2996383).sum := by decide
  have hdescent : baseEnd_2996383 < baseStart_2996383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996424 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 2, 8]
def baseStart_2996424 : Nat := 118140960795 + 2996424 * 2 ^ 59
def prefixEnd_2996424 : Nat := 4983230072969 + 3 ^ 40 * 2996424 * 2
def baseEnd_2996424 : Nat := 1025737171111926474013135

theorem tailTrace_2996424 : CollatzResearch.WordTrace tailWord_2996424 prefixEnd_2996424 1025737171111926474013135 := by
  unfold tailWord_2996424
  simp only [CollatzResearch.WordTrace]
  refine ⟨54644280848237535660966163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72859041130983380881288217 54644280848237535660966163)
  ·
    refine ⟨81966421272356303491449245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54644280848237535660966163 81966421272356303491449245)
    ·
      refine ⟨30737407977133613809293467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81966421272356303491449245 30737407977133613809293467)
      ·
        refine ⟨46106111965700420713940201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30737407977133613809293467 46106111965700420713940201)
        ·
          refine ⟨34579583974275315535455151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46106111965700420713940201 34579583974275315535455151)
          ·
            refine ⟨51869375961412973303182727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34579583974275315535455151 51869375961412973303182727)
            ·
              refine ⟨77804063942119459954774091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51869375961412973303182727 77804063942119459954774091)
              ·
                refine ⟨116706095913179189932161137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77804063942119459954774091 116706095913179189932161137)
                ·
                  refine ⟨87529571934884392449120853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116706095913179189932161137 87529571934884392449120853)
                  ·
                    refine ⟨1025737171111926474013135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87529571934884392449120853 1025737171111926474013135)
                    ·
                      rfl

theorem cell22_2996424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_2996424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996424 prefixEnd_2996424 := by exact prefixLift 2996424
  have htrace : WordTrace (prefixWord ++ tailWord_2996424) baseStart_2996424 baseEnd_2996424 := by
    simpa [prefixWord, tailWord_2996424, baseEnd_2996424] using wordTrace_append hprefix tailTrace_2996424
  have hstable : (prefixWord ++ tailWord_2996424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996424).length < 2 ^ (prefixWord ++ tailWord_2996424).sum := by decide
  have hdescent : baseEnd_2996424 < baseStart_2996424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996439 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 8]
def baseStart_2996439 : Nat := 118140960795 + 2996439 * 2 ^ 59
def prefixEnd_2996439 : Nat := 4983230072969 + 3 ^ 40 * 2996439 * 2
def baseEnd_2996439 : Nat := 341914101972823811629363

theorem tailTrace_2996439 : CollatzResearch.WordTrace tailWord_2996439 prefixEnd_2996439 341914101972823811629363 := by
  unfold tailWord_2996439
  simp only [CollatzResearch.WordTrace]
  refine ⟨109289108791420728883728371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72859405860947152589152247 109289108791420728883728371)
  ·
    refine ⟨163933663187131093325592557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109289108791420728883728371 163933663187131093325592557)
    ·
      refine ⟨61475123695174159997097209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163933663187131093325592557 61475123695174159997097209)
      ·
        refine ⟨46106342771380619997822907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61475123695174159997097209 46106342771380619997822907)
        ·
          refine ⟨69159514157070929996734361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46106342771380619997822907 69159514157070929996734361)
          ·
            refine ⟨51869635617803197497550771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69159514157070929996734361 51869635617803197497550771)
            ·
              refine ⟨77804453426704796246326157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51869635617803197497550771 77804453426704796246326157)
              ·
                refine ⟨29176670035014298592372309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77804453426704796246326157 29176670035014298592372309)
                ·
                  refine ⟨341914101972823811629363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29176670035014298592372309 341914101972823811629363)
                  ·
                    rfl

theorem cell22_2996439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 8].length) (baseStart_2996439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996439 prefixEnd_2996439 := by exact prefixLift 2996439
  have htrace : WordTrace (prefixWord ++ tailWord_2996439) baseStart_2996439 baseEnd_2996439 := by
    simpa [prefixWord, tailWord_2996439, baseEnd_2996439] using wordTrace_append hprefix tailTrace_2996439
  have hstable : (prefixWord ++ tailWord_2996439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996439).length < 2 ^ (prefixWord ++ tailWord_2996439).sum := by decide
  have hdescent : baseEnd_2996439 < baseStart_2996439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996488 : List Nat := [2, 1, 3, 2, 3, 2, 2, 1, 1, 5]
def baseStart_2996488 : Nat := 118140960795 + 2996488 * 2 ^ 59
def prefixEnd_2996488 : Nat := 4983230072969 + 3 ^ 40 * 2996488 * 2
def baseEnd_2996488 : Nat := 1025759079619851640412939

theorem tailTrace_2996488 : CollatzResearch.WordTrace tailWord_2996488 prefixEnd_2996488 1025759079619851640412939 := by
  unfold tailWord_2996488
  simp only [CollatzResearch.WordTrace]
  refine ⟨54645447984121605126131059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72860597312162140168174745 54645447984121605126131059)
  ·
    refine ⟨81968171976182407689196589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54645447984121605126131059 81968171976182407689196589)
    ·
      refine ⟨30738064491068402883448721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81968171976182407689196589 30738064491068402883448721)
      ·
        refine ⟨23053548368301302162586541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30738064491068402883448721 23053548368301302162586541)
        ·
          refine ⟨8645080638112988310969953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23053548368301302162586541 8645080638112988310969953)
          ·
            refine ⟨6483810478584741233227465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8645080638112988310969953 6483810478584741233227465)
            ·
              refine ⟨4862857858938555924920599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6483810478584741233227465 4862857858938555924920599)
              ·
                refine ⟨7294286788407833887380899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4862857858938555924920599 7294286788407833887380899)
                ·
                  refine ⟨10941430182611750831071349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7294286788407833887380899 10941430182611750831071349)
                  ·
                    refine ⟨1025759079619851640412939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10941430182611750831071349 1025759079619851640412939)
                    ·
                      rfl

theorem cell22_2996488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_2996488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996488 prefixEnd_2996488 := by exact prefixLift 2996488
  have htrace : WordTrace (prefixWord ++ tailWord_2996488) baseStart_2996488 baseEnd_2996488 := by
    simpa [prefixWord, tailWord_2996488, baseEnd_2996488] using wordTrace_append hprefix tailTrace_2996488
  have hstable : (prefixWord ++ tailWord_2996488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996488).length < 2 ^ (prefixWord ++ tailWord_2996488).sum := by decide
  have hdescent : baseEnd_2996488 < baseStart_2996488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996503 : List Nat := [1, 1, 3, 4, 1, 2, 3, 1, 2, 4]
def baseStart_2996503 : Nat := 118140960795 + 2996503 * 2 ^ 59
def prefixEnd_2996503 : Nat := 4983230072969 + 3 ^ 40 * 2996503 * 2
def baseEnd_2996503 : Nat := 1025764214426396601287893

theorem tailTrace_2996503 : CollatzResearch.WordTrace tailWord_2996503 prefixEnd_2996503 1025764214426396601287893 := by
  unfold tailWord_2996503
  simp only [CollatzResearch.WordTrace]
  refine ⟨109291443063188867814058163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72860962042125911876038775 109291443063188867814058163)
  ·
    refine ⟨163937164594783301721087245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109291443063188867814058163 163937164594783301721087245)
    ·
      refine ⟨61476436723043738145407717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163937164594783301721087245 61476436723043738145407717)
      ·
        refine ⟨11526831885570700902263947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61476436723043738145407717 11526831885570700902263947)
        ·
          refine ⟨17290247828356051353395921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11526831885570700902263947 17290247828356051353395921)
          ·
            refine ⟨12967685871267038515046941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17290247828356051353395921 12967685871267038515046941)
            ·
              refine ⟨4862882201725139443142603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12967685871267038515046941 4862882201725139443142603)
              ·
                refine ⟨7294323302587709164713905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4862882201725139443142603 7294323302587709164713905)
                ·
                  refine ⟨5470742476940781873535429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7294323302587709164713905 5470742476940781873535429)
                  ·
                    refine ⟨1025764214426396601287893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5470742476940781873535429 1025764214426396601287893)
                    ·
                      rfl

theorem cell22_2996503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_2996503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996503 prefixEnd_2996503 := by exact prefixLift 2996503
  have htrace : WordTrace (prefixWord ++ tailWord_2996503) baseStart_2996503 baseEnd_2996503 := by
    simpa [prefixWord, tailWord_2996503, baseEnd_2996503] using wordTrace_append hprefix tailTrace_2996503
  have hstable : (prefixWord ++ tailWord_2996503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996503).length < 2 ^ (prefixWord ++ tailWord_2996503).sum := by decide
  have hdescent : baseEnd_2996503 < baseStart_2996503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996509 : List Nat := [1, 4, 2, 3, 3, 1, 2, 1, 1, 4]
def baseStart_2996509 : Nat := 118140960795 + 2996509 * 2 ^ 59
def prefixEnd_2996509 : Nat := 4983230072969 + 3 ^ 40 * 2996509 * 2
def baseEnd_2996509 : Nat := 1025766268349014585637875

theorem tailTrace_2996509 : CollatzResearch.WordTrace tailWord_2996509 prefixEnd_2996509 1025766268349014585637875 := by
  unfold tailWord_2996509
  simp only [CollatzResearch.WordTrace]
  refine ⟨109291661901167130838776581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72861107934111420559184387 109291661901167130838776581)
  ·
    refine ⟨20492186606468837032270609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109291661901167130838776581 20492186606468837032270609)
    ·
      refine ⟨15369139954851627774202957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20492186606468837032270609 15369139954851627774202957)
      ·
        refine ⟨5763427483069360415326109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15369139954851627774202957 5763427483069360415326109)
        ·
          refine ⟨2161285306151010155747291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5763427483069360415326109 2161285306151010155747291)
          ·
            refine ⟨3241927959226515233620937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2161285306151010155747291 3241927959226515233620937)
            ·
              refine ⟨2431445969419886425215703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3241927959226515233620937 2431445969419886425215703)
              ·
                refine ⟨3647168954129829637823555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2431445969419886425215703 3647168954129829637823555)
                ·
                  refine ⟨5470753431194744456735333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647168954129829637823555 5470753431194744456735333)
                  ·
                    refine ⟨1025766268349014585637875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5470753431194744456735333 1025766268349014585637875)
                    ·
                      rfl

theorem cell22_2996509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_2996509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996509 prefixEnd_2996509 := by exact prefixLift 2996509
  have htrace : WordTrace (prefixWord ++ tailWord_2996509) baseStart_2996509 baseEnd_2996509 := by
    simpa [prefixWord, tailWord_2996509, baseEnd_2996509] using wordTrace_append hprefix tailTrace_2996509
  have hstable : (prefixWord ++ tailWord_2996509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996509).length < 2 ^ (prefixWord ++ tailWord_2996509).sum := by decide
  have hdescent : baseEnd_2996509 < baseStart_2996509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996584 : List Nat := [2, 1, 4, 2, 2, 2, 3, 2, 1, 3]
def baseStart_2996584 : Nat := 118140960795 + 2996584 * 2 ^ 59
def prefixEnd_2996584 : Nat := 4983230072969 + 3 ^ 40 * 2996584 * 2
def baseEnd_2996584 : Nat := 1025791942381739390012645

theorem tailTrace_2996584 : CollatzResearch.WordTrace tailWord_2996584 prefixEnd_2996584 1025791942381739390012645 := by
  unfold tailWord_2996584
  simp only [CollatzResearch.WordTrace]
  refine ⟨54647198687947709323878403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72862931583930279098504537 54647198687947709323878403)
  ·
    refine ⟨81970798031921563985817605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54647198687947709323878403 81970798031921563985817605)
    ·
      refine ⟨15369524630985293247340801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81970798031921563985817605 15369524630985293247340801)
      ·
        refine ⟨11527143473238969935505601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15369524630985293247340801 11527143473238969935505601)
        ·
          refine ⟨8645357604929227451629201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11527143473238969935505601 8645357604929227451629201)
          ·
            refine ⟨6484018203696920588721901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8645357604929227451629201 6484018203696920588721901)
            ·
              refine ⟨2431506826386345220770713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6484018203696920588721901 2431506826386345220770713)
              ·
                refine ⟨1823630119789758915578035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2431506826386345220770713 1823630119789758915578035)
                ·
                  refine ⟨2735445179684638373367053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1823630119789758915578035 2735445179684638373367053)
                  ·
                    refine ⟨1025791942381739390012645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2735445179684638373367053 1025791942381739390012645)
                    ·
                      rfl

theorem cell22_2996584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_2996584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996584 prefixEnd_2996584 := by exact prefixLift 2996584
  have htrace : WordTrace (prefixWord ++ tailWord_2996584) baseStart_2996584 baseEnd_2996584 := by
    simpa [prefixWord, tailWord_2996584, baseEnd_2996584] using wordTrace_append hprefix tailTrace_2996584
  have hstable : (prefixWord ++ tailWord_2996584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996584).length < 2 ^ (prefixWord ++ tailWord_2996584).sum := by decide
  have hdescent : baseEnd_2996584 < baseStart_2996584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996591 : List Nat := [1, 1, 2, 1, 3, 1, 2, 5, 6]
def baseStart_2996591 : Nat := 118140960795 + 2996591 * 2 ^ 59
def prefixEnd_2996591 : Nat := 4983230072969 + 3 ^ 40 * 2996591 * 2
def baseEnd_2996591 : Nat := 341931446208264568362541

theorem tailTrace_2996591 : CollatzResearch.WordTrace tailWord_2996591 prefixEnd_2996591 341931446208264568362541 := by
  unfold tailWord_2996591
  simp only [CollatzResearch.WordTrace]
  refine ⟨109294652686870058843261627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72863101791246705895507751 109294652686870058843261627)
  ·
    refine ⟨163941979030305088264892441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109294652686870058843261627 163941979030305088264892441)
    ·
      refine ⟨122956484272728816198669331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163941979030305088264892441 122956484272728816198669331)
      ·
        refine ⟨184434726409093224298003997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122956484272728816198669331 184434726409093224298003997)
        ·
          refine ⟨69163022403409959111751499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184434726409093224298003997 69163022403409959111751499)
          ·
            refine ⟨103744533605114938667627249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69163022403409959111751499 103744533605114938667627249)
            ·
              refine ⟨77808400203836204000720437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103744533605114938667627249 77808400203836204000720437)
              ·
                refine ⟨7294537519109644125067541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77808400203836204000720437 7294537519109644125067541)
                ·
                  refine ⟨341931446208264568362541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7294537519109644125067541 341931446208264568362541)
                  ·
                    rfl

theorem cell22_2996591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 6].length) (baseStart_2996591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996591 prefixEnd_2996591 := by exact prefixLift 2996591
  have htrace : WordTrace (prefixWord ++ tailWord_2996591) baseStart_2996591 baseEnd_2996591 := by
    simpa [prefixWord, tailWord_2996591, baseEnd_2996591] using wordTrace_append hprefix tailTrace_2996591
  have hstable : (prefixWord ++ tailWord_2996591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996591).length < 2 ^ (prefixWord ++ tailWord_2996591).sum := by decide
  have hdescent : baseEnd_2996591 < baseStart_2996591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996597 : List Nat := [1, 3, 4, 1, 2, 3, 2, 1, 5]
def baseStart_2996597 : Nat := 118140960795 + 2996597 * 2 ^ 59
def prefixEnd_2996597 : Nat := 4983230072969 + 3 ^ 40 * 2996597 * 2
def baseEnd_2996597 : Nat := 341932130849137229812535

theorem tailTrace_2996597 : CollatzResearch.WordTrace tailWord_2996597 prefixEnd_2996597 341932130849137229812535 := by
  unfold tailWord_2996597
  simp only [CollatzResearch.WordTrace]
  refine ⟨109294871524848321867980045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72863247683232214578653363 109294871524848321867980045)
  ·
    refine ⟨40985576821818120700492517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109294871524848321867980045 40985576821818120700492517)
    ·
      refine ⟨7684795654090897631342347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40985576821818120700492517 7684795654090897631342347)
      ·
        refine ⟨11527193481136346447013521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7684795654090897631342347 11527193481136346447013521)
        ·
          refine ⟨8645395110852259835260141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11527193481136346447013521 8645395110852259835260141)
          ·
            refine ⟨3242023166569597438222553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8645395110852259835260141 3242023166569597438222553)
            ·
              refine ⟨2431517374927198078666915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3242023166569597438222553 2431517374927198078666915)
              ·
                refine ⟨3647276062390797118000373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2431517374927198078666915 3647276062390797118000373)
                ·
                  refine ⟨341932130849137229812535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3647276062390797118000373 341932130849137229812535)
                  ·
                    rfl

theorem cell22_2996597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_2996597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996597 prefixEnd_2996597 := by exact prefixLift 2996597
  have htrace : WordTrace (prefixWord ++ tailWord_2996597) baseStart_2996597 baseEnd_2996597 := by
    simpa [prefixWord, tailWord_2996597, baseEnd_2996597] using wordTrace_append hprefix tailTrace_2996597
  have hstable : (prefixWord ++ tailWord_2996597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996597).length < 2 ^ (prefixWord ++ tailWord_2996597).sum := by decide
  have hdescent : baseEnd_2996597 < baseStart_2996597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996636 : List Nat := [2, 2, 3, 15]
def baseStart_2996636 : Nat := 118140960795 + 2996636 * 2 ^ 59
def prefixEnd_2996636 : Nat := 4983230072969 + 3 ^ 40 * 2996636 * 2
def baseEnd_2996636 : Nat := 1407146423929257321965

theorem tailTrace_2996636 : CollatzResearch.WordTrace tailWord_2996636 prefixEnd_2996636 1407146423929257321965 := by
  unfold tailWord_2996636
  simp only [CollatzResearch.WordTrace]
  refine ⟨54648146985853515764324881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72864195981138021019099841 54648146985853515764324881)
  ·
    refine ⟨40986110239390136823243661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54648146985853515764324881 40986110239390136823243661)
    ·
      refine ⟨15369791339771301308716373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40986110239390136823243661 15369791339771301308716373)
      ·
        refine ⟨1407146423929257321965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 15369791339771301308716373 1407146423929257321965)
        ·
          rfl

theorem cell22_2996636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 15].length) (baseStart_2996636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996636 prefixEnd_2996636 := by exact prefixLift 2996636
  have htrace : WordTrace (prefixWord ++ tailWord_2996636) baseStart_2996636 baseEnd_2996636 := by
    simpa [prefixWord, tailWord_2996636, baseEnd_2996636] using wordTrace_append hprefix tailTrace_2996636
  have hstable : (prefixWord ++ tailWord_2996636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996636).length < 2 ^ (prefixWord ++ tailWord_2996636).sum := by decide
  have hdescent : baseEnd_2996636 < baseStart_2996636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996640 : List Nat := [2, 1, 1, 4, 1, 3, 1, 4, 2, 3]
def baseStart_2996640 : Nat := 118140960795 + 2996640 * 2 ^ 59
def prefixEnd_2996640 : Nat := 4983230072969 + 3 ^ 40 * 2996640 * 2
def baseEnd_2996640 : Nat := 1025811112326173910612473

theorem tailTrace_2996640 : CollatzResearch.WordTrace tailWord_2996640 prefixEnd_2996640 1025811112326173910612473 := by
  unfold tailWord_2996640
  simp only [CollatzResearch.WordTrace]
  refine ⟨54648219931846270105897687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72864293242461693474530249 54648219931846270105897687)
  ·
    refine ⟨81972329897769405158846531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54648219931846270105897687 81972329897769405158846531)
    ·
      refine ⟨122958494846654107738269797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81972329897769405158846531 122958494846654107738269797)
      ·
        refine ⟨23054717783747645200925587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122958494846654107738269797 23054717783747645200925587)
        ·
          refine ⟨34582076675621467801388381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23054717783747645200925587 34582076675621467801388381)
          ·
            refine ⟨12968278753358050425520643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34582076675621467801388381 12968278753358050425520643)
            ·
              refine ⟨19452418130037075638280965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12968278753358050425520643 19452418130037075638280965)
              ·
                refine ⟨3647328399381951682177681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19452418130037075638280965 3647328399381951682177681)
                ·
                  refine ⟨2735496299536463761633261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3647328399381951682177681 2735496299536463761633261)
                  ·
                    refine ⟨1025811112326173910612473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2735496299536463761633261 1025811112326173910612473)
                    ·
                      rfl

theorem cell22_2996640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 2, 3].length) (baseStart_2996640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996640 prefixEnd_2996640 := by exact prefixLift 2996640
  have htrace : WordTrace (prefixWord ++ tailWord_2996640) baseStart_2996640 baseEnd_2996640 := by
    simpa [prefixWord, tailWord_2996640, baseEnd_2996640] using wordTrace_append hprefix tailTrace_2996640
  have hstable : (prefixWord ++ tailWord_2996640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996640).length < 2 ^ (prefixWord ++ tailWord_2996640).sum := by decide
  have hdescent : baseEnd_2996640 < baseStart_2996640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996698 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 7]
def baseStart_2996698 : Nat := 118140960795 + 2996698 * 2 ^ 59
def prefixEnd_2996698 : Nat := 4983230072969 + 3 ^ 40 * 2996698 * 2
def baseEnd_2996698 : Nat := 341943655637160364220765

theorem tailTrace_2996698 : CollatzResearch.WordTrace tailWord_2996698 prefixEnd_2996698 341943655637160364220765 := by
  unfold tailWord_2996698
  simp only [CollatzResearch.WordTrace]
  refine ⟨27324638824370604029351687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72865703531654944078271165 27324638824370604029351687)
  ·
    refine ⟨40986958236555906044027531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27324638824370604029351687 40986958236555906044027531)
    ·
      refine ⟨61480437354833859066041297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40986958236555906044027531 61480437354833859066041297)
      ·
        refine ⟨46110328016125394299530973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61480437354833859066041297 46110328016125394299530973)
        ·
          refine ⟨17291373006047022862324115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46110328016125394299530973 17291373006047022862324115)
          ·
            refine ⟨25937059509070534293486173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17291373006047022862324115 25937059509070534293486173)
            ·
              refine ⟨9726397315901450360057315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25937059509070534293486173 9726397315901450360057315)
              ·
                refine ⟨14589595973852175540085973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9726397315901450360057315 14589595973852175540085973)
                ·
                  refine ⟨341943655637160364220765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14589595973852175540085973 341943655637160364220765)
                  ·
                    rfl

theorem cell22_2996698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_2996698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996698 prefixEnd_2996698 := by exact prefixLift 2996698
  have htrace : WordTrace (prefixWord ++ tailWord_2996698) baseStart_2996698 baseEnd_2996698 := by
    simpa [prefixWord, tailWord_2996698, baseEnd_2996698] using wordTrace_append hprefix tailTrace_2996698
  have hstable : (prefixWord ++ tailWord_2996698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996698).length < 2 ^ (prefixWord ++ tailWord_2996698).sum := by decide
  have hdescent : baseEnd_2996698 < baseStart_2996698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996715 : List Nat := [1, 1, 1, 1, 2, 3, 7, 1, 5]
def baseStart_2996715 : Nat := 118140960795 + 2996715 * 2 ^ 59
def prefixEnd_2996715 : Nat := 4983230072969 + 3 ^ 40 * 2996715 * 2
def baseEnd_2996715 : Nat := 341945595452966238329081

theorem tailTrace_2996715 : CollatzResearch.WordTrace tailWord_2996715 prefixEnd_2996715 341945595452966238329081 := by
  unfold tailWord_2996715
  simp only [CollatzResearch.WordTrace]
  refine ⟨109299175338420828020775599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72866116892280552013850399 109299175338420828020775599)
  ·
    refine ⟨163948763007631242031163399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109299175338420828020775599 163948763007631242031163399)
    ·
      refine ⟨245923144511446863046745099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163948763007631242031163399 245923144511446863046745099)
      ·
        refine ⟨368884716767170294570117649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245923144511446863046745099 368884716767170294570117649)
        ·
          refine ⟨276663537575377720927588237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368884716767170294570117649 276663537575377720927588237)
          ·
            refine ⟨103748826590766645347845589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276663537575377720927588237 103748826590766645347845589)
            ·
              refine ⟨2431613123221093250340131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 103748826590766645347845589 2431613123221093250340131)
              ·
                refine ⟨3647419684831639875510197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2431613123221093250340131 3647419684831639875510197)
                ·
                  refine ⟨341945595452966238329081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3647419684831639875510197 341945595452966238329081)
                  ·
                    rfl

theorem cell22_2996715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 5].length) (baseStart_2996715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996715 prefixEnd_2996715 := by exact prefixLift 2996715
  have htrace : WordTrace (prefixWord ++ tailWord_2996715) baseStart_2996715 baseEnd_2996715 := by
    simpa [prefixWord, tailWord_2996715, baseEnd_2996715] using wordTrace_append hprefix tailTrace_2996715
  have hstable : (prefixWord ++ tailWord_2996715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996715).length < 2 ^ (prefixWord ++ tailWord_2996715).sum := by decide
  have hdescent : baseEnd_2996715 < baseStart_2996715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996760 : List Nat := [2, 1, 2, 3, 3, 1, 3, 1, 6]
def baseStart_2996760 : Nat := 118140960795 + 2996760 * 2 ^ 59
def prefixEnd_2996760 : Nat := 4983230072969 + 3 ^ 40 * 2996760 * 2
def baseEnd_2996760 : Nat := 341950730259511199204035

theorem tailTrace_2996760 : CollatzResearch.WordTrace tailWord_2996760 prefixEnd_2996760 341950730259511199204035 := by
  unfold tailWord_2996760
  simp only [CollatzResearch.WordTrace]
  refine ⟨54650408311628900353081867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72867211082171867137442489 54650408311628900353081867)
  ·
    refine ⟨81975612467443350529622801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54650408311628900353081867 81975612467443350529622801)
    ·
      refine ⟨61481709350582512897217101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81975612467443350529622801 61481709350582512897217101)
      ·
        refine ⟨23055641006468442336456413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61481709350582512897217101 23055641006468442336456413)
        ·
          refine ⟨8645865377425665876171155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23055641006468442336456413 8645865377425665876171155)
          ·
            refine ⟨12968798066138498814256733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8645865377425665876171155 12968798066138498814256733)
            ·
              refine ⟨4863299274801937055346275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12968798066138498814256733 4863299274801937055346275)
              ·
                refine ⟨7294948912202905583019413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4863299274801937055346275 7294948912202905583019413)
                ·
                  refine ⟨341950730259511199204035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7294948912202905583019413 341950730259511199204035)
                  ·
                    rfl

theorem cell22_2996760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 6].length) (baseStart_2996760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996760 prefixEnd_2996760 := by exact prefixLift 2996760
  have htrace : WordTrace (prefixWord ++ tailWord_2996760) baseStart_2996760 baseEnd_2996760 := by
    simpa [prefixWord, tailWord_2996760, baseEnd_2996760] using wordTrace_append hprefix tailTrace_2996760
  have hstable : (prefixWord ++ tailWord_2996760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996760).length < 2 ^ (prefixWord ++ tailWord_2996760).sum := by decide
  have hdescent : baseEnd_2996760 < baseStart_2996760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996773 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 3, 6]
def baseStart_2996773 : Nat := 118140960795 + 2996773 * 2 ^ 59
def prefixEnd_2996773 : Nat := 4983230072969 + 3 ^ 40 * 2996773 * 2
def baseEnd_2996773 : Nat := 1025856640944205897037065

theorem tailTrace_2996773 : CollatzResearch.WordTrace tailWord_2996773 prefixEnd_2996773 1025856640944205897037065 := by
  unfold tailWord_2996773
  simp only [CollatzResearch.WordTrace]
  refine ⟨109301290772210703926386973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72867527181473802617591315 109301290772210703926386973)
  ·
    refine ⟨40987984039579013972395115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109301290772210703926386973 40987984039579013972395115)
    ·
      refine ⟨61481976059368520958592673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40987984039579013972395115 61481976059368520958592673)
      ·
        refine ⟨46111482044526390718944505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61481976059368520958592673 46111482044526390718944505)
        ·
          refine ⟨34583611533394793039208379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46111482044526390718944505 34583611533394793039208379)
          ·
            refine ⟨51875417300092189558812569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34583611533394793039208379 51875417300092189558812569)
            ·
              refine ⟨38906562975069142169109427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51875417300092189558812569 38906562975069142169109427)
              ·
                refine ⟨58359844462603713253664141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38906562975069142169109427 58359844462603713253664141)
                ·
                  refine ⟨21884941673476392470124053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58359844462603713253664141 21884941673476392470124053)
                  ·
                    refine ⟨1025856640944205897037065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21884941673476392470124053 1025856640944205897037065)
                    ·
                      rfl

theorem cell22_2996773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_2996773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996773 prefixEnd_2996773 := by exact prefixLift 2996773
  have htrace : WordTrace (prefixWord ++ tailWord_2996773) baseStart_2996773 baseEnd_2996773 := by
    simpa [prefixWord, tailWord_2996773, baseEnd_2996773] using wordTrace_append hprefix tailTrace_2996773
  have hstable : (prefixWord ++ tailWord_2996773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996773).length < 2 ^ (prefixWord ++ tailWord_2996773).sum := by decide
  have hdescent : baseEnd_2996773 < baseStart_2996773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996865 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 4, 5]
def baseStart_2996865 : Nat := 118140960795 + 2996865 * 2 ^ 59
def prefixEnd_2996865 : Nat := 4983230072969 + 3 ^ 40 * 2996865 * 2
def baseEnd_2996865 : Nat := 1025888134424348323736783

theorem tailTrace_2996865 : CollatzResearch.WordTrace tailWord_2996865 prefixEnd_2996865 1025888134424348323736783 := by
  unfold tailWord_2996865
  simp only [CollatzResearch.WordTrace]
  refine ⟨109304646287877403638736049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72869764191918269092490699 109304646287877403638736049)
  ·
    refine ⟨81978484715908052729052037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109304646287877403638736049 81978484715908052729052037)
    ·
      refine ⟨15370965884232759886697257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81978484715908052729052037 15370965884232759886697257)
      ·
        refine ⟨11528224413174569915022943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15370965884232759886697257 11528224413174569915022943)
        ·
          refine ⟨17292336619761854872534415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11528224413174569915022943 17292336619761854872534415)
          ·
            refine ⟨25938504929642782308801623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17292336619761854872534415 25938504929642782308801623)
            ·
              refine ⟨38907757394464173463202435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25938504929642782308801623 38907757394464173463202435)
              ·
                refine ⟨58361636091696260194803653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38907757394464173463202435 58361636091696260194803653)
                ·
                  refine ⟨10942806767193048786525685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58361636091696260194803653 10942806767193048786525685)
                  ·
                    refine ⟨1025888134424348323736783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10942806767193048786525685 1025888134424348323736783)
                    ·
                      rfl

theorem cell22_2996865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_2996865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996865 prefixEnd_2996865 := by exact prefixLift 2996865
  have htrace : WordTrace (prefixWord ++ tailWord_2996865) baseStart_2996865 baseEnd_2996865 := by
    simpa [prefixWord, tailWord_2996865, baseEnd_2996865] using wordTrace_append hprefix tailTrace_2996865
  have hstable : (prefixWord ++ tailWord_2996865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996865).length < 2 ^ (prefixWord ++ tailWord_2996865).sum := by decide
  have hdescent : baseEnd_2996865 < baseStart_2996865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996882 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_2996882 : Nat := 118140960795 + 2996882 * 2 ^ 59
def prefixEnd_2996882 : Nat := 4983230072969 + 3 ^ 40 * 2996882 * 2
def baseEnd_2996882 : Nat := 1025893953871765946061731

theorem tailTrace_2996882 : CollatzResearch.WordTrace tailWord_2996882 prefixEnd_2996882 1025893953871765946061731 := by
  unfold tailWord_2996882
  simp only [CollatzResearch.WordTrace]
  refine ⟨27326316582203953885526225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72870177552543877028069933 27326316582203953885526225)
  ·
    refine ⟨20494737436652965414144669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27326316582203953885526225 20494737436652965414144669)
    ·
      refine ⟨7685526538744862030304251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20494737436652965414144669 7685526538744862030304251)
      ·
        refine ⟨11528289808117293045456377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7685526538744862030304251 11528289808117293045456377)
        ·
          refine ⟨8646217356087969784092283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11528289808117293045456377 8646217356087969784092283)
          ·
            refine ⟨12969326034131954676138425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8646217356087969784092283 12969326034131954676138425)
            ·
              refine ⟨9726994525598966007103819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12969326034131954676138425 9726994525598966007103819)
              ·
                refine ⟨14590491788398449010655729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9726994525598966007103819 14590491788398449010655729)
                ·
                  refine ⟨10942868841298836757991797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14590491788398449010655729 10942868841298836757991797)
                  ·
                    refine ⟨1025893953871765946061731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10942868841298836757991797 1025893953871765946061731)
                    ·
                      rfl

theorem cell22_2996882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_2996882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996882 prefixEnd_2996882 := by exact prefixLift 2996882
  have htrace : WordTrace (prefixWord ++ tailWord_2996882) baseStart_2996882 baseEnd_2996882 := by
    simpa [prefixWord, tailWord_2996882, baseEnd_2996882] using wordTrace_append hprefix tailTrace_2996882
  have hstable : (prefixWord ++ tailWord_2996882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996882).length < 2 ^ (prefixWord ++ tailWord_2996882).sum := by decide
  have hdescent : baseEnd_2996882 < baseStart_2996882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996927 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 4, 3]
def baseStart_2996927 : Nat := 118140960795 + 2996927 * 2 ^ 59
def prefixEnd_2996927 : Nat := 4983230072969 + 3 ^ 40 * 2996927 * 2
def baseEnd_2996927 : Nat := 1025909358291400828686593

theorem tailTrace_2996927 : CollatzResearch.WordTrace tailWord_2996927 prefixEnd_2996927 1025909358291400828686593 := by
  unfold tailWord_2996927
  simp only [CollatzResearch.WordTrace]
  refine ⟨109306907613652788227493035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72871271742435192151662023 109306907613652788227493035)
  ·
    refine ⟨163960361420479182341239553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109306907613652788227493035 163960361420479182341239553)
    ·
      refine ⟨122970271065359386755929665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163960361420479182341239553 122970271065359386755929665)
      ·
        refine ⟨92227703299019540066947249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122970271065359386755929665 92227703299019540066947249)
        ·
          refine ⟨69170777474264655050210437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92227703299019540066947249 69170777474264655050210437)
          ·
            refine ⟨12969520776424622821914457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69170777474264655050210437 12969520776424622821914457)
            ·
              refine ⟨9727140582318467116435843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12969520776424622821914457 9727140582318467116435843)
              ·
                refine ⟨14590710873477700674653765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9727140582318467116435843 14590710873477700674653765)
                ·
                  refine ⟨2735758288777068876497581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14590710873477700674653765 2735758288777068876497581)
                  ·
                    refine ⟨1025909358291400828686593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2735758288777068876497581 1025909358291400828686593)
                    ·
                      rfl

theorem cell22_2996927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 3].length) (baseStart_2996927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996927 prefixEnd_2996927 := by exact prefixLift 2996927
  have htrace : WordTrace (prefixWord ++ tailWord_2996927) baseStart_2996927 baseEnd_2996927 := by
    simpa [prefixWord, tailWord_2996927, baseEnd_2996927] using wordTrace_append hprefix tailTrace_2996927
  have hstable : (prefixWord ++ tailWord_2996927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996927).length < 2 ^ (prefixWord ++ tailWord_2996927).sum := by decide
  have hdescent : baseEnd_2996927 < baseStart_2996927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996948 : List Nat := [2, 4, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_2996948 : Nat := 118140960795 + 2996948 * 2 ^ 59
def prefixEnd_2996948 : Nat := 4983230072969 + 3 ^ 40 * 2996948 * 2
def baseEnd_2996948 : Nat := 1025916547020563773911529

theorem tailTrace_2996948 : CollatzResearch.WordTrace tailWord_2996948 prefixEnd_2996948 1025916547020563773911529 := by
  unfold tailWord_2996948
  simp only [CollatzResearch.WordTrace]
  refine ⟨54653836773288354407003749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72871782364384472542671665 54653836773288354407003749)
  ·
    refine ⟨10247594394991566451313203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54653836773288354407003749 10247594394991566451313203)
    ·
      refine ⟨15371391592487349676969805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10247594394991566451313203 15371391592487349676969805)
      ·
        refine ⟨5764271847182756128863677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15371391592487349676969805 5764271847182756128863677)
        ·
          refine ⟨2161601942693533548323879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5764271847182756128863677 2161601942693533548323879)
          ·
            refine ⟨3242402914040300322485819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2161601942693533548323879 3242402914040300322485819)
            ·
              refine ⟨4863604371060450483728729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3242402914040300322485819 4863604371060450483728729)
              ·
                refine ⟨3647703278295337862796547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4863604371060450483728729 3647703278295337862796547)
                ·
                  refine ⟨5471554917443006794194821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3647703278295337862796547 5471554917443006794194821)
                  ·
                    refine ⟨1025916547020563773911529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5471554917443006794194821 1025916547020563773911529)
                    ·
                      rfl

theorem cell22_2996948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_2996948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996948 prefixEnd_2996948 := by exact prefixLift 2996948
  have htrace : WordTrace (prefixWord ++ tailWord_2996948) baseStart_2996948 baseEnd_2996948 := by
    simpa [prefixWord, tailWord_2996948, baseEnd_2996948] using wordTrace_append hprefix tailTrace_2996948
  have hstable : (prefixWord ++ tailWord_2996948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996948).length < 2 ^ (prefixWord ++ tailWord_2996948).sum := by decide
  have hdescent : baseEnd_2996948 < baseStart_2996948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2996985 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 7]
def baseStart_2996985 : Nat := 118140960795 + 2996985 * 2 ^ 59
def prefixEnd_2996985 : Nat := 4983230072969 + 3 ^ 40 * 2996985 * 2
def baseEnd_2996985 : Nat := 341976404292236003578805

theorem tailTrace_2996985 : CollatzResearch.WordTrace tailWord_2996985 prefixEnd_2996985 341976404292236003578805 := by
  unfold tailWord_2996985
  simp only [CollatzResearch.WordTrace]
  refine ⟨109309023047442664133104409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72872682031628442755402939 109309023047442664133104409)
  ·
    refine ⟨81981767285581998099828307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109309023047442664133104409 81981767285581998099828307)
    ·
      refine ⟨122972650928372997149742461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81981767285581998099828307 122972650928372997149742461)
      ·
        refine ⟨46114744098139873931153423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122972650928372997149742461 46114744098139873931153423)
        ·
          refine ⟨69172116147209810896730135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46114744098139873931153423 69172116147209810896730135)
          ·
            refine ⟨103758174220814716345095203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69172116147209810896730135 103758174220814716345095203)
            ·
              refine ⟨155637261331222074517642805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103758174220814716345095203 155637261331222074517642805)
              ·
                refine ⟨14590993249802069486029013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 155637261331222074517642805 14590993249802069486029013)
                ·
                  refine ⟨341976404292236003578805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14590993249802069486029013 341976404292236003578805)
                  ·
                    rfl

theorem cell22_2996985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 7].length) (baseStart_2996985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2996985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2996985 prefixEnd_2996985 := by exact prefixLift 2996985
  have htrace : WordTrace (prefixWord ++ tailWord_2996985) baseStart_2996985 baseEnd_2996985 := by
    simpa [prefixWord, tailWord_2996985, baseEnd_2996985] using wordTrace_append hprefix tailTrace_2996985
  have hstable : (prefixWord ++ tailWord_2996985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2996985).length < 2 ^ (prefixWord ++ tailWord_2996985).sum := by decide
  have hdescent : baseEnd_2996985 < baseStart_2996985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2996985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997002 : List Nat := [3, 1, 2, 2, 1, 2, 1, 5, 5]
def baseStart_2997002 : Nat := 118140960795 + 2997002 * 2 ^ 59
def prefixEnd_2997002 : Nat := 4983230072969 + 3 ^ 40 * 2997002 * 2
def baseEnd_2997002 : Nat := 341978344108041877687121

theorem tailTrace_2997002 : CollatzResearch.WordTrace tailWord_2997002 prefixEnd_2997002 341978344108041877687121 := by
  unfold tailWord_2997002
  simp only [CollatzResearch.WordTrace]
  refine ⟨27327410772095269009118315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72873095392254050690982173 27327410772095269009118315)
  ·
    refine ⟨40991116158142903513677473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27327410772095269009118315 40991116158142903513677473)
    ·
      refine ⟨30743337118607177635258105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40991116158142903513677473 30743337118607177635258105)
      ·
        refine ⟨23057502838955383226443579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30743337118607177635258105 23057502838955383226443579)
        ·
          refine ⟨34586254258433074839665369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23057502838955383226443579 34586254258433074839665369)
          ·
            refine ⟨25939690693824806129749027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34586254258433074839665369 25939690693824806129749027)
            ·
              refine ⟨38909536040737209194623541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25939690693824806129749027 38909536040737209194623541)
              ·
                refine ⟨3647769003819113361995957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38909536040737209194623541 3647769003819113361995957)
                ·
                  refine ⟨341978344108041877687121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3647769003819113361995957 341978344108041877687121)
                  ·
                    rfl

theorem cell22_2997002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_2997002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997002 prefixEnd_2997002 := by exact prefixLift 2997002
  have htrace : WordTrace (prefixWord ++ tailWord_2997002) baseStart_2997002 baseEnd_2997002 := by
    simpa [prefixWord, tailWord_2997002, baseEnd_2997002] using wordTrace_append hprefix tailTrace_2997002
  have hstable : (prefixWord ++ tailWord_2997002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997002).length < 2 ^ (prefixWord ++ tailWord_2997002).sum := by decide
  have hdescent : baseEnd_2997002 < baseStart_2997002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997047 : List Nat := [1, 1, 3, 1, 2, 1, 6, 1, 6]
def baseStart_2997047 : Nat := 118140960795 + 2997047 * 2 ^ 59
def prefixEnd_2997047 : Nat := 4983230072969 + 3 ^ 40 * 2997047 * 2
def baseEnd_2997047 : Nat := 341983478914586838562075

theorem tailTrace_2997047 : CollatzResearch.WordTrace tailWord_2997047 prefixEnd_2997047 341983478914586838562075 := by
  unfold tailWord_2997047
  simp only [CollatzResearch.WordTrace]
  refine ⟨109311284373218048721861395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72874189582145365814574263 109311284373218048721861395)
  ·
    refine ⟨163966926559827073082792093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109311284373218048721861395 163966926559827073082792093)
    ·
      refine ⟨61487597459935152406047035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163966926559827073082792093 61487597459935152406047035)
      ·
        refine ⟨92231396189902728609070553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61487597459935152406047035 92231396189902728609070553)
        ·
          refine ⟨69173547142427046456802915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92231396189902728609070553 69173547142427046456802915)
          ·
            refine ⟨103760320713640569685204373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69173547142427046456802915 103760320713640569685204373)
            ·
              refine ⟨4863765033451901703993955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 103760320713640569685204373 4863765033451901703993955)
              ·
                refine ⟨7295647550177852555990933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4863765033451901703993955 7295647550177852555990933)
                ·
                  refine ⟨341983478914586838562075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7295647550177852555990933 341983478914586838562075)
                  ·
                    rfl

theorem cell22_2997047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 6].length) (baseStart_2997047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997047 prefixEnd_2997047 := by exact prefixLift 2997047
  have htrace : WordTrace (prefixWord ++ tailWord_2997047) baseStart_2997047 baseEnd_2997047 := by
    simpa [prefixWord, tailWord_2997047, baseEnd_2997047] using wordTrace_append hprefix tailTrace_2997047
  have hstable : (prefixWord ++ tailWord_2997047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997047).length < 2 ^ (prefixWord ++ tailWord_2997047).sum := by decide
  have hdescent : baseEnd_2997047 < baseStart_2997047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997077 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 1, 6]
def baseStart_2997077 : Nat := 118140960795 + 2997077 * 2 ^ 59
def prefixEnd_2997077 : Nat := 4983230072969 + 3 ^ 40 * 2997077 * 2
def baseEnd_2997077 : Nat := 1025960706356850437436133

theorem tailTrace_2997077 : CollatzResearch.WordTrace tailWord_2997077 prefixEnd_2997077 1025960706356850437436133 := by
  unfold tailWord_2997077
  simp only [CollatzResearch.WordTrace]
  refine ⟨109312378563109363845453485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72874919042072909230302323 109312378563109363845453485)
  ·
    refine ⟨40992141961166011442045057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109312378563109363845453485 40992141961166011442045057)
    ·
      refine ⟨30744106470874508581533793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40992141961166011442045057 30744106470874508581533793)
      ·
        refine ⟨23058079853155881436150345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30744106470874508581533793 23058079853155881436150345)
        ·
          refine ⟨17293559889866911077112759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23058079853155881436150345 17293559889866911077112759)
          ·
            refine ⟨25940339834800366615669139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17293559889866911077112759 25940339834800366615669139)
            ·
              refine ⟨38910509752200549923503709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25940339834800366615669139 38910509752200549923503709)
              ·
                refine ⟨14591441157075206221313891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38910509752200549923503709 14591441157075206221313891)
                ·
                  refine ⟨21887161735612809331970837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14591441157075206221313891 21887161735612809331970837)
                  ·
                    refine ⟨1025960706356850437436133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21887161735612809331970837 1025960706356850437436133)
                    ·
                      rfl

theorem cell22_2997077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_2997077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997077 prefixEnd_2997077 := by exact prefixLift 2997077
  have htrace : WordTrace (prefixWord ++ tailWord_2997077) baseStart_2997077 baseEnd_2997077 := by
    simpa [prefixWord, tailWord_2997077, baseEnd_2997077] using wordTrace_append hprefix tailTrace_2997077
  have hstable : (prefixWord ++ tailWord_2997077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997077).length < 2 ^ (prefixWord ++ tailWord_2997077).sum := by decide
  have hdescent : baseEnd_2997077 < baseStart_2997077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997079 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 4, 3]
def baseStart_2997079 : Nat := 118140960795 + 2997079 * 2 ^ 59
def prefixEnd_2997079 : Nat := 4983230072969 + 3 ^ 40 * 2997079 * 2
def baseEnd_2997079 : Nat := 1025961390997723098886127

theorem tailTrace_2997079 : CollatzResearch.WordTrace tailWord_2997079 prefixEnd_2997079 1025961390997723098886127 := by
  unfold tailWord_2997079
  simp only [CollatzResearch.WordTrace]
  refine ⟨109312451509102118187026291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72874967672734745458017527 109312451509102118187026291)
  ·
    refine ⟨163968677263653177280539437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109312451509102118187026291 163968677263653177280539437)
    ·
      refine ⟨61488253973869941480202289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163968677263653177280539437 61488253973869941480202289)
      ·
        refine ⟨46116190480402456110151717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61488253973869941480202289 46116190480402456110151717)
        ·
          refine ⟨8646785715075460520653447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46116190480402456110151717 8646785715075460520653447)
          ·
            refine ⟨12970178572613190780980171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8646785715075460520653447 12970178572613190780980171)
            ·
              refine ⟨19455267858919786171470257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12970178572613190780980171 19455267858919786171470257)
              ·
                refine ⟨14591450894189839628602693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19455267858919786171470257 14591450894189839628602693)
                ·
                  refine ⟨2735897042660594930363005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14591450894189839628602693 2735897042660594930363005)
                  ·
                    refine ⟨1025961390997723098886127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2735897042660594930363005 1025961390997723098886127)
                    ·
                      rfl

theorem cell22_2997079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_2997079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997079 prefixEnd_2997079 := by exact prefixLift 2997079
  have htrace : WordTrace (prefixWord ++ tailWord_2997079) baseStart_2997079 baseEnd_2997079 := by
    simpa [prefixWord, tailWord_2997079, baseEnd_2997079] using wordTrace_append hprefix tailTrace_2997079
  have hstable : (prefixWord ++ tailWord_2997079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997079).length < 2 ^ (prefixWord ++ tailWord_2997079).sum := by decide
  have hdescent : baseEnd_2997079 < baseStart_2997079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997081 : List Nat := [1, 2, 1, 2, 2, 6, 1, 3, 4]
def baseStart_2997081 : Nat := 118140960795 + 2997081 * 2 ^ 59
def prefixEnd_2997081 : Nat := 4983230072969 + 3 ^ 40 * 2997081 * 2
def baseEnd_2997081 : Nat := 341987358546198586778707

theorem tailTrace_2997081 : CollatzResearch.WordTrace tailWord_2997081 prefixEnd_2997081 341987358546198586778707 := by
  unfold tailWord_2997081
  simp only [CollatzResearch.WordTrace]
  refine ⟨109312524455094872528599097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72875016303396581685732731 109312524455094872528599097)
  ·
    refine ⟨81984393341321154396449323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109312524455094872528599097 81984393341321154396449323)
    ·
      refine ⟨122976590011981731594673985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81984393341321154396449323 122976590011981731594673985)
      ·
        refine ⟨92232442508986298696005489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122976590011981731594673985 92232442508986298696005489)
        ·
          refine ⟨69174331881739724022004117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92232442508986298696005489 69174331881739724022004117)
          ·
            refine ⟨3242546806956549563531443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69174331881739724022004117 3242546806956549563531443)
            ·
              refine ⟨4863820210434824345297165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3242546806956549563531443 4863820210434824345297165)
              ·
                refine ⟨1823932578913059129486437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4863820210434824345297165 1823932578913059129486437)
                ·
                  refine ⟨341987358546198586778707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1823932578913059129486437 341987358546198586778707)
                  ·
                    rfl

theorem cell22_2997081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 4].length) (baseStart_2997081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997081 prefixEnd_2997081 := by exact prefixLift 2997081
  have htrace : WordTrace (prefixWord ++ tailWord_2997081) baseStart_2997081 baseEnd_2997081 := by
    simpa [prefixWord, tailWord_2997081, baseEnd_2997081] using wordTrace_append hprefix tailTrace_2997081
  have hstable : (prefixWord ++ tailWord_2997081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997081).length < 2 ^ (prefixWord ++ tailWord_2997081).sum := by decide
  have hdescent : baseEnd_2997081 < baseStart_2997081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997092 : List Nat := [2, 3, 1, 1, 4, 1, 10]
def baseStart_2997092 : Nat := 118140960795 + 2997092 * 2 ^ 59
def prefixEnd_2997092 : Nat := 4983230072969 + 3 ^ 40 * 2997092 * 2
def baseEnd_2997092 : Nat := 37998734857903533270781

theorem tailTrace_2997092 : CollatzResearch.WordTrace tailWord_2997092 prefixEnd_2997092 37998734857903533270781 := by
  unfold tailWord_2997092
  simp only [CollatzResearch.WordTrace]
  refine ⟨54656462829027510703624765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72875283772036680938166353 54656462829027510703624765)
  ·
    refine ⟨20496173560885316513859287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54656462829027510703624765 20496173560885316513859287)
    ·
      refine ⟨30744260341327974770788931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20496173560885316513859287 30744260341327974770788931)
      ·
        refine ⟨46116390511991962156183397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30744260341327974770788931 46116390511991962156183397)
        ·
          refine ⟨8646823220998492904284387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46116390511991962156183397 8646823220998492904284387)
          ·
            refine ⟨12970234831497739356426581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8646823220998492904284387 12970234831497739356426581)
            ·
              refine ⟨37998734857903533270781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12970234831497739356426581 37998734857903533270781)
              ·
                rfl

theorem cell22_2997092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 10].length) (baseStart_2997092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997092 prefixEnd_2997092 := by exact prefixLift 2997092
  have htrace : WordTrace (prefixWord ++ tailWord_2997092) baseStart_2997092 baseEnd_2997092 := by
    simpa [prefixWord, tailWord_2997092, baseEnd_2997092] using wordTrace_append hprefix tailTrace_2997092
  have hstable : (prefixWord ++ tailWord_2997092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997092).length < 2 ^ (prefixWord ++ tailWord_2997092).sum := by decide
  have hdescent : baseEnd_2997092 < baseStart_2997092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997109 : List Nat := [1, 3, 4, 1, 1, 3, 2, 7]
def baseStart_2997109 : Nat := 118140960795 + 2997109 * 2 ^ 59
def prefixEnd_2997109 : Nat := 4983230072969 + 3 ^ 40 * 2997109 * 2
def baseEnd_2997109 : Nat := 113996851178979224515115

theorem tailTrace_2997109 : CollatzResearch.WordTrace tailWord_2997109 prefixEnd_2997109 113996851178979224515115 := by
  unfold tailWord_2997109
  simp only [CollatzResearch.WordTrace]
  refine ⟨109313545698993433310618381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72875697132662288873745587 109313545698993433310618381)
  ·
    refine ⟨40992579637122537491481893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109313545698993433310618381 40992579637122537491481893)
    ·
      refine ⟨7686108681960475779652855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40992579637122537491481893 7686108681960475779652855)
      ·
        refine ⟨11529163022940713669479283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7686108681960475779652855 11529163022940713669479283)
        ·
          refine ⟨17293744534411070504218925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11529163022940713669479283 17293744534411070504218925)
          ·
            refine ⟨6485154200404151439082097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17293744534411070504218925 6485154200404151439082097)
            ·
              refine ⟨4863865650303113579311573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6485154200404151439082097 4863865650303113579311573)
              ·
                refine ⟨113996851178979224515115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4863865650303113579311573 113996851178979224515115)
                ·
                  rfl

theorem cell22_2997109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 7].length) (baseStart_2997109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997109 prefixEnd_2997109 := by exact prefixLift 2997109
  have htrace : WordTrace (prefixWord ++ tailWord_2997109) baseStart_2997109 baseEnd_2997109 := by
    simpa [prefixWord, tailWord_2997109, baseEnd_2997109] using wordTrace_append hprefix tailTrace_2997109
  have hstable : (prefixWord ++ tailWord_2997109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997109).length < 2 ^ (prefixWord ++ tailWord_2997109).sum := by decide
  have hdescent : baseEnd_2997109 < baseStart_2997109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997113 : List Nat := [1, 2, 1, 3, 2, 5, 2, 1, 2, 3]
def baseStart_2997113 : Nat := 118140960795 + 2997113 * 2 ^ 59
def prefixEnd_2997113 : Nat := 4983230072969 + 3 ^ 40 * 2997113 * 2
def baseEnd_2997113 : Nat := 1025973029892558343536023

theorem tailTrace_2997113 : CollatzResearch.WordTrace tailWord_2997113 prefixEnd_2997113 1025973029892558343536023 := by
  unfold tailWord_2997113
  simp only [CollatzResearch.WordTrace]
  refine ⟨109313691590978941993763993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72875794393985961329175995 109313691590978941993763993)
  ·
    refine ⟨81985268693234206495322995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109313691590978941993763993 81985268693234206495322995)
    ·
      refine ⟨122977903039851309742984493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81985268693234206495322995 122977903039851309742984493)
      ·
        refine ⟨46116713639944241153619185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122977903039851309742984493 46116713639944241153619185)
        ·
          refine ⟨34587535229958180865214389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46116713639944241153619185 34587535229958180865214389)
          ·
            refine ⟨3242581427808579456113849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34587535229958180865214389 3242581427808579456113849)
            ·
              refine ⟨2431936070856434592085387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3242581427808579456113849 2431936070856434592085387)
              ·
                refine ⟨3647904106284651888128081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2431936070856434592085387 3647904106284651888128081)
                ·
                  refine ⟨2735928079713488916096061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3647904106284651888128081 2735928079713488916096061)
                  ·
                    refine ⟨1025973029892558343536023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2735928079713488916096061 1025973029892558343536023)
                    ·
                      rfl

theorem cell22_2997113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 2, 3].length) (baseStart_2997113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997113 prefixEnd_2997113 := by exact prefixLift 2997113
  have htrace : WordTrace (prefixWord ++ tailWord_2997113) baseStart_2997113 baseEnd_2997113 := by
    simpa [prefixWord, tailWord_2997113, baseEnd_2997113] using wordTrace_append hprefix tailTrace_2997113
  have hstable : (prefixWord ++ tailWord_2997113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997113).length < 2 ^ (prefixWord ++ tailWord_2997113).sum := by decide
  have hdescent : baseEnd_2997113 < baseStart_2997113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997124 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 5, 3]
def baseStart_2997124 : Nat := 118140960795 + 2997124 * 2 ^ 59
def prefixEnd_2997124 : Nat := 4983230072969 + 3 ^ 40 * 2997124 * 2
def baseEnd_2997124 : Nat := 1025976795417357981510989

theorem tailTrace_2997124 : CollatzResearch.WordTrace tailWord_2997124 prefixEnd_2997124 1025976795417357981510989 := by
  unfold tailWord_2997124
  simp only [CollatzResearch.WordTrace]
  refine ⟨54657046396969545436207213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72876061862626060581609617 54657046396969545436207213)
  ·
    refine ⟨20496392398863579538577705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54657046396969545436207213 20496392398863579538577705)
    ·
      refine ⟨15372294299147684653933279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20496392398863579538577705 15372294299147684653933279)
      ·
        refine ⟨23058441448721526980899919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15372294299147684653933279 23058441448721526980899919)
        ·
          refine ⟨34587662173082290471349879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23058441448721526980899919 34587662173082290471349879)
          ·
            refine ⟨51881493259623435707024819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34587662173082290471349879 51881493259623435707024819)
            ·
              refine ⟨77822239889435153560537229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51881493259623435707024819 77822239889435153560537229)
              ·
                refine ⟨29183339958538182585201461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77822239889435153560537229 29183339958538182585201461)
                ·
                  refine ⟨2735938121112954617362637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29183339958538182585201461 2735938121112954617362637)
                  ·
                    refine ⟨1025976795417357981510989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2735938121112954617362637 1025976795417357981510989)
                    ·
                      rfl

theorem cell22_2997124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_2997124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997124 prefixEnd_2997124 := by exact prefixLift 2997124
  have htrace : WordTrace (prefixWord ++ tailWord_2997124) baseStart_2997124 baseEnd_2997124 := by
    simpa [prefixWord, tailWord_2997124, baseEnd_2997124] using wordTrace_append hprefix tailTrace_2997124
  have hstable : (prefixWord ++ tailWord_2997124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997124).length < 2 ^ (prefixWord ++ tailWord_2997124).sum := by decide
  have hdescent : baseEnd_2997124 < baseStart_2997124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997184 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 3, 4]
def baseStart_2997184 : Nat := 118140960795 + 2997184 * 2 ^ 59
def prefixEnd_2997184 : Nat := 4983230072969 + 3 ^ 40 * 2997184 * 2
def baseEnd_2997184 : Nat := 1025997334643537825010805

theorem tailTrace_2997184 : CollatzResearch.WordTrace tailWord_2997184 prefixEnd_2997184 1025997334643537825010805 := by
  unfold tailWord_2997184
  simp only [CollatzResearch.WordTrace]
  refine ⟨54658140586860860559799303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72877520782481147413065737 54658140586860860559799303)
  ·
    refine ⟨81987210880291290839698955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54658140586860860559799303 81987210880291290839698955)
    ·
      refine ⟨122980816320436936259548433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81987210880291290839698955 122980816320436936259548433)
      ·
        refine ⟨92235612240327702194661325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122980816320436936259548433 92235612240327702194661325)
        ·
          refine ⟨34588354590122888322997997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92235612240327702194661325 34588354590122888322997997)
          ·
            refine ⟨12970632971296083121124249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34588354590122888322997997 12970632971296083121124249)
            ·
              refine ⟨9727974728472062340843187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12970632971296083121124249 9727974728472062340843187)
              ·
                refine ⟨14591962092708093511264781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9727974728472062340843187 14591962092708093511264781)
                ·
                  refine ⟨5471985784765535066724293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14591962092708093511264781 5471985784765535066724293)
                  ·
                    refine ⟨1025997334643537825010805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5471985784765535066724293 1025997334643537825010805)
                    ·
                      rfl

theorem cell22_2997184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_2997184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997184 prefixEnd_2997184 := by exact prefixLift 2997184
  have htrace : WordTrace (prefixWord ++ tailWord_2997184) baseStart_2997184 baseEnd_2997184 := by
    simpa [prefixWord, tailWord_2997184, baseEnd_2997184] using wordTrace_append hprefix tailTrace_2997184
  have hstable : (prefixWord ++ tailWord_2997184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997184).length < 2 ^ (prefixWord ++ tailWord_2997184).sum := by decide
  have hdescent : baseEnd_2997184 < baseStart_2997184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997231 : List Nat := [1, 1, 2, 1, 4, 5, 1, 1, 1, 5]
def baseStart_2997231 : Nat := 118140960795 + 2997231 * 2 ^ 59
def prefixEnd_2997231 : Nat := 4983230072969 + 3 ^ 40 * 2997231 * 2
def baseEnd_2997231 : Nat := 1026013423704045369085661

theorem tailTrace_2997231 : CollatzResearch.WordTrace tailWord_2997231 prefixEnd_2997231 1026013423704045369085661 := by
  unfold tailWord_2997231
  simp only [CollatzResearch.WordTrace]
  refine ⟨109317995404551448146559547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72878663603034298764373031 109317995404551448146559547)
  ·
    refine ⟨163976993106827172219839321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109317995404551448146559547 163976993106827172219839321)
    ·
      refine ⟨122982744830120379164879491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163976993106827172219839321 122982744830120379164879491)
      ·
        refine ⟨184474117245180568747319237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122982744830120379164879491 184474117245180568747319237)
        ·
          refine ⟨34588896983471356640122357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184474117245180568747319237 34588896983471356640122357)
          ·
            refine ⟨3242709092200439685011471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34588896983471356640122357 3242709092200439685011471)
            ·
              refine ⟨4864063638300659527517207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3242709092200439685011471 4864063638300659527517207)
              ·
                refine ⟨7296095457450989291275811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4864063638300659527517207 7296095457450989291275811)
                ·
                  refine ⟨10944143186176483936913717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7296095457450989291275811 10944143186176483936913717)
                  ·
                    refine ⟨1026013423704045369085661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10944143186176483936913717 1026013423704045369085661)
                    ·
                      rfl

theorem cell22_2997231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 5].length) (baseStart_2997231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997231 prefixEnd_2997231 := by exact prefixLift 2997231
  have htrace : WordTrace (prefixWord ++ tailWord_2997231) baseStart_2997231 baseEnd_2997231 := by
    simpa [prefixWord, tailWord_2997231, baseEnd_2997231] using wordTrace_append hprefix tailTrace_2997231
  have hstable : (prefixWord ++ tailWord_2997231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997231).length < 2 ^ (prefixWord ++ tailWord_2997231).sum := by decide
  have hdescent : baseEnd_2997231 < baseStart_2997231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997244 : List Nat := [2, 2, 2, 1, 2, 4, 1, 8]
def baseStart_2997244 : Nat := 118140960795 + 2997244 * 2 ^ 59
def prefixEnd_2997244 : Nat := 4983230072969 + 3 ^ 40 * 2997244 * 2
def baseEnd_2997244 : Nat := 114001985985524185390069

theorem tailTrace_2997244 : CollatzResearch.WordTrace tailWord_2997244 prefixEnd_2997244 114001985985524185390069 := by
  unfold tailWord_2997244
  simp only [CollatzResearch.WordTrace]
  refine ⟨54659234776752175683391393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72878979702336234244521857 54659234776752175683391393)
  ·
    refine ⟨40994426082564131762543545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54659234776752175683391393 40994426082564131762543545)
    ·
      refine ⟨30745819561923098821907659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40994426082564131762543545 30745819561923098821907659)
      ·
        refine ⟨46118729342884648232861489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30745819561923098821907659 46118729342884648232861489)
        ·
          refine ⟨34589047007163486174646117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46118729342884648232861489 34589047007163486174646117)
          ·
            refine ⟨6485446313843153657746147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34589047007163486174646117 6485446313843153657746147)
            ·
              refine ⟨9728169470764730486619221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6485446313843153657746147 9728169470764730486619221)
              ·
                refine ⟨114001985985524185390069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9728169470764730486619221 114001985985524185390069)
                ·
                  rfl

theorem cell22_2997244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 8].length) (baseStart_2997244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997244 prefixEnd_2997244 := by exact prefixLift 2997244
  have htrace : WordTrace (prefixWord ++ tailWord_2997244) baseStart_2997244 baseEnd_2997244 := by
    simpa [prefixWord, tailWord_2997244, baseEnd_2997244] using wordTrace_append hprefix tailTrace_2997244
  have hstable : (prefixWord ++ tailWord_2997244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997244).length < 2 ^ (prefixWord ++ tailWord_2997244).sum := by decide
  have hdescent : baseEnd_2997244 < baseStart_2997244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997274 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 2, 6]
def baseStart_2997274 : Nat := 118140960795 + 2997274 * 2 ^ 59
def prefixEnd_2997274 : Nat := 4983230072969 + 3 ^ 40 * 2997274 * 2
def baseEnd_2997274 : Nat := 1026028143482807590260529

theorem tailTrace_2997274 : CollatzResearch.WordTrace tailWord_2997274 prefixEnd_2997274 1026028143482807590260529 := by
  unfold tailWord_2997274
  simp only [CollatzResearch.WordTrace]
  refine ⟨27329890935848916622593719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72879709162263777660249917 27329890935848916622593719)
  ·
    refine ⟨40994836403773374933890579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27329890935848916622593719 40994836403773374933890579)
    ·
      refine ⟨61492254605660062400835869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40994836403773374933890579 61492254605660062400835869)
      ·
        refine ⟨23059595477122523400313451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61492254605660062400835869 23059595477122523400313451)
        ·
          refine ⟨34589393215683785100470177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23059595477122523400313451 34589393215683785100470177)
          ·
            refine ⟨25942044911762838825352633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34589393215683785100470177 25942044911762838825352633)
            ·
              refine ⟨19456533683822129119014475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25942044911762838825352633 19456533683822129119014475)
              ·
                refine ⟨29184800525733193678521713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19456533683822129119014475 29184800525733193678521713)
                ·
                  refine ⟨21888600394299895258891285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29184800525733193678521713 21888600394299895258891285)
                  ·
                    refine ⟨1026028143482807590260529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21888600394299895258891285 1026028143482807590260529)
                    ·
                      rfl

theorem cell22_2997274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_2997274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997274 prefixEnd_2997274 := by exact prefixLift 2997274
  have htrace : WordTrace (prefixWord ++ tailWord_2997274) baseStart_2997274 baseEnd_2997274 := by
    simpa [prefixWord, tailWord_2997274, baseEnd_2997274] using wordTrace_append hprefix tailTrace_2997274
  have hstable : (prefixWord ++ tailWord_2997274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997274).length < 2 ^ (prefixWord ++ tailWord_2997274).sum := by decide
  have hdescent : baseEnd_2997274 < baseStart_2997274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997351 : List Nat := [1, 1, 5, 1, 1, 4, 1, 2, 6]
def baseStart_2997351 : Nat := 118140960795 + 2997351 * 2 ^ 59
def prefixEnd_2997351 : Nat := 4983230072969 + 3 ^ 40 * 2997351 * 2
def baseEnd_2997351 : Nat := 342018167385468352028431

theorem tailTrace_2997351 : CollatzResearch.WordTrace tailWord_2997351 prefixEnd_2997351 342018167385468352028431 := by
  unfold tailWord_2997351
  simp only [CollatzResearch.WordTrace]
  refine ⟨109322372164116708640927907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72881581442744472427285271 109322372164116708640927907)
  ·
    refine ⟨163983558246175062961391861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109322372164116708640927907 163983558246175062961391861)
    ·
      refine ⟨15373458585578912152630487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163983558246175062961391861 15373458585578912152630487)
      ·
        refine ⟨23060187878368368228945731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15373458585578912152630487 23060187878368368228945731)
        ·
          refine ⟨34590281817552552343418597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23060187878368368228945731 34590281817552552343418597)
          ·
            refine ⟨6485677840791103564390987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34590281817552552343418597 6485677840791103564390987)
            ·
              refine ⟨9728516761186655346586481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6485677840791103564390987 9728516761186655346586481)
              ·
                refine ⟨7296387570889991509939861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9728516761186655346586481 7296387570889991509939861)
                ·
                  refine ⟨342018167385468352028431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7296387570889991509939861 342018167385468352028431)
                  ·
                    rfl

theorem cell22_2997351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 6].length) (baseStart_2997351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997351 prefixEnd_2997351 := by exact prefixLift 2997351
  have htrace : WordTrace (prefixWord ++ tailWord_2997351) baseStart_2997351 baseEnd_2997351 := by
    simpa [prefixWord, tailWord_2997351, baseEnd_2997351] using wordTrace_append hprefix tailTrace_2997351
  have hstable : (prefixWord ++ tailWord_2997351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997351).length < 2 ^ (prefixWord ++ tailWord_2997351).sum := by decide
  have hdescent : baseEnd_2997351 < baseStart_2997351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997374 : List Nat := [4, 2, 4, 1, 1, 2, 1, 2, 5]
def baseStart_2997374 : Nat := 118140960795 + 2997374 * 2 ^ 59
def prefixEnd_2997374 : Nat := 4983230072969 + 3 ^ 40 * 2997374 * 2
def baseEnd_2997374 : Nat := 342020791842146887586741

theorem tailTrace_2997374 : CollatzResearch.WordTrace tailWord_2997374 prefixEnd_2997374 342020791842146887586741 := by
  unfold tailWord_2997374
  simp only [CollatzResearch.WordTrace]
  refine ⟨13665401380379172946126897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72882140695355589046010117 13665401380379172946126897)
  ·
    refine ⟨10249051035284379709595173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13665401380379172946126897 10249051035284379709595173)
    ·
      refine ⟨1921697069115821195549095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10249051035284379709595173 1921697069115821195549095)
      ·
        refine ⟨2882545603673731793323643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1921697069115821195549095 2882545603673731793323643)
        ·
          refine ⟨4323818405510597689985465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2882545603673731793323643 4323818405510597689985465)
          ·
            refine ⟨3242863804132948267489099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4323818405510597689985465 3242863804132948267489099)
            ·
              refine ⟨4864295706199422401233649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3242863804132948267489099 4864295706199422401233649)
              ·
                refine ⟨3648221779649566800925237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4864295706199422401233649 3648221779649566800925237)
                ·
                  refine ⟨342020791842146887586741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3648221779649566800925237 342020791842146887586741)
                  ·
                    rfl

theorem cell22_2997374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_2997374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997374 prefixEnd_2997374 := by exact prefixLift 2997374
  have htrace : WordTrace (prefixWord ++ tailWord_2997374) baseStart_2997374 baseEnd_2997374 := by
    simpa [prefixWord, tailWord_2997374, baseEnd_2997374] using wordTrace_append hprefix tailTrace_2997374
  have hstable : (prefixWord ++ tailWord_2997374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997374).length < 2 ^ (prefixWord ++ tailWord_2997374).sum := by decide
  have hdescent : baseEnd_2997374 < baseStart_2997374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997379 : List Nat := [1, 1, 1, 3, 3, 2, 11]
def baseStart_2997379 : Nat := 118140960795 + 2997379 * 2 ^ 59
def prefixEnd_2997379 : Nat := 4983230072969 + 3 ^ 40 * 2997379 * 2
def baseEnd_2997379 : Nat := 38002373597356382088341

theorem tailTrace_2997379 : CollatzResearch.WordTrace tailWord_2997379 prefixEnd_2997379 38002373597356382088341 := by
  unfold tailWord_2997379
  simp only [CollatzResearch.WordTrace]
  refine ⟨109323393408015269422947191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72882262272010179615298127 109323393408015269422947191)
  ·
    refine ⟨163985090112022904134420787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109323393408015269422947191 163985090112022904134420787)
    ·
      refine ⟨245977635168034356201631181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163985090112022904134420787 245977635168034356201631181)
      ·
        refine ⟨92241613188012883575611693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245977635168034356201631181 92241613188012883575611693)
        ·
          refine ⟨34590604945504831340854385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92241613188012883575611693 34590604945504831340854385)
          ·
            refine ⟨25942953709128623505640789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34590604945504831340854385 25942953709128623505640789)
            ·
              refine ⟨38002373597356382088341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25942953709128623505640789 38002373597356382088341)
              ·
                rfl

theorem cell22_2997379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 11].length) (baseStart_2997379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997379 prefixEnd_2997379 := by exact prefixLift 2997379
  have htrace : WordTrace (prefixWord ++ tailWord_2997379) baseStart_2997379 baseEnd_2997379 := by
    simpa [prefixWord, tailWord_2997379, baseEnd_2997379] using wordTrace_append hprefix tailTrace_2997379
  have hstable : (prefixWord ++ tailWord_2997379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997379).length < 2 ^ (prefixWord ++ tailWord_2997379).sum := by decide
  have hdescent : baseEnd_2997379 < baseStart_2997379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997413 : List Nat := [1, 3, 1, 2, 1, 6, 2, 6]
def baseStart_2997413 : Nat := 118140960795 + 2997413 * 2 ^ 59
def prefixEnd_2997413 : Nat := 4983230072969 + 3 ^ 40 * 2997413 * 2
def baseEnd_2997413 : Nat := 114008414002606395670567

theorem tailTrace_2997413 : CollatzResearch.WordTrace tailWord_2997413 prefixEnd_2997413 114008414002606395670567 := by
  unfold tailWord_2997413
  simp only [CollatzResearch.WordTrace]
  refine ⟨109324633489892093229684893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72883088993261395486456595 109324633489892093229684893)
  ·
    refine ⟨40996737558709534961131835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109324633489892093229684893 40996737558709534961131835)
    ·
      refine ⟨61495106338064302441697753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40996737558709534961131835 61495106338064302441697753)
      ·
        refine ⟨46121329753548226831273315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61495106338064302441697753 46121329753548226831273315)
        ·
          refine ⟨69181994630322340246909973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46121329753548226831273315 69181994630322340246909973)
          ·
            refine ⟨3242905998296359699073905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69181994630322340246909973 3242905998296359699073905)
            ·
              refine ⟨2432179498722269774305429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3242905998296359699073905 2432179498722269774305429)
              ·
                refine ⟨114008414002606395670567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2432179498722269774305429 114008414002606395670567)
                ·
                  rfl

theorem cell22_2997413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 6].length) (baseStart_2997413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997413 prefixEnd_2997413 := by exact prefixLift 2997413
  have htrace : WordTrace (prefixWord ++ tailWord_2997413) baseStart_2997413 baseEnd_2997413 := by
    simpa [prefixWord, tailWord_2997413, baseEnd_2997413] using wordTrace_append hprefix tailTrace_2997413
  have hstable : (prefixWord ++ tailWord_2997413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997413).length < 2 ^ (prefixWord ++ tailWord_2997413).sum := by decide
  have hdescent : baseEnd_2997413 < baseStart_2997413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997458 : List Nat := [3, 2, 2, 2, 1, 1, 3, 3, 5]
def baseStart_2997458 : Nat := 118140960795 + 2997458 * 2 ^ 59
def prefixEnd_2997458 : Nat := 4983230072969 + 3 ^ 40 * 2997458 * 2
def baseEnd_2997458 : Nat := 342030376814364147886655

theorem tailTrace_2997458 : CollatzResearch.WordTrace tailWord_2997458 prefixEnd_2997458 342030376814364147886655 := by
  unfold tailWord_2997458
  simp only [CollatzResearch.WordTrace]
  refine ⟨27331568693682266478768257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72884183183152710610048685 27331568693682266478768257)
  ·
    refine ⟨20498676520261699859076193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27331568693682266478768257 20498676520261699859076193)
    ·
      refine ⟨15374007390196274894307145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20498676520261699859076193 15374007390196274894307145)
      ·
        refine ⟨11530505542647206170730359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15374007390196274894307145 11530505542647206170730359)
        ·
          refine ⟨17295758313970809256095539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11530505542647206170730359 17295758313970809256095539)
          ·
            refine ⟨25943637470956213884143309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17295758313970809256095539 25943637470956213884143309)
            ·
              refine ⟨9728864051608580206553741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25943637470956213884143309 9728864051608580206553741)
              ·
                refine ⟨3648324019353217577457653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9728864051608580206553741 3648324019353217577457653)
                ·
                  refine ⟨342030376814364147886655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3648324019353217577457653 342030376814364147886655)
                  ·
                    rfl

theorem cell22_2997458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_2997458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997458 prefixEnd_2997458 := by exact prefixLift 2997458
  have htrace : WordTrace (prefixWord ++ tailWord_2997458) baseStart_2997458 baseEnd_2997458 := by
    simpa [prefixWord, tailWord_2997458, baseEnd_2997458] using wordTrace_append hprefix tailTrace_2997458
  have hstable : (prefixWord ++ tailWord_2997458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997458).length < 2 ^ (prefixWord ++ tailWord_2997458).sum := by decide
  have hdescent : baseEnd_2997458 < baseStart_2997458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997518 : List Nat := [4, 1, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_2997518 : Nat := 118140960795 + 2997518 * 2 ^ 59
def prefixEnd_2997518 : Nat := 4983230072969 + 3 ^ 40 * 2997518 * 2
def baseEnd_2997518 : Nat := 1026111669669272287159781

theorem tailTrace_2997518 : CollatzResearch.WordTrace tailWord_2997518 prefixEnd_2997518 1026111669669272287159781 := by
  unfold tailWord_2997518
  simp only [CollatzResearch.WordTrace]
  refine ⟨13666057894313962020282151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72885642103007797441504805 13666057894313962020282151)
  ·
    refine ⟨20499086841470943030423227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13666057894313962020282151 20499086841470943030423227)
    ·
      refine ⟨30748630262206414545634841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20499086841470943030423227 30748630262206414545634841)
      ·
        refine ⟨23061472696654810909226131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30748630262206414545634841 23061472696654810909226131)
        ·
          refine ⟨34592209044982216363839197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23061472696654810909226131 34592209044982216363839197)
          ·
            refine ⟨12972078391868331136439699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34592209044982216363839197 12972078391868331136439699)
            ·
              refine ⟨19458117587802496704659549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12972078391868331136439699 19458117587802496704659549)
              ·
                refine ⟨7296794095425936264247331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19458117587802496704659549 7296794095425936264247331)
                ·
                  refine ⟨10945191143138904396370997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7296794095425936264247331 10945191143138904396370997)
                  ·
                    refine ⟨1026111669669272287159781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10945191143138904396370997 1026111669669272287159781)
                    ·
                      rfl

theorem cell22_2997518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_2997518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997518 prefixEnd_2997518 := by exact prefixLift 2997518
  have htrace : WordTrace (prefixWord ++ tailWord_2997518) baseStart_2997518 baseEnd_2997518 := by
    simpa [prefixWord, tailWord_2997518, baseEnd_2997518] using wordTrace_append hprefix tailTrace_2997518
  have hstable : (prefixWord ++ tailWord_2997518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997518).length < 2 ^ (prefixWord ++ tailWord_2997518).sum := by decide
  have hdescent : baseEnd_2997518 < baseStart_2997518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997569 : List Nat := [1, 2, 5, 2, 1, 2, 3, 1, 2, 3]
def baseStart_2997569 : Nat := 118140960795 + 2997569 * 2 ^ 59
def prefixEnd_2997569 : Nat := 4983230072969 + 3 ^ 40 * 2997569 * 2
def baseEnd_2997569 : Nat := 1026129128011525154134625

theorem tailTrace_2997569 : CollatzResearch.WordTrace tailWord_2997569 prefixEnd_2997569 1026129128011525154134625 := by
  unfold tailWord_2997569
  simp only [CollatzResearch.WordTrace]
  refine ⟨109330323277326931872363761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72886882184884621248242507 109330323277326931872363761)
  ·
    refine ⟨81997742457995198904272821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109330323277326931872363761 81997742457995198904272821)
    ·
      refine ⟨7687288355437049897275577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81997742457995198904272821 7687288355437049897275577)
      ·
        refine ⟨5765466266577787422956683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7687288355437049897275577 5765466266577787422956683)
        ·
          refine ⟨8648199399866681134435025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5765466266577787422956683 8648199399866681134435025)
          ·
            refine ⟨6486149549900010850826269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8648199399866681134435025 6486149549900010850826269)
            ·
              refine ⟨2432306081212504069059851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6486149549900010850826269 2432306081212504069059851)
              ·
                refine ⟨3648459121818756103589777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2432306081212504069059851 3648459121818756103589777)
                ·
                  refine ⟨2736344341364067077692333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3648459121818756103589777 2736344341364067077692333)
                  ·
                    refine ⟨1026129128011525154134625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2736344341364067077692333 1026129128011525154134625)
                    ·
                      rfl

theorem cell22_2997569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_2997569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997569 prefixEnd_2997569 := by exact prefixLift 2997569
  have htrace : WordTrace (prefixWord ++ tailWord_2997569) baseStart_2997569 baseEnd_2997569 := by
    simpa [prefixWord, tailWord_2997569, baseEnd_2997569] using wordTrace_append hprefix tailTrace_2997569
  have hstable : (prefixWord ++ tailWord_2997569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997569).length < 2 ^ (prefixWord ++ tailWord_2997569).sum := by decide
  have hdescent : baseEnd_2997569 < baseStart_2997569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997580 : List Nat := [2, 2, 1, 3, 2, 2, 2, 2, 3, 3]
def baseStart_2997580 : Nat := 118140960795 + 2997580 * 2 ^ 59
def prefixEnd_2997580 : Nat := 4983230072969 + 3 ^ 40 * 2997580 * 2
def baseEnd_2997580 : Nat := 1026132893536324792109591

theorem tailTrace_2997580 : CollatzResearch.WordTrace tailWord_2997580 prefixEnd_2997580 1026132893536324792109591 := by
  unfold tailWord_2997580
  simp only [CollatzResearch.WordTrace]
  refine ⟨54665362240143540375507097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72887149653524720500676129 54665362240143540375507097)
  ·
    refine ⟨40999021680107655281630323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54665362240143540375507097 40999021680107655281630323)
    ·
      refine ⟨61498532520161482922445485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40999021680107655281630323 61498532520161482922445485)
      ·
        refine ⟨23061949695060556095917057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61498532520161482922445485 23061949695060556095917057)
        ·
          refine ⟨17296462271295417071937793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23061949695060556095917057 17296462271295417071937793)
          ·
            refine ⟨12972346703471562803953345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17296462271295417071937793 12972346703471562803953345)
            ·
              refine ⟨9729260027603672102965009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12972346703471562803953345 9729260027603672102965009)
              ·
                refine ⟨7296945020702754077223757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9729260027603672102965009 7296945020702754077223757)
                ·
                  refine ⟨2736354382763532778958909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7296945020702754077223757 2736354382763532778958909)
                  ·
                    refine ⟨1026132893536324792109591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2736354382763532778958909 1026132893536324792109591)
                    ·
                      rfl

theorem cell22_2997580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_2997580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997580 prefixEnd_2997580 := by exact prefixLift 2997580
  have htrace : WordTrace (prefixWord ++ tailWord_2997580) baseStart_2997580 baseEnd_2997580 := by
    simpa [prefixWord, tailWord_2997580, baseEnd_2997580] using wordTrace_append hprefix tailTrace_2997580
  have hstable : (prefixWord ++ tailWord_2997580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997580).length < 2 ^ (prefixWord ++ tailWord_2997580).sum := by decide
  have hdescent : baseEnd_2997580 < baseStart_2997580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997623 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 3, 4]
def baseStart_2997623 : Nat := 118140960795 + 2997623 * 2 ^ 59
def prefixEnd_2997623 : Nat := 4983230072969 + 3 ^ 40 * 2997623 * 2
def baseEnd_2997623 : Nat := 1026147613315087013284459

theorem tailTrace_2997623 : CollatzResearch.WordTrace tailWord_2997623 prefixEnd_2997623 1026147613315087013284459 := by
  unfold tailWord_2997623
  simp only [CollatzResearch.WordTrace]
  refine ⟨109332292819131299094829523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72888195212754199396553015 109332292819131299094829523)
  ·
    refine ⟨163998439228696948642244285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109332292819131299094829523 163998439228696948642244285)
    ·
      refine ⟨61499414710761355740841607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163998439228696948642244285 61499414710761355740841607)
      ·
        refine ⟨92249122066142033611262411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61499414710761355740841607 92249122066142033611262411)
        ·
          refine ⟨138373683099213050416893617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92249122066142033611262411 138373683099213050416893617)
          ·
            refine ⟨103780262324409787812670213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138373683099213050416893617 103780262324409787812670213)
            ·
              refine ⟨19458799185826835214875665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103780262324409787812670213 19458799185826835214875665)
              ·
                refine ⟨14594099389370126411156749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19458799185826835214875665 14594099389370126411156749)
                ·
                  refine ⟨5472787271013797404183781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14594099389370126411156749 5472787271013797404183781)
                  ·
                    refine ⟨1026147613315087013284459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5472787271013797404183781 1026147613315087013284459)
                    ·
                      rfl

theorem cell22_2997623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_2997623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997623 prefixEnd_2997623 := by exact prefixLift 2997623
  have htrace : WordTrace (prefixWord ++ tailWord_2997623) baseStart_2997623 baseEnd_2997623 := by
    simpa [prefixWord, tailWord_2997623, baseEnd_2997623] using wordTrace_append hprefix tailTrace_2997623
  have hstable : (prefixWord ++ tailWord_2997623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997623).length < 2 ^ (prefixWord ++ tailWord_2997623).sum := by decide
  have hdescent : baseEnd_2997623 < baseStart_2997623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997640 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 3, 4]
def baseStart_2997640 : Nat := 118140960795 + 2997640 * 2 ^ 59
def prefixEnd_2997640 : Nat := 4983230072969 + 3 ^ 40 * 2997640 * 2
def baseEnd_2997640 : Nat := 1026153432762504635609407

theorem tailTrace_2997640 : CollatzResearch.WordTrace tailWord_2997640 prefixEnd_2997640 1026153432762504635609407 := by
  unfold tailWord_2997640
  simp only [CollatzResearch.WordTrace]
  refine ⟨54666456430034855499099187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72888608573379807332132249 54666456430034855499099187)
  ·
    refine ⟨81999684645052283248648781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54666456430034855499099187 81999684645052283248648781)
    ·
      refine ⟨30749881741894606218243293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81999684645052283248648781 30749881741894606218243293)
      ·
        refine ⟨11531205653210477331841235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30749881741894606218243293 11531205653210477331841235)
        ·
          refine ⟨17296808479815715997761853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11531205653210477331841235 17296808479815715997761853)
          ·
            refine ⟨6486303179930893499160695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17296808479815715997761853 6486303179930893499160695)
            ·
              refine ⟨9729454769896340248741043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6486303179930893499160695 9729454769896340248741043)
              ·
                refine ⟨14594182154844510373111565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9729454769896340248741043 14594182154844510373111565)
                ·
                  refine ⟨5472818308066691389916837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14594182154844510373111565 5472818308066691389916837)
                  ·
                    refine ⟨1026153432762504635609407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5472818308066691389916837 1026153432762504635609407)
                    ·
                      rfl

theorem cell22_2997640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_2997640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997640 prefixEnd_2997640 := by exact prefixLift 2997640
  have htrace : WordTrace (prefixWord ++ tailWord_2997640) baseStart_2997640 baseEnd_2997640 := by
    simpa [prefixWord, tailWord_2997640, baseEnd_2997640] using wordTrace_append hprefix tailTrace_2997640
  have hstable : (prefixWord ++ tailWord_2997640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997640).length < 2 ^ (prefixWord ++ tailWord_2997640).sum := by decide
  have hdescent : baseEnd_2997640 < baseStart_2997640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997653 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 3, 5]
def baseStart_2997653 : Nat := 118140960795 + 2997653 * 2 ^ 59
def prefixEnd_2997653 : Nat := 4983230072969 + 3 ^ 40 * 2997653 * 2
def baseEnd_2997653 : Nat := 1026157882928176935034367

theorem tailTrace_2997653 : CollatzResearch.WordTrace tailWord_2997653 prefixEnd_2997653 1026157882928176935034367 := by
  unfold tailWord_2997653
  simp only [CollatzResearch.WordTrace]
  refine ⟨109333387009022614218421613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72888924672681742812281075 109333387009022614218421613)
  ·
    refine ⟨41000020128383480331908105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109333387009022614218421613 41000020128383480331908105)
    ·
      refine ⟨30750015096287610248931079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41000020128383480331908105 30750015096287610248931079)
      ·
        refine ⟨46125022644431415373396619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30750015096287610248931079 46125022644431415373396619)
        ·
          refine ⟨69187533966647123060094929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46125022644431415373396619 69187533966647123060094929)
          ·
            refine ⟨51890650474985342295071197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69187533966647123060094929 51890650474985342295071197)
            ·
              refine ⟨19458993928119503360651699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51890650474985342295071197 19458993928119503360651699)
              ·
                refine ⟨29188490892179255040977549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19458993928119503360651699 29188490892179255040977549)
                ·
                  refine ⟨10945684084567220640366581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29188490892179255040977549 10945684084567220640366581)
                  ·
                    refine ⟨1026157882928176935034367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10945684084567220640366581 1026157882928176935034367)
                    ·
                      rfl

theorem cell22_2997653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_2997653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997653 prefixEnd_2997653 := by exact prefixLift 2997653
  have htrace : WordTrace (prefixWord ++ tailWord_2997653) baseStart_2997653 baseEnd_2997653 := by
    simpa [prefixWord, tailWord_2997653, baseEnd_2997653] using wordTrace_append hprefix tailTrace_2997653
  have hstable : (prefixWord ++ tailWord_2997653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997653).length < 2 ^ (prefixWord ++ tailWord_2997653).sum := by decide
  have hdescent : baseEnd_2997653 < baseStart_2997653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997655 : List Nat := [1, 1, 3, 3, 1, 1, 1, 7, 4]
def baseStart_2997655 : Nat := 118140960795 + 2997655 * 2 ^ 59
def prefixEnd_2997655 : Nat := 4983230072969 + 3 ^ 40 * 2997655 * 2
def baseEnd_2997655 : Nat := 342052855856349865494787

theorem tailTrace_2997655 : CollatzResearch.WordTrace tailWord_2997655 prefixEnd_2997655 342052855856349865494787 := by
  unfold tailWord_2997655
  simp only [CollatzResearch.WordTrace]
  refine ⟨109333459955015368559994419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72888973303343579039996279 109333459955015368559994419)
  ·
    refine ⟨164000189932523052839991629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109333459955015368559994419 164000189932523052839991629)
    ·
      refine ⟨61500071224696144814996861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164000189932523052839991629 61500071224696144814996861)
      ·
        refine ⟨23062526709261054305623823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61500071224696144814996861 23062526709261054305623823)
        ·
          refine ⟨34593790063891581458435735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23062526709261054305623823 34593790063891581458435735)
          ·
            refine ⟨51890685095837372187653603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34593790063891581458435735 51890685095837372187653603)
            ·
              refine ⟨77836027643756058281480405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51890685095837372187653603 77836027643756058281480405)
              ·
                refine ⟨1824281897900532615972197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 77836027643756058281480405 1824281897900532615972197)
                ·
                  refine ⟨342052855856349865494787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1824281897900532615972197 342052855856349865494787)
                  ·
                    rfl

theorem cell22_2997655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 4].length) (baseStart_2997655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997655 prefixEnd_2997655 := by exact prefixLift 2997655
  have htrace : WordTrace (prefixWord ++ tailWord_2997655) baseStart_2997655 baseEnd_2997655 := by
    simpa [prefixWord, tailWord_2997655, baseEnd_2997655] using wordTrace_append hprefix tailTrace_2997655
  have hstable : (prefixWord ++ tailWord_2997655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997655).length < 2 ^ (prefixWord ++ tailWord_2997655).sum := by decide
  have hdescent : baseEnd_2997655 < baseStart_2997655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997657 : List Nat := [1, 2, 1, 2, 1, 6, 3, 1, 1, 4]
def baseStart_2997657 : Nat := 118140960795 + 2997657 * 2 ^ 59
def prefixEnd_2997657 : Nat := 4983230072969 + 3 ^ 40 * 2997657 * 2
def baseEnd_2997657 : Nat := 1026159252209922257934355

theorem tailTrace_2997657 : CollatzResearch.WordTrace tailWord_2997657 prefixEnd_2997657 1026159252209922257934355 := by
  unfold tailWord_2997657
  simp only [CollatzResearch.WordTrace]
  refine ⟨109333532901008122901567225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72889021934005415267711483 109333532901008122901567225)
  ·
    refine ⟨82000149675756092176175419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109333532901008122901567225 82000149675756092176175419)
    ·
      refine ⟨123000224513634138264263129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82000149675756092176175419 123000224513634138264263129)
      ·
        refine ⟨92250168385225603698197347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123000224513634138264263129 92250168385225603698197347)
        ·
          refine ⟨138375252577838405547296021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92250168385225603698197347 138375252577838405547296021)
          ·
            refine ⟨6486339964586175260029501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 138375252577838405547296021 6486339964586175260029501)
            ·
              refine ⟨2432377486719815722511063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6486339964586175260029501 2432377486719815722511063)
              ·
                refine ⟨3648566230079723583766595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2432377486719815722511063 3648566230079723583766595)
                ·
                  refine ⟨5472849345119585375649893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3648566230079723583766595 5472849345119585375649893)
                  ·
                    refine ⟨1026159252209922257934355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5472849345119585375649893 1026159252209922257934355)
                    ·
                      rfl

theorem cell22_2997657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 1, 4].length) (baseStart_2997657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997657 prefixEnd_2997657 := by exact prefixLift 2997657
  have htrace : WordTrace (prefixWord ++ tailWord_2997657) baseStart_2997657 baseEnd_2997657 := by
    simpa [prefixWord, tailWord_2997657, baseEnd_2997657] using wordTrace_append hprefix tailTrace_2997657
  have hstable : (prefixWord ++ tailWord_2997657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997657).length < 2 ^ (prefixWord ++ tailWord_2997657).sum := by decide
  have hdescent : baseEnd_2997657 < baseStart_2997657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997668 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_2997668 : Nat := 118140960795 + 2997668 * 2 ^ 59
def prefixEnd_2997668 : Nat := 4983230072969 + 3 ^ 40 * 2997668 * 2
def baseEnd_2997668 : Nat := 1026163017734721895909321

theorem tailTrace_2997668 : CollatzResearch.WordTrace tailWord_2997668 prefixEnd_2997668 1026163017734721895909321 := by
  unfold tailWord_2997668
  simp only [CollatzResearch.WordTrace]
  refine ⟨54666967051984135890108829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72889289402645514520145105 54666967051984135890108829)
  ·
    refine ⟨20500112644494050958790811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54666967051984135890108829 20500112644494050958790811)
    ·
      refine ⟨30750168966741076438186217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20500112644494050958790811 30750168966741076438186217)
      ·
        refine ⟨23062626725055807328639663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30750168966741076438186217 23062626725055807328639663)
        ·
          refine ⟨34593940087583710992959495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23062626725055807328639663 34593940087583710992959495)
          ·
            refine ⟨51890910131375566489439243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34593940087583710992959495 51890910131375566489439243)
            ·
              refine ⟨77836365197063349734158865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51890910131375566489439243 77836365197063349734158865)
              ·
                refine ⟨58377273897797512300619149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77836365197063349734158865 58377273897797512300619149)
                ·
                  refine ⟨21891477711674067112732181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58377273897797512300619149 21891477711674067112732181)
                  ·
                    refine ⟨1026163017734721895909321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21891477711674067112732181 1026163017734721895909321)
                    ·
                      rfl

theorem cell22_2997668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_2997668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997668 prefixEnd_2997668 := by exact prefixLift 2997668
  have htrace : WordTrace (prefixWord ++ tailWord_2997668) baseStart_2997668 baseEnd_2997668 := by
    simpa [prefixWord, tailWord_2997668, baseEnd_2997668] using wordTrace_append hprefix tailTrace_2997668
  have hstable : (prefixWord ++ tailWord_2997668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997668).length < 2 ^ (prefixWord ++ tailWord_2997668).sum := by decide
  have hdescent : baseEnd_2997668 < baseStart_2997668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997749 : List Nat := [1, 3, 5, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2997749 : Nat := 118140960795 + 2997749 * 2 ^ 59
def prefixEnd_2997749 : Nat := 4983230072969 + 3 ^ 40 * 2997749 * 2
def baseEnd_2997749 : Nat := 1026190745690064684634073

theorem tailTrace_2997749 : CollatzResearch.WordTrace tailWord_2997749 prefixEnd_2997749 1026190745690064684634073 := by
  unfold tailWord_2997749
  simp only [CollatzResearch.WordTrace]
  refine ⟨109336888416674822613916301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72891258944449881742610867 109336888416674822613916301)
  ·
    refine ⟨41001333156253058480218613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109336888416674822613916301 41001333156253058480218613)
    ·
      refine ⟨3843874983398724232520495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41001333156253058480218613 3843874983398724232520495)
      ·
        refine ⟨5765812475098086348780743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3843874983398724232520495 5765812475098086348780743)
        ·
          refine ⟨8648718712647129523171115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5765812475098086348780743 8648718712647129523171115)
          ·
            refine ⟨12973078068970694284756673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8648718712647129523171115 12973078068970694284756673)
            ·
              refine ⟨9729808551728020713567505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12973078068970694284756673 9729808551728020713567505)
              ·
                refine ⟨7297356413796015535175629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9729808551728020713567505 7297356413796015535175629)
                ·
                  refine ⟨2736508655173505825690861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7297356413796015535175629 2736508655173505825690861)
                  ·
                    refine ⟨1026190745690064684634073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2736508655173505825690861 1026190745690064684634073)
                    ·
                      rfl

theorem cell22_2997749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2997749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997749 prefixEnd_2997749 := by exact prefixLift 2997749
  have htrace : WordTrace (prefixWord ++ tailWord_2997749) baseStart_2997749 baseEnd_2997749 := by
    simpa [prefixWord, tailWord_2997749, baseEnd_2997749] using wordTrace_append hprefix tailTrace_2997749
  have hstable : (prefixWord ++ tailWord_2997749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997749).length < 2 ^ (prefixWord ++ tailWord_2997749).sum := by decide
  have hdescent : baseEnd_2997749 < baseStart_2997749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997762 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 7]
def baseStart_2997762 : Nat := 118140960795 + 2997762 * 2 ^ 59
def prefixEnd_2997762 : Nat := 4983230072969 + 3 ^ 40 * 2997762 * 2
def baseEnd_2997762 : Nat := 342065065285245661353011

theorem tailTrace_2997762 : CollatzResearch.WordTrace tailWord_2997762 prefixEnd_2997762 342065065285245661353011 := by
  unfold tailWord_2997762
  simp only [CollatzResearch.WordTrace]
  refine ⟨27334340641406931458534885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72891575043751817222759693 27334340641406931458534885)
  ·
    refine ⟨5125188870263799648475291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27334340641406931458534885 5125188870263799648475291)
    ·
      refine ⟨7687783305395699472712937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5125188870263799648475291 7687783305395699472712937)
      ·
        refine ⟨5765837479046774604534703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7687783305395699472712937 5765837479046774604534703)
        ·
          refine ⟨8648756218570161906802055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5765837479046774604534703 8648756218570161906802055)
          ·
            refine ⟨12973134327855242860203083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8648756218570161906802055 12973134327855242860203083)
            ·
              refine ⟨19459701491782864290304625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12973134327855242860203083 19459701491782864290304625)
              ·
                refine ⟨14594776118837148217728469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19459701491782864290304625 14594776118837148217728469)
                ·
                  refine ⟨342065065285245661353011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14594776118837148217728469 342065065285245661353011)
                  ·
                    rfl

theorem cell22_2997762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_2997762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997762 prefixEnd_2997762 := by exact prefixLift 2997762
  have htrace : WordTrace (prefixWord ++ tailWord_2997762) baseStart_2997762 baseEnd_2997762 := by
    simpa [prefixWord, tailWord_2997762, baseEnd_2997762] using wordTrace_append hprefix tailTrace_2997762
  have hstable : (prefixWord ++ tailWord_2997762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997762).length < 2 ^ (prefixWord ++ tailWord_2997762).sum := by decide
  have hdescent : baseEnd_2997762 < baseStart_2997762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997852 : List Nat := [2, 2, 4, 1, 2, 1, 3, 7]
def baseStart_2997852 : Nat := 118140960795 + 2997852 * 2 ^ 59
def prefixEnd_2997852 : Nat := 4983230072969 + 3 ^ 40 * 2997852 * 2
def baseEnd_2997852 : Nat := 114025111632778527700973

theorem tailTrace_2997852 : CollatzResearch.WordTrace tailWord_2997852 prefixEnd_2997852 114025111632778527700973 := by
  unfold tailWord_2997852
  simp only [CollatzResearch.WordTrace]
  refine ⟨54670322567650835602457905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72893763423534447469943873 54670322567650835602457905)
  ·
    refine ⟨41002741925738126701843429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54670322567650835602457905 41002741925738126701843429)
    ·
      refine ⟨7688014111075898756595643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41002741925738126701843429 7688014111075898756595643)
      ·
        refine ⟨11532021166613848134893465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7688014111075898756595643 11532021166613848134893465)
        ·
          refine ⟨8649015874960386101170099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11532021166613848134893465 8649015874960386101170099)
          ·
            refine ⟨12973523812440579151755149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8649015874960386101170099 12973523812440579151755149)
            ·
              refine ⟨4865071429665217181908181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12973523812440579151755149 4865071429665217181908181)
              ·
                refine ⟨114025111632778527700973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4865071429665217181908181 114025111632778527700973)
                ·
                  rfl

theorem cell22_2997852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 7].length) (baseStart_2997852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997852 prefixEnd_2997852 := by exact prefixLift 2997852
  have htrace : WordTrace (prefixWord ++ tailWord_2997852) baseStart_2997852 baseEnd_2997852 := by
    simpa [prefixWord, tailWord_2997852, baseEnd_2997852] using wordTrace_append hprefix tailTrace_2997852
  have hstable : (prefixWord ++ tailWord_2997852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997852).length < 2 ^ (prefixWord ++ tailWord_2997852).sum := by decide
  have hdescent : baseEnd_2997852 < baseStart_2997852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997869 : List Nat := [1, 5, 1, 1, 4, 1, 3, 6]
def baseStart_2997869 : Nat := 118140960795 + 2997869 * 2 ^ 59
def prefixEnd_2997869 : Nat := 4983230072969 + 3 ^ 40 * 2997869 * 2
def baseEnd_2997869 : Nat := 114025758238047152403745

theorem tailTrace_2997869 : CollatzResearch.WordTrace tailWord_2997869 prefixEnd_2997869 114025758238047152403745 := by
  unfold tailWord_2997869
  simp only [CollatzResearch.WordTrace]
  refine ⟨109341265176240083108284661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72894176784160055405523107 109341265176240083108284661)
  ·
    refine ⟨10250743610272507791401687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109341265176240083108284661 10250743610272507791401687)
    ·
      refine ⟨15376115415408761687102531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10250743610272507791401687 15376115415408761687102531)
      ·
        refine ⟨23064173123113142530653797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15376115415408761687102531 23064173123113142530653797)
        ·
          refine ⟨4324532460583714224497587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23064173123113142530653797 4324532460583714224497587)
          ·
            refine ⟨6486798690875571336746381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4324532460583714224497587 6486798690875571336746381)
            ·
              refine ⟨2432549509078339251279893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6486798690875571336746381 2432549509078339251279893)
              ·
                refine ⟨114025758238047152403745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2432549509078339251279893 114025758238047152403745)
                ·
                  rfl

theorem cell22_2997869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 6].length) (baseStart_2997869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997869 prefixEnd_2997869 := by exact prefixLift 2997869
  have htrace : WordTrace (prefixWord ++ tailWord_2997869) baseStart_2997869 baseEnd_2997869 := by
    simpa [prefixWord, tailWord_2997869, baseEnd_2997869] using wordTrace_append hprefix tailTrace_2997869
  have hstable : (prefixWord ++ tailWord_2997869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997869).length < 2 ^ (prefixWord ++ tailWord_2997869).sum := by decide
  have hdescent : baseEnd_2997869 < baseStart_2997869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997897 : List Nat := [1, 2, 1, 1, 4, 1, 5, 2, 5]
def baseStart_2997897 : Nat := 118140960795 + 2997897 * 2 ^ 59
def prefixEnd_2997897 : Nat := 4983230072969 + 3 ^ 40 * 2997897 * 2
def baseEnd_2997897 : Nat := 342080469704880543977873

theorem tailTrace_2997897 : CollatzResearch.WordTrace tailWord_2997897 prefixEnd_2997897 342080469704880543977873 := by
  unfold tailWord_2997897
  simp only [CollatzResearch.WordTrace]
  refine ⟨109342286420138643890303945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72894857613425762593535963 109342286420138643890303945)
  ·
    refine ⟨82006714815103982917727959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109342286420138643890303945 82006714815103982917727959)
    ·
      refine ⟨123010072222655974376591939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82006714815103982917727959 123010072222655974376591939)
      ·
        refine ⟨184515108333983961564887909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123010072222655974376591939 184515108333983961564887909)
        ·
          refine ⟨34596582812621992793416483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184515108333983961564887909 34596582812621992793416483)
          ·
            refine ⟨51894874218932989190124725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34596582812621992793416483 51894874218932989190124725)
            ·
              refine ⟨4865144458024967736574193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51894874218932989190124725 4865144458024967736574193)
              ·
                refine ⟨3648858343518725802430645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4865144458024967736574193 3648858343518725802430645)
                ·
                  refine ⟨342080469704880543977873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3648858343518725802430645 342080469704880543977873)
                  ·
                    rfl

theorem cell22_2997897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 5].length) (baseStart_2997897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997897 prefixEnd_2997897 := by exact prefixLift 2997897
  have htrace : WordTrace (prefixWord ++ tailWord_2997897) baseStart_2997897 baseEnd_2997897 := by
    simpa [prefixWord, tailWord_2997897, baseEnd_2997897] using wordTrace_append hprefix tailTrace_2997897
  have hstable : (prefixWord ++ tailWord_2997897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997897).length < 2 ^ (prefixWord ++ tailWord_2997897).sum := by decide
  have hdescent : baseEnd_2997897 < baseStart_2997897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
