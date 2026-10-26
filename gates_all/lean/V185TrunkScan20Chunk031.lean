import V185TrunkScan20Chunk030

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_188780 : List Nat := [2, 2, 1, 1, 6, 1, 3, 2, 2]
def baseStart_188780 : Nat := 118140960795 + 188780 * 2 ^ 59
def prefixEnd_188780 : Nat := 4983230072969 + 3 ^ 40 * 188780 * 2
def baseEnd_188780 : Nat := 86164335960779227628287

theorem tailTrace_188780 : CollatzResearch.WordTrace tailWord_188780 prefixEnd_188780 86164335960779227628287 := by
  unfold tailWord_188780
  simp only [CollatzResearch.WordTrace]
  refine ⟨3442686128044887951133897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4590248170726517268178529 3442686128044887951133897)
  ·
    refine ⟨2582014596033665963350423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3442686128044887951133897 2582014596033665963350423)
    ·
      refine ⟨3873021894050498945025635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2582014596033665963350423 3873021894050498945025635)
      ·
        refine ⟨5809532841075748417538453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3873021894050498945025635 5809532841075748417538453)
        ·
          refine ⟨272321851925425707072115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5809532841075748417538453 272321851925425707072115)
          ·
            refine ⟨408482777888138560608173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272321851925425707072115 408482777888138560608173)
            ·
              refine ⟨153181041708051960228065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 408482777888138560608173 153181041708051960228065)
              ·
                refine ⟨114885781281038970171049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153181041708051960228065 114885781281038970171049)
                ·
                  refine ⟨86164335960779227628287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114885781281038970171049 86164335960779227628287)
                  ·
                    rfl

theorem cell20_188780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_188780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188780 prefixEnd_188780 := by exact prefixLift 188780
  have htrace : WordTrace (prefixWord ++ tailWord_188780) baseStart_188780 baseEnd_188780 := by
    simpa [prefixWord, tailWord_188780, baseEnd_188780] using wordTrace_append hprefix tailTrace_188780
  have hstable : (prefixWord ++ tailWord_188780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188780).length < 2 ^ (prefixWord ++ tailWord_188780).sum := by decide
  have hdescent : baseEnd_188780 < baseStart_188780 := by decide
  rcases family_descends (prefixWord ++ tailWord_188780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188784 : List Nat := [2, 1, 1, 1, 4, 5, 1, 1, 4]
def baseStart_188784 : Nat := 118140960795 + 188784 * 2 ^ 59
def prefixEnd_188784 : Nat := 4983230072969 + 3 ^ 40 * 188784 * 2
def baseEnd_188784 : Nat := 86166161669772991494937

theorem tailTrace_188784 : CollatzResearch.WordTrace tailWord_188784 prefixEnd_188784 86166161669772991494937 := by
  unfold tailWord_188784
  simp only [CollatzResearch.WordTrace]
  refine ⟨3442759074037642292706703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4590345432050189723608937 3442759074037642292706703)
  ·
    refine ⟨5164138611056463439060055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3442759074037642292706703 5164138611056463439060055)
    ·
      refine ⟨7746207916584695158590083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5164138611056463439060055 7746207916584695158590083)
      ·
        refine ⟨11619311874877042737885125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7746207916584695158590083 11619311874877042737885125)
        ·
          refine ⟨2178620976539445513353461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11619311874877042737885125 2178620976539445513353461)
          ·
            refine ⟨204245716550573016876887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2178620976539445513353461 204245716550573016876887)
            ·
              refine ⟨306368574825859525315331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204245716550573016876887 306368574825859525315331)
              ·
                refine ⟨459552862238789287972997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306368574825859525315331 459552862238789287972997)
                ·
                  refine ⟨86166161669772991494937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 459552862238789287972997 86166161669772991494937)
                  ·
                    rfl

theorem cell20_188784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 4].length) (baseStart_188784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188784 prefixEnd_188784 := by exact prefixLift 188784
  have htrace : WordTrace (prefixWord ++ tailWord_188784) baseStart_188784 baseEnd_188784 := by
    simpa [prefixWord, tailWord_188784, baseEnd_188784] using wordTrace_append hprefix tailTrace_188784
  have hstable : (prefixWord ++ tailWord_188784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188784).length < 2 ^ (prefixWord ++ tailWord_188784).sum := by decide
  have hdescent : baseEnd_188784 < baseStart_188784 := by decide
  rcases family_descends (prefixWord ++ tailWord_188784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188790 : List Nat := [5, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_188790 : Nat := 118140960795 + 188790 * 2 ^ 59
def prefixEnd_188790 : Nat := 4983230072969 + 3 ^ 40 * 188790 * 2
def baseEnd_188790 : Nat := 86168900233263637294913

theorem tailTrace_188790 : CollatzResearch.WordTrace tailWord_188790 prefixEnd_188790 86168900233263637294913 := by
  unfold tailWord_188790
  simp only [CollatzResearch.WordTrace]
  refine ⟨430358561628346725633239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4590491324035698406754549 430358561628346725633239)
  ·
    refine ⟨645537842442520088449859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 430358561628346725633239 645537842442520088449859)
    ·
      refine ⟨968306763663780132674789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 645537842442520088449859 968306763663780132674789)
      ·
        refine ⟨181557518186958774876523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 968306763663780132674789 181557518186958774876523)
        ·
          refine ⟨272336277280438162314785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181557518186958774876523 272336277280438162314785)
          ·
            refine ⟨204252207960328621736089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272336277280438162314785 204252207960328621736089)
            ·
              refine ⟨153189155970246466302067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204252207960328621736089 153189155970246466302067)
              ·
                refine ⟨229783733955369699453101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153189155970246466302067 229783733955369699453101)
                ·
                  refine ⟨86168900233263637294913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229783733955369699453101 86168900233263637294913)
                  ·
                    rfl

theorem cell20_188790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_188790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188790 prefixEnd_188790 := by exact prefixLift 188790
  have htrace : WordTrace (prefixWord ++ tailWord_188790) baseStart_188790 baseEnd_188790 := by
    simpa [prefixWord, tailWord_188790, baseEnd_188790] using wordTrace_append hprefix tailTrace_188790
  have hstable : (prefixWord ++ tailWord_188790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188790).length < 2 ^ (prefixWord ++ tailWord_188790).sum := by decide
  have hdescent : baseEnd_188790 < baseStart_188790 := by decide
  rcases family_descends (prefixWord ++ tailWord_188790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188812 : List Nat := [2, 2, 1, 2, 1, 4, 2, 6]
def baseStart_188812 : Nat := 118140960795 + 188812 * 2 ^ 59
def prefixEnd_188812 : Nat := 4983230072969 + 3 ^ 40 * 188812 * 2
def baseEnd_188812 : Nat := 28726313877576446187163

theorem tailTrace_188812 : CollatzResearch.WordTrace tailWord_188812 prefixEnd_188812 28726313877576446187163 := by
  unfold tailWord_188812
  simp only [CollatzResearch.WordTrace]
  refine ⟨3443269695986922683716345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4591026261315896911621793 3443269695986922683716345)
  ·
    refine ⟨2582452271990192012787259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3443269695986922683716345 2582452271990192012787259)
    ·
      refine ⟨3873678407985288019180889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2582452271990192012787259 3873678407985288019180889)
      ·
        refine ⟨2905258805988966014385667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3873678407985288019180889 2905258805988966014385667)
        ·
          refine ⟨4357888208983449021578501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2905258805988966014385667 4357888208983449021578501)
          ·
            refine ⟨817104039184396691545969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4357888208983449021578501 817104039184396691545969)
            ·
              refine ⟨612828029388297518659477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 817104039184396691545969 612828029388297518659477)
              ·
                refine ⟨28726313877576446187163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 612828029388297518659477 28726313877576446187163)
                ·
                  rfl

theorem cell20_188812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_188812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188812 prefixEnd_188812 := by exact prefixLift 188812
  have htrace : WordTrace (prefixWord ++ tailWord_188812) baseStart_188812 baseEnd_188812 := by
    simpa [prefixWord, tailWord_188812, baseEnd_188812] using wordTrace_append hprefix tailTrace_188812
  have hstable : (prefixWord ++ tailWord_188812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188812).length < 2 ^ (prefixWord ++ tailWord_188812).sum := by decide
  have hdescent : baseEnd_188812 < baseStart_188812 := by decide
  rcases family_descends (prefixWord ++ tailWord_188812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188829 : List Nat := [1, 4, 2, 1, 5, 7]
def baseStart_188829 : Nat := 118140960795 + 188829 * 2 ^ 59
def prefixEnd_188829 : Nat := 4983230072969 + 3 ^ 40 * 188829 * 2
def baseEnd_188829 : Nat := 3192100033183438333139

theorem tailTrace_188829 : CollatzResearch.WordTrace tailWord_188829 prefixEnd_188829 3192100033183438333139 := by
  unfold tailWord_188829
  simp only [CollatzResearch.WordTrace]
  refine ⟨6887159432912257270801541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4591439621941504847201027 6887159432912257270801541)
  ·
    refine ⟨1291342393671048238275289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6887159432912257270801541 1291342393671048238275289)
    ·
      refine ⟨968506795253286178706467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1291342393671048238275289 968506795253286178706467)
      ·
        refine ⟨1452760192879929268059701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 968506795253286178706467 1452760192879929268059701)
        ·
          refine ⟨136196268082493368880597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1452760192879929268059701 136196268082493368880597)
          ·
            refine ⟨3192100033183438333139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 136196268082493368880597 3192100033183438333139)
            ·
              rfl

theorem cell20_188829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 7].length) (baseStart_188829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188829 prefixEnd_188829 := by exact prefixLift 188829
  have htrace : WordTrace (prefixWord ++ tailWord_188829) baseStart_188829 baseEnd_188829 := by
    simpa [prefixWord, tailWord_188829, baseEnd_188829] using wordTrace_append hprefix tailTrace_188829
  have hstable : (prefixWord ++ tailWord_188829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188829).length < 2 ^ (prefixWord ++ tailWord_188829).sum := by decide
  have hdescent : baseEnd_188829 < baseStart_188829 := by decide
  rcases family_descends (prefixWord ++ tailWord_188829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188836 : List Nat := [2, 3, 1, 2, 1, 1, 3, 4, 3]
def baseStart_188836 : Nat := 118140960795 + 188836 * 2 ^ 59
def prefixEnd_188836 : Nat := 4983230072969 + 3 ^ 40 * 188836 * 2
def baseEnd_188836 : Nat := 86189895886691921761391

theorem tailTrace_188836 : CollatzResearch.WordTrace tailWord_188836 prefixEnd_188836 86189895886691921761391 := by
  unfold tailWord_188836
  simp only [CollatzResearch.WordTrace]
  refine ⟨3443707371943448733153181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4591609829257931644204241 3443707371943448733153181)
  ·
    refine ⟨1291390264478793274932443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3443707371943448733153181 1291390264478793274932443)
    ·
      refine ⟨1937085396718189912398665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1291390264478793274932443 1937085396718189912398665)
      ·
        refine ⟨1452814047538642434298999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1937085396718189912398665 1452814047538642434298999)
        ·
          refine ⟨2179221071307963651448499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1452814047538642434298999 2179221071307963651448499)
          ·
            refine ⟨3268831606961945477172749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2179221071307963651448499 3268831606961945477172749)
            ·
              refine ⟨1225811852610729553939781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3268831606961945477172749 1225811852610729553939781)
              ·
                refine ⟨229839722364511791363709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1225811852610729553939781 229839722364511791363709)
                ·
                  refine ⟨86189895886691921761391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 229839722364511791363709 86189895886691921761391)
                  ·
                    rfl

theorem cell20_188836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_188836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188836 prefixEnd_188836 := by exact prefixLift 188836
  have htrace : WordTrace (prefixWord ++ tailWord_188836) baseStart_188836 baseEnd_188836 := by
    simpa [prefixWord, tailWord_188836, baseEnd_188836] using wordTrace_append hprefix tailTrace_188836
  have hstable : (prefixWord ++ tailWord_188836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188836).length < 2 ^ (prefixWord ++ tailWord_188836).sum := by decide
  have hdescent : baseEnd_188836 < baseStart_188836 := by decide
  rcases family_descends (prefixWord ++ tailWord_188836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188839 : List Nat := [1, 1, 6, 1, 1, 3, 1, 4, 2]
def baseStart_188839 : Nat := 118140960795 + 188839 * 2 ^ 59
def prefixEnd_188839 : Nat := 4983230072969 + 3 ^ 40 * 188839 * 2
def baseEnd_188839 : Nat := 86191265168437244661379

theorem tailTrace_188839 : CollatzResearch.WordTrace tailWord_188839 prefixEnd_188839 86191265168437244661379 := by
  unfold tailWord_188839
  simp only [CollatzResearch.WordTrace]
  refine ⟨6887524162876028978665571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4591682775250685985777047 6887524162876028978665571)
  ·
    refine ⟨10331286244314043467998357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6887524162876028978665571 10331286244314043467998357)
    ·
      refine ⟨484279042702220787562423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10331286244314043467998357 484279042702220787562423)
      ·
        refine ⟨726418564053331181343635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484279042702220787562423 726418564053331181343635)
        ·
          refine ⟨1089627846079996772015453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726418564053331181343635 1089627846079996772015453)
          ·
            refine ⟨408610442279998789505795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1089627846079996772015453 408610442279998789505795)
            ·
              refine ⟨612915663419998184258693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408610442279998789505795 612915663419998184258693)
              ·
                refine ⟨114921686891249659548505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 612915663419998184258693 114921686891249659548505)
                ·
                  refine ⟨86191265168437244661379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114921686891249659548505 86191265168437244661379)
                  ·
                    rfl

theorem cell20_188839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 2].length) (baseStart_188839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188839 prefixEnd_188839 := by exact prefixLift 188839
  have htrace : WordTrace (prefixWord ++ tailWord_188839) baseStart_188839 baseEnd_188839 := by
    simpa [prefixWord, tailWord_188839, baseEnd_188839] using wordTrace_append hprefix tailTrace_188839
  have hstable : (prefixWord ++ tailWord_188839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188839).length < 2 ^ (prefixWord ++ tailWord_188839).sum := by decide
  have hdescent : baseEnd_188839 < baseStart_188839 := by decide
  rcases family_descends (prefixWord ++ tailWord_188839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188842 : List Nat := [3, 1, 6, 1, 1, 2, 1, 5]
def baseStart_188842 : Nat := 118140960795 + 188842 * 2 ^ 59
def prefixEnd_188842 : Nat := 4983230072969 + 3 ^ 40 * 188842 * 2
def baseEnd_188842 : Nat := 28730878150060855853789

theorem tailTrace_188842 : CollatzResearch.WordTrace tailWord_188842 prefixEnd_188842 28730878150060855853789 := by
  unfold tailWord_188842
  simp only [CollatzResearch.WordTrace]
  refine ⟨1721908395466290122756195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4591755721243440327349853 1721908395466290122756195)
  ·
    refine ⟨2582862593199435184134293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1721908395466290122756195 2582862593199435184134293)
    ·
      refine ⟨121071684056223524256295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2582862593199435184134293 121071684056223524256295)
      ·
        refine ⟨181607526084335286384443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121071684056223524256295 181607526084335286384443)
        ·
          refine ⟨272411289126502929576665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181607526084335286384443 272411289126502929576665)
          ·
            refine ⟨204308466844877197182499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272411289126502929576665 204308466844877197182499)
            ·
              refine ⟨306462700267315795773749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204308466844877197182499 306462700267315795773749)
              ·
                refine ⟨28730878150060855853789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 306462700267315795773749 28730878150060855853789)
                ·
                  rfl

theorem cell20_188842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_188842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188842 prefixEnd_188842 := by exact prefixLift 188842
  have htrace : WordTrace (prefixWord ++ tailWord_188842) baseStart_188842 baseEnd_188842 := by
    simpa [prefixWord, tailWord_188842, baseEnd_188842] using wordTrace_append hprefix tailTrace_188842
  have hstable : (prefixWord ++ tailWord_188842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188842).length < 2 ^ (prefixWord ++ tailWord_188842).sum := by decide
  have hdescent : baseEnd_188842 < baseStart_188842 := by decide
  rcases family_descends (prefixWord ++ tailWord_188842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188860 : List Nat := [2, 2, 2, 4, 1, 2, 1, 2, 4]
def baseStart_188860 : Nat := 118140960795 + 188860 * 2 ^ 59
def prefixEnd_188860 : Nat := 4983230072969 + 3 ^ 40 * 188860 * 2
def baseEnd_188860 : Nat := 86200850140654504961293

theorem tailTrace_188860 : CollatzResearch.WordTrace tailWord_188860 prefixEnd_188860 86200850140654504961293 := by
  unfold tailWord_188860
  simp only [CollatzResearch.WordTrace]
  refine ⟨3444145047899974782590017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4592193397199966376786689 3444145047899974782590017)
  ·
    refine ⟨2583108785924981086942513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3444145047899974782590017 2583108785924981086942513)
    ·
      refine ⟨1937331589443735815206885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2583108785924981086942513 1937331589443735815206885)
      ·
        refine ⟨363249673020700465351291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1937331589443735815206885 363249673020700465351291)
        ·
          refine ⟨544874509531050698026937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363249673020700465351291 544874509531050698026937)
          ·
            refine ⟨408655882148288023520203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 544874509531050698026937 408655882148288023520203)
            ·
              refine ⟨612983823222432035280305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408655882148288023520203 612983823222432035280305)
              ·
                refine ⟨459737867416824026460229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 612983823222432035280305 459737867416824026460229)
                ·
                  refine ⟨86200850140654504961293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 459737867416824026460229 86200850140654504961293)
                  ·
                    rfl

theorem cell20_188860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_188860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188860 prefixEnd_188860 := by exact prefixLift 188860
  have htrace : WordTrace (prefixWord ++ tailWord_188860) baseStart_188860 baseEnd_188860 := by
    simpa [prefixWord, tailWord_188860, baseEnd_188860] using wordTrace_append hprefix tailTrace_188860
  have hstable : (prefixWord ++ tailWord_188860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188860).length < 2 ^ (prefixWord ++ tailWord_188860).sum := by decide
  have hdescent : baseEnd_188860 < baseStart_188860 := by decide
  rcases family_descends (prefixWord ++ tailWord_188860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188932 : List Nat := [2, 3, 2, 3, 1, 3, 1, 3, 2]
def baseStart_188932 : Nat := 118140960795 + 188932 * 2 ^ 59
def prefixEnd_188932 : Nat := 4983230072969 + 3 ^ 40 * 188932 * 2
def baseEnd_188932 : Nat := 86233712902542254560999

theorem tailTrace_188932 : CollatzResearch.WordTrace tailWord_188932 prefixEnd_188932 86233712902542254560999 := by
  unfold tailWord_188932
  simp only [CollatzResearch.WordTrace]
  refine ⟨3445458075769552930900525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4593944101026070574534033 3445458075769552930900525)
  ·
    refine ⟨1292046778413582349087697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3445458075769552930900525 1292046778413582349087697)
    ·
      refine ⟨969035083810186761815773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1292046778413582349087697 969035083810186761815773)
      ·
        refine ⟨363388156428820035680915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 969035083810186761815773 363388156428820035680915)
        ·
          refine ⟨545082234643230053521373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363388156428820035680915 545082234643230053521373)
          ·
            refine ⟨204405837991211270070515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 545082234643230053521373 204405837991211270070515)
            ·
              refine ⟨306608756986816905105773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204405837991211270070515 306608756986816905105773)
              ·
                refine ⟨114978283870056339414665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306608756986816905105773 114978283870056339414665)
                ·
                  refine ⟨86233712902542254560999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114978283870056339414665 86233712902542254560999)
                  ·
                    rfl

theorem cell20_188932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_188932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188932 prefixEnd_188932 := by exact prefixLift 188932
  have htrace : WordTrace (prefixWord ++ tailWord_188932) baseStart_188932 baseEnd_188932 := by
    simpa [prefixWord, tailWord_188932, baseEnd_188932] using wordTrace_append hprefix tailTrace_188932
  have hstable : (prefixWord ++ tailWord_188932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188932).length < 2 ^ (prefixWord ++ tailWord_188932).sum := by decide
  have hdescent : baseEnd_188932 < baseStart_188932 := by decide
  rcases family_descends (prefixWord ++ tailWord_188932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188933 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 5]
def baseStart_188933 : Nat := 118140960795 + 188933 * 2 ^ 59
def prefixEnd_188933 : Nat := 4983230072969 + 3 ^ 40 * 188933 * 2
def baseEnd_188933 : Nat := 86234169329790695527661

theorem tailTrace_188933 : CollatzResearch.WordTrace tailWord_188933 prefixEnd_188933 86234169329790695527661 := by
  unfold tailWord_188933
  simp only [CollatzResearch.WordTrace]
  refine ⟨6890952624535483032587453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4593968416356988688391635 6890952624535483032587453)
  ·
    refine ⟨2584107234200806137220295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6890952624535483032587453 2584107234200806137220295)
    ·
      refine ⟨3876160851301209205830443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2584107234200806137220295 3876160851301209205830443)
      ·
        refine ⟨5814241276951813808745665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3876160851301209205830443 5814241276951813808745665)
        ·
          refine ⟨4360680957713860356559249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5814241276951813808745665 4360680957713860356559249)
          ·
            refine ⟨3270510718285395267419437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4360680957713860356559249 3270510718285395267419437)
            ·
              refine ⟨1226441519357023225282289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3270510718285395267419437 1226441519357023225282289)
              ·
                refine ⟨919831139517767418961717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1226441519357023225282289 919831139517767418961717)
                ·
                  refine ⟨86234169329790695527661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 919831139517767418961717 86234169329790695527661)
                  ·
                    rfl

theorem cell20_188933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_188933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_188933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_188933 prefixEnd_188933 := by exact prefixLift 188933
  have htrace : WordTrace (prefixWord ++ tailWord_188933) baseStart_188933 baseEnd_188933 := by
    simpa [prefixWord, tailWord_188933, baseEnd_188933] using wordTrace_append hprefix tailTrace_188933
  have hstable : (prefixWord ++ tailWord_188933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188933).length < 2 ^ (prefixWord ++ tailWord_188933).sum := by decide
  have hdescent : baseEnd_188933 < baseStart_188933 := by decide
  rcases family_descends (prefixWord ++ tailWord_188933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189005 : List Nat := [1, 6, 1, 1, 2, 1, 1, 4, 3]
def baseStart_189005 : Nat := 118140960795 + 189005 * 2 ^ 59
def prefixEnd_189005 : Nat := 4983230072969 + 3 ^ 40 * 189005 * 2
def baseEnd_189005 : Nat := 86267032091678445127367

theorem tailTrace_189005 : CollatzResearch.WordTrace tailWord_189005 prefixEnd_189005 86267032091678445127367 := by
  unfold tailWord_189005
  simp only [CollatzResearch.WordTrace]
  refine ⟨6893578680274639329208469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4595719120183092886138979 6893578680274639329208469)
  ·
    refine ⟨323136500637873718556647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6893578680274639329208469 323136500637873718556647)
    ·
      refine ⟨484704750956810577834971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323136500637873718556647 484704750956810577834971)
      ·
        refine ⟨727057126435215866752457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484704750956810577834971 727057126435215866752457)
        ·
          refine ⟨545292844826411900064343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 727057126435215866752457 545292844826411900064343)
          ·
            refine ⟨817939267239617850096515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545292844826411900064343 817939267239617850096515)
            ·
              refine ⟨1226908900859426775144773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 817939267239617850096515 1226908900859426775144773)
              ·
                refine ⟨230045418911142520339645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1226908900859426775144773 230045418911142520339645)
                ·
                  refine ⟨86267032091678445127367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230045418911142520339645 86267032091678445127367)
                  ·
                    rfl

theorem cell20_189005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_189005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189005 prefixEnd_189005 := by exact prefixLift 189005
  have htrace : WordTrace (prefixWord ++ tailWord_189005) baseStart_189005 baseEnd_189005 := by
    simpa [prefixWord, tailWord_189005, baseEnd_189005] using wordTrace_append hprefix tailTrace_189005
  have hstable : (prefixWord ++ tailWord_189005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189005).length < 2 ^ (prefixWord ++ tailWord_189005).sum := by decide
  have hdescent : baseEnd_189005 < baseStart_189005 := by decide
  rcases family_descends (prefixWord ++ tailWord_189005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189046 : List Nat := [5, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_189046 : Nat := 118140960795 + 189046 * 2 ^ 59
def prefixEnd_189046 : Nat := 4983230072969 + 3 ^ 40 * 189046 * 2
def baseEnd_189046 : Nat := 86285745608864524760533

theorem tailTrace_189046 : CollatzResearch.WordTrace tailWord_189046 prefixEnd_189046 86285745608864524760533 := by
  unfold tailWord_189046
  simp only [CollatzResearch.WordTrace]
  refine ⟨430942129570381458215687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4596716048750735554300661 430942129570381458215687)
  ·
    refine ⟨646413194355572187323531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 430942129570381458215687 646413194355572187323531)
    ·
      refine ⟨969619791533358280985297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 646413194355572187323531 969619791533358280985297)
      ·
        refine ⟨727214843650018710738973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 969619791533358280985297 727214843650018710738973)
        ·
          refine ⟨272705566368757016527115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 727214843650018710738973 272705566368757016527115)
          ·
            refine ⟨409058349553135524790673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272705566368757016527115 409058349553135524790673)
            ·
              refine ⟨306793762164851643593005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409058349553135524790673 306793762164851643593005)
              ·
                refine ⟨115047660811819366347377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306793762164851643593005 115047660811819366347377)
                ·
                  refine ⟨86285745608864524760533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115047660811819366347377 86285745608864524760533)
                  ·
                    rfl

theorem cell20_189046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_189046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189046 prefixEnd_189046 := by exact prefixLift 189046
  have htrace : WordTrace (prefixWord ++ tailWord_189046) baseStart_189046 baseEnd_189046 := by
    simpa [prefixWord, tailWord_189046, baseEnd_189046] using wordTrace_append hprefix tailTrace_189046
  have hstable : (prefixWord ++ tailWord_189046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189046).length < 2 ^ (prefixWord ++ tailWord_189046).sum := by decide
  have hdescent : baseEnd_189046 < baseStart_189046 := by decide
  rcases family_descends (prefixWord ++ tailWord_189046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189173 : List Nat := [1, 3, 6, 1, 2, 1, 2, 2, 2]
def baseStart_189173 : Nat := 118140960795 + 189173 * 2 ^ 59
def prefixEnd_189173 : Nat := 4983230072969 + 3 ^ 40 * 189173 * 2
def baseEnd_189173 : Nat := 86343711869416527526681

theorem tailTrace_189173 : CollatzResearch.WordTrace tailWord_189173 prefixEnd_189173 86343711869416527526681 := by
  unfold tailWord_189173
  simp only [CollatzResearch.WordTrace]
  refine ⟨6899706143666004021324173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4599804095777336014216115 6899706143666004021324173)
  ·
    refine ⟨2587389803874751507996565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6899706143666004021324173 2587389803874751507996565)
    ·
      refine ⟨121283897056628976937339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2587389803874751507996565 121283897056628976937339)
      ·
        refine ⟨181925845584943465406009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121283897056628976937339 181925845584943465406009)
        ·
          refine ⟨136444384188707599054507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181925845584943465406009 136444384188707599054507)
          ·
            refine ⟨204666576283061398581761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136444384188707599054507 204666576283061398581761)
            ·
              refine ⟨153499932212296048936321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204666576283061398581761 153499932212296048936321)
              ·
                refine ⟨115124949159222036702241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153499932212296048936321 115124949159222036702241)
                ·
                  refine ⟨86343711869416527526681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115124949159222036702241 86343711869416527526681)
                  ·
                    rfl

theorem cell20_189173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_189173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189173 prefixEnd_189173 := by exact prefixLift 189173
  have htrace : WordTrace (prefixWord ++ tailWord_189173) baseStart_189173 baseEnd_189173 := by
    simpa [prefixWord, tailWord_189173, baseEnd_189173] using wordTrace_append hprefix tailTrace_189173
  have hstable : (prefixWord ++ tailWord_189173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189173).length < 2 ^ (prefixWord ++ tailWord_189173).sum := by decide
  have hdescent : baseEnd_189173 < baseStart_189173 := by decide
  rcases family_descends (prefixWord ++ tailWord_189173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189192 : List Nat := [2, 1, 3, 2, 2, 2, 3, 5]
def baseStart_189192 : Nat := 118140960795 + 189192 * 2 ^ 59
def prefixEnd_189192 : Nat := 4983230072969 + 3 ^ 40 * 189192 * 2
def baseEnd_189192 : Nat := 28784127995712301964423

theorem tailTrace_189192 : CollatzResearch.WordTrace tailWord_189192 prefixEnd_189192 28784127995712301964423 := by
  unfold tailWord_189192
  simp only [CollatzResearch.WordTrace]
  refine ⟨3450199565298585133132915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4600266087064780177510553 3450199565298585133132915)
  ·
    refine ⟨5175299347947877699699373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3450199565298585133132915 5175299347947877699699373)
    ·
      refine ⟨1940737255480454137387265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5175299347947877699699373 1940737255480454137387265)
      ·
        refine ⟨1455552941610340603040449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1940737255480454137387265 1455552941610340603040449)
        ·
          refine ⟨1091664706207755452280337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1455552941610340603040449 1091664706207755452280337)
          ·
            refine ⟨818748529655816589210253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1091664706207755452280337 818748529655816589210253)
            ·
              refine ⟨307030698620931220953845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 818748529655816589210253 307030698620931220953845)
              ·
                refine ⟨28784127995712301964423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 307030698620931220953845 28784127995712301964423)
                ·
                  rfl

theorem cell20_189192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_189192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189192 prefixEnd_189192 := by exact prefixLift 189192
  have htrace : WordTrace (prefixWord ++ tailWord_189192) baseStart_189192 baseEnd_189192 := by
    simpa [prefixWord, tailWord_189192, baseEnd_189192] using wordTrace_append hprefix tailTrace_189192
  have hstable : (prefixWord ++ tailWord_189192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189192).length < 2 ^ (prefixWord ++ tailWord_189192).sum := by decide
  have hdescent : baseEnd_189192 < baseStart_189192 := by decide
  rcases family_descends (prefixWord ++ tailWord_189192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189199 : List Nat := [1, 1, 2, 1, 1, 1, 5, 5, 3]
def baseStart_189199 : Nat := 118140960795 + 189199 * 2 ^ 59
def prefixEnd_189199 : Nat := 4983230072969 + 3 ^ 40 * 189199 * 2
def baseEnd_189199 : Nat := 86355578977875992659907

theorem tailTrace_189199 : CollatzResearch.WordTrace tailWord_189199 prefixEnd_189199 86355578977875992659907 := by
  unfold tailWord_189199
  simp only [CollatzResearch.WordTrace]
  refine ⟨6900654441571810461770651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4600436294381206974513767 6900654441571810461770651)
  ·
    refine ⟨10350981662357715692655977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6900654441571810461770651 10350981662357715692655977)
    ·
      refine ⟨7763236246768286769491983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10350981662357715692655977 7763236246768286769491983)
      ·
        refine ⟨11644854370152430154237975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7763236246768286769491983 11644854370152430154237975)
        ·
          refine ⟨17467281555228645231356963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11644854370152430154237975 17467281555228645231356963)
          ·
            refine ⟨26200922332842967847035445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17467281555228645231356963 26200922332842967847035445)
            ·
              refine ⟨2456336468704028235659573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26200922332842967847035445 2456336468704028235659573)
              ·
                refine ⟨230281543941002647093085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2456336468704028235659573 230281543941002647093085)
                ·
                  refine ⟨86355578977875992659907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230281543941002647093085 86355578977875992659907)
                  ·
                    rfl

theorem cell20_189199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 3].length) (baseStart_189199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189199 prefixEnd_189199 := by exact prefixLift 189199
  have htrace : WordTrace (prefixWord ++ tailWord_189199) baseStart_189199 baseEnd_189199 := by
    simpa [prefixWord, tailWord_189199, baseEnd_189199] using wordTrace_append hprefix tailTrace_189199
  have hstable : (prefixWord ++ tailWord_189199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189199).length < 2 ^ (prefixWord ++ tailWord_189199).sum := by decide
  have hdescent : baseEnd_189199 < baseStart_189199 := by decide
  rcases family_descends (prefixWord ++ tailWord_189199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189229 : List Nat := [1, 5, 3, 2, 1, 2, 1, 2, 3]
def baseStart_189229 : Nat := 118140960795 + 189229 * 2 ^ 59
def prefixEnd_189229 : Nat := 4983230072969 + 3 ^ 40 * 189229 * 2
def baseEnd_189229 : Nat := 86369271795329221659785

theorem tailTrace_189229 : CollatzResearch.WordTrace tailWord_189229 prefixEnd_189229 86369271795329221659785 := by
  unfold tailWord_189229
  simp only [CollatzResearch.WordTrace]
  refine ⟨6901748631463125585362741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4601165754308750390241827 6901748631463125585362741)
  ·
    refine ⟨647038934199668023627757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6901748631463125585362741 647038934199668023627757)
    ·
      refine ⟨242639600324875508860409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 647038934199668023627757 242639600324875508860409)
      ·
        refine ⟨181979700243656631645307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242639600324875508860409 181979700243656631645307)
        ·
          refine ⟨272969550365484947467961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181979700243656631645307 272969550365484947467961)
          ·
            refine ⟨204727162774113710600971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272969550365484947467961 204727162774113710600971)
            ·
              refine ⟨307090744161170565901457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204727162774113710600971 307090744161170565901457)
              ·
                refine ⟨230318058120877924426093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307090744161170565901457 230318058120877924426093)
                ·
                  refine ⟨86369271795329221659785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230318058120877924426093 86369271795329221659785)
                  ·
                    rfl

theorem cell20_189229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_189229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189229 prefixEnd_189229 := by exact prefixLift 189229
  have htrace : WordTrace (prefixWord ++ tailWord_189229) baseStart_189229 baseEnd_189229 := by
    simpa [prefixWord, tailWord_189229, baseEnd_189229] using wordTrace_append hprefix tailTrace_189229
  have hstable : (prefixWord ++ tailWord_189229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189229).length < 2 ^ (prefixWord ++ tailWord_189229).sum := by decide
  have hdescent : baseEnd_189229 < baseStart_189229 := by decide
  rcases family_descends (prefixWord ++ tailWord_189229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189251 : List Nat := [1, 1, 1, 3, 1, 4, 2, 7]
def baseStart_189251 : Nat := 118140960795 + 189251 * 2 ^ 59
def prefixEnd_189251 : Nat := 4983230072969 + 3 ^ 40 * 189251 * 2
def baseEnd_189251 : Nat := 28793104398264974308787

theorem tailTrace_189251 : CollatzResearch.WordTrace tailWord_189251 prefixEnd_189251 28793104398264974308787 := by
  unfold tailWord_189251
  simp only [CollatzResearch.WordTrace]
  refine ⟨6902551037383423342663607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4601700691588948895109071 6902551037383423342663607)
  ·
    refine ⟨10353826556075135013995411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6902551037383423342663607 10353826556075135013995411)
    ·
      refine ⟨15530739834112702520993117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10353826556075135013995411 15530739834112702520993117)
      ·
        refine ⟨5824027437792263445372419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15530739834112702520993117 5824027437792263445372419)
        ·
          refine ⟨8736041156688395168058629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5824027437792263445372419 8736041156688395168058629)
          ·
            refine ⟨1638007716879074094010993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8736041156688395168058629 1638007716879074094010993)
            ·
              refine ⟨1228505787659305570508245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1638007716879074094010993 1228505787659305570508245)
              ·
                refine ⟨28793104398264974308787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1228505787659305570508245 28793104398264974308787)
                ·
                  rfl

theorem cell20_189251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 7].length) (baseStart_189251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189251 prefixEnd_189251 := by exact prefixLift 189251
  have htrace : WordTrace (prefixWord ++ tailWord_189251) baseStart_189251 baseEnd_189251 := by
    simpa [prefixWord, tailWord_189251, baseEnd_189251] using wordTrace_append hprefix tailTrace_189251
  have hstable : (prefixWord ++ tailWord_189251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189251).length < 2 ^ (prefixWord ++ tailWord_189251).sum := by decide
  have hdescent : baseEnd_189251 < baseStart_189251 := by decide
  rcases family_descends (prefixWord ++ tailWord_189251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189299 : List Nat := [1, 1, 1, 2, 2, 1, 4, 6, 2]
def baseStart_189299 : Nat := 118140960795 + 189299 * 2 ^ 59
def prefixEnd_189299 : Nat := 4983230072969 + 3 ^ 40 * 189299 * 2
def baseEnd_189299 : Nat := 86401221702720089326165

theorem tailTrace_189299 : CollatzResearch.WordTrace tailWord_189299 prefixEnd_189299 86401221702720089326165 := by
  unfold tailWord_189299
  simp only [CollatzResearch.WordTrace]
  refine ⟨6904301741209527540410951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4602867827473018360273967 6904301741209527540410951)
  ·
    refine ⟨10356452611814291310616427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6904301741209527540410951 10356452611814291310616427)
    ·
      refine ⟨15534678917721436965924641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10356452611814291310616427 15534678917721436965924641)
      ·
        refine ⟨11651009188291077724443481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15534678917721436965924641 11651009188291077724443481)
        ·
          refine ⟨8738256891218308293332611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11651009188291077724443481 8738256891218308293332611)
          ·
            refine ⟨13107385336827462439998917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8738256891218308293332611 13107385336827462439998917)
            ·
              refine ⟨2457634750655149207499797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13107385336827462439998917 2457634750655149207499797)
              ·
                refine ⟨115201628936960119101553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2457634750655149207499797 115201628936960119101553)
                ·
                  refine ⟨86401221702720089326165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115201628936960119101553 86401221702720089326165)
                  ·
                    rfl

theorem cell20_189299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 2].length) (baseStart_189299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189299 prefixEnd_189299 := by exact prefixLift 189299
  have htrace : WordTrace (prefixWord ++ tailWord_189299) baseStart_189299 baseEnd_189299 := by
    simpa [prefixWord, tailWord_189299, baseEnd_189299] using wordTrace_append hprefix tailTrace_189299
  have hstable : (prefixWord ++ tailWord_189299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189299).length < 2 ^ (prefixWord ++ tailWord_189299).sum := by decide
  have hdescent : baseEnd_189299 < baseStart_189299 := by decide
  rcases family_descends (prefixWord ++ tailWord_189299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189337 : List Nat := [1, 2, 1, 2, 1, 3, 1, 7, 2]
def baseStart_189337 : Nat := 118140960795 + 189337 * 2 ^ 59
def prefixEnd_189337 : Nat := 4983230072969 + 3 ^ 40 * 189337 * 2
def baseEnd_189337 : Nat := 86418565938160846059343

theorem tailTrace_189337 : CollatzResearch.WordTrace tailWord_189337 prefixEnd_189337 86418565938160846059343 := by
  unfold tailWord_189337
  simp only [CollatzResearch.WordTrace]
  refine ⟨6905687715071860030294265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4603791810047906686862843 6905687715071860030294265)
  ·
    refine ⟨5179265786303895022720699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6905687715071860030294265 5179265786303895022720699)
    ·
      refine ⟨7768898679455842534081049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5179265786303895022720699 7768898679455842534081049)
      ·
        refine ⟨5826674009591881900560787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7768898679455842534081049 5826674009591881900560787)
        ·
          refine ⟨8740011014387822850841181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5826674009591881900560787 8740011014387822850841181)
          ·
            refine ⟨3277504130395433569065443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8740011014387822850841181 3277504130395433569065443)
            ·
              refine ⟨4916256195593150353598165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3277504130395433569065443 4916256195593150353598165)
              ·
                refine ⟨115224754584214461412457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4916256195593150353598165 115224754584214461412457)
                ·
                  refine ⟨86418565938160846059343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115224754584214461412457 86418565938160846059343)
                  ·
                    rfl

theorem cell20_189337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 2].length) (baseStart_189337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189337 prefixEnd_189337 := by exact prefixLift 189337
  have htrace : WordTrace (prefixWord ++ tailWord_189337) baseStart_189337 baseEnd_189337 := by
    simpa [prefixWord, tailWord_189337, baseEnd_189337] using wordTrace_append hprefix tailTrace_189337
  have hstable : (prefixWord ++ tailWord_189337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189337).length < 2 ^ (prefixWord ++ tailWord_189337).sum := by decide
  have hdescent : baseEnd_189337 < baseStart_189337 := by decide
  rcases family_descends (prefixWord ++ tailWord_189337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189357 : List Nat := [1, 5, 2, 3, 2, 1, 1, 5]
def baseStart_189357 : Nat := 118140960795 + 189357 * 2 ^ 59
def prefixEnd_189357 : Nat := 4983230072969 + 3 ^ 40 * 189357 * 2
def baseEnd_189357 : Nat := 28809231494376555130865

theorem tailTrace_189357 : CollatzResearch.WordTrace tailWord_189357 prefixEnd_189357 28809231494376555130865 := by
  unfold tailWord_189357
  simp only [CollatzResearch.WordTrace]
  refine ⟨6906417174999403446022325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4604278116666268964014883 6906417174999403446022325)
  ·
    refine ⟨647476610156194073064593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6906417174999403446022325 647476610156194073064593)
    ·
      refine ⟨485607457617145554798445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 647476610156194073064593 485607457617145554798445)
      ·
        refine ⟨182102796606429583049417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 485607457617145554798445 182102796606429583049417)
        ·
          refine ⟨136577097454822187287063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182102796606429583049417 136577097454822187287063)
          ·
            refine ⟨204865646182233280930595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136577097454822187287063 204865646182233280930595)
            ·
              refine ⟨307298469273349921395893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204865646182233280930595 307298469273349921395893)
              ·
                refine ⟨28809231494376555130865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 307298469273349921395893 28809231494376555130865)
                ·
                  rfl

theorem cell20_189357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 5].length) (baseStart_189357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189357 prefixEnd_189357 := by exact prefixLift 189357
  have htrace : WordTrace (prefixWord ++ tailWord_189357) baseStart_189357 baseEnd_189357 := by
    simpa [prefixWord, tailWord_189357, baseEnd_189357] using wordTrace_append hprefix tailTrace_189357
  have hstable : (prefixWord ++ tailWord_189357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189357).length < 2 ^ (prefixWord ++ tailWord_189357).sum := by decide
  have hdescent : baseEnd_189357 < baseStart_189357 := by decide
  rcases family_descends (prefixWord ++ tailWord_189357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189361 : List Nat := [1, 2, 2, 4, 3, 2, 1, 5]
def baseStart_189361 : Nat := 118140960795 + 189361 * 2 ^ 59
def prefixEnd_189361 : Nat := 4983230072969 + 3 ^ 40 * 189361 * 2
def baseEnd_189361 : Nat := 28809840064041143086415

theorem tailTrace_189361 : CollatzResearch.WordTrace tailWord_189361 prefixEnd_189361 28809840064041143086415 := by
  unfold tailWord_189361
  simp only [CollatzResearch.WordTrace]
  refine ⟨6906563066984912129167937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4604375377989941419445291 6906563066984912129167937)
  ·
    refine ⟨5179922300238684096875953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6906563066984912129167937 5179922300238684096875953)
    ·
      refine ⟨3884941725179013072656965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5179922300238684096875953 3884941725179013072656965)
      ·
        refine ⟨728426573471064951123181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3884941725179013072656965 728426573471064951123181)
        ·
          refine ⟨273159965051649356671193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 728426573471064951123181 273159965051649356671193)
          ·
            refine ⟨204869973788737017503395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273159965051649356671193 204869973788737017503395)
            ·
              refine ⟨307304960683105526255093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204869973788737017503395 307304960683105526255093)
              ·
                refine ⟨28809840064041143086415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 307304960683105526255093 28809840064041143086415)
                ·
                  rfl

theorem cell20_189361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 5].length) (baseStart_189361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189361 prefixEnd_189361 := by exact prefixLift 189361
  have htrace : WordTrace (prefixWord ++ tailWord_189361) baseStart_189361 baseEnd_189361 := by
    simpa [prefixWord, tailWord_189361, baseEnd_189361] using wordTrace_append hprefix tailTrace_189361
  have hstable : (prefixWord ++ tailWord_189361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189361).length < 2 ^ (prefixWord ++ tailWord_189361).sum := by decide
  have hdescent : baseEnd_189361 < baseStart_189361 := by decide
  rcases family_descends (prefixWord ++ tailWord_189361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189468 : List Nat := [2, 2, 3, 1, 4, 2, 1, 1, 4]
def baseStart_189468 : Nat := 118140960795 + 189468 * 2 ^ 59
def prefixEnd_189468 : Nat := 4983230072969 + 3 ^ 40 * 189468 * 2
def baseEnd_189468 : Nat := 86478357907706612692141

theorem tailTrace_189468 : CollatzResearch.WordTrace tailWord_189468 prefixEnd_189468 86478357907706612692141 := by
  unfold tailWord_189468
  simp only [CollatzResearch.WordTrace]
  refine ⟨3455232838798634701656529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4606977118398179602208705 3455232838798634701656529)
  ·
    refine ⟨2591424629098976026242397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3455232838798634701656529 2591424629098976026242397)
    ·
      refine ⟨971784235912116009840899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2591424629098976026242397 971784235912116009840899)
      ·
        refine ⟨1457676353868174014761349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 971784235912116009840899 1457676353868174014761349)
        ·
          refine ⟨273314316350282627767753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1457676353868174014761349 273314316350282627767753)
          ·
            refine ⟨204985737262711970825815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273314316350282627767753 204985737262711970825815)
            ·
              refine ⟨307478605894067956238723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204985737262711970825815 307478605894067956238723)
              ·
                refine ⟨461217908841101934358085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307478605894067956238723 461217908841101934358085)
                ·
                  refine ⟨86478357907706612692141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 461217908841101934358085 86478357907706612692141)
                  ·
                    rfl

theorem cell20_189468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_189468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189468 prefixEnd_189468 := by exact prefixLift 189468
  have htrace : WordTrace (prefixWord ++ tailWord_189468) baseStart_189468 baseEnd_189468 := by
    simpa [prefixWord, tailWord_189468, baseEnd_189468] using wordTrace_append hprefix tailTrace_189468
  have hstable : (prefixWord ++ tailWord_189468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189468).length < 2 ^ (prefixWord ++ tailWord_189468).sum := by decide
  have hdescent : baseEnd_189468 < baseStart_189468 := by decide
  rcases family_descends (prefixWord ++ tailWord_189468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189541 : List Nat := [1, 3, 1, 3, 2, 1, 1, 5, 3]
def baseStart_189541 : Nat := 118140960795 + 189541 * 2 ^ 59
def prefixEnd_189541 : Nat := 4983230072969 + 3 ^ 40 * 189541 * 2
def baseEnd_189541 : Nat := 86511677096842803258509

theorem tailTrace_189541 : CollatzResearch.WordTrace tailWord_189541 prefixEnd_189541 86511677096842803258509 := by
  unfold tailWord_189541
  simp only [CollatzResearch.WordTrace]
  refine ⟨6913128206332802870720477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4608752137555201913813651 6913128206332802870720477)
  ·
    refine ⟨2592423077374801076520179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6913128206332802870720477 2592423077374801076520179)
    ·
      refine ⟨3888634616062201614780269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2592423077374801076520179 3888634616062201614780269)
      ·
        refine ⟨1458237981023325605542601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3888634616062201614780269 1458237981023325605542601)
        ·
          refine ⟨1093678485767494204156951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1458237981023325605542601 1093678485767494204156951)
          ·
            refine ⟨1640517728651241306235427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1093678485767494204156951 1640517728651241306235427)
            ·
              refine ⟨2460776592976861959353141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1640517728651241306235427 2460776592976861959353141)
              ·
                refine ⟨230697805591580808689357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2460776592976861959353141 230697805591580808689357)
                ·
                  refine ⟨86511677096842803258509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230697805591580808689357 86511677096842803258509)
                  ·
                    rfl

theorem cell20_189541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_189541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189541 prefixEnd_189541 := by exact prefixLift 189541
  have htrace : WordTrace (prefixWord ++ tailWord_189541) baseStart_189541 baseEnd_189541 := by
    simpa [prefixWord, tailWord_189541, baseEnd_189541] using wordTrace_append hprefix tailTrace_189541
  have hstable : (prefixWord ++ tailWord_189541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189541).length < 2 ^ (prefixWord ++ tailWord_189541).sum := by decide
  have hdescent : baseEnd_189541 < baseStart_189541 := by decide
  rcases family_descends (prefixWord ++ tailWord_189541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189544 : List Nat := [2, 1, 4, 4, 1, 1, 1, 2, 4]
def baseStart_189544 : Nat := 118140960795 + 189544 * 2 ^ 59
def prefixEnd_189544 : Nat := 4983230072969 + 3 ^ 40 * 189544 * 2
def baseEnd_189544 : Nat := 86513046378588126158497

theorem tailTrace_189544 : CollatzResearch.WordTrace tailWord_189544 prefixEnd_189544 86513046378588126158497 := by
  unfold tailWord_189544
  simp only [CollatzResearch.WordTrace]
  refine ⟨3456618812660967191539843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4608825083547956255386457 3456618812660967191539843)
  ·
    refine ⟨5184928218991450787309765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3456618812660967191539843 5184928218991450787309765)
    ·
      refine ⟨972174041060897022620581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5184928218991450787309765 972174041060897022620581)
      ·
        refine ⟨182282632698918191741359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 972174041060897022620581 182282632698918191741359)
        ·
          refine ⟨273423949048377287612039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182282632698918191741359 273423949048377287612039)
          ·
            refine ⟨410135923572565931418059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273423949048377287612039 410135923572565931418059)
            ·
              refine ⟨615203885358848897127089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410135923572565931418059 615203885358848897127089)
              ·
                refine ⟨461402914019136672845317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615203885358848897127089 461402914019136672845317)
                ·
                  refine ⟨86513046378588126158497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 461402914019136672845317 86513046378588126158497)
                  ·
                    rfl

theorem cell20_189544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 4].length) (baseStart_189544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189544 prefixEnd_189544 := by exact prefixLift 189544
  have htrace : WordTrace (prefixWord ++ tailWord_189544) baseStart_189544 baseEnd_189544 := by
    simpa [prefixWord, tailWord_189544, baseEnd_189544] using wordTrace_append hprefix tailTrace_189544
  have hstable : (prefixWord ++ tailWord_189544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189544).length < 2 ^ (prefixWord ++ tailWord_189544).sum := by decide
  have hdescent : baseEnd_189544 < baseStart_189544 := by decide
  rcases family_descends (prefixWord ++ tailWord_189544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189548 : List Nat := [2, 2, 1, 1, 3, 2, 3, 2, 4]
def baseStart_189548 : Nat := 118140960795 + 189548 * 2 ^ 59
def prefixEnd_189548 : Nat := 4983230072969 + 3 ^ 40 * 189548 * 2
def baseEnd_189548 : Nat := 86514872087581890025147

theorem tailTrace_189548 : CollatzResearch.WordTrace tailWord_189548 prefixEnd_189548 86514872087581890025147 := by
  unfold tailWord_189548
  simp only [CollatzResearch.WordTrace]
  refine ⟨3456691758653721533112649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4608922344871628710816865 3456691758653721533112649)
  ·
    refine ⟨2592518818990291149834487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3456691758653721533112649 2592518818990291149834487)
    ·
      refine ⟨3888778228485436724751731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2592518818990291149834487 3888778228485436724751731)
      ·
        refine ⟨5833167342728155087127597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3888778228485436724751731 5833167342728155087127597)
        ·
          refine ⟨2187437753523058157672849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5833167342728155087127597 2187437753523058157672849)
          ·
            refine ⟨1640578315142293618254637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2187437753523058157672849 1640578315142293618254637)
            ·
              refine ⟨615216868178360106845489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1640578315142293618254637 615216868178360106845489)
              ·
                refine ⟨461412651133770080134117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615216868178360106845489 461412651133770080134117)
                ·
                  refine ⟨86514872087581890025147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 461412651133770080134117 86514872087581890025147)
                  ·
                    rfl

theorem cell20_189548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_189548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189548 prefixEnd_189548 := by exact prefixLift 189548
  have htrace : WordTrace (prefixWord ++ tailWord_189548) baseStart_189548 baseEnd_189548 := by
    simpa [prefixWord, tailWord_189548, baseEnd_189548] using wordTrace_append hprefix tailTrace_189548
  have hstable : (prefixWord ++ tailWord_189548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189548).length < 2 ^ (prefixWord ++ tailWord_189548).sum := by decide
  have hdescent : baseEnd_189548 < baseStart_189548 := by decide
  rcases family_descends (prefixWord ++ tailWord_189548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189582 : List Nat := [4, 1, 1, 3, 2, 1, 2, 4, 2]
def baseStart_189582 : Nat := 118140960795 + 189582 * 2 ^ 59
def prefixEnd_189582 : Nat := 4983230072969 + 3 ^ 40 * 189582 * 2
def baseEnd_189582 : Nat := 86530390614028882891675

theorem tailTrace_189582 : CollatzResearch.WordTrace tailWord_189582 prefixEnd_189582 86530390614028882891675 := by
  unfold tailWord_189582
  simp only [CollatzResearch.WordTrace]
  refine ⟨864327949898033359120375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4609749066122844581975333 864327949898033359120375)
  ·
    refine ⟨1296491924847050038680563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 864327949898033359120375 1296491924847050038680563)
    ·
      refine ⟨1944737887270575058020845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1296491924847050038680563 1944737887270575058020845)
      ·
        refine ⟨729276707726465646757817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1944737887270575058020845 729276707726465646757817)
        ·
          refine ⟨546957530794849235068363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 729276707726465646757817 546957530794849235068363)
          ·
            refine ⟨820436296192273852602545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546957530794849235068363 820436296192273852602545)
            ·
              refine ⟨615327222144205389451909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820436296192273852602545 615327222144205389451909)
              ·
                refine ⟨115373854152038510522233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 615327222144205389451909 115373854152038510522233)
                ·
                  refine ⟨86530390614028882891675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115373854152038510522233 86530390614028882891675)
                  ·
                    rfl

theorem cell20_189582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_189582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189582 prefixEnd_189582 := by exact prefixLift 189582
  have htrace : WordTrace (prefixWord ++ tailWord_189582) baseStart_189582 baseEnd_189582 := by
    simpa [prefixWord, tailWord_189582, baseEnd_189582] using wordTrace_append hprefix tailTrace_189582
  have hstable : (prefixWord ++ tailWord_189582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189582).length < 2 ^ (prefixWord ++ tailWord_189582).sum := by decide
  have hdescent : baseEnd_189582 < baseStart_189582 := by decide
  rcases family_descends (prefixWord ++ tailWord_189582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189617 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 5]
def baseStart_189617 : Nat := 118140960795 + 189617 * 2 ^ 59
def prefixEnd_189617 : Nat := 4983230072969 + 3 ^ 40 * 189617 * 2
def baseEnd_189617 : Nat := 86546365567724316724865

theorem tailTrace_189617 : CollatzResearch.WordTrace tailWord_189617 prefixEnd_189617 86546365567724316724865 := by
  unfold tailWord_189617
  simp only [CollatzResearch.WordTrace]
  refine ⟨6915900154057467850487105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4610600102704978566991403 6915900154057467850487105)
  ·
    refine ⟨5186925115543100887865329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6915900154057467850487105 5186925115543100887865329)
    ·
      refine ⟨3890193836657325665898997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5186925115543100887865329 3890193836657325665898997)
      ·
        refine ⟨364705672186624281178031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3890193836657325665898997 364705672186624281178031)
        ·
          refine ⟨547058508279936421767047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364705672186624281178031 547058508279936421767047)
          ·
            refine ⟨820587762419904632650571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547058508279936421767047 820587762419904632650571)
            ·
              refine ⟨1230881643629856948975857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 820587762419904632650571 1230881643629856948975857)
              ·
                refine ⟨923161232722392711731893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1230881643629856948975857 923161232722392711731893)
                ·
                  refine ⟨86546365567724316724865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 923161232722392711731893 86546365567724316724865)
                  ·
                    rfl

theorem cell20_189617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_189617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189617 prefixEnd_189617 := by exact prefixLift 189617
  have htrace : WordTrace (prefixWord ++ tailWord_189617) baseStart_189617 baseEnd_189617 := by
    simpa [prefixWord, tailWord_189617, baseEnd_189617] using wordTrace_append hprefix tailTrace_189617
  have hstable : (prefixWord ++ tailWord_189617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189617).length < 2 ^ (prefixWord ++ tailWord_189617).sum := by decide
  have hdescent : baseEnd_189617 < baseStart_189617 := by decide
  rcases family_descends (prefixWord ++ tailWord_189617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189692 : List Nat := [2, 2, 2, 1, 6, 1, 2, 2, 2]
def baseStart_189692 : Nat := 118140960795 + 189692 * 2 ^ 59
def prefixEnd_189692 : Nat := 4983230072969 + 3 ^ 40 * 189692 * 2
def baseEnd_189692 : Nat := 86580597611357389224559

theorem tailTrace_189692 : CollatzResearch.WordTrace tailWord_189692 prefixEnd_189692 86580597611357389224559 := by
  unfold tailWord_189692
  simp only [CollatzResearch.WordTrace]
  refine ⟨3459317814392877829733665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4612423752523837106311553 3459317814392877829733665)
  ·
    refine ⟨2594488360794658372300249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3459317814392877829733665 2594488360794658372300249)
    ·
      refine ⟨1945866270595993779225187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2594488360794658372300249 1945866270595993779225187)
      ·
        refine ⟨2918799405893990668837781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1945866270595993779225187 2918799405893990668837781)
        ·
          refine ⟨136818722151280812601771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2918799405893990668837781 136818722151280812601771)
          ·
            refine ⟨205228083226921218902657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136818722151280812601771 205228083226921218902657)
            ·
              refine ⟨153921062420190914176993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205228083226921218902657 153921062420190914176993)
              ·
                refine ⟨115440796815143185632745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153921062420190914176993 115440796815143185632745)
                ·
                  refine ⟨86580597611357389224559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115440796815143185632745 86580597611357389224559)
                  ·
                    rfl

theorem cell20_189692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_189692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189692 prefixEnd_189692 := by exact prefixLift 189692
  have htrace : WordTrace (prefixWord ++ tailWord_189692) baseStart_189692 baseEnd_189692 := by
    simpa [prefixWord, tailWord_189692, baseEnd_189692] using wordTrace_append hprefix tailTrace_189692
  have hstable : (prefixWord ++ tailWord_189692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189692).length < 2 ^ (prefixWord ++ tailWord_189692).sum := by decide
  have hdescent : baseEnd_189692 < baseStart_189692 := by decide
  rcases family_descends (prefixWord ++ tailWord_189692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189707 : List Nat := [1, 1, 1, 1, 5, 3, 3, 5]
def baseStart_189707 : Nat := 118140960795 + 189707 * 2 ^ 59
def prefixEnd_189707 : Nat := 4983230072969 + 3 ^ 40 * 189707 * 2
def baseEnd_189707 : Nat := 28862481340028001241499

theorem tailTrace_189707 : CollatzResearch.WordTrace tailWord_189707 prefixEnd_189707 28862481340028001241499 := by
  unfold tailWord_189707
  simp only [CollatzResearch.WordTrace]
  refine ⟨6919182723731413221263375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4612788482487608814175583 6919182723731413221263375)
  ·
    refine ⟨10378774085597119831895063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6919182723731413221263375 10378774085597119831895063)
    ·
      refine ⟨15568161128395679747842595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10378774085597119831895063 15568161128395679747842595)
      ·
        refine ⟨23352241692593519621763893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15568161128395679747842595 23352241692593519621763893)
        ·
          refine ⟨2189272658680642464540365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23352241692593519621763893 2189272658680642464540365)
          ·
            refine ⟨820977247005240924202637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2189272658680642464540365 820977247005240924202637)
            ·
              refine ⟨307866467626965346575989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 820977247005240924202637 307866467626965346575989)
              ·
                refine ⟨28862481340028001241499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 307866467626965346575989 28862481340028001241499)
                ·
                  rfl

theorem cell20_189707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 5].length) (baseStart_189707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189707 prefixEnd_189707 := by exact prefixLift 189707
  have htrace : WordTrace (prefixWord ++ tailWord_189707) baseStart_189707 baseEnd_189707 := by
    simpa [prefixWord, tailWord_189707, baseEnd_189707] using wordTrace_append hprefix tailTrace_189707
  have hstable : (prefixWord ++ tailWord_189707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189707).length < 2 ^ (prefixWord ++ tailWord_189707).sum := by decide
  have hdescent : baseEnd_189707 < baseStart_189707 := by decide
  rcases family_descends (prefixWord ++ tailWord_189707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189745 : List Nat := [1, 2, 2, 3, 3, 2, 7]
def baseStart_189745 : Nat := 118140960795 + 189745 * 2 ^ 59
def prefixEnd_189745 : Nat := 4983230072969 + 3 ^ 40 * 189745 * 2
def baseEnd_189745 : Nat := 9622754250613862273075

theorem tailTrace_189745 : CollatzResearch.WordTrace tailWord_189745 prefixEnd_189745 9622754250613862273075 := by
  unfold tailWord_189745
  simp only [CollatzResearch.WordTrace]
  refine ⟨6920568697593745711146689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4613712465062497140764459 6920568697593745711146689)
  ·
    refine ⟨5190426523195309283360017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6920568697593745711146689 5190426523195309283360017)
    ·
      refine ⟨3892819892396481962520013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5190426523195309283360017 3892819892396481962520013)
      ·
        refine ⟨1459807459648680735945005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3892819892396481962520013 1459807459648680735945005)
        ·
          refine ⟨547427797368255275979377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1459807459648680735945005 547427797368255275979377)
          ·
            refine ⟨410570848026191456984533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547427797368255275979377 410570848026191456984533)
            ·
              refine ⟨9622754250613862273075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 410570848026191456984533 9622754250613862273075)
              ·
                rfl

theorem cell20_189745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 7].length) (baseStart_189745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189745 prefixEnd_189745 := by exact prefixLift 189745
  have htrace : WordTrace (prefixWord ++ tailWord_189745) baseStart_189745 baseEnd_189745 := by
    simpa [prefixWord, tailWord_189745, baseEnd_189745] using wordTrace_append hprefix tailTrace_189745
  have hstable : (prefixWord ++ tailWord_189745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189745).length < 2 ^ (prefixWord ++ tailWord_189745).sum := by decide
  have hdescent : baseEnd_189745 < baseStart_189745 := by decide
  rcases family_descends (prefixWord ++ tailWord_189745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189783 : List Nat := [1, 1, 3, 2, 3, 3, 1, 6]
def baseStart_189783 : Nat := 118140960795 + 189783 * 2 ^ 59
def prefixEnd_189783 : Nat := 4983230072969 + 3 ^ 40 * 189783 * 2
def baseEnd_189783 : Nat := 28874044163655172396951

theorem tailTrace_189783 : CollatzResearch.WordTrace tailWord_189783 prefixEnd_189783 28874044163655172396951 := by
  unfold tailWord_189783
  simp only [CollatzResearch.WordTrace]
  refine ⟨6921954671456078201030003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4614636447637385467353335 6921954671456078201030003)
  ·
    refine ⟨10382932007184117301545005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6921954671456078201030003 10382932007184117301545005)
    ·
      refine ⟨3893599502694043988079377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10382932007184117301545005 3893599502694043988079377)
      ·
        refine ⟨2920199627020532991059533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3893599502694043988079377 2920199627020532991059533)
        ·
          refine ⟨1095074860132699871647325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2920199627020532991059533 1095074860132699871647325)
          ·
            refine ⟨410653072549762451867747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1095074860132699871647325 410653072549762451867747)
            ·
              refine ⟨615979608824643677801621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410653072549762451867747 615979608824643677801621)
              ·
                refine ⟨28874044163655172396951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 615979608824643677801621 28874044163655172396951)
                ·
                  rfl

theorem cell20_189783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 6].length) (baseStart_189783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189783 prefixEnd_189783 := by exact prefixLift 189783
  have htrace : WordTrace (prefixWord ++ tailWord_189783) baseStart_189783 baseEnd_189783 := by
    simpa [prefixWord, tailWord_189783, baseEnd_189783] using wordTrace_append hprefix tailTrace_189783
  have hstable : (prefixWord ++ tailWord_189783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189783).length < 2 ^ (prefixWord ++ tailWord_189783).sum := by decide
  have hdescent : baseEnd_189783 < baseStart_189783 := by decide
  rcases family_descends (prefixWord ++ tailWord_189783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189800 : List Nat := [2, 1, 4, 2, 3, 2, 6]
def baseStart_189800 : Nat := 118140960795 + 189800 * 2 ^ 59
def prefixEnd_189800 : Nat := 4983230072969 + 3 ^ 40 * 189800 * 2
def baseEnd_189800 : Nat := 9625543528243223736013

theorem tailTrace_189800 : CollatzResearch.WordTrace tailWord_189800 prefixEnd_189800 9625543528243223736013 := by
  unfold tailWord_189800
  simp only [CollatzResearch.WordTrace]
  refine ⟨3461287356197245052199427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4615049808262993402932569 3461287356197245052199427)
  ·
    refine ⟨5191931034295867578299141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3461287356197245052199427 5191931034295867578299141)
    ·
      refine ⟨973487068930475170931089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5191931034295867578299141 973487068930475170931089)
      ·
        refine ⟨730115301697856378198317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 973487068930475170931089 730115301697856378198317)
        ·
          refine ⟨273793238136696141824369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 730115301697856378198317 273793238136696141824369)
          ·
            refine ⟨205344928602522106368277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273793238136696141824369 205344928602522106368277)
            ·
              refine ⟨9625543528243223736013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 205344928602522106368277 9625543528243223736013)
              ·
                rfl

theorem cell20_189800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 6].length) (baseStart_189800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189800 prefixEnd_189800 := by exact prefixLift 189800
  have htrace : WordTrace (prefixWord ++ tailWord_189800) baseStart_189800 baseEnd_189800 := by
    simpa [prefixWord, tailWord_189800, baseEnd_189800] using wordTrace_append hprefix tailTrace_189800
  have hstable : (prefixWord ++ tailWord_189800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189800).length < 2 ^ (prefixWord ++ tailWord_189800).sum := by decide
  have hdescent : baseEnd_189800 < baseStart_189800 := by decide
  rcases family_descends (prefixWord ++ tailWord_189800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189806 : List Nat := [4, 1, 2, 4, 1, 1, 3, 2, 2]
def baseStart_189806 : Nat := 118140960795 + 189806 * 2 ^ 59
def prefixEnd_189806 : Nat := 4983230072969 + 3 ^ 40 * 189806 * 2
def baseEnd_189806 : Nat := 86632630317679659424093

theorem tailTrace_189806 : CollatzResearch.WordTrace tailWord_189806 prefixEnd_189806 86632630317679659424093 := by
  unfold tailWord_189806
  simp only [CollatzResearch.WordTrace]
  refine ⟨865349193796594141139659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4615195700248502086078181 865349193796594141139659)
  ·
    refine ⟨1298023790694891211709489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 865349193796594141139659 1298023790694891211709489)
    ·
      refine ⟨973517843021168408782117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1298023790694891211709489 973517843021168408782117)
      ·
        refine ⟨182534595566469076646647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 973517843021168408782117 182534595566469076646647)
        ·
          refine ⟨273801893349703614969971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182534595566469076646647 273801893349703614969971)
          ·
            refine ⟨410702840024555422454957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273801893349703614969971 410702840024555422454957)
            ·
              refine ⟨154013565009208283420609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 410702840024555422454957 154013565009208283420609)
              ·
                refine ⟨115510173756906212565457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154013565009208283420609 115510173756906212565457)
                ·
                  refine ⟨86632630317679659424093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115510173756906212565457 86632630317679659424093)
                  ·
                    rfl

theorem cell20_189806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_189806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189806 prefixEnd_189806 := by exact prefixLift 189806
  have htrace : WordTrace (prefixWord ++ tailWord_189806) baseStart_189806 baseEnd_189806 := by
    simpa [prefixWord, tailWord_189806, baseEnd_189806] using wordTrace_append hprefix tailTrace_189806
  have hstable : (prefixWord ++ tailWord_189806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189806).length < 2 ^ (prefixWord ++ tailWord_189806).sum := by decide
  have hdescent : baseEnd_189806 < baseStart_189806 := by decide
  rcases family_descends (prefixWord ++ tailWord_189806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189810 : List Nat := [3, 2, 1, 2, 1, 2, 5, 2, 2]
def baseStart_189810 : Nat := 118140960795 + 189810 * 2 ^ 59
def prefixEnd_189810 : Nat := 4983230072969 + 3 ^ 40 * 189810 * 2
def baseEnd_189810 : Nat := 86634456026673423290743

theorem tailTrace_189810 : CollatzResearch.WordTrace tailWord_189810 prefixEnd_189810 86634456026673423290743 := by
  unfold tailWord_189810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1730734860589565453065721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4615292961572174541508589 1730734860589565453065721)
  ·
    refine ⟨1298051145442174089799291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1730734860589565453065721 1298051145442174089799291)
    ·
      refine ⟨1947076718163261134698937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1298051145442174089799291 1947076718163261134698937)
      ·
        refine ⟨1460307538622445851024203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1947076718163261134698937 1460307538622445851024203)
        ·
          refine ⟨2190461307933668776536305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1460307538622445851024203 2190461307933668776536305)
          ·
            refine ⟨1642845980950251582402229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2190461307933668776536305 1642845980950251582402229)
            ·
              refine ⟨154016810714086085850209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1642845980950251582402229 154016810714086085850209)
              ·
                refine ⟨115512608035564564387657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154016810714086085850209 115512608035564564387657)
                ·
                  refine ⟨86634456026673423290743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115512608035564564387657 86634456026673423290743)
                  ·
                    rfl

theorem cell20_189810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_189810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189810 prefixEnd_189810 := by exact prefixLift 189810
  have htrace : WordTrace (prefixWord ++ tailWord_189810) baseStart_189810 baseEnd_189810 := by
    simpa [prefixWord, tailWord_189810, baseEnd_189810] using wordTrace_append hprefix tailTrace_189810
  have hstable : (prefixWord ++ tailWord_189810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189810).length < 2 ^ (prefixWord ++ tailWord_189810).sum := by decide
  have hdescent : baseEnd_189810 < baseStart_189810 := by decide
  rcases family_descends (prefixWord ++ tailWord_189810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189821 : List Nat := [1, 4, 1, 1, 2, 2, 4, 5]
def baseStart_189821 : Nat := 118140960795 + 189821 * 2 ^ 59
def prefixEnd_189821 : Nat := 4983230072969 + 3 ^ 40 * 189821 * 2
def baseEnd_189821 : Nat := 28879825575468757974677

theorem tailTrace_189821 : CollatzResearch.WordTrace tailWord_189821 prefixEnd_189821 28879825575468757974677 := by
  unfold tailWord_189821
  simp only [CollatzResearch.WordTrace]
  refine ⟨6923340645318410690913317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4615560430212273793942211 6923340645318410690913317)
  ·
    refine ⟨1298126370997202004546247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6923340645318410690913317 1298126370997202004546247)
    ·
      refine ⟨1947189556495803006819371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1298126370997202004546247 1947189556495803006819371)
      ·
        refine ⟨2920784334743704510229057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1947189556495803006819371 2920784334743704510229057)
        ·
          refine ⟨2190588251057778382671793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2920784334743704510229057 2190588251057778382671793)
          ·
            refine ⟨1642941188293333787003845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2190588251057778382671793 1642941188293333787003845)
            ·
              refine ⟨308051472805000085063221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1642941188293333787003845 308051472805000085063221)
              ·
                refine ⟨28879825575468757974677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 308051472805000085063221 28879825575468757974677)
                ·
                  rfl

theorem cell20_189821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 5].length) (baseStart_189821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189821 prefixEnd_189821 := by exact prefixLift 189821
  have htrace : WordTrace (prefixWord ++ tailWord_189821) baseStart_189821 baseEnd_189821 := by
    simpa [prefixWord, tailWord_189821, baseEnd_189821] using wordTrace_append hprefix tailTrace_189821
  have hstable : (prefixWord ++ tailWord_189821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189821).length < 2 ^ (prefixWord ++ tailWord_189821).sum := by decide
  have hdescent : baseEnd_189821 < baseStart_189821 := by decide
  rcases family_descends (prefixWord ++ tailWord_189821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189835 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 6]
def baseStart_189835 : Nat := 118140960795 + 189835 * 2 ^ 59
def prefixEnd_189835 : Nat := 4983230072969 + 3 ^ 40 * 189835 * 2
def baseEnd_189835 : Nat := 86645866707884447457307

theorem tailTrace_189835 : CollatzResearch.WordTrace tailWord_189835 prefixEnd_189835 86645866707884447457307 := by
  unfold tailWord_189835
  simp only [CollatzResearch.WordTrace]
  refine ⟨6923851267267691081922959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4615900844845127387948639 6923851267267691081922959)
  ·
    refine ⟨10385776900901536622884439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6923851267267691081922959 10385776900901536622884439)
    ·
      refine ⟨15578665351352304934326659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10385776900901536622884439 15578665351352304934326659)
      ·
        refine ⟨23367998027028457401489989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15578665351352304934326659 23367998027028457401489989)
        ·
          refine ⟨4381499630067835762779373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23367998027028457401489989 4381499630067835762779373)
          ·
            refine ⟨1643062361275438411042265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4381499630067835762779373 1643062361275438411042265)
            ·
              refine ⟨1232296770956578808281699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1643062361275438411042265 1232296770956578808281699)
              ·
                refine ⟨1848445156434868212422549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1232296770956578808281699 1848445156434868212422549)
                ·
                  refine ⟨86645866707884447457307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1848445156434868212422549 86645866707884447457307)
                  ·
                    rfl

theorem cell20_189835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_189835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189835 prefixEnd_189835 := by exact prefixLift 189835
  have htrace : WordTrace (prefixWord ++ tailWord_189835) baseStart_189835 baseEnd_189835 := by
    simpa [prefixWord, tailWord_189835, baseEnd_189835] using wordTrace_append hprefix tailTrace_189835
  have hstable : (prefixWord ++ tailWord_189835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189835).length < 2 ^ (prefixWord ++ tailWord_189835).sum := by decide
  have hdescent : baseEnd_189835 < baseStart_189835 := by decide
  rcases family_descends (prefixWord ++ tailWord_189835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189921 : List Nat := [1, 2, 3, 1, 2, 3, 3, 2, 3]
def baseStart_189921 : Nat := 118140960795 + 189921 * 2 ^ 59
def prefixEnd_189921 : Nat := 4983230072969 + 3 ^ 40 * 189921 * 2
def baseEnd_189921 : Nat := 86685119451250370590289

theorem tailTrace_189921 : CollatzResearch.WordTrace tailWord_189921 prefixEnd_189921 86685119451250370590289 := by
  unfold tailWord_189921
  simp only [CollatzResearch.WordTrace]
  refine ⟨6926987944956127769553617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4617991963304085179702411 6926987944956127769553617)
  ·
    refine ⟨5195240958717095827165213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6926987944956127769553617 5195240958717095827165213)
    ·
      refine ⟨1948215359518910935186955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5195240958717095827165213 1948215359518910935186955)
      ·
        refine ⟨2922323039278366402780433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1948215359518910935186955 2922323039278366402780433)
        ·
          refine ⟨2191742279458774802085325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2922323039278366402780433 2191742279458774802085325)
          ·
            refine ⟨821903354797040550781997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2191742279458774802085325 821903354797040550781997)
            ·
              refine ⟨308213758048890206543249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 821903354797040550781997 308213758048890206543249)
              ·
                refine ⟨231160318536667654907437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308213758048890206543249 231160318536667654907437)
                ·
                  refine ⟨86685119451250370590289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231160318536667654907437 86685119451250370590289)
                  ·
                    rfl

theorem cell20_189921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_189921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189921 prefixEnd_189921 := by exact prefixLift 189921
  have htrace : WordTrace (prefixWord ++ tailWord_189921) baseStart_189921 baseEnd_189921 := by
    simpa [prefixWord, tailWord_189921, baseEnd_189921] using wordTrace_append hprefix tailTrace_189921
  have hstable : (prefixWord ++ tailWord_189921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189921).length < 2 ^ (prefixWord ++ tailWord_189921).sum := by decide
  have hdescent : baseEnd_189921 < baseStart_189921 := by decide
  rcases family_descends (prefixWord ++ tailWord_189921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189928 : List Nat := [2, 1, 4, 1, 1, 2, 4, 1, 4]
def baseStart_189928 : Nat := 118140960795 + 189928 * 2 ^ 59
def prefixEnd_189928 : Nat := 4983230072969 + 3 ^ 40 * 189928 * 2
def baseEnd_189928 : Nat := 86688314441989457356927

theorem tailTrace_189928 : CollatzResearch.WordTrace tailWord_189928 prefixEnd_189928 86688314441989457356927 := by
  unfold tailWord_189928
  simp only [CollatzResearch.WordTrace]
  refine ⟨3463621627965383982529219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4618162170620511976705625 3463621627965383982529219)
  ·
    refine ⟨5195432441948075973793829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3463621627965383982529219 5195432441948075973793829)
    ·
      refine ⟨974143582865264245086343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5195432441948075973793829 974143582865264245086343)
      ·
        refine ⟨1461215374297896367629515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 974143582865264245086343 1461215374297896367629515)
        ·
          refine ⟨2191823061446844551444273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1461215374297896367629515 2191823061446844551444273)
          ·
            refine ⟨1643867296085133413583205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2191823061446844551444273 1643867296085133413583205)
            ·
              refine ⟨308225118015962515046851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1643867296085133413583205 308225118015962515046851)
              ·
                refine ⟨462337677023943772570277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308225118015962515046851 462337677023943772570277)
                ·
                  refine ⟨86688314441989457356927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 462337677023943772570277 86688314441989457356927)
                  ·
                    rfl

theorem cell20_189928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_189928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189928 prefixEnd_189928 := by exact prefixLift 189928
  have htrace : WordTrace (prefixWord ++ tailWord_189928) baseStart_189928 baseEnd_189928 := by
    simpa [prefixWord, tailWord_189928, baseEnd_189928] using wordTrace_append hprefix tailTrace_189928
  have hstable : (prefixWord ++ tailWord_189928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189928).length < 2 ^ (prefixWord ++ tailWord_189928).sum := by decide
  have hdescent : baseEnd_189928 < baseStart_189928 := by decide
  rcases family_descends (prefixWord ++ tailWord_189928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189962 : List Nat := [3, 1, 2, 2, 2, 4, 1, 3, 2]
def baseStart_189962 : Nat := 118140960795 + 189962 * 2 ^ 59
def prefixEnd_189962 : Nat := 4983230072969 + 3 ^ 40 * 189962 * 2
def baseEnd_189962 : Nat := 86703832968436450223455

theorem tailTrace_189962 : CollatzResearch.WordTrace tailWord_189962 prefixEnd_189962 86703832968436450223455 := by
  unfold tailWord_189962
  simp only [CollatzResearch.WordTrace]
  refine ⟨1732120834451897942949035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4618988891871727847864093 1732120834451897942949035)
  ·
    refine ⟨2598181251677846914423553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1732120834451897942949035 2598181251677846914423553)
    ·
      refine ⟨1948635938758385185817665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2598181251677846914423553 1948635938758385185817665)
      ·
        refine ⟨1461476954068788889363249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1948635938758385185817665 1461476954068788889363249)
        ·
          refine ⟨1096107715551591667022437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1461476954068788889363249 1096107715551591667022437)
          ·
            refine ⟨205520196665923437566707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1096107715551591667022437 205520196665923437566707)
            ·
              refine ⟨308280294998885156350061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205520196665923437566707 308280294998885156350061)
              ·
                refine ⟨115605110624581933631273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 308280294998885156350061 115605110624581933631273)
                ·
                  refine ⟨86703832968436450223455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115605110624581933631273 86703832968436450223455)
                  ·
                    rfl

theorem cell20_189962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_189962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189962 prefixEnd_189962 := by exact prefixLift 189962
  have htrace : WordTrace (prefixWord ++ tailWord_189962) baseStart_189962 baseEnd_189962 := by
    simpa [prefixWord, tailWord_189962, baseEnd_189962] using wordTrace_append hprefix tailTrace_189962
  have hstable : (prefixWord ++ tailWord_189962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189962).length < 2 ^ (prefixWord ++ tailWord_189962).sum := by decide
  have hdescent : baseEnd_189962 < baseStart_189962 := by decide
  rcases family_descends (prefixWord ++ tailWord_189962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189973 : List Nat := [1, 3, 2, 1, 3, 4, 6]
def baseStart_189973 : Nat := 118140960795 + 189973 * 2 ^ 59
def prefixEnd_189973 : Nat := 4983230072969 + 3 ^ 40 * 189973 * 2
def baseEnd_189973 : Nat := 9634317074241033428527

theorem tailTrace_189973 : CollatzResearch.WordTrace tailWord_189973 prefixEnd_189973 9634317074241033428527 := by
  unfold tailWord_189973
  simp only [CollatzResearch.WordTrace]
  refine ⟨6928884540767740650446573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4619256360511827100297715 6928884540767740650446573)
  ·
    refine ⟨2598331702787902743917465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6928884540767740650446573 2598331702787902743917465)
    ·
      refine ⟨1948748777090927057938099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2598331702787902743917465 1948748777090927057938099)
      ·
        refine ⟨2923123165636390586907149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1948748777090927057938099 2923123165636390586907149)
        ·
          refine ⟨1096171187113646470090181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2923123165636390586907149 1096171187113646470090181)
          ·
            refine ⟨205532097583808713141909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1096171187113646470090181 205532097583808713141909)
            ·
              refine ⟨9634317074241033428527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 205532097583808713141909 9634317074241033428527)
              ·
                rfl

theorem cell20_189973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 6].length) (baseStart_189973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189973 prefixEnd_189973 := by exact prefixLift 189973
  have htrace : WordTrace (prefixWord ++ tailWord_189973) baseStart_189973 baseEnd_189973 := by
    simpa [prefixWord, tailWord_189973, baseEnd_189973] using wordTrace_append hprefix tailTrace_189973
  have hstable : (prefixWord ++ tailWord_189973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189973).length < 2 ^ (prefixWord ++ tailWord_189973).sum := by decide
  have hdescent : baseEnd_189973 < baseStart_189973 := by decide
  rcases family_descends (prefixWord ++ tailWord_189973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189980 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 5]
def baseStart_189980 : Nat := 118140960795 + 189980 * 2 ^ 59
def prefixEnd_189980 : Nat := 4983230072969 + 3 ^ 40 * 189980 * 2
def baseEnd_189980 : Nat := 86712048658908387623381

theorem tailTrace_189980 : CollatzResearch.WordTrace tailWord_189980 prefixEnd_189980 86712048658908387623381 := by
  unfold tailWord_189980
  simp only [CollatzResearch.WordTrace]
  refine ⟨3464569925871190422975697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4619426567828253897300929 3464569925871190422975697)
  ·
    refine ⟨2598427444403392817231773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3464569925871190422975697 2598427444403392817231773)
    ·
      refine ⟨974410291651272306461915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2598427444403392817231773 974410291651272306461915)
      ·
        refine ⟨1461615437476908459692873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 974410291651272306461915 1461615437476908459692873)
        ·
          refine ⟨1096211578107681344769655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1461615437476908459692873 1096211578107681344769655)
          ·
            refine ⟨1644317367161522017154483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096211578107681344769655 1644317367161522017154483)
            ·
              refine ⟨2466476050742283025731725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1644317367161522017154483 2466476050742283025731725)
              ·
                refine ⟨924928519028356134649397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2466476050742283025731725 924928519028356134649397)
                ·
                  refine ⟨86712048658908387623381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 924928519028356134649397 86712048658908387623381)
                  ·
                    rfl

theorem cell20_189980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_189980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_189980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_189980 prefixEnd_189980 := by exact prefixLift 189980
  have htrace : WordTrace (prefixWord ++ tailWord_189980) baseStart_189980 baseEnd_189980 := by
    simpa [prefixWord, tailWord_189980, baseEnd_189980] using wordTrace_append hprefix tailTrace_189980
  have hstable : (prefixWord ++ tailWord_189980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189980).length < 2 ^ (prefixWord ++ tailWord_189980).sum := by decide
  have hdescent : baseEnd_189980 < baseStart_189980 := by decide
  rcases family_descends (prefixWord ++ tailWord_189980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190066 : List Nat := [3, 2, 1, 2, 3, 2, 3, 4]
def baseStart_190066 : Nat := 118140960795 + 190066 * 2 ^ 59
def prefixEnd_190066 : Nat := 4983230072969 + 3 ^ 40 * 190066 * 2
def baseEnd_190066 : Nat := 28917100467424770252121

theorem tailTrace_190066 : CollatzResearch.WordTrace tailWord_190066 prefixEnd_190066 28917100467424770252121 := by
  unfold tailWord_190066
  simp only [CollatzResearch.WordTrace]
  refine ⟨1733069132357704383395513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4621517686287211689054701 1733069132357704383395513)
  ·
    refine ⟨1299801849268278287546635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1733069132357704383395513 1299801849268278287546635)
    ·
      refine ⟨1949702773902417431319953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1299801849268278287546635 1949702773902417431319953)
      ·
        refine ⟨1462277080426813073489965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1949702773902417431319953 1462277080426813073489965)
        ·
          refine ⟨548353905160054902558737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1462277080426813073489965 548353905160054902558737)
          ·
            refine ⟨411265428870041176919053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548353905160054902558737 411265428870041176919053)
            ·
              refine ⟨154224535826265441344645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 411265428870041176919053 154224535826265441344645)
              ·
                refine ⟨28917100467424770252121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154224535826265441344645 28917100467424770252121)
                ·
                  rfl

theorem cell20_190066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_190066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190066 prefixEnd_190066 := by exact prefixLift 190066
  have htrace : WordTrace (prefixWord ++ tailWord_190066) baseStart_190066 baseEnd_190066 := by
    simpa [prefixWord, tailWord_190066, baseEnd_190066] using wordTrace_append hprefix tailTrace_190066
  have hstable : (prefixWord ++ tailWord_190066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190066).length < 2 ^ (prefixWord ++ tailWord_190066).sum := by decide
  have hdescent : baseEnd_190066 < baseStart_190066 := by decide
  rcases family_descends (prefixWord ++ tailWord_190066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190090 : List Nat := [3, 1, 2, 3, 2, 3, 1, 2, 3]
def baseStart_190090 : Nat := 118140960795 + 190090 * 2 ^ 59
def prefixEnd_190090 : Nat := 4983230072969 + 3 ^ 40 * 190090 * 2
def baseEnd_190090 : Nat := 86762255656236893956265

theorem tailTrace_190090 : CollatzResearch.WordTrace tailWord_190090 prefixEnd_190090 86762255656236893956265 := by
  unfold tailWord_190090
  simp only [CollatzResearch.WordTrace]
  refine ⟨1733287970335967408113931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4622101254229246421637149 1733287970335967408113931)
  ·
    refine ⟨2599931955503951112170897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1733287970335967408113931 2599931955503951112170897)
    ·
      refine ⟨1949948966627963334128173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2599931955503951112170897 1949948966627963334128173)
      ·
        refine ⟨731230862485486250298065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1949948966627963334128173 731230862485486250298065)
        ·
          refine ⟨548423146864114687723549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 731230862485486250298065 548423146864114687723549)
          ·
            refine ⟨205658680074043007896331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 548423146864114687723549 205658680074043007896331)
            ·
              refine ⟨308488020111064511844497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205658680074043007896331 308488020111064511844497)
              ·
                refine ⟨231366015083298383883373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308488020111064511844497 231366015083298383883373)
                ·
                  refine ⟨86762255656236893956265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231366015083298383883373 86762255656236893956265)
                  ·
                    rfl

theorem cell20_190090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_190090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190090 prefixEnd_190090 := by exact prefixLift 190090
  have htrace : WordTrace (prefixWord ++ tailWord_190090) baseStart_190090 baseEnd_190090 := by
    simpa [prefixWord, tailWord_190090, baseEnd_190090] using wordTrace_append hprefix tailTrace_190090
  have hstable : (prefixWord ++ tailWord_190090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190090).length < 2 ^ (prefixWord ++ tailWord_190090).sum := by decide
  have hdescent : baseEnd_190090 < baseStart_190090 := by decide
  rcases family_descends (prefixWord ++ tailWord_190090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190125 : List Nat := [1, 5, 2, 1, 1, 1, 3, 6]
def baseStart_190125 : Nat := 118140960795 + 190125 * 2 ^ 59
def prefixEnd_190125 : Nat := 4983230072969 + 3 ^ 40 * 190125 * 2
def baseEnd_190125 : Nat := 28926076869977442596485

theorem tailTrace_190125 : CollatzResearch.WordTrace tailWord_190125 prefixEnd_190125 28926076869977442596485 := by
  unfold tailWord_190125
  simp only [CollatzResearch.WordTrace]
  refine ⟨6934428436217070609979829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4622952290811380406653219 6934428436217070609979829)
  ·
    refine ⟨650102665895350369685609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6934428436217070609979829 650102665895350369685609)
    ·
      refine ⟨487576999421512777264207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 650102665895350369685609 487576999421512777264207)
      ·
        refine ⟨731365499132269165896311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487576999421512777264207 731365499132269165896311)
        ·
          refine ⟨1097048248698403748844467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 731365499132269165896311 1097048248698403748844467)
          ·
            refine ⟨1645572373047605623266701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097048248698403748844467 1645572373047605623266701)
            ·
              refine ⟨617089639892852108725013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1645572373047605623266701 617089639892852108725013)
              ·
                refine ⟨28926076869977442596485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 617089639892852108725013 28926076869977442596485)
                ·
                  rfl

theorem cell20_190125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 6].length) (baseStart_190125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190125 prefixEnd_190125 := by exact prefixLift 190125
  have htrace : WordTrace (prefixWord ++ tailWord_190125) baseStart_190125 baseEnd_190125 := by
    simpa [prefixWord, tailWord_190125, baseEnd_190125] using wordTrace_append hprefix tailTrace_190125
  have hstable : (prefixWord ++ tailWord_190125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190125).length < 2 ^ (prefixWord ++ tailWord_190125).sum := by decide
  have hdescent : baseEnd_190125 < baseStart_190125 := by decide
  rcases family_descends (prefixWord ++ tailWord_190125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190135 : List Nat := [1, 1, 3, 1, 5, 1, 3, 3, 2]
def baseStart_190135 : Nat := 118140960795 + 190135 * 2 ^ 59
def prefixEnd_190135 : Nat := 4983230072969 + 3 ^ 40 * 190135 * 2
def baseEnd_190135 : Nat := 86782794882416737456081

theorem tailTrace_190135 : CollatzResearch.WordTrace tailWord_190135 prefixEnd_190135 86782794882416737456081 := by
  unfold tailWord_190135
  simp only [CollatzResearch.WordTrace]
  refine ⟨6934793166180842317843859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4623195444120561545229239 6934793166180842317843859)
  ·
    refine ⟨10402189749271263476765789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6934793166180842317843859 10402189749271263476765789)
    ·
      refine ⟨3900821155976723803787171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10402189749271263476765789 3900821155976723803787171)
      ·
        refine ⟨5851231733965085705680757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3900821155976723803787171 5851231733965085705680757)
        ·
          refine ⟨548552975059226784907571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5851231733965085705680757 548552975059226784907571)
          ·
            refine ⟨822829462588840177361357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548552975059226784907571 822829462588840177361357)
            ·
              refine ⟨308561048470815066510509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 822829462588840177361357 308561048470815066510509)
              ·
                refine ⟨115710393176555649941441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 308561048470815066510509 115710393176555649941441)
                ·
                  refine ⟨86782794882416737456081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115710393176555649941441 86782794882416737456081)
                  ·
                    rfl

theorem cell20_190135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 2].length) (baseStart_190135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190135 prefixEnd_190135 := by exact prefixLift 190135
  have htrace : WordTrace (prefixWord ++ tailWord_190135) baseStart_190135 baseEnd_190135 := by
    simpa [prefixWord, tailWord_190135, baseEnd_190135] using wordTrace_append hprefix tailTrace_190135
  have hstable : (prefixWord ++ tailWord_190135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190135).length < 2 ^ (prefixWord ++ tailWord_190135).sum := by decide
  have hdescent : baseEnd_190135 < baseStart_190135 := by decide
  rcases family_descends (prefixWord ++ tailWord_190135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190211 : List Nat := [1, 1, 1, 3, 2, 2, 6, 2, 2]
def baseStart_190211 : Nat := 118140960795 + 190211 * 2 ^ 59
def prefixEnd_190211 : Nat := 4983230072969 + 3 ^ 40 * 190211 * 2
def baseEnd_190211 : Nat := 86817483353298250922437

theorem tailTrace_190211 : CollatzResearch.WordTrace tailWord_190211 prefixEnd_190211 86817483353298250922437 := by
  unfold tailWord_190211
  simp only [CollatzResearch.WordTrace]
  refine ⟨6937565113905507297610487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4625043409270338198406991 6937565113905507297610487)
  ·
    refine ⟨10406347670858260946415731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6937565113905507297610487 10406347670858260946415731)
    ·
      refine ⟨15609521506287391419623597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10406347670858260946415731 15609521506287391419623597)
      ·
        refine ⟨5853570564857771782358849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15609521506287391419623597 5853570564857771782358849)
        ·
          refine ⟨4390177923643328836769137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5853570564857771782358849 4390177923643328836769137)
          ·
            refine ⟨3292633442732496627576853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4390177923643328836769137 3292633442732496627576853)
            ·
              refine ⟨154342192628085779417665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3292633442732496627576853 154342192628085779417665)
              ·
                refine ⟨115756644471064334563249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154342192628085779417665 115756644471064334563249)
                ·
                  refine ⟨86817483353298250922437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115756644471064334563249 86817483353298250922437)
                  ·
                    rfl

theorem cell20_190211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 2].length) (baseStart_190211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190211 prefixEnd_190211 := by exact prefixLift 190211
  have htrace : WordTrace (prefixWord ++ tailWord_190211) baseStart_190211 baseEnd_190211 := by
    simpa [prefixWord, tailWord_190211, baseEnd_190211] using wordTrace_append hprefix tailTrace_190211
  have hstable : (prefixWord ++ tailWord_190211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190211).length < 2 ^ (prefixWord ++ tailWord_190211).sum := by decide
  have hdescent : baseEnd_190211 < baseStart_190211 := by decide
  rcases family_descends (prefixWord ++ tailWord_190211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190239 : List Nat := [1, 1, 2, 4, 2, 1, 5, 4]
def baseStart_190239 : Nat := 118140960795 + 190239 * 2 ^ 59
def prefixEnd_190239 : Nat := 4983230072969 + 3 ^ 40 * 190239 * 2
def baseEnd_190239 : Nat := 28943421105418199329663

theorem tailTrace_190239 : CollatzResearch.WordTrace tailWord_190239 prefixEnd_190239 28943421105418199329663 := by
  unfold tailWord_190239
  simp only [CollatzResearch.WordTrace]
  refine ⟨6938586357804068079629771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4625724238536045386419847 6938586357804068079629771)
  ·
    refine ⟨10407879536706102119444657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6938586357804068079629771 10407879536706102119444657)
    ·
      refine ⟨7805909652529576589583493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10407879536706102119444657 7805909652529576589583493)
      ·
        refine ⟨1463608059849295610546905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7805909652529576589583493 1463608059849295610546905)
        ·
          refine ⟨1097706044886971707910179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1463608059849295610546905 1097706044886971707910179)
          ·
            refine ⟨1646559067330457561865269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097706044886971707910179 1646559067330457561865269)
            ·
              refine ⟨154364912562230396424869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1646559067330457561865269 154364912562230396424869)
              ·
                refine ⟨28943421105418199329663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154364912562230396424869 28943421105418199329663)
                ·
                  rfl

theorem cell20_190239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 4].length) (baseStart_190239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190239 prefixEnd_190239 := by exact prefixLift 190239
  have htrace : WordTrace (prefixWord ++ tailWord_190239) baseStart_190239 baseEnd_190239 := by
    simpa [prefixWord, tailWord_190239, baseEnd_190239] using wordTrace_append hprefix tailTrace_190239
  have hstable : (prefixWord ++ tailWord_190239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190239).length < 2 ^ (prefixWord ++ tailWord_190239).sum := by decide
  have hdescent : baseEnd_190239 < baseStart_190239 := by decide
  rcases family_descends (prefixWord ++ tailWord_190239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190270 : List Nat := [4, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_190270 : Nat := 118140960795 + 190270 * 2 ^ 59
def prefixEnd_190270 : Nat := 4983230072969 + 3 ^ 40 * 190270 * 2
def baseEnd_190270 : Nat := 86844412560956267955529

theorem tailTrace_190270 : CollatzResearch.WordTrace tailWord_190270 prefixEnd_190270 86844412560956267955529 := by
  unfold tailWord_190270
  simp only [CollatzResearch.WordTrace]
  refine ⟨867464627586470046751033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4626478013794506916005509 867464627586470046751033)
  ·
    refine ⟨650598470689852535063275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 867464627586470046751033 650598470689852535063275)
    ·
      refine ⟨975897706034778802594913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 650598470689852535063275 975897706034778802594913)
      ·
        refine ⟨731923279526084101946185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 975897706034778802594913 731923279526084101946185)
        ·
          refine ⟨548942459644563076459639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 731923279526084101946185 548942459644563076459639)
          ·
            refine ⟨823413689466844614689459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548942459644563076459639 823413689466844614689459)
            ·
              refine ⟨1235120534200266922034189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823413689466844614689459 1235120534200266922034189)
              ·
                refine ⟨463170200325100095762821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1235120534200266922034189 463170200325100095762821)
                ·
                  refine ⟨86844412560956267955529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 463170200325100095762821 86844412560956267955529)
                  ·
                    rfl

theorem cell20_190270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_190270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190270 prefixEnd_190270 := by exact prefixLift 190270
  have htrace : WordTrace (prefixWord ++ tailWord_190270) baseStart_190270 baseEnd_190270 := by
    simpa [prefixWord, tailWord_190270, baseEnd_190270] using wordTrace_append hprefix tailTrace_190270
  have hstable : (prefixWord ++ tailWord_190270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190270).length < 2 ^ (prefixWord ++ tailWord_190270).sum := by decide
  have hdescent : baseEnd_190270 < baseStart_190270 := by decide
  rcases family_descends (prefixWord ++ tailWord_190270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190298 : List Nat := [3, 1, 1, 2, 1, 3, 3, 6]
def baseStart_190298 : Nat := 118140960795 + 190298 * 2 ^ 59
def prefixEnd_190298 : Nat := 4983230072969 + 3 ^ 40 * 190298 * 2
def baseEnd_190298 : Nat := 28952397507970871674027

theorem tailTrace_190298 : CollatzResearch.WordTrace tailWord_190298 prefixEnd_190298 28952397507970871674027 := by
  unfold tailWord_190298
  simp only [CollatzResearch.WordTrace]
  refine ⟨1735184566147580289006887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4627158843060214104018365 1735184566147580289006887)
  ·
    refine ⟨2602776849221370433510331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1735184566147580289006887 2602776849221370433510331)
    ·
      refine ⟨3904165273832055650265497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2602776849221370433510331 3904165273832055650265497)
      ·
        refine ⟨2928123955374041737699123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3904165273832055650265497 2928123955374041737699123)
        ·
          refine ⟨4392185933061062606548685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2928123955374041737699123 4392185933061062606548685)
          ·
            refine ⟨1647069724897898477455757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4392185933061062606548685 1647069724897898477455757)
            ·
              refine ⟨617651146836711929045909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1647069724897898477455757 617651146836711929045909)
              ·
                refine ⟨28952397507970871674027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 617651146836711929045909 28952397507970871674027)
                ·
                  rfl

theorem cell20_190298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_190298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190298 prefixEnd_190298 := by exact prefixLift 190298
  have htrace : WordTrace (prefixWord ++ tailWord_190298) baseStart_190298 baseEnd_190298 := by
    simpa [prefixWord, tailWord_190298, baseEnd_190298] using wordTrace_append hprefix tailTrace_190298
  have hstable : (prefixWord ++ tailWord_190298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190298).length < 2 ^ (prefixWord ++ tailWord_190298).sum := by decide
  have hdescent : baseEnd_190298 < baseStart_190298 := by decide
  rcases family_descends (prefixWord ++ tailWord_190298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190305 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 7]
def baseStart_190305 : Nat := 118140960795 + 190305 * 2 ^ 59
def prefixEnd_190305 : Nat := 4983230072969 + 3 ^ 40 * 190305 * 2
def baseEnd_190305 : Nat := 86860387514651701788719

theorem tailTrace_190305 : CollatzResearch.WordTrace tailWord_190305 prefixEnd_190305 86860387514651701788719 := by
  unfold tailWord_190305
  simp only [CollatzResearch.WordTrace]
  refine ⟨6940993575564961351532369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4627329050376640901021579 6940993575564961351532369)
  ·
    refine ⟨5205745181673721013649277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6940993575564961351532369 5205745181673721013649277)
    ·
      refine ⟨1952154443127645380118479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5205745181673721013649277 1952154443127645380118479)
      ·
        refine ⟨2928231664691468070177719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1952154443127645380118479 2928231664691468070177719)
        ·
          refine ⟨4392347497037202105266579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2928231664691468070177719 4392347497037202105266579)
          ·
            refine ⟨6588521245555803157899869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4392347497037202105266579 6588521245555803157899869)
            ·
              refine ⟨2470695467083426184212451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6588521245555803157899869 2470695467083426184212451)
              ·
                refine ⟨3706043200625139276318677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2470695467083426184212451 3706043200625139276318677)
                ·
                  refine ⟨86860387514651701788719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3706043200625139276318677 86860387514651701788719)
                  ·
                    rfl

theorem cell20_190305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_190305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190305 prefixEnd_190305 := by exact prefixLift 190305
  have htrace : WordTrace (prefixWord ++ tailWord_190305) baseStart_190305 baseEnd_190305 := by
    simpa [prefixWord, tailWord_190305, baseEnd_190305] using wordTrace_append hprefix tailTrace_190305
  have hstable : (prefixWord ++ tailWord_190305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190305).length < 2 ^ (prefixWord ++ tailWord_190305).sum := by decide
  have hdescent : baseEnd_190305 < baseStart_190305 := by decide
  rcases family_descends (prefixWord ++ tailWord_190305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190322 : List Nat := [3, 2, 1, 2, 1, 1, 1, 6, 3]
def baseStart_190322 : Nat := 118140960795 + 190322 * 2 ^ 59
def prefixEnd_190322 : Nat := 4983230072969 + 3 ^ 40 * 190322 * 2
def baseEnd_190322 : Nat := 86868146777875198221983

theorem tailTrace_190322 : CollatzResearch.WordTrace tailWord_190322 prefixEnd_190322 86868146777875198221983 := by
  unfold tailWord_190322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1735403404125843313725305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4627742411002248836600813 1735403404125843313725305)
  ·
    refine ⟨1301552553094382485293979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1735403404125843313725305 1301552553094382485293979)
    ·
      refine ⟨1952328829641573727940969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1301552553094382485293979 1952328829641573727940969)
      ·
        refine ⟨1464246622231180295955727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1952328829641573727940969 1464246622231180295955727)
        ·
          refine ⟨2196369933346770443933591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1464246622231180295955727 2196369933346770443933591)
          ·
            refine ⟨3294554900020155665900387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2196369933346770443933591 3294554900020155665900387)
            ·
              refine ⟨4941832350030233498850581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3294554900020155665900387 4941832350030233498850581)
              ·
                refine ⟨231648391407667195258621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4941832350030233498850581 231648391407667195258621)
                ·
                  refine ⟨86868146777875198221983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231648391407667195258621 86868146777875198221983)
                  ·
                    rfl

theorem cell20_190322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_190322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190322 prefixEnd_190322 := by exact prefixLift 190322
  have htrace : WordTrace (prefixWord ++ tailWord_190322) baseStart_190322 baseEnd_190322 := by
    simpa [prefixWord, tailWord_190322, baseEnd_190322] using wordTrace_append hprefix tailTrace_190322
  have hstable : (prefixWord ++ tailWord_190322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190322).length < 2 ^ (prefixWord ++ tailWord_190322).sum := by decide
  have hdescent : baseEnd_190322 < baseStart_190322 := by decide
  rcases family_descends (prefixWord ++ tailWord_190322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190336 : List Nat := [2, 1, 1, 2, 1, 2, 6, 5]
def baseStart_190336 : Nat := 118140960795 + 190336 * 2 ^ 59
def prefixEnd_190336 : Nat := 4983230072969 + 3 ^ 40 * 190336 * 2
def baseEnd_190336 : Nat := 28958178919784457251753

theorem tailTrace_190336 : CollatzResearch.WordTrace tailWord_190336 prefixEnd_190336 28958178919784457251753 := by
  unfold tailWord_190336
  simp only [CollatzResearch.WordTrace]
  refine ⟨3471062119226326822955431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4628082825635102430607241 3471062119226326822955431)
  ·
    refine ⟨5206593178839490234433147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3471062119226326822955431 5206593178839490234433147)
    ·
      refine ⟨7809889768259235351649721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5206593178839490234433147 7809889768259235351649721)
      ·
        refine ⟨5857417326194426513737291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7809889768259235351649721 5857417326194426513737291)
        ·
          refine ⟨8786125989291639770605937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5857417326194426513737291 8786125989291639770605937)
          ·
            refine ⟨6589594491968729827954453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8786125989291639770605937 6589594491968729827954453)
            ·
              refine ⟨308887241811034210685365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6589594491968729827954453 308887241811034210685365)
              ·
                refine ⟨28958178919784457251753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 308887241811034210685365 28958178919784457251753)
                ·
                  rfl

theorem cell20_190336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_190336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190336 prefixEnd_190336 := by exact prefixLift 190336
  have htrace : WordTrace (prefixWord ++ tailWord_190336) baseStart_190336 baseEnd_190336 := by
    simpa [prefixWord, tailWord_190336, baseEnd_190336] using wordTrace_append hprefix tailTrace_190336
  have hstable : (prefixWord ++ tailWord_190336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190336).length < 2 ^ (prefixWord ++ tailWord_190336).sum := by decide
  have hdescent : baseEnd_190336 < baseStart_190336 := by decide
  rcases family_descends (prefixWord ++ tailWord_190336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190339 : List Nat := [1, 1, 1, 3, 4, 2, 4, 1, 3]
def baseStart_190339 : Nat := 118140960795 + 190339 * 2 ^ 59
def prefixEnd_190339 : Nat := 4983230072969 + 3 ^ 40 * 190339 * 2
def baseEnd_190339 : Nat := 86875906041098694655247

theorem tailTrace_190339 : CollatzResearch.WordTrace tailWord_190339 prefixEnd_190339 86875906041098694655247 := by
  unfold tailWord_190339
  simp only [CollatzResearch.WordTrace]
  refine ⟨6942233657441785158270071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4628155771627856772180047 6942233657441785158270071)
  ·
    refine ⟨10413350486162677737405107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6942233657441785158270071 10413350486162677737405107)
    ·
      refine ⟨15620025729244016606107661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10413350486162677737405107 15620025729244016606107661)
      ·
        refine ⟨5857509648466506227290373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15620025729244016606107661 5857509648466506227290373)
        ·
          refine ⟨1098283059087469917616945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5857509648466506227290373 1098283059087469917616945)
          ·
            refine ⟨823712294315602438212709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1098283059087469917616945 823712294315602438212709)
            ·
              refine ⟨154446055184175457164883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 823712294315602438212709 154446055184175457164883)
              ·
                refine ⟨231669082776263185747325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154446055184175457164883 231669082776263185747325)
                ·
                  refine ⟨86875906041098694655247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231669082776263185747325 86875906041098694655247)
                  ·
                    rfl

theorem cell20_190339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 3].length) (baseStart_190339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190339 prefixEnd_190339 := by exact prefixLift 190339
  have htrace : WordTrace (prefixWord ++ tailWord_190339) baseStart_190339 baseEnd_190339 := by
    simpa [prefixWord, tailWord_190339, baseEnd_190339] using wordTrace_append hprefix tailTrace_190339
  have hstable : (prefixWord ++ tailWord_190339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190339).length < 2 ^ (prefixWord ++ tailWord_190339).sum := by decide
  have hdescent : baseEnd_190339 < baseStart_190339 := by decide
  rcases family_descends (prefixWord ++ tailWord_190339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190376 : List Nat := [2, 1, 6, 2, 1, 2, 2, 2, 2]
def baseStart_190376 : Nat := 118140960795 + 190376 * 2 ^ 59
def prefixEnd_190376 : Nat := 4983230072969 + 3 ^ 40 * 190376 * 2
def baseEnd_190376 : Nat := 86892793849291010421763

theorem tailTrace_190376 : CollatzResearch.WordTrace tailWord_190376 prefixEnd_190376 86892793849291010421763 := by
  unfold tailWord_190376
  simp only [CollatzResearch.WordTrace]
  refine ⟨3471791579153870238683491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4629055438871826984911321 3471791579153870238683491)
  ·
    refine ⟨5207687368730805358025237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3471791579153870238683491 5207687368730805358025237)
    ·
      refine ⟨244110345409256501157433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5207687368730805358025237 244110345409256501157433)
      ·
        refine ⟨183082759056942375868075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244110345409256501157433 183082759056942375868075)
        ·
          refine ⟨274624138585413563802113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183082759056942375868075 274624138585413563802113)
          ·
            refine ⟨205968103939060172851585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274624138585413563802113 205968103939060172851585)
            ·
              refine ⟨154476077954295129638689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205968103939060172851585 154476077954295129638689)
              ·
                refine ⟨115857058465721347229017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154476077954295129638689 115857058465721347229017)
                ·
                  refine ⟨86892793849291010421763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115857058465721347229017 86892793849291010421763)
                  ·
                    rfl

theorem cell20_190376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 2].length) (baseStart_190376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190376 prefixEnd_190376 := by exact prefixLift 190376
  have htrace : WordTrace (prefixWord ++ tailWord_190376) baseStart_190376 baseEnd_190376 := by
    simpa [prefixWord, tailWord_190376, baseEnd_190376] using wordTrace_append hprefix tailTrace_190376
  have hstable : (prefixWord ++ tailWord_190376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190376).length < 2 ^ (prefixWord ++ tailWord_190376).sum := by decide
  have hdescent : baseEnd_190376 < baseStart_190376 := by decide
  rcases family_descends (prefixWord ++ tailWord_190376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190418 : List Nat := [3, 2, 2, 3, 2, 1, 2, 3, 2]
def baseStart_190418 : Nat := 118140960795 + 190418 * 2 ^ 59
def prefixEnd_190418 : Nat := 4983230072969 + 3 ^ 40 * 190418 * 2
def baseEnd_190418 : Nat := 86911963793725531021591

theorem tailTrace_190418 : CollatzResearch.WordTrace tailWord_190418 prefixEnd_190418 86911963793725531021591 := by
  unfold tailWord_190418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1736278756038895412598977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4630076682770387766930605 1736278756038895412598977)
  ·
    refine ⟨1302209067029171559449233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1736278756038895412598977 1302209067029171559449233)
    ·
      refine ⟨976656800271878669586925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1302209067029171559449233 976656800271878669586925)
      ·
        refine ⟨366246300101954501095097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 976656800271878669586925 366246300101954501095097)
        ·
          refine ⟨274684725076465875821323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366246300101954501095097 274684725076465875821323)
          ·
            refine ⟨412027087614698813731985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274684725076465875821323 412027087614698813731985)
            ·
              refine ⟨309020315711024110298989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412027087614698813731985 309020315711024110298989)
              ·
                refine ⟨115882618391634041362121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 309020315711024110298989 115882618391634041362121)
                ·
                  refine ⟨86911963793725531021591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115882618391634041362121 86911963793725531021591)
                  ·
                    rfl

theorem cell20_190418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_190418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190418 prefixEnd_190418 := by exact prefixLift 190418
  have htrace : WordTrace (prefixWord ++ tailWord_190418) baseStart_190418 baseEnd_190418 := by
    simpa [prefixWord, tailWord_190418, baseEnd_190418] using wordTrace_append hprefix tailTrace_190418
  have hstable : (prefixWord ++ tailWord_190418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190418).length < 2 ^ (prefixWord ++ tailWord_190418).sum := by decide
  have hdescent : baseEnd_190418 < baseStart_190418 := by decide
  rcases family_descends (prefixWord ++ tailWord_190418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190428 : List Nat := [2, 2, 6, 1, 1, 2, 1, 2, 3]
def baseStart_190428 : Nat := 118140960795 + 190428 * 2 ^ 59
def prefixEnd_190428 : Nat := 4983230072969 + 3 ^ 40 * 190428 * 2
def baseEnd_190428 : Nat := 86916528066209940688217

theorem tailTrace_190428 : CollatzResearch.WordTrace tailWord_190428 prefixEnd_190428 86916528066209940688217 := by
  unfold tailWord_190428
  simp only [CollatzResearch.WordTrace]
  refine ⟨3472739877059676679129969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4630319836079568905506625 3472739877059676679129969)
  ·
    refine ⟨2604554907794757509347477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3472739877059676679129969 2604554907794757509347477)
    ·
      refine ⟨122088511302879258250663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2604554907794757509347477 122088511302879258250663)
      ·
        refine ⟨183132766954318887375995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122088511302879258250663 183132766954318887375995)
        ·
          refine ⟨274699150431478331063993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183132766954318887375995 274699150431478331063993)
          ·
            refine ⟨206024362823608748297995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274699150431478331063993 206024362823608748297995)
            ·
              refine ⟨309036544235413122446993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206024362823608748297995 309036544235413122446993)
              ·
                refine ⟨231777408176559841835245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309036544235413122446993 231777408176559841835245)
                ·
                  refine ⟨86916528066209940688217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231777408176559841835245 86916528066209940688217)
                  ·
                    rfl

theorem cell20_190428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_190428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190428 prefixEnd_190428 := by exact prefixLift 190428
  have htrace : WordTrace (prefixWord ++ tailWord_190428) baseStart_190428 baseEnd_190428 := by
    simpa [prefixWord, tailWord_190428, baseEnd_190428] using wordTrace_append hprefix tailTrace_190428
  have hstable : (prefixWord ++ tailWord_190428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190428).length < 2 ^ (prefixWord ++ tailWord_190428).sum := by decide
  have hdescent : baseEnd_190428 < baseStart_190428 := by decide
  rcases family_descends (prefixWord ++ tailWord_190428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190429 : List Nat := [1, 4, 3, 1, 3, 1, 7]
def baseStart_190429 : Nat := 118140960795 + 190429 * 2 ^ 59
def prefixEnd_190429 : Nat := 4983230072969 + 3 ^ 40 * 190429 * 2
def baseEnd_190429 : Nat := 9657442721495375739431

theorem tailTrace_190429 : CollatzResearch.WordTrace tailWord_190429 prefixEnd_190429 9657442721495375739431 := by
  unfold tailWord_190429
  simp only [CollatzResearch.WordTrace]
  refine ⟨6945516227115730529046341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4630344151410487019364227 6945516227115730529046341)
  ·
    refine ⟨1302284292584199474196189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6945516227115730529046341 1302284292584199474196189)
    ·
      refine ⟨488356609719074802823571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1302284292584199474196189 488356609719074802823571)
      ·
        refine ⟨732534914578612204235357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488356609719074802823571 732534914578612204235357)
        ·
          refine ⟨274700592966979576588259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 732534914578612204235357 274700592966979576588259)
          ·
            refine ⟨412050889450469364882389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274700592966979576588259 412050889450469364882389)
            ·
              refine ⟨9657442721495375739431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 412050889450469364882389 9657442721495375739431)
              ·
                rfl

theorem cell20_190429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 7].length) (baseStart_190429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190429 prefixEnd_190429 := by exact prefixLift 190429
  have htrace : WordTrace (prefixWord ++ tailWord_190429) baseStart_190429 baseEnd_190429 := by
    simpa [prefixWord, tailWord_190429, baseEnd_190429] using wordTrace_append hprefix tailTrace_190429
  have hstable : (prefixWord ++ tailWord_190429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190429).length < 2 ^ (prefixWord ++ tailWord_190429).sum := by decide
  have hdescent : baseEnd_190429 < baseStart_190429 := by decide
  rcases family_descends (prefixWord ++ tailWord_190429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190464 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 6]
def baseStart_190464 : Nat := 118140960795 + 190464 * 2 ^ 59
def prefixEnd_190464 : Nat := 4983230072969 + 3 ^ 40 * 190464 * 2
def baseEnd_190464 : Nat := 86932959447153815488069

theorem tailTrace_190464 : CollatzResearch.WordTrace tailWord_190464 prefixEnd_190464 86932959447153815488069 := by
  unfold tailWord_190464
  simp only [CollatzResearch.WordTrace]
  refine ⟨3473396390994465753285223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4631195187992621004380297 3473396390994465753285223)
  ·
    refine ⟨5210094586491698629927835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3473396390994465753285223 5210094586491698629927835)
    ·
      refine ⟨7815141879737547944891753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5210094586491698629927835 7815141879737547944891753)
      ·
        refine ⟨5861356409803160958668815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7815141879737547944891753 5861356409803160958668815)
        ·
          refine ⟨8792034614704741438003223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5861356409803160958668815 8792034614704741438003223)
          ·
            refine ⟨13188051922057112157004835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8792034614704741438003223 13188051922057112157004835)
            ·
              refine ⟨19782077883085668235507253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13188051922057112157004835 19782077883085668235507253)
              ·
                refine ⟨1854569801539281397078805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19782077883085668235507253 1854569801539281397078805)
                ·
                  refine ⟨86932959447153815488069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1854569801539281397078805 86932959447153815488069)
                  ·
                    rfl

theorem cell20_190464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_190464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190464 prefixEnd_190464 := by exact prefixLift 190464
  have htrace : WordTrace (prefixWord ++ tailWord_190464) baseStart_190464 baseEnd_190464 := by
    simpa [prefixWord, tailWord_190464, baseEnd_190464] using wordTrace_append hprefix tailTrace_190464
  have hstable : (prefixWord ++ tailWord_190464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190464).length < 2 ^ (prefixWord ++ tailWord_190464).sum := by decide
  have hdescent : baseEnd_190464 < baseStart_190464 := by decide
  rcases family_descends (prefixWord ++ tailWord_190464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190495 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 5]
def baseStart_190495 : Nat := 118140960795 + 190495 * 2 ^ 59
def prefixEnd_190495 : Nat := 4983230072969 + 3 ^ 40 * 190495 * 2
def baseEnd_190495 : Nat := 86947108691855485454609

theorem tailTrace_190495 : CollatzResearch.WordTrace tailWord_190495 prefixEnd_190495 86947108691855485454609 := by
  unfold tailWord_190495
  simp only [CollatzResearch.WordTrace]
  refine ⟨6947923444876623800948939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4631948963251082533965959 6947923444876623800948939)
  ·
    refine ⟨10421885167314935701423409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6947923444876623800948939 10421885167314935701423409)
    ·
      refine ⟨7816413875486201776067557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10421885167314935701423409 7816413875486201776067557)
      ·
        refine ⟨1465577601653662833012667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7816413875486201776067557 1465577601653662833012667)
        ·
          refine ⟨2198366402480494249519001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1465577601653662833012667 2198366402480494249519001)
          ·
            refine ⟨1648774801860370687139251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2198366402480494249519001 1648774801860370687139251)
            ·
              refine ⟨2473162202790556030708877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648774801860370687139251 2473162202790556030708877)
              ·
                refine ⟨927435826046458511515829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2473162202790556030708877 927435826046458511515829)
                ·
                  refine ⟨86947108691855485454609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 927435826046458511515829 86947108691855485454609)
                  ·
                    rfl

theorem cell20_190495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_190495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190495 prefixEnd_190495 := by exact prefixLift 190495
  have htrace : WordTrace (prefixWord ++ tailWord_190495) baseStart_190495 baseEnd_190495 := by
    simpa [prefixWord, tailWord_190495, baseEnd_190495] using wordTrace_append hprefix tailTrace_190495
  have hstable : (prefixWord ++ tailWord_190495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190495).length < 2 ^ (prefixWord ++ tailWord_190495).sum := by decide
  have hdescent : baseEnd_190495 < baseStart_190495 := by decide
  rcases family_descends (prefixWord ++ tailWord_190495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190504 : List Nat := [2, 1, 5, 3, 2, 1, 2, 1, 3]
def baseStart_190504 : Nat := 118140960795 + 190504 * 2 ^ 59
def prefixEnd_190504 : Nat := 4983230072969 + 3 ^ 40 * 190504 * 2
def baseEnd_190504 : Nat := 86951216537091454154573

theorem tailTrace_190504 : CollatzResearch.WordTrace tailWord_190504 prefixEnd_190504 86951216537091454154573 := by
  unfold tailWord_190504
  simp only [CollatzResearch.WordTrace]
  refine ⟨3474125850922009169013283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4632167801229345558684377 3474125850922009169013283)
  ·
    refine ⟨5211188776383013753519925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3474125850922009169013283 5211188776383013753519925)
    ·
      refine ⟨488548947785907539392493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5211188776383013753519925 488548947785907539392493)
      ·
        refine ⟨183205855419715327272185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 488548947785907539392493 183205855419715327272185)
        ·
          refine ⟨137404391564786495454139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183205855419715327272185 137404391564786495454139)
          ·
            refine ⟨206106587347179743181209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137404391564786495454139 206106587347179743181209)
            ·
              refine ⟨154579940510384807385907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206106587347179743181209 154579940510384807385907)
              ·
                refine ⟨231869910765577211078861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154579940510384807385907 231869910765577211078861)
                ·
                  refine ⟨86951216537091454154573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231869910765577211078861 86951216537091454154573)
                  ·
                    rfl

theorem cell20_190504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 3].length) (baseStart_190504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190504 prefixEnd_190504 := by exact prefixLift 190504
  have htrace : WordTrace (prefixWord ++ tailWord_190504) baseStart_190504 baseEnd_190504 := by
    simpa [prefixWord, tailWord_190504, baseEnd_190504] using wordTrace_append hprefix tailTrace_190504
  have hstable : (prefixWord ++ tailWord_190504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190504).length < 2 ^ (prefixWord ++ tailWord_190504).sum := by decide
  have hdescent : baseEnd_190504 < baseStart_190504 := by decide
  rcases family_descends (prefixWord ++ tailWord_190504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190512 : List Nat := [2, 1, 1, 1, 2, 6, 1, 3, 3]
def baseStart_190512 : Nat := 118140960795 + 190512 * 2 ^ 59
def prefixEnd_190512 : Nat := 4983230072969 + 3 ^ 40 * 190512 * 2
def baseEnd_190512 : Nat := 86954867955078981887873

theorem tailTrace_190512 : CollatzResearch.WordTrace tailWord_190512 prefixEnd_190512 86954867955078981887873 := by
  unfold tailWord_190512
  simp only [CollatzResearch.WordTrace]
  refine ⟨3474271742907517852158895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4632362323876690469545193 3474271742907517852158895)
  ·
    refine ⟨5211407614361276778238343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3474271742907517852158895 5211407614361276778238343)
    ·
      refine ⟨7817111421541915167357515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5211407614361276778238343 7817111421541915167357515)
      ·
        refine ⟨11725667132312872751036273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7817111421541915167357515 11725667132312872751036273)
        ·
          refine ⟨8794250349234654563277205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11725667132312872751036273 8794250349234654563277205)
          ·
            refine ⟨412230485120374432653619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8794250349234654563277205 412230485120374432653619)
            ·
              refine ⟨618345727680561648980429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412230485120374432653619 618345727680561648980429)
              ·
                refine ⟨231879647880210618367661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 618345727680561648980429 231879647880210618367661)
                ·
                  refine ⟨86954867955078981887873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231879647880210618367661 86954867955078981887873)
                  ·
                    rfl

theorem cell20_190512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_190512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190512 prefixEnd_190512 := by exact prefixLift 190512
  have htrace : WordTrace (prefixWord ++ tailWord_190512) baseStart_190512 baseEnd_190512 := by
    simpa [prefixWord, tailWord_190512, baseEnd_190512] using wordTrace_append hprefix tailTrace_190512
  have hstable : (prefixWord ++ tailWord_190512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190512).length < 2 ^ (prefixWord ++ tailWord_190512).sum := by decide
  have hdescent : baseEnd_190512 < baseStart_190512 := by decide
  rcases family_descends (prefixWord ++ tailWord_190512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190564 : List Nat := [2, 3, 1, 1, 2, 1, 5, 5]
def baseStart_190564 : Nat := 118140960795 + 190564 * 2 ^ 59
def prefixEnd_190564 : Nat := 4983230072969 + 3 ^ 40 * 190564 * 2
def baseEnd_190564 : Nat := 28992867390665970718109

theorem tailTrace_190564 : CollatzResearch.WordTrace tailWord_190564 prefixEnd_190564 28992867390665970718109 := by
  unfold tailWord_190564
  simp only [CollatzResearch.WordTrace]
  refine ⟨3475220040813324292605373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4633626721084432390140497 3475220040813324292605373)
  ·
    refine ⟨1303207515304996609727015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3475220040813324292605373 1303207515304996609727015)
    ·
      refine ⟨1954811272957494914590523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1303207515304996609727015 1954811272957494914590523)
      ·
        refine ⟨2932216909436242371885785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1954811272957494914590523 2932216909436242371885785)
        ·
          refine ⟨2199162682077181778914339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2932216909436242371885785 2199162682077181778914339)
          ·
            refine ⟨3298744023115772668371509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2199162682077181778914339 3298744023115772668371509)
            ·
              refine ⟨309257252167103687659829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3298744023115772668371509 309257252167103687659829)
              ·
                refine ⟨28992867390665970718109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 309257252167103687659829 28992867390665970718109)
                ·
                  rfl

theorem cell20_190564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_190564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190564 prefixEnd_190564 := by exact prefixLift 190564
  have htrace : WordTrace (prefixWord ++ tailWord_190564) baseStart_190564 baseEnd_190564 := by
    simpa [prefixWord, tailWord_190564, baseEnd_190564] using wordTrace_append hprefix tailTrace_190564
  have hstable : (prefixWord ++ tailWord_190564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190564).length < 2 ^ (prefixWord ++ tailWord_190564).sum := by decide
  have hdescent : baseEnd_190564 < baseStart_190564 := by decide
  rcases family_descends (prefixWord ++ tailWord_190564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190602 : List Nat := [3, 1, 2, 3, 1, 3, 7]
def baseStart_190602 : Nat := 118140960795 + 190602 * 2 ^ 59
def prefixEnd_190602 : Nat := 4983230072969 + 3 ^ 40 * 190602 * 2
def baseEnd_190602 : Nat := 9666216267493185431945

theorem tailTrace_190602 : CollatzResearch.WordTrace tailWord_190602 prefixEnd_190602 9666216267493185431945 := by
  unfold tailWord_190602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1737956513872245268773515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4634550703659320716729373 1737956513872245268773515)
  ·
    refine ⟨2606934770808367903160273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1737956513872245268773515 2606934770808367903160273)
    ·
      refine ⟨1955201078106275927370205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2606934770808367903160273 1955201078106275927370205)
      ·
        refine ⟨733200404289853472763827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1955201078106275927370205 733200404289853472763827)
        ·
          refine ⟨1099800606434780209145741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733200404289853472763827 1099800606434780209145741)
          ·
            refine ⟨412425227413042578429653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1099800606434780209145741 412425227413042578429653)
            ·
              refine ⟨9666216267493185431945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 412425227413042578429653 9666216267493185431945)
              ·
                rfl

theorem cell20_190602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 7].length) (baseStart_190602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190602 prefixEnd_190602 := by exact prefixLift 190602
  have htrace : WordTrace (prefixWord ++ tailWord_190602) baseStart_190602 baseEnd_190602 := by
    simpa [prefixWord, tailWord_190602, baseEnd_190602] using wordTrace_append hprefix tailTrace_190602
  have hstable : (prefixWord ++ tailWord_190602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190602).length < 2 ^ (prefixWord ++ tailWord_190602).sum := by decide
  have hdescent : baseEnd_190602 < baseStart_190602 := by decide
  rcases family_descends (prefixWord ++ tailWord_190602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190647 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 5]
def baseStart_190647 : Nat := 118140960795 + 190647 * 2 ^ 59
def prefixEnd_190647 : Nat := 4983230072969 + 3 ^ 40 * 190647 * 2
def baseEnd_190647 : Nat := 87016485633618512387321

theorem tailTrace_190647 : CollatzResearch.WordTrace tailWord_190647 prefixEnd_190647 87016485633618512387321 := by
  unfold tailWord_190647
  simp only [CollatzResearch.WordTrace]
  refine ⟨6953467340325953760482195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4635644893550635840321463 6953467340325953760482195)
  ·
    refine ⟨10430201010488930640723293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6953467340325953760482195 10430201010488930640723293)
    ·
      refine ⟨3911325378933348990271235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10430201010488930640723293 3911325378933348990271235)
      ·
        refine ⟨5866988068400023485406853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3911325378933348990271235 5866988068400023485406853)
        ·
          refine ⟨1100060262825004403513785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5866988068400023485406853 1100060262825004403513785)
          ·
            refine ⟨825045197118753302635339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1100060262825004403513785 825045197118753302635339)
            ·
              refine ⟨1237567795678129953953009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 825045197118753302635339 1237567795678129953953009)
              ·
                refine ⟨928175846758597465464757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1237567795678129953953009 928175846758597465464757)
                ·
                  refine ⟨87016485633618512387321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 928175846758597465464757 87016485633618512387321)
                  ·
                    rfl

theorem cell20_190647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_190647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190647 prefixEnd_190647 := by exact prefixLift 190647
  have htrace : WordTrace (prefixWord ++ tailWord_190647) baseStart_190647 baseEnd_190647 := by
    simpa [prefixWord, tailWord_190647, baseEnd_190647] using wordTrace_append hprefix tailTrace_190647
  have hstable : (prefixWord ++ tailWord_190647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190647).length < 2 ^ (prefixWord ++ tailWord_190647).sum := by decide
  have hdescent : baseEnd_190647 < baseStart_190647 := by decide
  rcases family_descends (prefixWord ++ tailWord_190647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190650 : List Nat := [3, 1, 1, 1, 2, 2, 5, 3, 2]
def baseStart_190650 : Nat := 118140960795 + 190650 * 2 ^ 59
def prefixEnd_190650 : Nat := 4983230072969 + 3 ^ 40 * 190650 * 2
def baseEnd_190650 : Nat := 87017854915363835287309

theorem tailTrace_190650 : CollatzResearch.WordTrace tailWord_190650 prefixEnd_190650 87017854915363835287309 := by
  unfold tailWord_190650
  simp only [CollatzResearch.WordTrace]
  refine ⟨1738394189828771318210351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4635717839543390181894269 1738394189828771318210351)
  ·
    refine ⟨2607591284743156977315527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1738394189828771318210351 2607591284743156977315527)
    ·
      refine ⟨3911386927114735465973291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2607591284743156977315527 3911386927114735465973291)
      ·
        refine ⟨5867080390672103198959937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3911386927114735465973291 5867080390672103198959937)
        ·
          refine ⟨4400310293004077399219953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5867080390672103198959937 4400310293004077399219953)
          ·
            refine ⟨3300232719753058049414965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4400310293004077399219953 3300232719753058049414965)
            ·
              refine ⟨309396817476849192132653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3300232719753058049414965 309396817476849192132653)
              ·
                refine ⟨116023806553818447049745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 309396817476849192132653 116023806553818447049745)
                ·
                  refine ⟨87017854915363835287309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116023806553818447049745 87017854915363835287309)
                  ·
                    rfl

theorem cell20_190650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_190650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190650 prefixEnd_190650 := by exact prefixLift 190650
  have htrace : WordTrace (prefixWord ++ tailWord_190650) baseStart_190650 baseEnd_190650 := by
    simpa [prefixWord, tailWord_190650, baseEnd_190650] using wordTrace_append hprefix tailTrace_190650
  have hstable : (prefixWord ++ tailWord_190650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190650).length < 2 ^ (prefixWord ++ tailWord_190650).sum := by decide
  have hdescent : baseEnd_190650 < baseStart_190650 := by decide
  rcases family_descends (prefixWord ++ tailWord_190650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190661 : List Nat := [1, 3, 1, 1, 1, 1, 12]
def baseStart_190661 : Nat := 118140960795 + 190661 * 2 ^ 59
def prefixEnd_190661 : Nat := 4983230072969 + 3 ^ 40 * 190661 * 2
def baseEnd_190661 : Nat := 9669208401677409546733

theorem tailTrace_190661 : CollatzResearch.WordTrace tailWord_190661 prefixEnd_190661 9669208401677409546733 := by
  unfold tailWord_190661
  simp only [CollatzResearch.WordTrace]
  refine ⟨6953977962275234151491837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4635985308183489434327891 6953977962275234151491837)
  ·
    refine ⟨2607741735853212806809439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6953977962275234151491837 2607741735853212806809439)
    ·
      refine ⟨3911612603779819210214159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2607741735853212806809439 3911612603779819210214159)
      ·
        refine ⟨5867418905669728815321239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3911612603779819210214159 5867418905669728815321239)
        ·
          refine ⟨8801128358504593222981859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5867418905669728815321239 8801128358504593222981859)
          ·
            refine ⟨13201692537756889834472789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8801128358504593222981859 13201692537756889834472789)
            ·
              refine ⟨9669208401677409546733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 13201692537756889834472789 9669208401677409546733)
              ·
                rfl

theorem cell20_190661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 12].length) (baseStart_190661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190661 prefixEnd_190661 := by exact prefixLift 190661
  have htrace : WordTrace (prefixWord ++ tailWord_190661) baseStart_190661 baseEnd_190661 := by
    simpa [prefixWord, tailWord_190661, baseEnd_190661] using wordTrace_append hprefix tailTrace_190661
  have hstable : (prefixWord ++ tailWord_190661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190661).length < 2 ^ (prefixWord ++ tailWord_190661).sum := by decide
  have hdescent : baseEnd_190661 < baseStart_190661 := by decide
  rcases family_descends (prefixWord ++ tailWord_190661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190677 : List Nat := [1, 3, 2, 4, 3, 1, 2, 1, 3]
def baseStart_190677 : Nat := 118140960795 + 190677 * 2 ^ 59
def prefixEnd_190677 : Nat := 4983230072969 + 3 ^ 40 * 190677 * 2
def baseEnd_190677 : Nat := 87030178451071741387199

theorem tailTrace_190677 : CollatzResearch.WordTrace tailWord_190677 prefixEnd_190677 87030178451071741387199 := by
  unfold tailWord_190677
  simp only [CollatzResearch.WordTrace]
  refine ⟨6954561530217268884074285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4636374353478179256049523 6954561530217268884074285)
  ·
    refine ⟨2607960573831475831527857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6954561530217268884074285 2607960573831475831527857)
    ·
      refine ⟨1955970430373606873645893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2607960573831475831527857 1955970430373606873645893)
      ·
        refine ⟨366744455695051288808605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1955970430373606873645893 366744455695051288808605)
        ·
          refine ⟨137529170885644233303227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 366744455695051288808605 137529170885644233303227)
          ·
            refine ⟨206293756328466349954841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137529170885644233303227 206293756328466349954841)
            ·
              refine ⟨154720317246349762466131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206293756328466349954841 154720317246349762466131)
              ·
                refine ⟨232080475869524643699197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154720317246349762466131 232080475869524643699197)
                ·
                  refine ⟨87030178451071741387199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232080475869524643699197 87030178451071741387199)
                  ·
                    rfl

theorem cell20_190677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_190677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190677 prefixEnd_190677 := by exact prefixLift 190677
  have htrace : WordTrace (prefixWord ++ tailWord_190677) baseStart_190677 baseEnd_190677 := by
    simpa [prefixWord, tailWord_190677, baseEnd_190677] using wordTrace_append hprefix tailTrace_190677
  have hstable : (prefixWord ++ tailWord_190677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190677).length < 2 ^ (prefixWord ++ tailWord_190677).sum := by decide
  have hdescent : baseEnd_190677 < baseStart_190677 := by decide
  rcases family_descends (prefixWord ++ tailWord_190677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190692 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 6]
def baseStart_190692 : Nat := 118140960795 + 190692 * 2 ^ 59
def prefixEnd_190692 : Nat := 4983230072969 + 3 ^ 40 * 190692 * 2
def baseEnd_190692 : Nat := 87037024859798355887137

theorem tailTrace_190692 : CollatzResearch.WordTrace tailWord_190692 prefixEnd_190692 87037024859798355887137 := by
  unfold tailWord_190692
  simp only [CollatzResearch.WordTrace]
  refine ⟨3477554312581463222935165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4636739083441950963913553 3477554312581463222935165)
  ·
    refine ⟨1304082867218048708600687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3477554312581463222935165 1304082867218048708600687)
    ·
      refine ⟨1956124300827073062901031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1304082867218048708600687 1956124300827073062901031)
      ·
        refine ⟨2934186451240609594351547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1956124300827073062901031 2934186451240609594351547)
        ·
          refine ⟨4401279676860914391527321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2934186451240609594351547 4401279676860914391527321)
          ·
            refine ⟨3300959757645685793645491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4401279676860914391527321 3300959757645685793645491)
            ·
              refine ⟨4951439636468528690468237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3300959757645685793645491 4951439636468528690468237)
              ·
                refine ⟨1856789863675698258925589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4951439636468528690468237 1856789863675698258925589)
                ·
                  refine ⟨87037024859798355887137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1856789863675698258925589 87037024859798355887137)
                  ·
                    rfl

theorem cell20_190692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_190692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190692 prefixEnd_190692 := by exact prefixLift 190692
  have htrace : WordTrace (prefixWord ++ tailWord_190692) baseStart_190692 baseEnd_190692 := by
    simpa [prefixWord, tailWord_190692, baseEnd_190692] using wordTrace_append hprefix tailTrace_190692
  have hstable : (prefixWord ++ tailWord_190692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190692).length < 2 ^ (prefixWord ++ tailWord_190692).sum := by decide
  have hdescent : baseEnd_190692 < baseStart_190692 := by decide
  rcases family_descends (prefixWord ++ tailWord_190692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190699 : List Nat := [1, 1, 1, 1, 2, 5, 1, 8]
def baseStart_190699 : Nat := 118140960795 + 190699 * 2 ^ 59
def prefixEnd_190699 : Nat := 4983230072969 + 3 ^ 40 * 190699 * 2
def baseEnd_190699 : Nat := 29013406616845814217925

theorem tailTrace_190699 : CollatzResearch.WordTrace tailWord_190699 prefixEnd_190699 29013406616845814217925 := by
  unfold tailWord_190699
  simp only [CollatzResearch.WordTrace]
  refine ⟨6955363936137566641375151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4636909290758377760916767 6955363936137566641375151)
  ·
    refine ⟨10433045904206349962062727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6955363936137566641375151 10433045904206349962062727)
    ·
      refine ⟨15649568856309524943094091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10433045904206349962062727 15649568856309524943094091)
      ·
        refine ⟨23474353284464287414641137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15649568856309524943094091 23474353284464287414641137)
        ·
          refine ⟨17605764963348215560980853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23474353284464287414641137 17605764963348215560980853)
          ·
            refine ⟨1650540465313895208841955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17605764963348215560980853 1650540465313895208841955)
            ·
              refine ⟨2475810697970842813262933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1650540465313895208841955 2475810697970842813262933)
              ·
                refine ⟨29013406616845814217925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2475810697970842813262933 29013406616845814217925)
                ·
                  rfl

theorem cell20_190699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 8].length) (baseStart_190699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190699 prefixEnd_190699 := by exact prefixLift 190699
  have htrace : WordTrace (prefixWord ++ tailWord_190699) baseStart_190699 baseEnd_190699 := by
    simpa [prefixWord, tailWord_190699, baseEnd_190699] using wordTrace_append hprefix tailTrace_190699
  have hstable : (prefixWord ++ tailWord_190699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190699).length < 2 ^ (prefixWord ++ tailWord_190699).sum := by decide
  have hdescent : baseEnd_190699 < baseStart_190699 := by decide
  rcases family_descends (prefixWord ++ tailWord_190699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190722 : List Nat := [3, 4, 1, 1, 2, 1, 4, 2, 2]
def baseStart_190722 : Nat := 118140960795 + 190722 * 2 ^ 59
def prefixEnd_190722 : Nat := 4983230072969 + 3 ^ 40 * 190722 * 2
def baseEnd_190722 : Nat := 87050717677251584887015

theorem tailTrace_190722 : CollatzResearch.WordTrace tailWord_190722 prefixEnd_190722 87050717677251584887015 := by
  unfold tailWord_190722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1739050703763560392365605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4637468543369494379641613 1739050703763560392365605)
  ·
    refine ⟨326072006955667573568551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1739050703763560392365605 326072006955667573568551)
    ·
      refine ⟨489108010433501360352827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326072006955667573568551 489108010433501360352827)
      ·
        refine ⟨733662015650252040529241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489108010433501360352827 733662015650252040529241)
        ·
          refine ⟨550246511737689030396931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 733662015650252040529241 550246511737689030396931)
          ·
            refine ⟨825369767606533545595397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550246511737689030396931 825369767606533545595397)
            ·
              refine ⟨154756831426225039799137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 825369767606533545595397 154756831426225039799137)
              ·
                refine ⟨116067623569668779849353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154756831426225039799137 116067623569668779849353)
                ·
                  refine ⟨87050717677251584887015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116067623569668779849353 87050717677251584887015)
                  ·
                    rfl

theorem cell20_190722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_190722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190722 prefixEnd_190722 := by exact prefixLift 190722
  have htrace : WordTrace (prefixWord ++ tailWord_190722) baseStart_190722 baseEnd_190722 := by
    simpa [prefixWord, tailWord_190722, baseEnd_190722] using wordTrace_append hprefix tailTrace_190722
  have hstable : (prefixWord ++ tailWord_190722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190722).length < 2 ^ (prefixWord ++ tailWord_190722).sum := by decide
  have hdescent : baseEnd_190722 < baseStart_190722 := by decide
  rcases family_descends (prefixWord ++ tailWord_190722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190778 : List Nat := [3, 1, 1, 1, 4, 2, 3, 2, 3]
def baseStart_190778 : Nat := 118140960795 + 190778 * 2 ^ 59
def prefixEnd_190778 : Nat := 4983230072969 + 3 ^ 40 * 190778 * 2
def baseEnd_190778 : Nat := 87076277603164279020119

theorem tailTrace_190778 : CollatzResearch.WordTrace tailWord_190778 prefixEnd_190778 87076277603164279020119 := by
  unfold tailWord_190778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1739561325712840783375247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4638830201900908755667325 1739561325712840783375247)
  ·
    refine ⟨2609341988569261175062871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1739561325712840783375247 2609341988569261175062871)
    ·
      refine ⟨3914012982853891762594307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2609341988569261175062871 3914012982853891762594307)
      ·
        refine ⟨5871019474280837643891461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3914012982853891762594307 5871019474280837643891461)
        ·
          refine ⟨1100816151427657058229649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5871019474280837643891461 1100816151427657058229649)
          ·
            refine ⟨825612113570742793672237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1100816151427657058229649 825612113570742793672237)
            ·
              refine ⟨309604542589028547627089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 825612113570742793672237 309604542589028547627089)
              ·
                refine ⟨232203406941771410720317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309604542589028547627089 232203406941771410720317)
                ·
                  refine ⟨87076277603164279020119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232203406941771410720317 87076277603164279020119)
                  ·
                    rfl

theorem cell20_190778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_190778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190778 prefixEnd_190778 := by exact prefixLift 190778
  have htrace : WordTrace (prefixWord ++ tailWord_190778) baseStart_190778 baseEnd_190778 := by
    simpa [prefixWord, tailWord_190778, baseEnd_190778] using wordTrace_append hprefix tailTrace_190778
  have hstable : (prefixWord ++ tailWord_190778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190778).length < 2 ^ (prefixWord ++ tailWord_190778).sum := by decide
  have hdescent : baseEnd_190778 < baseStart_190778 := by decide
  rcases family_descends (prefixWord ++ tailWord_190778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190844 : List Nat := [2, 2, 2, 1, 1, 1, 2, 5, 4]
def baseStart_190844 : Nat := 118140960795 + 190844 * 2 ^ 59
def prefixEnd_190844 : Nat := 4983230072969 + 3 ^ 40 * 190844 * 2
def baseEnd_190844 : Nat := 87106401801561382819849

theorem tailTrace_190844 : CollatzResearch.WordTrace tailWord_190844 prefixEnd_190844 87106401801561382819849 := by
  unfold tailWord_190844
  simp only [CollatzResearch.WordTrace]
  refine ⟨3480326260306128202701793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4640435013741504270269057 3480326260306128202701793)
  ·
    refine ⟨2610244695229596152026345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3480326260306128202701793 2610244695229596152026345)
    ·
      refine ⟨1957683521422197114019759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2610244695229596152026345 1957683521422197114019759)
      ·
        refine ⟨2936525282133295671029639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1957683521422197114019759 2936525282133295671029639)
        ·
          refine ⟨4404787923199943506544459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2936525282133295671029639 4404787923199943506544459)
          ·
            refine ⟨6607181884799915259816689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4404787923199943506544459 6607181884799915259816689)
            ·
              refine ⟨4955386413599936444862517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6607181884799915259816689 4955386413599936444862517)
              ·
                refine ⟨464567476274994041705861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4955386413599936444862517 464567476274994041705861)
                ·
                  refine ⟨87106401801561382819849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 464567476274994041705861 87106401801561382819849)
                  ·
                    rfl

theorem cell20_190844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_190844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190844 prefixEnd_190844 := by exact prefixLift 190844
  have htrace : WordTrace (prefixWord ++ tailWord_190844) baseStart_190844 baseEnd_190844 := by
    simpa [prefixWord, tailWord_190844, baseEnd_190844] using wordTrace_append hprefix tailTrace_190844
  have hstable : (prefixWord ++ tailWord_190844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190844).length < 2 ^ (prefixWord ++ tailWord_190844).sum := by decide
  have hdescent : baseEnd_190844 < baseStart_190844 := by decide
  rcases family_descends (prefixWord ++ tailWord_190844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190850 : List Nat := [3, 4, 2, 1, 2, 1, 1, 3, 3]
def baseStart_190850 : Nat := 118140960795 + 190850 * 2 ^ 59
def prefixEnd_190850 : Nat := 4983230072969 + 3 ^ 40 * 190850 * 2
def baseEnd_190850 : Nat := 87109140365052028619825

theorem tailTrace_190850 : CollatzResearch.WordTrace tailWord_190850 prefixEnd_190850 87109140365052028619825 := by
  unfold tailWord_190850
  simp only [CollatzResearch.WordTrace]
  refine ⟨1740217839647629857530501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4640580905727012953414669 1740217839647629857530501)
  ·
    refine ⟨326290844933930598286969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1740217839647629857530501 326290844933930598286969)
    ·
      refine ⟨244718133700447948715227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326290844933930598286969 244718133700447948715227)
      ·
        refine ⟨367077200550671923072841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244718133700447948715227 367077200550671923072841)
        ·
          refine ⟨275307900413003942304631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367077200550671923072841 275307900413003942304631)
          ·
            refine ⟨412961850619505913456947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275307900413003942304631 412961850619505913456947)
            ·
              refine ⟨619442775929258870185421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412961850619505913456947 619442775929258870185421)
              ·
                refine ⟨232291040973472076319533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 619442775929258870185421 232291040973472076319533)
                ·
                  refine ⟨87109140365052028619825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232291040973472076319533 87109140365052028619825)
                  ·
                    rfl

theorem cell20_190850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_190850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190850 prefixEnd_190850 := by exact prefixLift 190850
  have htrace : WordTrace (prefixWord ++ tailWord_190850) baseStart_190850 baseEnd_190850 := by
    simpa [prefixWord, tailWord_190850, baseEnd_190850] using wordTrace_append hprefix tailTrace_190850
  have hstable : (prefixWord ++ tailWord_190850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190850).length < 2 ^ (prefixWord ++ tailWord_190850).sum := by decide
  have hdescent : baseEnd_190850 < baseStart_190850 := by decide
  rcases family_descends (prefixWord ++ tailWord_190850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190896 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 9]
def baseStart_190896 : Nat := 118140960795 + 190896 * 2 ^ 59
def prefixEnd_190896 : Nat := 4983230072969 + 3 ^ 40 * 190896 * 2
def baseEnd_190896 : Nat := 87130136018480313086303

theorem tailTrace_190896 : CollatzResearch.WordTrace tailWord_190896 prefixEnd_190896 87130136018480313086303 := by
  unfold tailWord_190896
  simp only [CollatzResearch.WordTrace]
  refine ⟨3481274558211934643148271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4641699410949246190864361 3481274558211934643148271)
  ·
    refine ⟨5221911837317901964722407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3481274558211934643148271 5221911837317901964722407)
    ·
      refine ⟨7832867755976852947083611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5221911837317901964722407 7832867755976852947083611)
      ·
        refine ⟨11749301633965279420625417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7832867755976852947083611 11749301633965279420625417)
        ·
          refine ⟨8811976225473959565469063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11749301633965279420625417 8811976225473959565469063)
          ·
            refine ⟨13217964338210939348203595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8811976225473959565469063 13217964338210939348203595)
            ·
              refine ⟨19826946507316409022305393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13217964338210939348203595 19826946507316409022305393)
              ·
                refine ⟨14870209880487306766729045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19826946507316409022305393 14870209880487306766729045)
                ·
                  refine ⟨87130136018480313086303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14870209880487306766729045 87130136018480313086303)
                  ·
                    rfl

theorem cell20_190896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_190896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190896 prefixEnd_190896 := by exact prefixLift 190896
  have htrace : WordTrace (prefixWord ++ tailWord_190896) baseStart_190896 baseEnd_190896 := by
    simpa [prefixWord, tailWord_190896, baseEnd_190896] using wordTrace_append hprefix tailTrace_190896
  have hstable : (prefixWord ++ tailWord_190896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190896).length < 2 ^ (prefixWord ++ tailWord_190896).sum := by decide
  have hdescent : baseEnd_190896 < baseStart_190896 := by decide
  rcases family_descends (prefixWord ++ tailWord_190896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190916 : List Nat := [2, 3, 3, 2, 2, 1, 1, 2, 4]
def baseStart_190916 : Nat := 118140960795 + 190916 * 2 ^ 59
def prefixEnd_190916 : Nat := 4983230072969 + 3 ^ 40 * 190916 * 2
def baseEnd_190916 : Nat := 87139264563449132419555

theorem tailTrace_190916 : CollatzResearch.WordTrace tailWord_190916 prefixEnd_190916 87139264563449132419555 := by
  unfold tailWord_190916
  simp only [CollatzResearch.WordTrace]
  refine ⟨3481639288175706351012301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4642185717567608468016401 3481639288175706351012301)
  ·
    refine ⟨1305614733065889881629613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3481639288175706351012301 1305614733065889881629613)
    ·
      refine ⟨489605524899708705611105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1305614733065889881629613 489605524899708705611105)
      ·
        refine ⟨367204143674781529208329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489605524899708705611105 367204143674781529208329)
        ·
          refine ⟨275403107756086146906247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367204143674781529208329 275403107756086146906247)
          ·
            refine ⟨413104661634129220359371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275403107756086146906247 413104661634129220359371)
            ·
              refine ⟨619656992451193830539057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413104661634129220359371 619656992451193830539057)
              ·
                refine ⟨464742744338395372904293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 619656992451193830539057 464742744338395372904293)
                ·
                  refine ⟨87139264563449132419555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 464742744338395372904293 87139264563449132419555)
                  ·
                    rfl

theorem cell20_190916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_190916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190916 prefixEnd_190916 := by exact prefixLift 190916
  have htrace : WordTrace (prefixWord ++ tailWord_190916) baseStart_190916 baseEnd_190916 := by
    simpa [prefixWord, tailWord_190916, baseEnd_190916] using wordTrace_append hprefix tailTrace_190916
  have hstable : (prefixWord ++ tailWord_190916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190916).length < 2 ^ (prefixWord ++ tailWord_190916).sum := by decide
  have hdescent : baseEnd_190916 < baseStart_190916 := by decide
  rcases family_descends (prefixWord ++ tailWord_190916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190920 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 6]
def baseStart_190920 : Nat := 118140960795 + 190920 * 2 ^ 59
def prefixEnd_190920 : Nat := 4983230072969 + 3 ^ 40 * 190920 * 2
def baseEnd_190920 : Nat := 87141090272442896286205

theorem tailTrace_190920 : CollatzResearch.WordTrace tailWord_190920 prefixEnd_190920 87141090272442896286205 := by
  unfold tailWord_190920
  simp only [CollatzResearch.WordTrace]
  refine ⟨3481712234168460692585107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4642282978891280923446809 3481712234168460692585107)
  ·
    refine ⟨5222568351252691038877661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3481712234168460692585107 5222568351252691038877661)
    ·
      refine ⟨1958463131719759139579123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5222568351252691038877661 1958463131719759139579123)
      ·
        refine ⟨2937694697579638709368685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1958463131719759139579123 2937694697579638709368685)
        ·
          refine ⟨1101635511592364516013257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2937694697579638709368685 1101635511592364516013257)
          ·
            refine ⟨826226633694273387009943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1101635511592364516013257 826226633694273387009943)
            ·
              refine ⟨1239339950541410080514915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826226633694273387009943 1239339950541410080514915)
              ·
                refine ⟨1859009925812115120772373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1239339950541410080514915 1859009925812115120772373)
                ·
                  refine ⟨87141090272442896286205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1859009925812115120772373 87141090272442896286205)
                  ·
                    rfl

theorem cell20_190920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_190920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190920 prefixEnd_190920 := by exact prefixLift 190920
  have htrace : WordTrace (prefixWord ++ tailWord_190920) baseStart_190920 baseEnd_190920 := by
    simpa [prefixWord, tailWord_190920, baseEnd_190920] using wordTrace_append hprefix tailTrace_190920
  have hstable : (prefixWord ++ tailWord_190920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190920).length < 2 ^ (prefixWord ++ tailWord_190920).sum := by decide
  have hdescent : baseEnd_190920 < baseStart_190920 := by decide
  rcases family_descends (prefixWord ++ tailWord_190920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190947 : List Nat := [1, 1, 1, 6, 3, 2, 1, 2, 3]
def baseStart_190947 : Nat := 118140960795 + 190947 * 2 ^ 59
def prefixEnd_190947 : Nat := 4983230072969 + 3 ^ 40 * 190947 * 2
def baseEnd_190947 : Nat := 87153413808150802386095

theorem tailTrace_190947 : CollatzResearch.WordTrace tailWord_190947 prefixEnd_190947 87153413808150802386095 := by
  unfold tailWord_190947
  simp only [CollatzResearch.WordTrace]
  refine ⟨6964409239239104996403095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4642939492826069997602063 6964409239239104996403095)
  ·
    refine ⟨10446613858858657494604643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6964409239239104996403095 10446613858858657494604643)
    ·
      refine ⟨15669920788287986241906965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10446613858858657494604643 15669920788287986241906965)
      ·
        refine ⟨734527536950999355089389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15669920788287986241906965 734527536950999355089389)
        ·
          refine ⟨275447826356624758158521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 734527536950999355089389 275447826356624758158521)
          ·
            refine ⟨206585869767468568618891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275447826356624758158521 206585869767468568618891)
            ·
              refine ⟨309878804651202852928337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206585869767468568618891 309878804651202852928337)
              ·
                refine ⟨232409103488402139696253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309878804651202852928337 232409103488402139696253)
                ·
                  refine ⟨87153413808150802386095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232409103488402139696253 87153413808150802386095)
                  ·
                    rfl

theorem cell20_190947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 3].length) (baseStart_190947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190947 prefixEnd_190947 := by exact prefixLift 190947
  have htrace : WordTrace (prefixWord ++ tailWord_190947) baseStart_190947 baseEnd_190947 := by
    simpa [prefixWord, tailWord_190947, baseEnd_190947] using wordTrace_append hprefix tailTrace_190947
  have hstable : (prefixWord ++ tailWord_190947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190947).length < 2 ^ (prefixWord ++ tailWord_190947).sum := by decide
  have hdescent : baseEnd_190947 < baseStart_190947 := by decide
  rcases family_descends (prefixWord ++ tailWord_190947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190951 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 5]
def baseStart_190951 : Nat := 118140960795 + 190951 * 2 ^ 59
def prefixEnd_190951 : Nat := 4983230072969 + 3 ^ 40 * 190951 * 2
def baseEnd_190951 : Nat := 87155239517144566252745

theorem tailTrace_190951 : CollatzResearch.WordTrace tailWord_190951 prefixEnd_190951 87155239517144566252745 := by
  unfold tailWord_190951
  simp only [CollatzResearch.WordTrace]
  refine ⟨6964555131224613679548707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4643036754149742453032471 6964555131224613679548707)
  ·
    refine ⟨10446832696836920519323061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6964555131224613679548707 10446832696836920519323061)
    ·
      refine ⟨979390565328461298686537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10446832696836920519323061 979390565328461298686537)
      ·
        refine ⟨734542923996345974014903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 979390565328461298686537 734542923996345974014903)
        ·
          refine ⟨1101814385994518961022355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734542923996345974014903 1101814385994518961022355)
          ·
            refine ⟨1652721578991778441533533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101814385994518961022355 1652721578991778441533533)
            ·
              refine ⟨619770592121916915575075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1652721578991778441533533 619770592121916915575075)
              ·
                refine ⟨929655888182875373362613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 619770592121916915575075 929655888182875373362613)
                ·
                  refine ⟨87155239517144566252745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 929655888182875373362613 87155239517144566252745)
                  ·
                    rfl

theorem cell20_190951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_190951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190951 prefixEnd_190951 := by exact prefixLift 190951
  have htrace : WordTrace (prefixWord ++ tailWord_190951) baseStart_190951 baseEnd_190951 := by
    simpa [prefixWord, tailWord_190951, baseEnd_190951] using wordTrace_append hprefix tailTrace_190951
  have hstable : (prefixWord ++ tailWord_190951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190951).length < 2 ^ (prefixWord ++ tailWord_190951).sum := by decide
  have hdescent : baseEnd_190951 < baseStart_190951 := by decide
  rcases family_descends (prefixWord ++ tailWord_190951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190954 : List Nat := [3, 1, 3, 1, 3, 1, 2, 4, 2]
def baseStart_190954 : Nat := 118140960795 + 190954 * 2 ^ 59
def prefixEnd_190954 : Nat := 4983230072969 + 3 ^ 40 * 190954 * 2
def baseEnd_190954 : Nat := 87156608798889889152733

theorem tailTrace_190954 : CollatzResearch.WordTrace tailWord_190954 prefixEnd_190954 87156608798889889152733 := by
  unfold tailWord_190954
  simp only [CollatzResearch.WordTrace]
  refine ⟨1741166137553436297976979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4643109700142496794605277 1741166137553436297976979)
  ·
    refine ⟨2611749206330154446965469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1741166137553436297976979 2611749206330154446965469)
    ·
      refine ⟨979405952373807917612051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2611749206330154446965469 979405952373807917612051)
      ·
        refine ⟨1469108928560711876418077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 979405952373807917612051 1469108928560711876418077)
        ·
          refine ⟨550915848210266953656779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1469108928560711876418077 550915848210266953656779)
          ·
            refine ⟨826373772315400430485169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550915848210266953656779 826373772315400430485169)
            ·
              refine ⟨619780329236550322863877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 826373772315400430485169 619780329236550322863877)
              ·
                refine ⟨116208811731853185536977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 619780329236550322863877 116208811731853185536977)
                ·
                  refine ⟨87156608798889889152733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116208811731853185536977 87156608798889889152733)
                  ·
                    rfl

theorem cell20_190954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_190954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190954 prefixEnd_190954 := by exact prefixLift 190954
  have htrace : WordTrace (prefixWord ++ tailWord_190954) baseStart_190954 baseEnd_190954 := by
    simpa [prefixWord, tailWord_190954, baseEnd_190954] using wordTrace_append hprefix tailTrace_190954
  have hstable : (prefixWord ++ tailWord_190954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190954).length < 2 ^ (prefixWord ++ tailWord_190954).sum := by decide
  have hdescent : baseEnd_190954 < baseStart_190954 := by decide
  rcases family_descends (prefixWord ++ tailWord_190954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190968 : List Nat := [2, 1, 2, 1, 1, 4, 5, 1, 3]
def baseStart_190968 : Nat := 118140960795 + 190968 * 2 ^ 59
def prefixEnd_190968 : Nat := 4983230072969 + 3 ^ 40 * 190968 * 2
def baseEnd_190968 : Nat := 87162998780368062686009

theorem tailTrace_190968 : CollatzResearch.WordTrace tailWord_190968 prefixEnd_190968 87162998780368062686009 := by
  unfold tailWord_190968
  simp only [CollatzResearch.WordTrace]
  refine ⟨3482587586081512791458779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4643450114775350388611705 3482587586081512791458779)
  ·
    refine ⟨5223881379122269187188169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3482587586081512791458779 5223881379122269187188169)
    ·
      refine ⟨3917911034341701890391127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5223881379122269187188169 3917911034341701890391127)
      ·
        refine ⟨5876866551512552835586691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3917911034341701890391127 5876866551512552835586691)
        ·
          refine ⟨8815299827268829253380037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5876866551512552835586691 8815299827268829253380037)
          ·
            refine ⟨1652868717612905485008757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8815299827268829253380037 1652868717612905485008757)
            ·
              refine ⟨154956442276209889219571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1652868717612905485008757 154956442276209889219571)
              ·
                refine ⟨232434663414314833829357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154956442276209889219571 232434663414314833829357)
                ·
                  refine ⟨87162998780368062686009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232434663414314833829357 87162998780368062686009)
                  ·
                    rfl

theorem cell20_190968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 3].length) (baseStart_190968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190968 prefixEnd_190968 := by exact prefixLift 190968
  have htrace : WordTrace (prefixWord ++ tailWord_190968) baseStart_190968 baseEnd_190968 := by
    simpa [prefixWord, tailWord_190968, baseEnd_190968] using wordTrace_append hprefix tailTrace_190968
  have hstable : (prefixWord ++ tailWord_190968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190968).length < 2 ^ (prefixWord ++ tailWord_190968).sum := by decide
  have hdescent : baseEnd_190968 < baseStart_190968 := by decide
  rcases family_descends (prefixWord ++ tailWord_190968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190999 : List Nat := [1, 1, 3, 6, 1, 2, 6]
def baseStart_190999 : Nat := 118140960795 + 190999 * 2 ^ 59
def prefixEnd_190999 : Nat := 4983230072969 + 3 ^ 40 * 190999 * 2
def baseEnd_190999 : Nat := 9686349780563303628061

theorem tailTrace_190999 : CollatzResearch.WordTrace tailWord_190999 prefixEnd_190999 9686349780563303628061 := by
  unfold tailWord_190999
  simp only [CollatzResearch.WordTrace]
  refine ⟨6966305835050717877296051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4644203890033811918197367 6966305835050717877296051)
  ·
    refine ⟨10449458752576076815944077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6966305835050717877296051 10449458752576076815944077)
    ·
      refine ⟨3918547032216028805979029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10449458752576076815944077 3918547032216028805979029)
      ·
        refine ⟨183681892135126350280267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3918547032216028805979029 183681892135126350280267)
        ·
          refine ⟨275522838202689525420401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183681892135126350280267 275522838202689525420401)
          ·
            refine ⟨206642128652017144065301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275522838202689525420401 206642128652017144065301)
            ·
              refine ⟨9686349780563303628061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 206642128652017144065301 9686349780563303628061)
              ·
                rfl

theorem cell20_190999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 6].length) (baseStart_190999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_190999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_190999 prefixEnd_190999 := by exact prefixLift 190999
  have htrace : WordTrace (prefixWord ++ tailWord_190999) baseStart_190999 baseEnd_190999 := by
    simpa [prefixWord, tailWord_190999, baseEnd_190999] using wordTrace_append hprefix tailTrace_190999
  have hstable : (prefixWord ++ tailWord_190999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190999).length < 2 ^ (prefixWord ++ tailWord_190999).sum := by decide
  have hdescent : baseEnd_190999 < baseStart_190999 := by decide
  rcases family_descends (prefixWord ++ tailWord_190999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191013 : List Nat := [1, 3, 1, 2, 2, 1, 2, 6, 2]
def baseStart_191013 : Nat := 118140960795 + 191013 * 2 ^ 59
def prefixEnd_191013 : Nat := 4983230072969 + 3 ^ 40 * 191013 * 2
def baseEnd_191013 : Nat := 87183538006547906185825

theorem tailTrace_191013 : CollatzResearch.WordTrace tailWord_191013 prefixEnd_191013 87183538006547906185825 := by
  unfold tailWord_191013
  simp only [CollatzResearch.WordTrace]
  refine ⟨6966816456999998268305693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4644544304666665512203795 6966816456999998268305693)
  ·
    refine ⟨2612556171374999350614635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6966816456999998268305693 2612556171374999350614635)
    ·
      refine ⟨3918834257062499025921953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2612556171374999350614635 3918834257062499025921953)
      ·
        refine ⟨2939125692796874269441465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3918834257062499025921953 2939125692796874269441465)
        ·
          refine ⟨2204344269597655702081099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2939125692796874269441465 2204344269597655702081099)
          ·
            refine ⟨3306516404396483553121649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2204344269597655702081099 3306516404396483553121649)
            ·
              refine ⟨2479887303297362664841237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3306516404396483553121649 2479887303297362664841237)
              ·
                refine ⟨116244717342063874914433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2479887303297362664841237 116244717342063874914433)
                ·
                  refine ⟨87183538006547906185825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116244717342063874914433 87183538006547906185825)
                  ·
                    rfl

theorem cell20_191013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_191013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191013 prefixEnd_191013 := by exact prefixLift 191013
  have htrace : WordTrace (prefixWord ++ tailWord_191013) baseStart_191013 baseEnd_191013 := by
    simpa [prefixWord, tailWord_191013, baseEnd_191013] using wordTrace_append hprefix tailTrace_191013
  have hstable : (prefixWord ++ tailWord_191013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191013).length < 2 ^ (prefixWord ++ tailWord_191013).sum := by decide
  have hdescent : baseEnd_191013 < baseStart_191013 := by decide
  rcases family_descends (prefixWord ++ tailWord_191013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191027 : List Nat := [1, 1, 1, 2, 4, 2, 3, 3, 3]
def baseStart_191027 : Nat := 118140960795 + 191027 * 2 ^ 59
def prefixEnd_191027 : Nat := 4983230072969 + 3 ^ 40 * 191027 * 2
def baseEnd_191027 : Nat := 87189927988026079719101

theorem tailTrace_191027 : CollatzResearch.WordTrace tailWord_191027 prefixEnd_191027 87189927988026079719101 := by
  unfold tailWord_191027
  simp only [CollatzResearch.WordTrace]
  refine ⟨6967327078949278659315335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4644884719299519106210223 6967327078949278659315335)
  ·
    refine ⟨10450990618423917988973003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6967327078949278659315335 10450990618423917988973003)
    ·
      refine ⟨15676485927635876983459505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10450990618423917988973003 15676485927635876983459505)
      ·
        refine ⟨11757364445726907737594629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15676485927635876983459505 11757364445726907737594629)
        ·
          refine ⟨2204505833573795200798993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11757364445726907737594629 2204505833573795200798993)
          ·
            refine ⟨1653379375180346400599245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2204505833573795200798993 1653379375180346400599245)
            ·
              refine ⟨620017265692629900224717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1653379375180346400599245 620017265692629900224717)
              ·
                refine ⟨232506474634736212584269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 620017265692629900224717 232506474634736212584269)
                ·
                  refine ⟨87189927988026079719101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232506474634736212584269 87189927988026079719101)
                  ·
                    rfl

theorem cell20_191027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 3].length) (baseStart_191027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191027 prefixEnd_191027 := by exact prefixLift 191027
  have htrace : WordTrace (prefixWord ++ tailWord_191027) baseStart_191027 baseEnd_191027 := by
    simpa [prefixWord, tailWord_191027, baseEnd_191027] using wordTrace_append hprefix tailTrace_191027
  have hstable : (prefixWord ++ tailWord_191027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191027).length < 2 ^ (prefixWord ++ tailWord_191027).sum := by decide
  have hdescent : baseEnd_191027 < baseStart_191027 := by decide
  rcases family_descends (prefixWord ++ tailWord_191027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191048 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 7]
def baseStart_191048 : Nat := 118140960795 + 191048 * 2 ^ 59
def prefixEnd_191048 : Nat := 4983230072969 + 3 ^ 40 * 191048 * 2
def baseEnd_191048 : Nat := 87199512960243340019015

theorem tailTrace_191048 : CollatzResearch.WordTrace tailWord_191048 prefixEnd_191048 87199512960243340019015 := by
  unfold tailWord_191048
  simp only [CollatzResearch.WordTrace]
  refine ⟨3484046505936599622914899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4645395341248799497219865 3484046505936599622914899)
  ·
    refine ⟨5226069758904899434372349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3484046505936599622914899 5226069758904899434372349)
    ·
      refine ⟨1959776159589337287889631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5226069758904899434372349 1959776159589337287889631)
      ·
        refine ⟨2939664239384005931834447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1959776159589337287889631 2939664239384005931834447)
        ·
          refine ⟨4409496359076008897751671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2939664239384005931834447 4409496359076008897751671)
          ·
            refine ⟨6614244538614013346627507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4409496359076008897751671 6614244538614013346627507)
            ·
              refine ⟨9921366807921020019941261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6614244538614013346627507 9921366807921020019941261)
              ·
                refine ⟨3720512552970382507477973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9921366807921020019941261 3720512552970382507477973)
                ·
                  refine ⟨87199512960243340019015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3720512552970382507477973 87199512960243340019015)
                  ·
                    rfl

theorem cell20_191048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_191048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191048 prefixEnd_191048 := by exact prefixLift 191048
  have htrace : WordTrace (prefixWord ++ tailWord_191048) baseStart_191048 baseEnd_191048 := by
    simpa [prefixWord, tailWord_191048, baseEnd_191048] using wordTrace_append hprefix tailTrace_191048
  have hstable : (prefixWord ++ tailWord_191048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191048).length < 2 ^ (prefixWord ++ tailWord_191048).sum := by decide
  have hdescent : baseEnd_191048 < baseStart_191048 := by decide
  rcases family_descends (prefixWord ++ tailWord_191048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191127 : List Nat := [1, 1, 3, 3, 2, 1, 1, 6, 2]
def baseStart_191127 : Nat := 118140960795 + 191127 * 2 ^ 59
def prefixEnd_191127 : Nat := 4983230072969 + 3 ^ 40 * 191127 * 2
def baseEnd_191127 : Nat := 87235570712870176385359

theorem tailTrace_191127 : CollatzResearch.WordTrace tailWord_191127 prefixEnd_191127 87235570712870176385359 := by
  unfold tailWord_191127
  simp only [CollatzResearch.WordTrace]
  refine ⟨6970974378586995737955635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4647316252391330491970423 6970974378586995737955635)
  ·
    refine ⟨10456461567880493606933453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6970974378586995737955635 10456461567880493606933453)
    ·
      refine ⟨3921173087955185102600045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10456461567880493606933453 3921173087955185102600045)
      ·
        refine ⟨1470439907983194413475017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3921173087955185102600045 1470439907983194413475017)
        ·
          refine ⟨1102829930987395810106263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1470439907983194413475017 1102829930987395810106263)
          ·
            refine ⟨1654244896481093715159395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102829930987395810106263 1654244896481093715159395)
            ·
              refine ⟨2481367344721640572739093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654244896481093715159395 2481367344721640572739093)
              ·
                refine ⟨116314094283826901847145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2481367344721640572739093 116314094283826901847145)
                ·
                  refine ⟨87235570712870176385359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116314094283826901847145 87235570712870176385359)
                  ·
                    rfl

theorem cell20_191127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 2].length) (baseStart_191127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191127 prefixEnd_191127 := by exact prefixLift 191127
  have htrace : WordTrace (prefixWord ++ tailWord_191127) baseStart_191127 baseEnd_191127 := by
    simpa [prefixWord, tailWord_191127, baseEnd_191127] using wordTrace_append hprefix tailTrace_191127
  have hstable : (prefixWord ++ tailWord_191127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191127).length < 2 ^ (prefixWord ++ tailWord_191127).sum := by decide
  have hdescent : baseEnd_191127 < baseStart_191127 := by decide
  rcases family_descends (prefixWord ++ tailWord_191127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191134 : List Nat := [4, 3, 1, 1, 1, 1, 2, 7]
def baseStart_191134 : Nat := 118140960795 + 191134 * 2 ^ 59
def prefixEnd_191134 : Nat := 4983230072969 + 3 ^ 40 * 191134 * 2
def baseEnd_191134 : Nat := 29079588567869754383999

theorem tailTrace_191134 : CollatzResearch.WordTrace tailWord_191134 prefixEnd_191134 29079588567869754383999 := by
  unfold tailWord_191134
  simp only [CollatzResearch.WordTrace]
  refine ⟨871403711195204491682557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4647486459707757288973637 871403711195204491682557)
  ·
    refine ⟨326776391698201684380959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 871403711195204491682557 326776391698201684380959)
    ·
      refine ⟨490164587547302526571439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326776391698201684380959 490164587547302526571439)
      ·
        refine ⟨735246881320953789857159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490164587547302526571439 735246881320953789857159)
        ·
          refine ⟨1102870321981430684785739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735246881320953789857159 1102870321981430684785739)
          ·
            refine ⟨1654305482972146027178609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102870321981430684785739 1654305482972146027178609)
            ·
              refine ⟨1240729112229109520383957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1654305482972146027178609 1240729112229109520383957)
              ·
                refine ⟨29079588567869754383999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1240729112229109520383957 29079588567869754383999)
                ·
                  rfl

theorem cell20_191134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_191134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191134 prefixEnd_191134 := by exact prefixLift 191134
  have htrace : WordTrace (prefixWord ++ tailWord_191134) baseStart_191134 baseEnd_191134 := by
    simpa [prefixWord, tailWord_191134, baseEnd_191134] using wordTrace_append hprefix tailTrace_191134
  have hstable : (prefixWord ++ tailWord_191134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191134).length < 2 ^ (prefixWord ++ tailWord_191134).sum := by decide
  have hdescent : baseEnd_191134 < baseStart_191134 := by decide
  rcases family_descends (prefixWord ++ tailWord_191134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191137 : List Nat := [1, 2, 3, 3, 3, 1, 3, 1, 3]
def baseStart_191137 : Nat := 118140960795 + 191137 * 2 ^ 59
def prefixEnd_191137 : Nat := 4983230072969 + 3 ^ 40 * 191137 * 2
def baseEnd_191137 : Nat := 87240134985354586051985

theorem tailTrace_191137 : CollatzResearch.WordTrace tailWord_191137 prefixEnd_191137 87240134985354586051985 := by
  unfold tailWord_191137
  simp only [CollatzResearch.WordTrace]
  refine ⟨6971339108550767445819665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4647559405700511630546443 6971339108550767445819665)
  ·
    refine ⟨5228504331413075584364749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6971339108550767445819665 5228504331413075584364749)
    ·
      refine ⟨1960689124279903344136781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5228504331413075584364749 1960689124279903344136781)
      ·
        refine ⟨735258421604963754051293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1960689124279903344136781 735258421604963754051293)
        ·
          refine ⟨275721908101861407769235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 735258421604963754051293 275721908101861407769235)
          ·
            refine ⟨413582862152792111653853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275721908101861407769235 413582862152792111653853)
            ·
              refine ⟨155093573307297041870195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 413582862152792111653853 155093573307297041870195)
              ·
                refine ⟨232640359960945562805293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155093573307297041870195 232640359960945562805293)
                ·
                  refine ⟨87240134985354586051985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232640359960945562805293 87240134985354586051985)
                  ·
                    rfl

theorem cell20_191137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 3].length) (baseStart_191137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191137 prefixEnd_191137 := by exact prefixLift 191137
  have htrace : WordTrace (prefixWord ++ tailWord_191137) baseStart_191137 baseEnd_191137 := by
    simpa [prefixWord, tailWord_191137, baseEnd_191137] using wordTrace_append hprefix tailTrace_191137
  have hstable : (prefixWord ++ tailWord_191137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191137).length < 2 ^ (prefixWord ++ tailWord_191137).sum := by decide
  have hdescent : baseEnd_191137 < baseStart_191137 := by decide
  rcases family_descends (prefixWord ++ tailWord_191137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191155 : List Nat := [1, 1, 1, 2, 3, 5, 1, 6]
def baseStart_191155 : Nat := 118140960795 + 191155 * 2 ^ 59
def prefixEnd_191155 : Nat := 4983230072969 + 3 ^ 40 * 191155 * 2
def baseEnd_191155 : Nat := 29082783558608841150637

theorem tailTrace_191155 : CollatzResearch.WordTrace tailWord_191155 prefixEnd_191155 29082783558608841150637 := by
  unfold tailWord_191155
  simp only [CollatzResearch.WordTrace]
  refine ⟨6971995622485556519974919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4647997081657037679983279 6971995622485556519974919)
  ·
    refine ⟨10457993433728334779962379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6971995622485556519974919 10457993433728334779962379)
    ·
      refine ⟨15686990150592502169943569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10457993433728334779962379 15686990150592502169943569)
      ·
        refine ⟨11765242612944376627457677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15686990150592502169943569 11765242612944376627457677)
        ·
          refine ⟨4411965979854141235296629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11765242612944376627457677 4411965979854141235296629)
          ·
            refine ⟨413621810611325740809059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4411965979854141235296629 413621810611325740809059)
            ·
              refine ⟨620432715916988611213589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413621810611325740809059 620432715916988611213589)
              ·
                refine ⟨29082783558608841150637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 620432715916988611213589 29082783558608841150637)
                ·
                  rfl

theorem cell20_191155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 6].length) (baseStart_191155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191155 prefixEnd_191155 := by exact prefixLift 191155
  have htrace : WordTrace (prefixWord ++ tailWord_191155) baseStart_191155 baseEnd_191155 := by
    simpa [prefixWord, tailWord_191155, baseEnd_191155] using wordTrace_append hprefix tailTrace_191155
  have hstable : (prefixWord ++ tailWord_191155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191155).length < 2 ^ (prefixWord ++ tailWord_191155).sum := by decide
  have hdescent : baseEnd_191155 < baseStart_191155 := by decide
  rcases family_descends (prefixWord ++ tailWord_191155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191162 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_191162 : Nat := 118140960795 + 191162 * 2 ^ 59
def prefixEnd_191162 : Nat := 4983230072969 + 3 ^ 40 * 191162 * 2
def baseEnd_191162 : Nat := 87251545666565610218549

theorem tailTrace_191162 : CollatzResearch.WordTrace tailWord_191162 prefixEnd_191162 87251545666565610218549 := by
  unfold tailWord_191162
  simp only [CollatzResearch.WordTrace]
  refine ⟨1743062733365049178869935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4648167288973464476986493 1743062733365049178869935)
  ·
    refine ⟨2614594100047573768304903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1743062733365049178869935 2614594100047573768304903)
    ·
      refine ⟨3921891150071360652457355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2614594100047573768304903 3921891150071360652457355)
      ·
        refine ⟨5882836725107040978686033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3921891150071360652457355 5882836725107040978686033)
        ·
          refine ⟨4412127543830280734014525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5882836725107040978686033 4412127543830280734014525)
          ·
            refine ⟨1654547828936355275255447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4412127543830280734014525 1654547828936355275255447)
            ·
              refine ⟨2481821743404532912883171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654547828936355275255447 2481821743404532912883171)
              ·
                refine ⟨3722732615106799369324757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2481821743404532912883171 3722732615106799369324757)
                ·
                  refine ⟨87251545666565610218549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3722732615106799369324757 87251545666565610218549)
                  ·
                    rfl

theorem cell20_191162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_191162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191162 prefixEnd_191162 := by exact prefixLift 191162
  have htrace : WordTrace (prefixWord ++ tailWord_191162) baseStart_191162 baseEnd_191162 := by
    simpa [prefixWord, tailWord_191162, baseEnd_191162] using wordTrace_append hprefix tailTrace_191162
  have hstable : (prefixWord ++ tailWord_191162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191162).length < 2 ^ (prefixWord ++ tailWord_191162).sum := by decide
  have hdescent : baseEnd_191162 < baseStart_191162 := by decide
  rcases family_descends (prefixWord ++ tailWord_191162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191172 : List Nat := [2, 3, 3, 1, 1, 4, 6]
def baseStart_191172 : Nat := 118140960795 + 191172 * 2 ^ 59
def prefixEnd_191172 : Nat := 4983230072969 + 3 ^ 40 * 191172 * 2
def baseEnd_191172 : Nat := 9695123326561113320575

theorem tailTrace_191172 : CollatzResearch.WordTrace tailWord_191172 prefixEnd_191172 9695123326561113320575 := by
  unfold tailWord_191172
  simp only [CollatzResearch.WordTrace]
  refine ⟨3486307831711984211671885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4648410442282645615562513 3486307831711984211671885)
  ·
    refine ⟨1307365436891994079376957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3486307831711984211671885 1307365436891994079376957)
    ·
      refine ⟨490262038834497779766359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1307365436891994079376957 490262038834497779766359)
      ·
        refine ⟨735393058251746669649539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490262038834497779766359 735393058251746669649539)
        ·
          refine ⟨1103089587377620004474309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735393058251746669649539 1103089587377620004474309)
          ·
            refine ⟨206829297633303750838933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1103089587377620004474309 206829297633303750838933)
            ·
              refine ⟨9695123326561113320575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 206829297633303750838933 9695123326561113320575)
              ·
                rfl

theorem cell20_191172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 6].length) (baseStart_191172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191172 prefixEnd_191172 := by exact prefixLift 191172
  have htrace : WordTrace (prefixWord ++ tailWord_191172) baseStart_191172 baseEnd_191172 := by
    simpa [prefixWord, tailWord_191172, baseEnd_191172] using wordTrace_append hprefix tailTrace_191172
  have hstable : (prefixWord ++ tailWord_191172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191172).length < 2 ^ (prefixWord ++ tailWord_191172).sum := by decide
  have hdescent : baseEnd_191172 < baseStart_191172 := by decide
  rcases family_descends (prefixWord ++ tailWord_191172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191189 : List Nat := [1, 3, 2, 5, 1, 1, 2, 5]
def baseStart_191189 : Nat := 118140960795 + 191189 * 2 ^ 59
def prefixEnd_191189 : Nat := 4983230072969 + 3 ^ 40 * 191189 * 2
def baseEnd_191189 : Nat := 29087956400757838772813

theorem tailTrace_191189 : CollatzResearch.WordTrace tailWord_191189 prefixEnd_191189 29087956400757838772813 := by
  unfold tailWord_191189
  simp only [CollatzResearch.WordTrace]
  refine ⟨6973235704362380326712621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4648823802908253551141747 6973235704362380326712621)
  ·
    refine ⟨2614963389135892622517233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6973235704362380326712621 2614963389135892622517233)
    ·
      refine ⟨1961222541851919466887925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2614963389135892622517233 1961222541851919466887925)
      ·
        refine ⟨183864613298617450020743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1961222541851919466887925 183864613298617450020743)
        ·
          refine ⟨275796919947926175031115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183864613298617450020743 275796919947926175031115)
          ·
            refine ⟨413695379921889262546673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275796919947926175031115 413695379921889262546673)
            ·
              refine ⟨310271534941416946910005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413695379921889262546673 310271534941416946910005)
              ·
                refine ⟨29087956400757838772813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 310271534941416946910005 29087956400757838772813)
                ·
                  rfl

theorem cell20_191189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 5].length) (baseStart_191189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191189 prefixEnd_191189 := by exact prefixLift 191189
  have htrace : WordTrace (prefixWord ++ tailWord_191189) baseStart_191189 baseEnd_191189 := by
    simpa [prefixWord, tailWord_191189, baseEnd_191189] using wordTrace_append hprefix tailTrace_191189
  have hstable : (prefixWord ++ tailWord_191189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191189).length < 2 ^ (prefixWord ++ tailWord_191189).sum := by decide
  have hdescent : baseEnd_191189 < baseStart_191189 := by decide
  rcases family_descends (prefixWord ++ tailWord_191189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191193 : List Nat := [1, 2, 1, 2, 3, 2, 4, 5]
def baseStart_191193 : Nat := 118140960795 + 191193 * 2 ^ 59
def prefixEnd_191193 : Nat := 4983230072969 + 3 ^ 40 * 191193 * 2
def baseEnd_191193 : Nat := 29088564970422426728363

theorem tailTrace_191193 : CollatzResearch.WordTrace tailWord_191193 prefixEnd_191193 29088564970422426728363 := by
  unfold tailWord_191193
  simp only [CollatzResearch.WordTrace]
  refine ⟨6973381596347889009858233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4648921064231926006572155 6973381596347889009858233)
  ·
    refine ⟨5230036197260916757393675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6973381596347889009858233 5230036197260916757393675)
    ·
      refine ⟨7845054295891375136090513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5230036197260916757393675 7845054295891375136090513)
      ·
        refine ⟨5883790721918531352067885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7845054295891375136090513 5883790721918531352067885)
        ·
          refine ⟨2206421520719449257025457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5883790721918531352067885 2206421520719449257025457)
          ·
            refine ⟨1654816140539586942769093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2206421520719449257025457 1654816140539586942769093)
            ·
              refine ⟨310278026351172551769205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1654816140539586942769093 310278026351172551769205)
              ·
                refine ⟨29088564970422426728363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 310278026351172551769205 29088564970422426728363)
                ·
                  rfl

theorem cell20_191193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 5].length) (baseStart_191193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191193 prefixEnd_191193 := by exact prefixLift 191193
  have htrace : WordTrace (prefixWord ++ tailWord_191193) baseStart_191193 baseEnd_191193 := by
    simpa [prefixWord, tailWord_191193, baseEnd_191193] using wordTrace_append hprefix tailTrace_191193
  have hstable : (prefixWord ++ tailWord_191193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191193).length < 2 ^ (prefixWord ++ tailWord_191193).sum := by decide
  have hdescent : baseEnd_191193 < baseStart_191193 := by decide
  rcases family_descends (prefixWord ++ tailWord_191193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191234 : List Nat := [3, 4, 1, 1, 1, 2, 1, 4, 3]
def baseStart_191234 : Nat := 118140960795 + 191234 * 2 ^ 59
def prefixEnd_191234 : Nat := 4983230072969 + 3 ^ 40 * 191234 * 2
def baseEnd_191234 : Nat := 87284408428453359818255

theorem tailTrace_191234 : CollatzResearch.WordTrace tailWord_191234 prefixEnd_191234 87284408428453359818255 := by
  unfold tailWord_191234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1743719247299838253025189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4649917992799568674733837 1743719247299838253025189)
  ·
    refine ⟨326947358868719672442223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1743719247299838253025189 326947358868719672442223)
    ·
      refine ⟨490421038303079508663335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326947358868719672442223 490421038303079508663335)
      ·
        refine ⟨735631557454619262995003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490421038303079508663335 735631557454619262995003)
        ·
          refine ⟨1103447336181928894492505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735631557454619262995003 1103447336181928894492505)
          ·
            refine ⟨827585502136446670869379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1103447336181928894492505 827585502136446670869379)
            ·
              refine ⟨1241378253204670006304069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 827585502136446670869379 1241378253204670006304069)
              ·
                refine ⟨232758422475875626182013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1241378253204670006304069 232758422475875626182013)
                ·
                  refine ⟨87284408428453359818255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232758422475875626182013 87284408428453359818255)
                  ·
                    rfl

theorem cell20_191234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_191234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191234 prefixEnd_191234 := by exact prefixLift 191234
  have htrace : WordTrace (prefixWord ++ tailWord_191234) baseStart_191234 baseEnd_191234 := by
    simpa [prefixWord, tailWord_191234, baseEnd_191234] using wordTrace_append hprefix tailTrace_191234
  have hstable : (prefixWord ++ tailWord_191234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191234).length < 2 ^ (prefixWord ++ tailWord_191234).sum := by decide
  have hdescent : baseEnd_191234 < baseStart_191234 := by decide
  rcases family_descends (prefixWord ++ tailWord_191234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191276 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 5]
def baseStart_191276 : Nat := 118140960795 + 191276 * 2 ^ 59
def prefixEnd_191276 : Nat := 4983230072969 + 3 ^ 40 * 191276 * 2
def baseEnd_191276 : Nat := 87303578372887880418083

theorem tailTrace_191276 : CollatzResearch.WordTrace tailWord_191276 prefixEnd_191276 87303578372887880418083 := by
  unfold tailWord_191276
  simp only [CollatzResearch.WordTrace]
  refine ⟨3488204427523597092564841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4650939236698129456753121 3488204427523597092564841)
  ·
    refine ⟨2616153320642697819423631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3488204427523597092564841 2616153320642697819423631)
    ·
      refine ⟨3924229980964046729135447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2616153320642697819423631 3924229980964046729135447)
      ·
        refine ⟨5886344971446070093703171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3924229980964046729135447 5886344971446070093703171)
        ·
          refine ⟨8829517457169105140554757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5886344971446070093703171 8829517457169105140554757)
          ·
            refine ⟨1655534523219207213854017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8829517457169105140554757 1655534523219207213854017)
            ·
              refine ⟨1241650892414405410390513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1655534523219207213854017 1241650892414405410390513)
              ·
                refine ⟨931238169310804057792885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1241650892414405410390513 931238169310804057792885)
                ·
                  refine ⟨87303578372887880418083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 931238169310804057792885 87303578372887880418083)
                  ·
                    rfl

theorem cell20_191276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_191276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191276 prefixEnd_191276 := by exact prefixLift 191276
  have htrace : WordTrace (prefixWord ++ tailWord_191276) baseStart_191276 baseEnd_191276 := by
    simpa [prefixWord, tailWord_191276, baseEnd_191276] using wordTrace_append hprefix tailTrace_191276
  have hstable : (prefixWord ++ tailWord_191276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191276).length < 2 ^ (prefixWord ++ tailWord_191276).sum := by decide
  have hdescent : baseEnd_191276 < baseStart_191276 := by decide
  rcases family_descends (prefixWord ++ tailWord_191276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191324 : List Nat := [2, 2, 4, 2, 1, 2, 1, 6]
def baseStart_191324 : Nat := 118140960795 + 191324 * 2 ^ 59
def prefixEnd_191324 : Nat := 4983230072969 + 3 ^ 40 * 191324 * 2
def baseEnd_191324 : Nat := 29108495626937682272629

theorem tailTrace_191324 : CollatzResearch.WordTrace tailWord_191324 prefixEnd_191324 29108495626937682272629 := by
  unfold tailWord_191324
  simp only [CollatzResearch.WordTrace]
  refine ⟨3489079779436649191438513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4652106372582198921918017 3489079779436649191438513)
  ·
    refine ⟨2616809834577486893578885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3489079779436649191438513 2616809834577486893578885)
    ·
      refine ⟨490651843983278792546041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2616809834577486893578885 490651843983278792546041)
      ·
        refine ⟨367988882987459094409531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490651843983278792546041 367988882987459094409531)
        ·
          refine ⟨551983324481188641614297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367988882987459094409531 551983324481188641614297)
          ·
            refine ⟨413987493360891481210723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 551983324481188641614297 413987493360891481210723)
            ·
              refine ⟨620981240041337221816085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413987493360891481210723 620981240041337221816085)
              ·
                refine ⟨29108495626937682272629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 620981240041337221816085 29108495626937682272629)
                ·
                  rfl

theorem cell20_191324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_191324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191324 prefixEnd_191324 := by exact prefixLift 191324
  have htrace : WordTrace (prefixWord ++ tailWord_191324) baseStart_191324 baseEnd_191324 := by
    simpa [prefixWord, tailWord_191324, baseEnd_191324] using wordTrace_append hprefix tailTrace_191324
  have hstable : (prefixWord ++ tailWord_191324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191324).length < 2 ^ (prefixWord ++ tailWord_191324).sum := by decide
  have hdescent : baseEnd_191324 < baseStart_191324 := by decide
  rcases family_descends (prefixWord ++ tailWord_191324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191330 : List Nat := [3, 3, 2, 1, 4, 1, 1, 3, 2]
def baseStart_191330 : Nat := 118140960795 + 191330 * 2 ^ 59
def prefixEnd_191330 : Nat := 4983230072969 + 3 ^ 40 * 191330 * 2
def baseEnd_191330 : Nat := 87328225444303692617863

theorem tailTrace_191330 : CollatzResearch.WordTrace tailWord_191330 prefixEnd_191330 87328225444303692617863 := by
  unfold tailWord_191330
  simp only [CollatzResearch.WordTrace]
  refine ⟨1744594599212890351898861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4652252264567707605063629 1744594599212890351898861)
  ·
    refine ⟨654222974704833881962073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1744594599212890351898861 654222974704833881962073)
    ·
      refine ⟨490667231028625411471555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 654222974704833881962073 490667231028625411471555)
      ·
        refine ⟨736000846542938117207333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490667231028625411471555 736000846542938117207333)
        ·
          refine ⟨138000158726800896976375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 736000846542938117207333 138000158726800896976375)
          ·
            refine ⟨207000238090201345464563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138000158726800896976375 207000238090201345464563)
            ·
              refine ⟨310500357135302018196845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207000238090201345464563 310500357135302018196845)
              ·
                refine ⟨116437633925738256823817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310500357135302018196845 116437633925738256823817)
                ·
                  refine ⟨87328225444303692617863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116437633925738256823817 87328225444303692617863)
                  ·
                    rfl

theorem cell20_191330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_191330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191330 prefixEnd_191330 := by exact prefixLift 191330
  have htrace : WordTrace (prefixWord ++ tailWord_191330) baseStart_191330 baseEnd_191330 := by
    simpa [prefixWord, tailWord_191330, baseEnd_191330] using wordTrace_append hprefix tailTrace_191330
  have hstable : (prefixWord ++ tailWord_191330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191330).length < 2 ^ (prefixWord ++ tailWord_191330).sum := by decide
  have hdescent : baseEnd_191330 < baseStart_191330 := by decide
  rcases family_descends (prefixWord ++ tailWord_191330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191345 : List Nat := [1, 2, 2, 2, 1, 6, 6]
def baseStart_191345 : Nat := 118140960795 + 191345 * 2 ^ 59
def prefixEnd_191345 : Nat := 4983230072969 + 3 ^ 40 * 191345 * 2
def baseEnd_191345 : Nat := 9703896872558923013089

theorem tailTrace_191345 : CollatzResearch.WordTrace tailWord_191345 prefixEnd_191345 9703896872558923013089 := by
  unfold tailWord_191345
  simp only [CollatzResearch.WordTrace]
  refine ⟨6978925491797218969391489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4652616994531479312927659 6978925491797218969391489)
  ·
    refine ⟨5234194118847914227043617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6978925491797218969391489 5234194118847914227043617)
    ·
      refine ⟨3925645589135935670282713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5234194118847914227043617 3925645589135935670282713)
      ·
        refine ⟨2944234191851951752712035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3925645589135935670282713 2944234191851951752712035)
        ·
          refine ⟨4416351287777927629068053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2944234191851951752712035 4416351287777927629068053)
          ·
            refine ⟨207016466614590357612565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4416351287777927629068053 207016466614590357612565)
            ·
              refine ⟨9703896872558923013089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 207016466614590357612565 9703896872558923013089)
              ·
                rfl

theorem cell20_191345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 6].length) (baseStart_191345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191345 prefixEnd_191345 := by exact prefixLift 191345
  have htrace : WordTrace (prefixWord ++ tailWord_191345) baseStart_191345 baseEnd_191345 := by
    simpa [prefixWord, tailWord_191345, baseEnd_191345] using wordTrace_append hprefix tailTrace_191345
  have hstable : (prefixWord ++ tailWord_191345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191345).length < 2 ^ (prefixWord ++ tailWord_191345).sum := by decide
  have hdescent : baseEnd_191345 < baseStart_191345 := by decide
  rcases family_descends (prefixWord ++ tailWord_191345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191369 : List Nat := [1, 2, 1, 1, 5, 3, 1, 3, 3]
def baseStart_191369 : Nat := 118140960795 + 191369 * 2 ^ 59
def prefixEnd_191369 : Nat := 4983230072969 + 3 ^ 40 * 191369 * 2
def baseEnd_191369 : Nat := 87346026106992890317703

theorem tailTrace_191369 : CollatzResearch.WordTrace tailWord_191369 prefixEnd_191369 87346026106992890317703 := by
  unfold tailWord_191369
  simp only [CollatzResearch.WordTrace]
  refine ⟨6979800843710271068265161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4653200562473514045510107 6979800843710271068265161)
  ·
    refine ⟨5234850632782703301198871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6979800843710271068265161 5234850632782703301198871)
    ·
      refine ⟨7852275949174054951798307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5234850632782703301198871 7852275949174054951798307)
      ·
        refine ⟨11778413923761082427697461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7852275949174054951798307 11778413923761082427697461)
        ·
          refine ⟨1104226305352601477596637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11778413923761082427697461 1104226305352601477596637)
          ·
            refine ⟨414084864507225554098739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1104226305352601477596637 414084864507225554098739)
            ·
              refine ⟨621127296760838331148109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414084864507225554098739 621127296760838331148109)
              ·
                refine ⟨232922736285314374180541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 621127296760838331148109 232922736285314374180541)
                ·
                  refine ⟨87346026106992890317703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232922736285314374180541 87346026106992890317703)
                  ·
                    rfl

theorem cell20_191369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_191369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191369 prefixEnd_191369 := by exact prefixLift 191369
  have htrace : WordTrace (prefixWord ++ tailWord_191369) baseStart_191369 baseEnd_191369 := by
    simpa [prefixWord, tailWord_191369, baseEnd_191369] using wordTrace_append hprefix tailTrace_191369
  have hstable : (prefixWord ++ tailWord_191369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191369).length < 2 ^ (prefixWord ++ tailWord_191369).sum := by decide
  have hdescent : baseEnd_191369 < baseStart_191369 := by decide
  rcases family_descends (prefixWord ++ tailWord_191369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191430 : List Nat := [6, 1, 3, 1, 1, 1, 3, 4]
def baseStart_191430 : Nat := 118140960795 + 191430 * 2 ^ 59
def prefixEnd_191430 : Nat := 4983230072969 + 3 ^ 40 * 191430 * 2
def baseEnd_191430 : Nat := 29124622723049263094707

theorem tailTrace_191430 : CollatzResearch.WordTrace tailWord_191430 prefixEnd_191430 29124622723049263094707 := by
  unfold tailWord_191430
  simp only [CollatzResearch.WordTrace]
  refine ⟨218188303015289952694867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4654683797659518990823829 218188303015289952694867)
  ·
    refine ⟨327282454522934929042301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218188303015289952694867 327282454522934929042301)
    ·
      refine ⟨122730920446100598390863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327282454522934929042301 122730920446100598390863)
      ·
        refine ⟨184096380669150897586295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122730920446100598390863 184096380669150897586295)
        ·
          refine ⟨276144571003726346379443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184096380669150897586295 276144571003726346379443)
          ·
            refine ⟨414216856505589519569165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276144571003726346379443 414216856505589519569165)
            ·
              refine ⟨155331321189596069838437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 414216856505589519569165 155331321189596069838437)
              ·
                refine ⟨29124622723049263094707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155331321189596069838437 29124622723049263094707)
                ·
                  rfl

theorem cell20_191430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_191430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191430 prefixEnd_191430 := by exact prefixLift 191430
  have htrace : WordTrace (prefixWord ++ tailWord_191430) baseStart_191430 baseEnd_191430 := by
    simpa [prefixWord, tailWord_191430, baseEnd_191430] using wordTrace_append hprefix tailTrace_191430
  have hstable : (prefixWord ++ tailWord_191430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191430).length < 2 ^ (prefixWord ++ tailWord_191430).sum := by decide
  have hdescent : baseEnd_191430 < baseStart_191430 := by decide
  rcases family_descends (prefixWord ++ tailWord_191430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191435 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 6]
def baseStart_191435 : Nat := 118140960795 + 191435 * 2 ^ 59
def prefixEnd_191435 : Nat := 4983230072969 + 3 ^ 40 * 191435 * 2
def baseEnd_191435 : Nat := 87376150305389994117433

theorem tailTrace_191435 : CollatzResearch.WordTrace tailWord_191435 prefixEnd_191435 87376150305389994117433 := by
  unfold tailWord_191435
  simp only [CollatzResearch.WordTrace]
  refine ⟨6982208061471164340167759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4654805374314109560111839 6982208061471164340167759)
  ·
    refine ⟨10473312092206746510251639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6982208061471164340167759 10473312092206746510251639)
    ·
      refine ⟨15709968138310119765377459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10473312092206746510251639 15709968138310119765377459)
      ·
        refine ⟨23564952207465179648066189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15709968138310119765377459 23564952207465179648066189)
        ·
          refine ⟨8836857077799442368024821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23564952207465179648066189 8836857077799442368024821)
          ·
            refine ⟨828455351043697722002327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8836857077799442368024821 828455351043697722002327)
            ·
              refine ⟨1242683026565546583003491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828455351043697722002327 1242683026565546583003491)
              ·
                refine ⟨1864024539848319874505237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1242683026565546583003491 1864024539848319874505237)
                ·
                  refine ⟨87376150305389994117433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1864024539848319874505237 87376150305389994117433)
                  ·
                    rfl

theorem cell20_191435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_191435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191435 prefixEnd_191435 := by exact prefixLift 191435
  have htrace : WordTrace (prefixWord ++ tailWord_191435) baseStart_191435 baseEnd_191435 := by
    simpa [prefixWord, tailWord_191435, baseEnd_191435] using wordTrace_append hprefix tailTrace_191435
  have hstable : (prefixWord ++ tailWord_191435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191435).length < 2 ^ (prefixWord ++ tailWord_191435).sum := by decide
  have hdescent : baseEnd_191435 < baseStart_191435 := by decide
  rcases family_descends (prefixWord ++ tailWord_191435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191438 : List Nat := [4, 1, 1, 1, 2, 4, 3, 4]
def baseStart_191438 : Nat := 118140960795 + 191438 * 2 ^ 59
def prefixEnd_191438 : Nat := 4983230072969 + 3 ^ 40 * 191438 * 2
def baseEnd_191438 : Nat := 29125839862378439005807

theorem tailTrace_191438 : CollatzResearch.WordTrace tailWord_191438 prefixEnd_191438 29125839862378439005807 := by
  unfold tailWord_191438
  simp only [CollatzResearch.WordTrace]
  refine ⟨872789685057536981565871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4654878320306863901684645 872789685057536981565871)
  ·
    refine ⟨1309184527586305472348807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 872789685057536981565871 1309184527586305472348807)
    ·
      refine ⟨1963776791379458208523211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1309184527586305472348807 1963776791379458208523211)
      ·
        refine ⟨2945665187069187312784817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1963776791379458208523211 2945665187069187312784817)
        ·
          refine ⟨2209248890301890484588613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2945665187069187312784817 2209248890301890484588613)
          ·
            refine ⟨414234166931604465860365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2209248890301890484588613 414234166931604465860365)
            ·
              refine ⟨155337812599351674697637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 414234166931604465860365 155337812599351674697637)
              ·
                refine ⟨29125839862378439005807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155337812599351674697637 29125839862378439005807)
                ·
                  rfl

theorem cell20_191438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_191438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191438 prefixEnd_191438 := by exact prefixLift 191438
  have htrace : WordTrace (prefixWord ++ tailWord_191438) baseStart_191438 baseEnd_191438 := by
    simpa [prefixWord, tailWord_191438, baseEnd_191438] using wordTrace_append hprefix tailTrace_191438
  have hstable : (prefixWord ++ tailWord_191438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191438).length < 2 ^ (prefixWord ++ tailWord_191438).sum := by decide
  have hdescent : baseEnd_191438 < baseStart_191438 := by decide
  rcases family_descends (prefixWord ++ tailWord_191438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191480 : List Nat := [2, 1, 2, 1, 1, 3, 1, 9]
def baseStart_191480 : Nat := 118140960795 + 191480 * 2 ^ 59
def prefixEnd_191480 : Nat := 4983230072969 + 3 ^ 40 * 191480 * 2
def baseEnd_191480 : Nat := 29132229843856612539083

theorem tailTrace_191480 : CollatzResearch.WordTrace tailWord_191480 prefixEnd_191480 29132229843856612539083 := by
  unfold tailWord_191480
  simp only [CollatzResearch.WordTrace]
  refine ⟨3491924673154068512777947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4655899564205424683703929 3491924673154068512777947)
  ·
    refine ⟨5237887009731102769166921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3491924673154068512777947 5237887009731102769166921)
    ·
      refine ⟨3928415257298327076875191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5237887009731102769166921 3928415257298327076875191)
      ·
        refine ⟨5892622885947490615312787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3928415257298327076875191 5892622885947490615312787)
        ·
          refine ⟨8838934328921235922969181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5892622885947490615312787 8838934328921235922969181)
          ·
            refine ⟨3314600373345463471113443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8838934328921235922969181 3314600373345463471113443)
            ·
              refine ⟨4971900560018195206670165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3314600373345463471113443 4971900560018195206670165)
              ·
                refine ⟨29132229843856612539083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4971900560018195206670165 29132229843856612539083)
                ·
                  rfl

theorem cell20_191480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_191480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191480 prefixEnd_191480 := by exact prefixLift 191480
  have htrace : WordTrace (prefixWord ++ tailWord_191480) baseStart_191480 baseEnd_191480 := by
    simpa [prefixWord, tailWord_191480, baseEnd_191480] using wordTrace_append hprefix tailTrace_191480
  have hstable : (prefixWord ++ tailWord_191480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191480).length < 2 ^ (prefixWord ++ tailWord_191480).sum := by decide
  have hdescent : baseEnd_191480 < baseStart_191480 := by decide
  rcases family_descends (prefixWord ++ tailWord_191480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191587 : List Nat := [1, 1, 1, 5, 1, 1, 1, 5, 4]
def baseStart_191587 : Nat := 118140960795 + 191587 * 2 ^ 59
def prefixEnd_191587 : Nat := 4983230072969 + 3 ^ 40 * 191587 * 2
def baseEnd_191587 : Nat := 87445527247153021050145

theorem tailTrace_191587 : CollatzResearch.WordTrace tailWord_191587 prefixEnd_191587 87445527247153021050145 := by
  unfold tailWord_191587
  simp only [CollatzResearch.WordTrace]
  refine ⟨6987751956920494299701015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4658501304613662866467343 6987751956920494299701015)
  ·
    refine ⟨10481627935380741449551523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6987751956920494299701015 10481627935380741449551523)
    ·
      refine ⟨15722441903071112174327285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10481627935380741449551523 15722441903071112174327285)
      ·
        refine ⟨1473978928412916766343183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15722441903071112174327285 1473978928412916766343183)
        ·
          refine ⟨2210968392619375149514775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1473978928412916766343183 2210968392619375149514775)
          ·
            refine ⟨3316452588929062724272163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2210968392619375149514775 3316452588929062724272163)
            ·
              refine ⟨4974678883393594086408245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3316452588929062724272163 4974678883393594086408245)
              ·
                refine ⟨466376145318149445600773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4974678883393594086408245 466376145318149445600773)
                ·
                  refine ⟨87445527247153021050145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 466376145318149445600773 87445527247153021050145)
                  ·
                    rfl

theorem cell20_191587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_191587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191587 prefixEnd_191587 := by exact prefixLift 191587
  have htrace : WordTrace (prefixWord ++ tailWord_191587) baseStart_191587 baseEnd_191587 := by
    simpa [prefixWord, tailWord_191587, baseEnd_191587] using wordTrace_append hprefix tailTrace_191587
  have hstable : (prefixWord ++ tailWord_191587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191587).length < 2 ^ (prefixWord ++ tailWord_191587).sum := by decide
  have hdescent : baseEnd_191587 < baseStart_191587 := by decide
  rcases family_descends (prefixWord ++ tailWord_191587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191597 : List Nat := [1, 5, 1, 1, 2, 2, 2, 3, 3]
def baseStart_191597 : Nat := 118140960795 + 191597 * 2 ^ 59
def prefixEnd_191597 : Nat := 4983230072969 + 3 ^ 40 * 191597 * 2
def baseEnd_191597 : Nat := 87450091519637430716771

theorem tailTrace_191597 : CollatzResearch.WordTrace tailWord_191597 prefixEnd_191597 87450091519637430716771 := by
  unfold tailWord_191597
  simp only [CollatzResearch.WordTrace]
  refine ⟨6988116686884266007565045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4658744457922844005043363 6988116686884266007565045)
  ·
    refine ⟨655135939395399938209223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6988116686884266007565045 655135939395399938209223)
    ·
      refine ⟨982703909093099907313835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 655135939395399938209223 982703909093099907313835)
      ·
        refine ⟨1474055863639649860970753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 982703909093099907313835 1474055863639649860970753)
        ·
          refine ⟨1105541897729737395728065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1474055863639649860970753 1105541897729737395728065)
          ·
            refine ⟨829156423297303046796049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1105541897729737395728065 829156423297303046796049)
            ·
              refine ⟨621867317472977285097037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 829156423297303046796049 621867317472977285097037)
              ·
                refine ⟨233200244052366481911389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 621867317472977285097037 233200244052366481911389)
                ·
                  refine ⟨87450091519637430716771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233200244052366481911389 87450091519637430716771)
                  ·
                    rfl

theorem cell20_191597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_191597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191597 prefixEnd_191597 := by exact prefixLift 191597
  have htrace : WordTrace (prefixWord ++ tailWord_191597) baseStart_191597 baseEnd_191597 := by
    simpa [prefixWord, tailWord_191597, baseEnd_191597] using wordTrace_append hprefix tailTrace_191597
  have hstable : (prefixWord ++ tailWord_191597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191597).length < 2 ^ (prefixWord ++ tailWord_191597).sum := by decide
  have hdescent : baseEnd_191597 < baseStart_191597 := by decide
  rcases family_descends (prefixWord ++ tailWord_191597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191642 : List Nat := [3, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_191642 : Nat := 118140960795 + 191642 * 2 ^ 59
def prefixEnd_191642 : Nat := 4983230072969 + 3 ^ 40 * 191642 * 2
def baseEnd_191642 : Nat := 87470630745817274216587

theorem tailTrace_191642 : CollatzResearch.WordTrace tailWord_191642 prefixEnd_191642 87470630745817274216587 := by
  unfold tailWord_191642
  simp only [CollatzResearch.WordTrace]
  refine ⟨1747439492930309673238295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4659838647814159128635453 1747439492930309673238295)
  ·
    refine ⟨2621159239395464509857443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1747439492930309673238295 2621159239395464509857443)
    ·
      refine ⟨3931738859093196764786165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2621159239395464509857443 3931738859093196764786165)
      ·
        refine ⟨368600518039987196698703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3931738859093196764786165 368600518039987196698703)
        ·
          refine ⟨552900777059980795048055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368600518039987196698703 552900777059980795048055)
          ·
            refine ⟨829351165589971192572083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552900777059980795048055 829351165589971192572083)
            ·
              refine ⟨1244026748384956788858125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829351165589971192572083 1244026748384956788858125)
              ·
                refine ⟨466510030644358795821797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1244026748384956788858125 466510030644358795821797)
                ·
                  refine ⟨87470630745817274216587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 466510030644358795821797 87470630745817274216587)
                  ·
                    rfl

theorem cell20_191642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_191642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191642 prefixEnd_191642 := by exact prefixLift 191642
  have htrace : WordTrace (prefixWord ++ tailWord_191642) baseStart_191642 baseEnd_191642 := by
    simpa [prefixWord, tailWord_191642, baseEnd_191642] using wordTrace_append hprefix tailTrace_191642
  have hstable : (prefixWord ++ tailWord_191642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191642).length < 2 ^ (prefixWord ++ tailWord_191642).sum := by decide
  have hdescent : baseEnd_191642 < baseStart_191642 := by decide
  rcases family_descends (prefixWord ++ tailWord_191642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191652 : List Nat := [2, 3, 1, 2, 3, 2, 3, 1, 3]
def baseStart_191652 : Nat := 118140960795 + 191652 * 2 ^ 59
def prefixEnd_191652 : Nat := 4983230072969 + 3 ^ 40 * 191652 * 2
def baseEnd_191652 : Nat := 87475195018301683883213

theorem tailTrace_191652 : CollatzResearch.WordTrace tailWord_191652 prefixEnd_191652 87475195018301683883213 := by
  unfold tailWord_191652
  simp only [CollatzResearch.WordTrace]
  refine ⟨3495061350842505200408605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4660081801123340267211473 3495061350842505200408605)
  ·
    refine ⟨1310648006565939450153227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3495061350842505200408605 1310648006565939450153227)
    ·
      refine ⟨1965972009848909175229841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1310648006565939450153227 1965972009848909175229841)
      ·
        refine ⟨1474479007386681881422381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1965972009848909175229841 1474479007386681881422381)
        ·
          refine ⟨552929627770005705533393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1474479007386681881422381 552929627770005705533393)
          ·
            refine ⟨414697220827504279150045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552929627770005705533393 414697220827504279150045)
            ·
              refine ⟨155511457810314104681267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 414697220827504279150045 155511457810314104681267)
              ·
                refine ⟨233267186715471157021901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155511457810314104681267 233267186715471157021901)
                ·
                  refine ⟨87475195018301683883213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233267186715471157021901 87475195018301683883213)
                  ·
                    rfl

theorem cell20_191652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_191652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191652 prefixEnd_191652 := by exact prefixLift 191652
  have htrace : WordTrace (prefixWord ++ tailWord_191652) baseStart_191652 baseEnd_191652 := by
    simpa [prefixWord, tailWord_191652, baseEnd_191652] using wordTrace_append hprefix tailTrace_191652
  have hstable : (prefixWord ++ tailWord_191652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191652).length < 2 ^ (prefixWord ++ tailWord_191652).sum := by decide
  have hdescent : baseEnd_191652 < baseStart_191652 := by decide
  rcases family_descends (prefixWord ++ tailWord_191652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191663 : List Nat := [1, 1, 2, 1, 2, 3, 4, 2, 4]
def baseStart_191663 : Nat := 118140960795 + 191663 * 2 ^ 59
def prefixEnd_191663 : Nat := 4983230072969 + 3 ^ 40 * 191663 * 2
def baseEnd_191663 : Nat := 87480215718034534516501

theorem tailTrace_191663 : CollatzResearch.WordTrace tailWord_191663 prefixEnd_191663 87480215718034534516501 := by
  unfold tailWord_191663
  simp only [CollatzResearch.WordTrace]
  refine ⟨6990523904645159279467643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4660349269763439519645095 6990523904645159279467643)
  ·
    refine ⟨10485785856967738919201465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6990523904645159279467643 10485785856967738919201465)
    ·
      refine ⟨7864339392725804189401099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10485785856967738919201465 7864339392725804189401099)
      ·
        refine ⟨11796509089088706284101649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7864339392725804189401099 11796509089088706284101649)
        ·
          refine ⟨8847381816816529713076237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11796509089088706284101649 8847381816816529713076237)
          ·
            refine ⟨3317768181306198642403589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8847381816816529713076237 3317768181306198642403589)
            ·
              refine ⟨622081533994912245450673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3317768181306198642403589 622081533994912245450673)
              ·
                refine ⟨466561150496184184088005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622081533994912245450673 466561150496184184088005)
                ·
                  refine ⟨87480215718034534516501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 466561150496184184088005 87480215718034534516501)
                  ·
                    rfl

theorem cell20_191663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_191663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191663 prefixEnd_191663 := by exact prefixLift 191663
  have htrace : WordTrace (prefixWord ++ tailWord_191663) baseStart_191663 baseEnd_191663 := by
    simpa [prefixWord, tailWord_191663, baseEnd_191663] using wordTrace_append hprefix tailTrace_191663
  have hstable : (prefixWord ++ tailWord_191663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191663).length < 2 ^ (prefixWord ++ tailWord_191663).sum := by decide
  have hdescent : baseEnd_191663 < baseStart_191663 := by decide
  rcases family_descends (prefixWord ++ tailWord_191663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191666 : List Nat := [3, 2, 1, 1, 1, 6, 2, 4]
def baseStart_191666 : Nat := 118140960795 + 191666 * 2 ^ 59
def prefixEnd_191666 : Nat := 4983230072969 + 3 ^ 40 * 191666 * 2
def baseEnd_191666 : Nat := 29160528333259952472163

theorem tailTrace_191666 : CollatzResearch.WordTrace tailWord_191666 prefixEnd_191666 29160528333259952472163 := by
  unfold tailWord_191666
  simp only [CollatzResearch.WordTrace]
  refine ⟨1747658330908572697956713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4660422215756193861217901 1747658330908572697956713)
  ·
    refine ⟨1310743748181429523467535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1747658330908572697956713 1310743748181429523467535)
    ·
      refine ⟨1966115622272144285201303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1310743748181429523467535 1966115622272144285201303)
      ·
        refine ⟨2949173433408216427801955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1966115622272144285201303 2949173433408216427801955)
        ·
          refine ⟨4423760150112324641702933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2949173433408216427801955 4423760150112324641702933)
          ·
            refine ⟨207363757036515217579825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4423760150112324641702933 207363757036515217579825)
            ·
              refine ⟨155522817777386413184869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207363757036515217579825 155522817777386413184869)
              ·
                refine ⟨29160528333259952472163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155522817777386413184869 29160528333259952472163)
                ·
                  rfl

theorem cell20_191666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_191666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191666 prefixEnd_191666 := by exact prefixLift 191666
  have htrace : WordTrace (prefixWord ++ tailWord_191666) baseStart_191666 baseEnd_191666 := by
    simpa [prefixWord, tailWord_191666, baseEnd_191666] using wordTrace_append hprefix tailTrace_191666
  have hstable : (prefixWord ++ tailWord_191666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191666).length < 2 ^ (prefixWord ++ tailWord_191666).sum := by decide
  have hdescent : baseEnd_191666 < baseStart_191666 := by decide
  rcases family_descends (prefixWord ++ tailWord_191666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191676 : List Nat := [2, 2, 2, 3, 2, 3, 1, 3, 2]
def baseStart_191676 : Nat := 118140960795 + 191676 * 2 ^ 59
def prefixEnd_191676 : Nat := 4983230072969 + 3 ^ 40 * 191676 * 2
def baseEnd_191676 : Nat := 87486149272264267083115

theorem tailTrace_191676 : CollatzResearch.WordTrace tailWord_191676 prefixEnd_191676 87486149272264267083115 := by
  unfold tailWord_191676
  simp only [CollatzResearch.WordTrace]
  refine ⟨3495499026799031249845441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4660665369065374999793921 3495499026799031249845441)
  ·
    refine ⟨2621624270099273437384081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3495499026799031249845441 2621624270099273437384081)
    ·
      refine ⟨1966218202574455078038061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2621624270099273437384081 1966218202574455078038061)
      ·
        refine ⟨737331825965420654264273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1966218202574455078038061 737331825965420654264273)
        ·
          refine ⟨552998869474065490698205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 737331825965420654264273 552998869474065490698205)
          ·
            refine ⟨207374576052774559011827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 552998869474065490698205 207374576052774559011827)
            ·
              refine ⟨311061864079161838517741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207374576052774559011827 311061864079161838517741)
              ·
                refine ⟨116648199029685689444153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311061864079161838517741 116648199029685689444153)
                ·
                  refine ⟨87486149272264267083115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116648199029685689444153 87486149272264267083115)
                  ·
                    rfl

theorem cell20_191676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_191676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191676 prefixEnd_191676 := by exact prefixLift 191676
  have htrace : WordTrace (prefixWord ++ tailWord_191676) baseStart_191676 baseEnd_191676 := by
    simpa [prefixWord, tailWord_191676, baseEnd_191676] using wordTrace_append hprefix tailTrace_191676
  have hstable : (prefixWord ++ tailWord_191676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191676).length < 2 ^ (prefixWord ++ tailWord_191676).sum := by decide
  have hdescent : baseEnd_191676 < baseStart_191676 := by decide
  rcases family_descends (prefixWord ++ tailWord_191676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191693 : List Nat := [1, 6, 2, 2, 1, 2, 1, 1, 4]
def baseStart_191693 : Nat := 118140960795 + 191693 * 2 ^ 59
def prefixEnd_191693 : Nat := 4983230072969 + 3 ^ 40 * 191693 * 2
def baseEnd_191693 : Nat := 87493908535487763516379

theorem tailTrace_191693 : CollatzResearch.WordTrace tailWord_191693 prefixEnd_191693 87493908535487763516379 := by
  unfold tailWord_191693
  simp only [CollatzResearch.WordTrace]
  refine ⟨6991618094536474403059733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4661078729690982935373155 6991618094536474403059733)
  ·
    refine ⟨327732098181397237643425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6991618094536474403059733 327732098181397237643425)
    ·
      refine ⟨245799073636047928232569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327732098181397237643425 245799073636047928232569)
      ·
        refine ⟨184349305227035946174427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245799073636047928232569 184349305227035946174427)
        ·
          refine ⟨276523957840553919261641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184349305227035946174427 276523957840553919261641)
          ·
            refine ⟨207392968380415439446231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276523957840553919261641 207392968380415439446231)
            ·
              refine ⟨311089452570623159169347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207392968380415439446231 311089452570623159169347)
              ·
                refine ⟨466634178855934738754021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311089452570623159169347 466634178855934738754021)
                ·
                  refine ⟨87493908535487763516379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 466634178855934738754021 87493908535487763516379)
                  ·
                    rfl

theorem cell20_191693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_191693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191693 prefixEnd_191693 := by exact prefixLift 191693
  have htrace : WordTrace (prefixWord ++ tailWord_191693) baseStart_191693 baseEnd_191693 := by
    simpa [prefixWord, tailWord_191693, baseEnd_191693] using wordTrace_append hprefix tailTrace_191693
  have hstable : (prefixWord ++ tailWord_191693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191693).length < 2 ^ (prefixWord ++ tailWord_191693).sum := by decide
  have hdescent : baseEnd_191693 < baseStart_191693 := by decide
  rcases family_descends (prefixWord ++ tailWord_191693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191711 : List Nat := [1, 1, 2, 3, 2, 1, 6, 1, 3]
def baseStart_191711 : Nat := 118140960795 + 191711 * 2 ^ 59
def prefixEnd_191711 : Nat := 4983230072969 + 3 ^ 40 * 191711 * 2
def baseEnd_191711 : Nat := 87502124225959700916305

theorem tailTrace_191711 : CollatzResearch.WordTrace tailWord_191711 prefixEnd_191711 87502124225959700916305 := by
  unfold tailWord_191711
  simp only [CollatzResearch.WordTrace]
  refine ⟨6992274608471263477214987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4661516405647508984809991 6992274608471263477214987)
  ·
    refine ⟨10488411912706895215822481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6992274608471263477214987 10488411912706895215822481)
    ·
      refine ⟨7866308934530171411866861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10488411912706895215822481 7866308934530171411866861)
      ·
        refine ⟨2949865850448814279450073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7866308934530171411866861 2949865850448814279450073)
        ·
          refine ⟨2212399387836610709587555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2949865850448814279450073 2212399387836610709587555)
          ·
            refine ⟨3318599081754916064381333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2212399387836610709587555 3318599081754916064381333)
            ·
              refine ⟨155559331957261690517875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3318599081754916064381333 155559331957261690517875)
              ·
                refine ⟨233338997935892535776813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155559331957261690517875 233338997935892535776813)
                ·
                  refine ⟨87502124225959700916305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233338997935892535776813 87502124225959700916305)
                  ·
                    rfl

theorem cell20_191711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 3].length) (baseStart_191711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191711 prefixEnd_191711 := by exact prefixLift 191711
  have htrace : WordTrace (prefixWord ++ tailWord_191711) baseStart_191711 baseEnd_191711 := by
    simpa [prefixWord, tailWord_191711, baseEnd_191711] using wordTrace_append hprefix tailTrace_191711
  have hstable : (prefixWord ++ tailWord_191711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191711).length < 2 ^ (prefixWord ++ tailWord_191711).sum := by decide
  have hdescent : baseEnd_191711 < baseStart_191711 := by decide
  rcases family_descends (prefixWord ++ tailWord_191711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191725 : List Nat := [1, 5, 1, 2, 2, 1, 2, 6]
def baseStart_191725 : Nat := 118140960795 + 191725 * 2 ^ 59
def prefixEnd_191725 : Nat := 4983230072969 + 3 ^ 40 * 191725 * 2
def baseEnd_191725 : Nat := 29169504735812624816527

theorem tailTrace_191725 : CollatzResearch.WordTrace tailWord_191725 prefixEnd_191725 29169504735812624816527 := by
  unfold tailWord_191725
  simp only [CollatzResearch.WordTrace]
  refine ⟨6992785230420543868224629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4661856820280362578816419 6992785230420543868224629)
  ·
    refine ⟨655573615351925987646059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6992785230420543868224629 655573615351925987646059)
    ·
      refine ⟨983360423027888981469089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 655573615351925987646059 983360423027888981469089)
      ·
        refine ⟨737520317270916736101817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 983360423027888981469089 737520317270916736101817)
        ·
          refine ⟨553140237953187552076363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 737520317270916736101817 553140237953187552076363)
          ·
            refine ⟨829710356929781328114545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553140237953187552076363 829710356929781328114545)
            ·
              refine ⟨622282767697335996085909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 829710356929781328114545 622282767697335996085909)
              ·
                refine ⟨29169504735812624816527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 622282767697335996085909 29169504735812624816527)
                ·
                  rfl

theorem cell20_191725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 6].length) (baseStart_191725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191725 prefixEnd_191725 := by exact prefixLift 191725
  have htrace : WordTrace (prefixWord ++ tailWord_191725) baseStart_191725 baseEnd_191725 := by
    simpa [prefixWord, tailWord_191725, baseEnd_191725] using wordTrace_append hprefix tailTrace_191725
  have hstable : (prefixWord ++ tailWord_191725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191725).length < 2 ^ (prefixWord ++ tailWord_191725).sum := by decide
  have hdescent : baseEnd_191725 < baseStart_191725 := by decide
  rcases family_descends (prefixWord ++ tailWord_191725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191791 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 5]
def baseStart_191791 : Nat := 118140960795 + 191791 * 2 ^ 59
def prefixEnd_191791 : Nat := 4983230072969 + 3 ^ 40 * 191791 * 2
def baseEnd_191791 : Nat := 87538638405834978249311

theorem tailTrace_191791 : CollatzResearch.WordTrace tailWord_191791 prefixEnd_191791 87538638405834978249311 := by
  unfold tailWord_191791
  simp only [CollatzResearch.WordTrace]
  refine ⟨6995192448181437140127227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4663461632120958093418151 6995192448181437140127227)
  ·
    refine ⟨10492788672272155710190841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6995192448181437140127227 10492788672272155710190841)
    ·
      refine ⟨7869591504204116782643131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10492788672272155710190841 7869591504204116782643131)
      ·
        refine ⟨11804387256306175173964697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7869591504204116782643131 11804387256306175173964697)
        ·
          refine ⟨8853290442229631380473523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11804387256306175173964697 8853290442229631380473523)
          ·
            refine ⟨13279935663344447070710285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8853290442229631380473523 13279935663344447070710285)
            ·
              refine ⟨4979975873754167651516357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13279935663344447070710285 4979975873754167651516357)
              ·
                refine ⟨933745476328906434659317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4979975873754167651516357 933745476328906434659317)
                ·
                  refine ⟨87538638405834978249311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 933745476328906434659317 87538638405834978249311)
                  ·
                    rfl

theorem cell20_191791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_191791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191791 prefixEnd_191791 := by exact prefixLift 191791
  have htrace : WordTrace (prefixWord ++ tailWord_191791) baseStart_191791 baseEnd_191791 := by
    simpa [prefixWord, tailWord_191791, baseEnd_191791] using wordTrace_append hprefix tailTrace_191791
  have hstable : (prefixWord ++ tailWord_191791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191791).length < 2 ^ (prefixWord ++ tailWord_191791).sum := by decide
  have hdescent : baseEnd_191791 < baseStart_191791 := by decide
  rcases family_descends (prefixWord ++ tailWord_191791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191801 : List Nat := [1, 2, 1, 6, 2, 1, 7]
def baseStart_191801 : Nat := 118140960795 + 191801 * 2 ^ 59
def prefixEnd_191801 : Nat := 4983230072969 + 3 ^ 40 * 191801 * 2
def baseEnd_191801 : Nat := 9727022519813265323993

theorem tailTrace_191801 : CollatzResearch.WordTrace tailWord_191801 prefixEnd_191801 9727022519813265323993 := by
  unfold tailWord_191801
  simp only [CollatzResearch.WordTrace]
  refine ⟨6995557178145208847991257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4663704785430139231994171 6995557178145208847991257)
  ·
    refine ⟨5246667883608906635993443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6995557178145208847991257 5246667883608906635993443)
    ·
      refine ⟨7870001825413359953990165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5246667883608906635993443 7870001825413359953990165)
      ·
        refine ⟨368906335566251247843289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7870001825413359953990165 368906335566251247843289)
        ·
          refine ⟨276679751674688435882467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368906335566251247843289 276679751674688435882467)
          ·
            refine ⟨415019627512032653823701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276679751674688435882467 415019627512032653823701)
            ·
              refine ⟨9727022519813265323993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 415019627512032653823701 9727022519813265323993)
              ·
                rfl

theorem cell20_191801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 7].length) (baseStart_191801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191801 prefixEnd_191801 := by exact prefixLift 191801
  have htrace : WordTrace (prefixWord ++ tailWord_191801) baseStart_191801 baseEnd_191801 := by
    simpa [prefixWord, tailWord_191801, baseEnd_191801] using wordTrace_append hprefix tailTrace_191801
  have hstable : (prefixWord ++ tailWord_191801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191801).length < 2 ^ (prefixWord ++ tailWord_191801).sum := by decide
  have hdescent : baseEnd_191801 < baseStart_191801 := by decide
  rcases family_descends (prefixWord ++ tailWord_191801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191815 : List Nat := [1, 1, 4, 1, 2, 3, 1, 3, 4]
def baseStart_191815 : Nat := 118140960795 + 191815 * 2 ^ 59
def prefixEnd_191815 : Nat := 4983230072969 + 3 ^ 40 * 191815 * 2
def baseEnd_191815 : Nat := 87549592659797561449213

theorem tailTrace_191815 : CollatzResearch.WordTrace tailWord_191815 prefixEnd_191815 87549592659797561449213 := by
  unfold tailWord_191815
  simp only [CollatzResearch.WordTrace]
  refine ⟨6996067800094489239000899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4664045200062992826000599 6996067800094489239000899)
  ·
    refine ⟨10494101700141733858501349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6996067800094489239000899 10494101700141733858501349)
    ·
      refine ⟨1967644068776575098469003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10494101700141733858501349 1967644068776575098469003)
      ·
        refine ⟨2951466103164862647703505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1967644068776575098469003 2951466103164862647703505)
        ·
          refine ⟨2213599577373646985777629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2951466103164862647703505 2213599577373646985777629)
          ·
            refine ⟨830099841515117619666611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2213599577373646985777629 830099841515117619666611)
            ·
              refine ⟨1245149762272676429499917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830099841515117619666611 1245149762272676429499917)
              ·
                refine ⟨466931160852253661062469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1245149762272676429499917 466931160852253661062469)
                ·
                  refine ⟨87549592659797561449213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 466931160852253661062469 87549592659797561449213)
                  ·
                    rfl

theorem cell20_191815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_191815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191815 prefixEnd_191815 := by exact prefixLift 191815
  have htrace : WordTrace (prefixWord ++ tailWord_191815) baseStart_191815 baseEnd_191815 := by
    simpa [prefixWord, tailWord_191815, baseEnd_191815] using wordTrace_append hprefix tailTrace_191815
  have hstable : (prefixWord ++ tailWord_191815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191815).length < 2 ^ (prefixWord ++ tailWord_191815).sum := by decide
  have hdescent : baseEnd_191815 < baseStart_191815 := by decide
  rcases family_descends (prefixWord ++ tailWord_191815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191822 : List Nat := [4, 1, 1, 1, 1, 1, 4, 7]
def baseStart_191822 : Nat := 118140960795 + 191822 * 2 ^ 59
def prefixEnd_191822 : Nat := 4983230072969 + 3 ^ 40 * 191822 * 2
def baseEnd_191822 : Nat := 29184262550178882738617

theorem tailTrace_191822 : CollatzResearch.WordTrace tailWord_191822 prefixEnd_191822 29184262550178882738617 := by
  unfold tailWord_191822
  simp only [CollatzResearch.WordTrace]
  refine ⟨874540388883641179313215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4664215407379419623003813 874540388883641179313215)
  ·
    refine ⟨1311810583325461768969823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 874540388883641179313215 1311810583325461768969823)
    ·
      refine ⟨1967715874988192653454735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1311810583325461768969823 1967715874988192653454735)
      ·
        refine ⟨2951573812482288980182103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1967715874988192653454735 2951573812482288980182103)
        ·
          refine ⟨4427360718723433470273155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2951573812482288980182103 4427360718723433470273155)
          ·
            refine ⟨6641041078085150205409733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4427360718723433470273155 6641041078085150205409733)
            ·
              refine ⟨1245195202140965663514325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6641041078085150205409733 1245195202140965663514325)
              ·
                refine ⟨29184262550178882738617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1245195202140965663514325 29184262550178882738617)
                ·
                  rfl

theorem cell20_191822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_191822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191822 prefixEnd_191822 := by exact prefixLift 191822
  have htrace : WordTrace (prefixWord ++ tailWord_191822) baseStart_191822 baseEnd_191822 := by
    simpa [prefixWord, tailWord_191822, baseEnd_191822] using wordTrace_append hprefix tailTrace_191822
  have hstable : (prefixWord ++ tailWord_191822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191822).length < 2 ^ (prefixWord ++ tailWord_191822).sum := by decide
  have hdescent : baseEnd_191822 < baseStart_191822 := by decide
  rcases family_descends (prefixWord ++ tailWord_191822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191825 : List Nat := [1, 2, 2, 1, 4, 1, 5, 1, 3]
def baseStart_191825 : Nat := 118140960795 + 191825 * 2 ^ 59
def prefixEnd_191825 : Nat := 4983230072969 + 3 ^ 40 * 191825 * 2
def baseEnd_191825 : Nat := 87554156932281971115839

theorem tailTrace_191825 : CollatzResearch.WordTrace tailWord_191825 prefixEnd_191825 87554156932281971115839 := by
  unfold tailWord_191825
  simp only [CollatzResearch.WordTrace]
  refine ⟨6996432530058260946864929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4664288353372173964576619 6996432530058260946864929)
  ·
    refine ⟨5247324397543695710148697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6996432530058260946864929 5247324397543695710148697)
    ·
      refine ⟨3935493298157771782611523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5247324397543695710148697 3935493298157771782611523)
      ·
        refine ⟨5903239947236657673917285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3935493298157771782611523 5903239947236657673917285)
        ·
          refine ⟨1106857490106873313859491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5903239947236657673917285 1106857490106873313859491)
          ·
            refine ⟨1660286235160309970789237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106857490106873313859491 1660286235160309970789237)
            ·
              refine ⟨155651834546279059761491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1660286235160309970789237 155651834546279059761491)
              ·
                refine ⟨233477751819418589642237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155651834546279059761491 233477751819418589642237)
                ·
                  refine ⟨87554156932281971115839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233477751819418589642237 87554156932281971115839)
                  ·
                    rfl

theorem cell20_191825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 3].length) (baseStart_191825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191825 prefixEnd_191825 := by exact prefixLift 191825
  have htrace : WordTrace (prefixWord ++ tailWord_191825) baseStart_191825 baseEnd_191825 := by
    simpa [prefixWord, tailWord_191825, baseEnd_191825] using wordTrace_append hprefix tailTrace_191825
  have hstable : (prefixWord ++ tailWord_191825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191825).length < 2 ^ (prefixWord ++ tailWord_191825).sum := by decide
  have hdescent : baseEnd_191825 < baseStart_191825 := by decide
  rcases family_descends (prefixWord ++ tailWord_191825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191867 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 5]
def baseStart_191867 : Nat := 118140960795 + 191867 * 2 ^ 59
def prefixEnd_191867 : Nat := 4983230072969 + 3 ^ 40 * 191867 * 2
def baseEnd_191867 : Nat := 87573326876716491715667

theorem tailTrace_191867 : CollatzResearch.WordTrace tailWord_191867 prefixEnd_191867 87573326876716491715667 := by
  unfold tailWord_191867
  simp only [CollatzResearch.WordTrace]
  refine ⟨6997964395906102119893855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4665309597270734746595903 6997964395906102119893855)
  ·
    refine ⟨10496946593859153179840783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6997964395906102119893855 10496946593859153179840783)
    ·
      refine ⟨15745419890788729769761175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10496946593859153179840783 15745419890788729769761175)
      ·
        refine ⟨23618129836183094654641763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15745419890788729769761175 23618129836183094654641763)
        ·
          refine ⟨35427194754274641981962645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23618129836183094654641763 35427194754274641981962645)
          ·
            refine ⟨1660649754106623842904499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35427194754274641981962645 1660649754106623842904499)
            ·
              refine ⟨2490974631159935764356749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1660649754106623842904499 2490974631159935764356749)
              ·
                refine ⟨934115486684975911633781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2490974631159935764356749 934115486684975911633781)
                ·
                  refine ⟨87573326876716491715667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 934115486684975911633781 87573326876716491715667)
                  ·
                    rfl

theorem cell20_191867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_191867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191867 prefixEnd_191867 := by exact prefixLift 191867
  have htrace : WordTrace (prefixWord ++ tailWord_191867) baseStart_191867 baseEnd_191867 := by
    simpa [prefixWord, tailWord_191867, baseEnd_191867] using wordTrace_append hprefix tailTrace_191867
  have hstable : (prefixWord ++ tailWord_191867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191867).length < 2 ^ (prefixWord ++ tailWord_191867).sum := by decide
  have hdescent : baseEnd_191867 < baseStart_191867 := by decide
  rcases family_descends (prefixWord ++ tailWord_191867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191880 : List Nat := [2, 1, 3, 3, 1, 4, 2, 1, 3]
def baseStart_191880 : Nat := 118140960795 + 191880 * 2 ^ 59
def prefixEnd_191880 : Nat := 4983230072969 + 3 ^ 40 * 191880 * 2
def baseEnd_191880 : Nat := 87579260430946224282281

theorem tailTrace_191880 : CollatzResearch.WordTrace tailWord_191880 prefixEnd_191880 87579260430946224282281 := by
  unfold tailWord_191880
  simp only [CollatzResearch.WordTrace]
  refine ⟨3499219272429502670058547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4665625696572670226744729 3499219272429502670058547)
  ·
    refine ⟨5248828908644254005087821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3499219272429502670058547 5248828908644254005087821)
    ·
      refine ⟨1968310840741595251907933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5248828908644254005087821 1968310840741595251907933)
      ·
        refine ⟨738116565278098219465475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1968310840741595251907933 738116565278098219465475)
        ·
          refine ⟨1107174847917147329198213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738116565278098219465475 1107174847917147329198213)
          ·
            refine ⟨207595283984465124224665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1107174847917147329198213 207595283984465124224665)
            ·
              refine ⟨155696462988348843168499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207595283984465124224665 155696462988348843168499)
              ·
                refine ⟨233544694482523264752749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155696462988348843168499 233544694482523264752749)
                ·
                  refine ⟨87579260430946224282281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233544694482523264752749 87579260430946224282281)
                  ·
                    rfl

theorem cell20_191880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 3].length) (baseStart_191880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191880 prefixEnd_191880 := by exact prefixLift 191880
  have htrace : WordTrace (prefixWord ++ tailWord_191880) baseStart_191880 baseEnd_191880 := by
    simpa [prefixWord, tailWord_191880, baseEnd_191880] using wordTrace_append hprefix tailTrace_191880
  have hstable : (prefixWord ++ tailWord_191880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191880).length < 2 ^ (prefixWord ++ tailWord_191880).sum := by decide
  have hdescent : baseEnd_191880 < baseStart_191880 := by decide
  rcases family_descends (prefixWord ++ tailWord_191880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191884 : List Nat := [2, 2, 1, 2, 1, 3, 3, 3, 3]
def baseStart_191884 : Nat := 118140960795 + 191884 * 2 ^ 59
def prefixEnd_191884 : Nat := 4983230072969 + 3 ^ 40 * 191884 * 2
def baseEnd_191884 : Nat := 87581086139939988148931

theorem tailTrace_191884 : CollatzResearch.WordTrace tailWord_191884 prefixEnd_191884 87581086139939988148931 := by
  unfold tailWord_191884
  simp only [CollatzResearch.WordTrace]
  refine ⟨3499292218422257011631353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4665722957896342682175137 3499292218422257011631353)
  ·
    refine ⟨2624469163816692758723515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3499292218422257011631353 2624469163816692758723515)
    ·
      refine ⟨3936703745725039138085273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2624469163816692758723515 3936703745725039138085273)
      ·
        refine ⟨2952527809293779353563955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3936703745725039138085273 2952527809293779353563955)
        ·
          refine ⟨4428791713940669030345933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2952527809293779353563955 4428791713940669030345933)
          ·
            refine ⟨1660796892727750886379725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4428791713940669030345933 1660796892727750886379725)
            ·
              refine ⟨622798834772906582392397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1660796892727750886379725 622798834772906582392397)
              ·
                refine ⟨233549563039839968397149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 622798834772906582392397 233549563039839968397149)
                ·
                  refine ⟨87581086139939988148931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233549563039839968397149 87581086139939988148931)
                  ·
                    rfl

theorem cell20_191884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_191884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191884 prefixEnd_191884 := by exact prefixLift 191884
  have htrace : WordTrace (prefixWord ++ tailWord_191884) baseStart_191884 baseEnd_191884 := by
    simpa [prefixWord, tailWord_191884, baseEnd_191884] using wordTrace_append hprefix tailTrace_191884
  have hstable : (prefixWord ++ tailWord_191884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191884).length < 2 ^ (prefixWord ++ tailWord_191884).sum := by decide
  have hdescent : baseEnd_191884 < baseStart_191884 := by decide
  rcases family_descends (prefixWord ++ tailWord_191884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191898 : List Nat := [3, 1, 1, 4, 1, 1, 1, 8]
def baseStart_191898 : Nat := 118140960795 + 191898 * 2 ^ 59
def prefixEnd_191898 : Nat := 4983230072969 + 3 ^ 40 * 191898 * 2
def baseEnd_191898 : Nat := 29195825373806053894069

theorem tailTrace_191898 : CollatzResearch.WordTrace tailWord_191898 prefixEnd_191898 29195825373806053894069 := by
  unfold tailWord_191898
  simp only [CollatzResearch.WordTrace]
  refine ⟨1749773764698448603568087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4666063372529196276181565 1749773764698448603568087)
  ·
    refine ⟨2624660647047672905352131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1749773764698448603568087 2624660647047672905352131)
    ·
      refine ⟨3936990970571509358028197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2624660647047672905352131 3936990970571509358028197)
      ·
        refine ⟨738185806982158004630287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3936990970571509358028197 738185806982158004630287)
        ·
          refine ⟨1107278710473237006945431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738185806982158004630287 1107278710473237006945431)
          ·
            refine ⟨1660918065709855510418147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107278710473237006945431 1660918065709855510418147)
            ·
              refine ⟨2491377098564783265627221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1660918065709855510418147 2491377098564783265627221)
              ·
                refine ⟨29195825373806053894069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2491377098564783265627221 29195825373806053894069)
                ·
                  rfl

theorem cell20_191898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_191898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191898 prefixEnd_191898 := by exact prefixLift 191898
  have htrace : WordTrace (prefixWord ++ tailWord_191898) baseStart_191898 baseEnd_191898 := by
    simpa [prefixWord, tailWord_191898, baseEnd_191898] using wordTrace_append hprefix tailTrace_191898
  have hstable : (prefixWord ++ tailWord_191898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191898).length < 2 ^ (prefixWord ++ tailWord_191898).sum := by decide
  have hdescent : baseEnd_191898 < baseStart_191898 := by decide
  rcases family_descends (prefixWord ++ tailWord_191898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191908 : List Nat := [2, 3, 1, 2, 1, 1, 1, 7, 2]
def baseStart_191908 : Nat := 118140960795 + 191908 * 2 ^ 59
def prefixEnd_191908 : Nat := 4983230072969 + 3 ^ 40 * 191908 * 2
def baseEnd_191908 : Nat := 87592040393902571348833

theorem tailTrace_191908 : CollatzResearch.WordTrace tailWord_191908 prefixEnd_191908 87592040393902571348833 := by
  unfold tailWord_191908
  simp only [CollatzResearch.WordTrace]
  refine ⟨3499729894378783061068189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4666306525838377414757585 3499729894378783061068189)
  ·
    refine ⟨1312398710392043647900571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3499729894378783061068189 1312398710392043647900571)
    ·
      refine ⟨1968598065588065471850857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1312398710392043647900571 1968598065588065471850857)
      ·
        refine ⟨1476448549191049103888143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1968598065588065471850857 1476448549191049103888143)
        ·
          refine ⟨2214672823786573655832215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476448549191049103888143 2214672823786573655832215)
          ·
            refine ⟨3322009235679860483748323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2214672823786573655832215 3322009235679860483748323)
            ·
              refine ⟨4983013853519790725622485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3322009235679860483748323 4983013853519790725622485)
              ·
                refine ⟨116789387191870095131777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4983013853519790725622485 116789387191870095131777)
                ·
                  refine ⟨87592040393902571348833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116789387191870095131777 87592040393902571348833)
                  ·
                    rfl

theorem cell20_191908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_191908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191908 prefixEnd_191908 := by exact prefixLift 191908
  have htrace : WordTrace (prefixWord ++ tailWord_191908) baseStart_191908 baseEnd_191908 := by
    simpa [prefixWord, tailWord_191908, baseEnd_191908] using wordTrace_append hprefix tailTrace_191908
  have hstable : (prefixWord ++ tailWord_191908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191908).length < 2 ^ (prefixWord ++ tailWord_191908).sum := by decide
  have hdescent : baseEnd_191908 < baseStart_191908 := by decide
  rcases family_descends (prefixWord ++ tailWord_191908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191925 : List Nat := [1, 3, 3, 2, 2, 2, 1, 4, 2]
def baseStart_191925 : Nat := 118140960795 + 191925 * 2 ^ 59
def prefixEnd_191925 : Nat := 4983230072969 + 3 ^ 40 * 191925 * 2
def baseEnd_191925 : Nat := 87599799657126067782097

theorem tailTrace_191925 : CollatzResearch.WordTrace tailWord_191925 prefixEnd_191925 87599799657126067782097 := by
  unfold tailWord_191925
  simp only [CollatzResearch.WordTrace]
  refine ⟨7000079829695978025505229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4666719886463985350336819 7000079829695978025505229)
  ·
    refine ⟨2625029936135991759564461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7000079829695978025505229 2625029936135991759564461)
    ·
      refine ⟨984386226050996909836673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2625029936135991759564461 984386226050996909836673)
      ·
        refine ⟨738289669538247682377505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 984386226050996909836673 738289669538247682377505)
        ·
          refine ⟨553717252153685761783129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 738289669538247682377505 553717252153685761783129)
          ·
            refine ⟨415287939115264321337347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 553717252153685761783129 415287939115264321337347)
            ·
              refine ⟨622931908672896482006021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415287939115264321337347 622931908672896482006021)
              ·
                refine ⟨116799732876168090376129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 622931908672896482006021 116799732876168090376129)
                ·
                  refine ⟨87599799657126067782097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116799732876168090376129 87599799657126067782097)
                  ·
                    rfl

theorem cell20_191925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_191925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191925 prefixEnd_191925 := by exact prefixLift 191925
  have htrace : WordTrace (prefixWord ++ tailWord_191925) baseStart_191925 baseEnd_191925 := by
    simpa [prefixWord, tailWord_191925, baseEnd_191925] using wordTrace_append hprefix tailTrace_191925
  have hstable : (prefixWord ++ tailWord_191925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191925).length < 2 ^ (prefixWord ++ tailWord_191925).sum := by decide
  have hdescent : baseEnd_191925 < baseStart_191925 := by decide
  rcases family_descends (prefixWord ++ tailWord_191925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191932 : List Nat := [2, 2, 2, 4, 2, 2, 1, 5]
def baseStart_191932 : Nat := 118140960795 + 191932 * 2 ^ 59
def prefixEnd_191932 : Nat := 4983230072969 + 3 ^ 40 * 191932 * 2
def baseEnd_191932 : Nat := 29200998215955051516245

theorem tailTrace_191932 : CollatzResearch.WordTrace tailWord_191932 prefixEnd_191932 29200998215955051516245 := by
  unfold tailWord_191932
  simp only [CollatzResearch.WordTrace]
  refine ⟨3500167570335309110505025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4666890093780412147340033 3500167570335309110505025)
  ·
    refine ⟨2625125677751481832878769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3500167570335309110505025 2625125677751481832878769)
    ·
      refine ⟨1968844258313611374659077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2625125677751481832878769 1968844258313611374659077)
      ·
        refine ⟨369158298433802132748577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1968844258313611374659077 369158298433802132748577)
        ·
          refine ⟨276868723825351599561433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369158298433802132748577 276868723825351599561433)
          ·
            refine ⟨207651542869013699671075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276868723825351599561433 207651542869013699671075)
            ·
              refine ⟨311477314303520549506613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207651542869013699671075 311477314303520549506613)
              ·
                refine ⟨29200998215955051516245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 311477314303520549506613 29200998215955051516245)
                ·
                  rfl

theorem cell20_191932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_191932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191932 prefixEnd_191932 := by exact prefixLift 191932
  have htrace : WordTrace (prefixWord ++ tailWord_191932) baseStart_191932 baseEnd_191932 := by
    simpa [prefixWord, tailWord_191932, baseEnd_191932] using wordTrace_append hprefix tailTrace_191932
  have hstable : (prefixWord ++ tailWord_191932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191932).length < 2 ^ (prefixWord ++ tailWord_191932).sum := by decide
  have hdescent : baseEnd_191932 < baseStart_191932 := by decide
  rcases family_descends (prefixWord ++ tailWord_191932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191936 : List Nat := [2, 1, 1, 2, 3, 1, 5, 5]
def baseStart_191936 : Nat := 118140960795 + 191936 * 2 ^ 59
def prefixEnd_191936 : Nat := 4983230072969 + 3 ^ 40 * 191936 * 2
def baseEnd_191936 : Nat := 29201606785619639471795

theorem tailTrace_191936 : CollatzResearch.WordTrace tailWord_191936 prefixEnd_191936 29201606785619639471795 := by
  unfold tailWord_191936
  simp only [CollatzResearch.WordTrace]
  refine ⟨3500240516328063452077831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4666987355104084602770441 3500240516328063452077831)
  ·
    refine ⟨5250360774492095178116747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3500240516328063452077831 5250360774492095178116747)
    ·
      refine ⟨7875541161738142767175121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5250360774492095178116747 7875541161738142767175121)
      ·
        refine ⟨5906655871303607075381341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7875541161738142767175121 5906655871303607075381341)
        ·
          refine ⟨2214995951738852653268003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5906655871303607075381341 2214995951738852653268003)
          ·
            refine ⟨3322493927608278979902005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2214995951738852653268003 3322493927608278979902005)
            ·
              refine ⟨311483805713276154365813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3322493927608278979902005 311483805713276154365813)
              ·
                refine ⟨29201606785619639471795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 311483805713276154365813 29201606785619639471795)
                ·
                  rfl

theorem cell20_191936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_191936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191936 prefixEnd_191936 := by exact prefixLift 191936
  have htrace : WordTrace (prefixWord ++ tailWord_191936) baseStart_191936 baseEnd_191936 := by
    simpa [prefixWord, tailWord_191936, baseEnd_191936] using wordTrace_append hprefix tailTrace_191936
  have hstable : (prefixWord ++ tailWord_191936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191936).length < 2 ^ (prefixWord ++ tailWord_191936).sum := by decide
  have hdescent : baseEnd_191936 < baseStart_191936 := by decide
  rcases family_descends (prefixWord ++ tailWord_191936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191984 : List Nat := [2, 1, 1, 1, 3, 4, 2, 4, 2]
def baseStart_191984 : Nat := 118140960795 + 191984 * 2 ^ 59
def prefixEnd_191984 : Nat := 4983230072969 + 3 ^ 40 * 191984 * 2
def baseEnd_191984 : Nat := 87626728864784084815189

theorem tailTrace_191984 : CollatzResearch.WordTrace tailWord_191984 prefixEnd_191984 87626728864784084815189 := by
  unfold tailWord_191984
  simp only [CollatzResearch.WordTrace]
  refine ⟨3501115868241115550951503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4668154490988154067935337 3501115868241115550951503)
  ·
    refine ⟨5251673802361673326427255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3501115868241115550951503 5251673802361673326427255)
    ·
      refine ⟨7877510703542509989640883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5251673802361673326427255 7877510703542509989640883)
      ·
        refine ⟨11816266055313764984461325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7877510703542509989640883 11816266055313764984461325)
        ·
          refine ⟨4431099770742661869172997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11816266055313764984461325 4431099770742661869172997)
          ·
            refine ⟨830831207014249100469937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4431099770742661869172997 830831207014249100469937)
            ·
              refine ⟨623123405260686825352453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 830831207014249100469937 623123405260686825352453)
              ·
                refine ⟨116835638486378779753585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 623123405260686825352453 116835638486378779753585)
                ·
                  refine ⟨87626728864784084815189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116835638486378779753585 87626728864784084815189)
                  ·
                    rfl

theorem cell20_191984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 2].length) (baseStart_191984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_191984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_191984 prefixEnd_191984 := by exact prefixLift 191984
  have htrace : WordTrace (prefixWord ++ tailWord_191984) baseStart_191984 baseEnd_191984 := by
    simpa [prefixWord, tailWord_191984, baseEnd_191984] using wordTrace_append hprefix tailTrace_191984
  have hstable : (prefixWord ++ tailWord_191984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191984).length < 2 ^ (prefixWord ++ tailWord_191984).sum := by decide
  have hdescent : baseEnd_191984 < baseStart_191984 := by decide
  rcases family_descends (prefixWord ++ tailWord_191984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192019 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 5]
def baseStart_192019 : Nat := 118140960795 + 192019 * 2 ^ 59
def prefixEnd_192019 : Nat := 4983230072969 + 3 ^ 40 * 192019 * 2
def baseEnd_192019 : Nat := 87642703818479518648379

theorem tailTrace_192019 : CollatzResearch.WordTrace tailWord_192019 prefixEnd_192019 87642703818479518648379 := by
  unfold tailWord_192019
  simp only [CollatzResearch.WordTrace]
  refine ⟨7003508291355432079427111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4669005527570288052951407 7003508291355432079427111)
  ·
    refine ⟨10505262437033148119140667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7003508291355432079427111 10505262437033148119140667)
    ·
      refine ⟨15757893655549722178711001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10505262437033148119140667 15757893655549722178711001)
      ·
        refine ⟨11818420241662291634033251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15757893655549722178711001 11818420241662291634033251)
        ·
          refine ⟨17727630362493437451049877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11818420241662291634033251 17727630362493437451049877)
          ·
            refine ⟨830982673241879880517963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17727630362493437451049877 830982673241879880517963)
            ·
              refine ⟨1246474009862819820776945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830982673241879880517963 1246474009862819820776945)
              ·
                refine ⟨934855507397114865582709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1246474009862819820776945 934855507397114865582709)
                ·
                  refine ⟨87642703818479518648379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 934855507397114865582709 87642703818479518648379)
                  ·
                    rfl

theorem cell20_192019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_192019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192019 prefixEnd_192019 := by exact prefixLift 192019
  have htrace : WordTrace (prefixWord ++ tailWord_192019) baseStart_192019 baseEnd_192019 := by
    simpa [prefixWord, tailWord_192019, baseEnd_192019] using wordTrace_append hprefix tailTrace_192019
  have hstable : (prefixWord ++ tailWord_192019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192019).length < 2 ^ (prefixWord ++ tailWord_192019).sum := by decide
  have hdescent : baseEnd_192019 < baseStart_192019 := by decide
  rcases family_descends (prefixWord ++ tailWord_192019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192053 : List Nat := [1, 3, 3, 1, 1, 3, 4, 1, 3]
def baseStart_192053 : Nat := 118140960795 + 192053 * 2 ^ 59
def prefixEnd_192053 : Nat := 4983230072969 + 3 ^ 40 * 192053 * 2
def baseEnd_192053 : Nat := 87658222344926511514907

theorem tailTrace_192053 : CollatzResearch.WordTrace tailWord_192053 prefixEnd_192053 87658222344926511514907 := by
  unfold tailWord_192053
  simp only [CollatzResearch.WordTrace]
  refine ⟨7004748373232255886164813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4669832248821503924109875 7004748373232255886164813)
  ·
    refine ⟨2626780639962095957311805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7004748373232255886164813 2626780639962095957311805)
    ·
      refine ⟨985042739985785983991927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2626780639962095957311805 985042739985785983991927)
      ·
        refine ⟨1477564109978678975987891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 985042739985785983991927 1477564109978678975987891)
        ·
          refine ⟨2216346164968018463981837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1477564109978678975987891 2216346164968018463981837)
          ·
            refine ⟨831129811863006923993189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2216346164968018463981837 831129811863006923993189)
            ·
              refine ⟨155836839724313798248723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 831129811863006923993189 155836839724313798248723)
              ·
                refine ⟨233755259586470697373085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155836839724313798248723 233755259586470697373085)
                ·
                  refine ⟨87658222344926511514907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233755259586470697373085 87658222344926511514907)
                  ·
                    rfl

theorem cell20_192053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_192053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192053 prefixEnd_192053 := by exact prefixLift 192053
  have htrace : WordTrace (prefixWord ++ tailWord_192053) baseStart_192053 baseEnd_192053 := by
    simpa [prefixWord, tailWord_192053, baseEnd_192053] using wordTrace_append hprefix tailTrace_192053
  have hstable : (prefixWord ++ tailWord_192053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192053).length < 2 ^ (prefixWord ++ tailWord_192053).sum := by decide
  have hdescent : baseEnd_192053 < baseStart_192053 := by decide
  rcases family_descends (prefixWord ++ tailWord_192053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192064 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 6]
def baseStart_192064 : Nat := 118140960795 + 192064 * 2 ^ 59
def prefixEnd_192064 : Nat := 4983230072969 + 3 ^ 40 * 192064 * 2
def baseEnd_192064 : Nat := 87663243044659362148195

theorem tailTrace_192064 : CollatzResearch.WordTrace tailWord_192064 prefixEnd_192064 87663243044659362148195 := by
  unfold tailWord_192064
  simp only [CollatzResearch.WordTrace]
  refine ⟨3502574788096202382407623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4670099717461603176543497 3502574788096202382407623)
  ·
    refine ⟨5253862182144303573611435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3502574788096202382407623 5253862182144303573611435)
    ·
      refine ⟨7880793273216455360417153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5253862182144303573611435 7880793273216455360417153)
      ·
        refine ⟨5910594954912341520312865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7880793273216455360417153 5910594954912341520312865)
        ·
          refine ⟨4432946216184256140234649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5910594954912341520312865 4432946216184256140234649)
          ·
            refine ⟨3324709662138192105175987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4432946216184256140234649 3324709662138192105175987)
            ·
              refine ⟨4987064493207288157763981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3324709662138192105175987 4987064493207288157763981)
              ·
                refine ⟨1870149184952733059161493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4987064493207288157763981 1870149184952733059161493)
                ·
                  refine ⟨87663243044659362148195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1870149184952733059161493 87663243044659362148195)
                  ·
                    rfl

theorem cell20_192064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_192064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192064 prefixEnd_192064 := by exact prefixLift 192064
  have htrace : WordTrace (prefixWord ++ tailWord_192064) baseStart_192064 baseEnd_192064 := by
    simpa [prefixWord, tailWord_192064, baseEnd_192064] using wordTrace_append hprefix tailTrace_192064
  have hstable : (prefixWord ++ tailWord_192064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192064).length < 2 ^ (prefixWord ++ tailWord_192064).sum := by decide
  have hdescent : baseEnd_192064 < baseStart_192064 := by decide
  rcases family_descends (prefixWord ++ tailWord_192064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192112 : List Nat := [2, 1, 1, 1, 6, 1, 2, 3, 3]
def baseStart_192112 : Nat := 118140960795 + 192112 * 2 ^ 59
def prefixEnd_192112 : Nat := 4983230072969 + 3 ^ 40 * 192112 * 2
def baseEnd_192112 : Nat := 87685151552584528547999

theorem tailTrace_192112 : CollatzResearch.WordTrace tailWord_192112 prefixEnd_192112 87685151552584528547999 := by
  unfold tailWord_192112
  simp only [CollatzResearch.WordTrace]
  refine ⟨3503450140009254481281295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4671266853345672641708393 3503450140009254481281295)
  ·
    refine ⟨5255175210013881721921943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3503450140009254481281295 5255175210013881721921943)
    ·
      refine ⟨7882762815020822582882915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5255175210013881721921943 7882762815020822582882915)
      ·
        refine ⟨11824144222531233874324373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7882762815020822582882915 11824144222531233874324373)
        ·
          refine ⟨554256760431151587858955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11824144222531233874324373 554256760431151587858955)
          ·
            refine ⟨831385140646727381788433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554256760431151587858955 831385140646727381788433)
            ·
              refine ⟨623538855485045536341325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831385140646727381788433 623538855485045536341325)
              ·
                refine ⟨233827070806892076127997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 623538855485045536341325 233827070806892076127997)
                ·
                  refine ⟨87685151552584528547999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233827070806892076127997 87685151552584528547999)
                  ·
                    rfl

theorem cell20_192112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_192112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192112 prefixEnd_192112 := by exact prefixLift 192112
  have htrace : WordTrace (prefixWord ++ tailWord_192112) baseStart_192112 baseEnd_192112 := by
    simpa [prefixWord, tailWord_192112, baseEnd_192112] using wordTrace_append hprefix tailTrace_192112
  have hstable : (prefixWord ++ tailWord_192112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192112).length < 2 ^ (prefixWord ++ tailWord_192112).sum := by decide
  have hdescent : baseEnd_192112 < baseStart_192112 := by decide
  rcases family_descends (prefixWord ++ tailWord_192112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192133 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 5]
def baseStart_192133 : Nat := 118140960795 + 192133 * 2 ^ 59
def prefixEnd_192133 : Nat := 4983230072969 + 3 ^ 40 * 192133 * 2
def baseEnd_192133 : Nat := 87694736524801788847913

theorem tailTrace_192133 : CollatzResearch.WordTrace tailWord_192133 prefixEnd_192133 87694736524801788847913 := by
  unfold tailWord_192133
  simp only [CollatzResearch.WordTrace]
  refine ⟨7007666212942429549077053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4671777475294953032718035 7007666212942429549077053)
  ·
    refine ⟨2627874829853411080903895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7007666212942429549077053 2627874829853411080903895)
    ·
      refine ⟨3941812244780116621355843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2627874829853411080903895 3941812244780116621355843)
      ·
        refine ⟨5912718367170174932033765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3941812244780116621355843 5912718367170174932033765)
        ·
          refine ⟨1108634693844407799756331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5912718367170174932033765 1108634693844407799756331)
          ·
            refine ⟨1662952040766611699634497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108634693844407799756331 1662952040766611699634497)
            ·
              refine ⟨1247214030574958774725873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1662952040766611699634497 1247214030574958774725873)
              ·
                refine ⟨935410522931219081044405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1247214030574958774725873 935410522931219081044405)
                ·
                  refine ⟨87694736524801788847913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 935410522931219081044405 87694736524801788847913)
                  ·
                    rfl

theorem cell20_192133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_192133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192133 prefixEnd_192133 := by exact prefixLift 192133
  have htrace : WordTrace (prefixWord ++ tailWord_192133) baseStart_192133 baseEnd_192133 := by
    simpa [prefixWord, tailWord_192133, baseEnd_192133] using wordTrace_append hprefix tailTrace_192133
  have hstable : (prefixWord ++ tailWord_192133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192133).length < 2 ^ (prefixWord ++ tailWord_192133).sum := by decide
  have hdescent : baseEnd_192133 < baseStart_192133 := by decide
  rcases family_descends (prefixWord ++ tailWord_192133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192140 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 6]
def baseStart_192140 : Nat := 118140960795 + 192140 * 2 ^ 59
def prefixEnd_192140 : Nat := 4983230072969 + 3 ^ 40 * 192140 * 2
def baseEnd_192140 : Nat := 87697931515540875614551

theorem tailTrace_192140 : CollatzResearch.WordTrace tailWord_192140 prefixEnd_192140 87697931515540875614551 := by
  unfold tailWord_192140
  simp only [CollatzResearch.WordTrace]
  refine ⟨3503960761958534872290937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4671947682611379829721249 3503960761958534872290937)
  ·
    refine ⟨2627970571468901154218203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3503960761958534872290937 2627970571468901154218203)
    ·
      refine ⟨3941955857203351731327305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2627970571468901154218203 3941955857203351731327305)
      ·
        refine ⟨2956466892902513798495479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3941955857203351731327305 2956466892902513798495479)
        ·
          refine ⟨4434700339353770697743219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2956466892902513798495479 4434700339353770697743219)
          ·
            refine ⟨6652050509030656046614829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4434700339353770697743219 6652050509030656046614829)
            ·
              refine ⟨2494518940886496017480561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6652050509030656046614829 2494518940886496017480561)
              ·
                refine ⟨1870889205664872013110421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2494518940886496017480561 1870889205664872013110421)
                ·
                  refine ⟨87697931515540875614551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1870889205664872013110421 87697931515540875614551)
                  ·
                    rfl

theorem cell20_192140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_192140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192140 prefixEnd_192140 := by exact prefixLift 192140
  have htrace : WordTrace (prefixWord ++ tailWord_192140) baseStart_192140 baseEnd_192140 := by
    simpa [prefixWord, tailWord_192140, baseEnd_192140] using wordTrace_append hprefix tailTrace_192140
  have hstable : (prefixWord ++ tailWord_192140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192140).length < 2 ^ (prefixWord ++ tailWord_192140).sum := by decide
  have hdescent : baseEnd_192140 < baseStart_192140 := by decide
  rcases family_descends (prefixWord ++ tailWord_192140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192146 : List Nat := [3, 2, 3, 1, 3, 2, 1, 2, 3]
def baseStart_192146 : Nat := 118140960795 + 192146 * 2 ^ 59
def prefixEnd_192146 : Nat := 4983230072969 + 3 ^ 40 * 192146 * 2
def baseEnd_192146 : Nat := 87700670079031521414527

theorem tailTrace_192146 : CollatzResearch.WordTrace tailWord_192146 prefixEnd_192146 87700670079031521414527 := by
  unfold tailWord_192146
  simp only [CollatzResearch.WordTrace]
  refine ⟨1752035090473833192325073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4672093574596888512866861 1752035090473833192325073)
  ·
    refine ⟨1314026317855374894243805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1752035090473833192325073 1314026317855374894243805)
    ·
      refine ⟨492759869195765585341427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1314026317855374894243805 492759869195765585341427)
      ·
        refine ⟨739139803793648378012141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492759869195765585341427 739139803793648378012141)
        ·
          refine ⟨277177426422618141754553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 739139803793648378012141 277177426422618141754553)
          ·
            refine ⟨207883069816963606315915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277177426422618141754553 207883069816963606315915)
            ·
              refine ⟨311824604725445409473873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207883069816963606315915 311824604725445409473873)
              ·
                refine ⟨233868453544084057105405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 311824604725445409473873 233868453544084057105405)
                ·
                  refine ⟨87700670079031521414527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233868453544084057105405 87700670079031521414527)
                  ·
                    rfl

theorem cell20_192146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_192146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192146 prefixEnd_192146 := by exact prefixLift 192146
  have htrace : WordTrace (prefixWord ++ tailWord_192146) baseStart_192146 baseEnd_192146 := by
    simpa [prefixWord, tailWord_192146, baseEnd_192146] using wordTrace_append hprefix tailTrace_192146
  have hstable : (prefixWord ++ tailWord_192146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192146).length < 2 ^ (prefixWord ++ tailWord_192146).sum := by decide
  have hdescent : baseEnd_192146 < baseStart_192146 := by decide
  rcases family_descends (prefixWord ++ tailWord_192146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192181 : List Nat := [1, 3, 3, 3, 2, 1, 1, 6]
def baseStart_192181 : Nat := 118140960795 + 192181 * 2 ^ 59
def prefixEnd_192181 : Nat := 4983230072969 + 3 ^ 40 * 192181 * 2
def baseEnd_192181 : Nat := 29238881677575651749239

theorem tailTrace_192181 : CollatzResearch.WordTrace tailWord_192181 prefixEnd_192181 29238881677575651749239 := by
  unfold tailWord_192181
  simp only [CollatzResearch.WordTrace]
  refine ⟨7009416916768533746824397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4672944611179022497882931 7009416916768533746824397)
  ·
    refine ⟨2628531343788200155059149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7009416916768533746824397 2628531343788200155059149)
    ·
      refine ⟨985699253920575058147181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2628531343788200155059149 985699253920575058147181)
      ·
        refine ⟨369637220220215646805193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 985699253920575058147181 369637220220215646805193)
        ·
          refine ⟨277227915165161735103895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369637220220215646805193 277227915165161735103895)
          ·
            refine ⟨415841872747742602655843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277227915165161735103895 415841872747742602655843)
            ·
              refine ⟨623762809121613903983765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415841872747742602655843 623762809121613903983765)
              ·
                refine ⟨29238881677575651749239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 623762809121613903983765 29238881677575651749239)
                ·
                  rfl

theorem cell20_192181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 6].length) (baseStart_192181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192181 prefixEnd_192181 := by exact prefixLift 192181
  have htrace : WordTrace (prefixWord ++ tailWord_192181) baseStart_192181 baseEnd_192181 := by
    simpa [prefixWord, tailWord_192181, baseEnd_192181] using wordTrace_append hprefix tailTrace_192181
  have hstable : (prefixWord ++ tailWord_192181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192181).length < 2 ^ (prefixWord ++ tailWord_192181).sum := by decide
  have hdescent : baseEnd_192181 < baseStart_192181 := by decide
  rcases family_descends (prefixWord ++ tailWord_192181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192194 : List Nat := [3, 5, 1, 2, 2, 1, 6]
def baseStart_192194 : Nat := 118140960795 + 192194 * 2 ^ 59
def prefixEnd_192194 : Nat := 4983230072969 + 3 ^ 40 * 192194 * 2
def baseEnd_192194 : Nat := 9746953176328520868259

theorem tailTrace_192194 : CollatzResearch.WordTrace tailWord_192194 prefixEnd_192194 9746953176328520868259 := by
  unfold tailWord_192194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1752472766430359241761909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4673260710480957978031757 1752472766430359241761909)
  ·
    refine ⟨164294321852846178915179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1752472766430359241761909 164294321852846178915179)
    ·
      refine ⟨246441482779269268372769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164294321852846178915179 246441482779269268372769)
      ·
        refine ⟨184831112084451951279577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246441482779269268372769 184831112084451951279577)
        ·
          refine ⟨138623334063338963459683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184831112084451951279577 138623334063338963459683)
          ·
            refine ⟨207935001095008445189525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138623334063338963459683 207935001095008445189525)
            ·
              refine ⟨9746953176328520868259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 207935001095008445189525 9746953176328520868259)
              ·
                rfl

theorem cell20_192194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 6].length) (baseStart_192194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192194 prefixEnd_192194 := by exact prefixLift 192194
  have htrace : WordTrace (prefixWord ++ tailWord_192194) baseStart_192194 baseEnd_192194 := by
    simpa [prefixWord, tailWord_192194, baseEnd_192194] using wordTrace_append hprefix tailTrace_192194
  have hstable : (prefixWord ++ tailWord_192194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192194).length < 2 ^ (prefixWord ++ tailWord_192194).sum := by decide
  have hdescent : baseEnd_192194 < baseStart_192194 := by decide
  rcases family_descends (prefixWord ++ tailWord_192194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192198 : List Nat := [6, 1, 2, 1, 1, 1, 8]
def baseStart_192198 : Nat := 118140960795 + 192198 * 2 ^ 59
def prefixEnd_192198 : Nat := 4983230072969 + 3 ^ 40 * 192198 * 2
def baseEnd_192198 : Nat := 9747156032883383520109

theorem tailTrace_192198 : CollatzResearch.WordTrace tailWord_192198 prefixEnd_192198 9747156032883383520109 := by
  unfold tailWord_192198
  simp only [CollatzResearch.WordTrace]
  refine ⟨219063654928342051568539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4673357971804630433462165 219063654928342051568539)
  ·
    refine ⟨328595482392513077352809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219063654928342051568539 328595482392513077352809)
    ·
      refine ⟨246446611794384808014607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328595482392513077352809 246446611794384808014607)
      ·
        refine ⟨369669917691577212021911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246446611794384808014607 369669917691577212021911)
        ·
          refine ⟨554504876537365818032867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369669917691577212021911 554504876537365818032867)
          ·
            refine ⟨831757314806048727049301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554504876537365818032867 831757314806048727049301)
            ·
              refine ⟨9747156032883383520109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 831757314806048727049301 9747156032883383520109)
              ·
                rfl

theorem cell20_192198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 8].length) (baseStart_192198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192198 prefixEnd_192198 := by exact prefixLift 192198
  have htrace : WordTrace (prefixWord ++ tailWord_192198) baseStart_192198 baseEnd_192198 := by
    simpa [prefixWord, tailWord_192198, baseEnd_192198] using wordTrace_append hprefix tailTrace_192198
  have hstable : (prefixWord ++ tailWord_192198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192198).length < 2 ^ (prefixWord ++ tailWord_192198).sum := by decide
  have hdescent : baseEnd_192198 < baseStart_192198 := by decide
  rcases family_descends (prefixWord ++ tailWord_192198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192205 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 5]
def baseStart_192205 : Nat := 118140960795 + 192205 * 2 ^ 59
def prefixEnd_192205 : Nat := 4983230072969 + 3 ^ 40 * 192205 * 2
def baseEnd_192205 : Nat := 87727599286689538447619

theorem tailTrace_192205 : CollatzResearch.WordTrace tailWord_192205 prefixEnd_192205 87727599286689538447619 := by
  unfold tailWord_192205
  simp only [CollatzResearch.WordTrace]
  refine ⟨7010292268681585845698069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4673528179121057230465379 7010292268681585845698069)
  ·
    refine ⟨328607450094449336517097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7010292268681585845698069 328607450094449336517097)
    ·
      refine ⟨246455587570837002387823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328607450094449336517097 246455587570837002387823)
      ·
        refine ⟨369683381356255503581735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246455587570837002387823 369683381356255503581735)
        ·
          refine ⟨554525072034383255372603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369683381356255503581735 554525072034383255372603)
          ·
            refine ⟨831787608051574883058905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554525072034383255372603 831787608051574883058905)
            ·
              refine ⟨623840706038681162294179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831787608051574883058905 623840706038681162294179)
              ·
                refine ⟨935761059058021743441269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623840706038681162294179 935761059058021743441269)
                ·
                  refine ⟨87727599286689538447619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 935761059058021743441269 87727599286689538447619)
                  ·
                    rfl

theorem cell20_192205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_192205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192205 prefixEnd_192205 := by exact prefixLift 192205
  have htrace : WordTrace (prefixWord ++ tailWord_192205) baseStart_192205 baseEnd_192205 := by
    simpa [prefixWord, tailWord_192205, baseEnd_192205] using wordTrace_append hprefix tailTrace_192205
  have hstable : (prefixWord ++ tailWord_192205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192205).length < 2 ^ (prefixWord ++ tailWord_192205).sum := by decide
  have hdescent : baseEnd_192205 < baseStart_192205 := by decide
  rcases family_descends (prefixWord ++ tailWord_192205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192209 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 5]
def baseStart_192209 : Nat := 118140960795 + 192209 * 2 ^ 59
def prefixEnd_192209 : Nat := 4983230072969 + 3 ^ 40 * 192209 * 2
def baseEnd_192209 : Nat := 87729424995683302314269

theorem tailTrace_192209 : CollatzResearch.WordTrace tailWord_192209 prefixEnd_192209 87729424995683302314269 := by
  unfold tailWord_192209
  simp only [CollatzResearch.WordTrace]
  refine ⟨7010438160667094528843681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4673625440444729685895787 7010438160667094528843681)
  ·
    refine ⟨5257828620500320896632761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7010438160667094528843681 5257828620500320896632761)
    ·
      refine ⟨3943371465375240672474571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5257828620500320896632761 3943371465375240672474571)
      ·
        refine ⟨5915057198062861008711857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3943371465375240672474571 5915057198062861008711857)
        ·
          refine ⟨4436292898547145756533893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5915057198062861008711857 4436292898547145756533893)
          ·
            refine ⟨831804918477589829350105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4436292898547145756533893 831804918477589829350105)
            ·
              refine ⟨623853688858192372012579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831804918477589829350105 623853688858192372012579)
              ·
                refine ⟨935780533287288558018869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623853688858192372012579 935780533287288558018869)
                ·
                  refine ⟨87729424995683302314269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 935780533287288558018869 87729424995683302314269)
                  ·
                    rfl

theorem cell20_192209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_192209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192209 prefixEnd_192209 := by exact prefixLift 192209
  have htrace : WordTrace (prefixWord ++ tailWord_192209) baseStart_192209 baseEnd_192209 := by
    simpa [prefixWord, tailWord_192209, baseEnd_192209] using wordTrace_append hprefix tailTrace_192209
  have hstable : (prefixWord ++ tailWord_192209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192209).length < 2 ^ (prefixWord ++ tailWord_192209).sum := by decide
  have hdescent : baseEnd_192209 < baseStart_192209 := by decide
  rcases family_descends (prefixWord ++ tailWord_192209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192212 : List Nat := [2, 4, 1, 3, 1, 1, 3, 1, 4]
def baseStart_192212 : Nat := 118140960795 + 192212 * 2 ^ 59
def prefixEnd_192212 : Nat := 4983230072969 + 3 ^ 40 * 192212 * 2
def baseEnd_192212 : Nat := 87730794277428625214257

theorem tailTrace_192212 : CollatzResearch.WordTrace tailWord_192212 prefixEnd_192212 87730794277428625214257 := by
  unfold tailWord_192212
  simp only [CollatzResearch.WordTrace]
  refine ⟨3505273789828113020601445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4673698386437484027468593 3505273789828113020601445)
  ·
    refine ⟨657238835592771191362771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3505273789828113020601445 657238835592771191362771)
    ·
      refine ⟨985858253389156787044157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 657238835592771191362771 985858253389156787044157)
      ·
        refine ⟨369696845020933795141559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 985858253389156787044157 369696845020933795141559)
        ·
          refine ⟨554545267531400692712339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369696845020933795141559 554545267531400692712339)
          ·
            refine ⟨831817901297101039068509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554545267531400692712339 831817901297101039068509)
            ·
              refine ⟨311931712986412889650691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 831817901297101039068509 311931712986412889650691)
              ·
                refine ⟨467897569479619334476037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311931712986412889650691 467897569479619334476037)
                ·
                  refine ⟨87730794277428625214257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 467897569479619334476037 87730794277428625214257)
                  ·
                    rfl

theorem cell20_192212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_192212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192212 prefixEnd_192212 := by exact prefixLift 192212
  have htrace : WordTrace (prefixWord ++ tailWord_192212) baseStart_192212 baseEnd_192212 := by
    simpa [prefixWord, tailWord_192212, baseEnd_192212] using wordTrace_append hprefix tailTrace_192212
  have hstable : (prefixWord ++ tailWord_192212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192212).length < 2 ^ (prefixWord ++ tailWord_192212).sum := by decide
  have hdescent : baseEnd_192212 < baseStart_192212 := by decide
  rcases family_descends (prefixWord ++ tailWord_192212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192263 : List Nat := [1, 1, 4, 4, 3, 1, 2, 2, 2]
def baseStart_192263 : Nat := 118140960795 + 192263 * 2 ^ 59
def prefixEnd_192263 : Nat := 4983230072969 + 3 ^ 40 * 192263 * 2
def baseEnd_192263 : Nat := 87754072067099114514049

theorem tailTrace_192263 : CollatzResearch.WordTrace tailWord_192263 prefixEnd_192263 87754072067099114514049 := by
  unfold tailWord_192263
  simp only [CollatzResearch.WordTrace]
  refine ⟨7012407702471461751309443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4674938468314307834206295 7012407702471461751309443)
  ·
    refine ⟨10518611553707192626964165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7012407702471461751309443 10518611553707192626964165)
    ·
      refine ⟨1972239666320098617555781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10518611553707192626964165 1972239666320098617555781)
      ·
        refine ⟨369794937435018490791709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1972239666320098617555781 369794937435018490791709)
        ·
          refine ⟨138673101538131934046891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 369794937435018490791709 138673101538131934046891)
          ·
            refine ⟨208009652307197901070337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138673101538131934046891 208009652307197901070337)
            ·
              refine ⟨156007239230398425802753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208009652307197901070337 156007239230398425802753)
              ·
                refine ⟨117005429422798819352065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156007239230398425802753 117005429422798819352065)
                ·
                  refine ⟨87754072067099114514049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117005429422798819352065 87754072067099114514049)
                  ·
                    rfl

theorem cell20_192263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 2].length) (baseStart_192263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192263 prefixEnd_192263 := by exact prefixLift 192263
  have htrace : WordTrace (prefixWord ++ tailWord_192263) baseStart_192263 baseEnd_192263 := by
    simpa [prefixWord, tailWord_192263, baseEnd_192263] using wordTrace_append hprefix tailTrace_192263
  have hstable : (prefixWord ++ tailWord_192263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192263).length < 2 ^ (prefixWord ++ tailWord_192263).sum := by decide
  have hdescent : baseEnd_192263 < baseStart_192263 := by decide
  rcases family_descends (prefixWord ++ tailWord_192263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192264 : List Nat := [2, 1, 3, 2, 2, 1, 4, 2, 3]
def baseStart_192264 : Nat := 118140960795 + 192264 * 2 ^ 59
def prefixEnd_192264 : Nat := 4983230072969 + 3 ^ 40 * 192264 * 2
def baseEnd_192264 : Nat := 87754528494347555480711

theorem tailTrace_192264 : CollatzResearch.WordTrace tailWord_192264 prefixEnd_192264 87754528494347555480711 := by
  unfold tailWord_192264
  simp only [CollatzResearch.WordTrace]
  refine ⟨3506222087733919461047923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4674962783645225948063897 3506222087733919461047923)
  ·
    refine ⟨5259333131600879191571885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3506222087733919461047923 5259333131600879191571885)
    ·
      refine ⟨1972249924350329696839457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5259333131600879191571885 1972249924350329696839457)
      ·
        refine ⟨1479187443262747272629593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1972249924350329696839457 1479187443262747272629593)
        ·
          refine ⟨1109390582447060454472195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1479187443262747272629593 1109390582447060454472195)
          ·
            refine ⟨1664085873670590681708293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1109390582447060454472195 1664085873670590681708293)
            ·
              refine ⟨312016101313235752820305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1664085873670590681708293 312016101313235752820305)
              ·
                refine ⟨234012075984926814615229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312016101313235752820305 234012075984926814615229)
                ·
                  refine ⟨87754528494347555480711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234012075984926814615229 87754528494347555480711)
                  ·
                    rfl

theorem cell20_192264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_192264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192264 prefixEnd_192264 := by exact prefixLift 192264
  have htrace : WordTrace (prefixWord ++ tailWord_192264) baseStart_192264 baseEnd_192264 := by
    simpa [prefixWord, tailWord_192264, baseEnd_192264] using wordTrace_append hprefix tailTrace_192264
  have hstable : (prefixWord ++ tailWord_192264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192264).length < 2 ^ (prefixWord ++ tailWord_192264).sum := by decide
  have hdescent : baseEnd_192264 < baseStart_192264 := by decide
  rcases family_descends (prefixWord ++ tailWord_192264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192274 : List Nat := [3, 2, 4, 1, 1, 3, 1, 5]
def baseStart_192274 : Nat := 118140960795 + 192274 * 2 ^ 59
def prefixEnd_192274 : Nat := 4983230072969 + 3 ^ 40 * 192274 * 2
def baseEnd_192274 : Nat := 29253030922277321715779

theorem tailTrace_192274 : CollatzResearch.WordTrace tailWord_192274 prefixEnd_192274 29253030922277321715779 := by
  unfold tailWord_192274
  simp only [CollatzResearch.WordTrace]
  refine ⟨1753202226357902657489969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4675205936954407086639917 1753202226357902657489969)
  ·
    refine ⟨1314901669768426993117477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1753202226357902657489969 1314901669768426993117477)
    ·
      refine ⟨246544063081580061209527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1314901669768426993117477 246544063081580061209527)
      ·
        refine ⟨369816094622370091814291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246544063081580061209527 369816094622370091814291)
        ·
          refine ⟨554724141933555137721437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369816094622370091814291 554724141933555137721437)
          ·
            refine ⟨208021553225083176645539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 554724141933555137721437 208021553225083176645539)
            ·
              refine ⟨312032329837624764968309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208021553225083176645539 312032329837624764968309)
              ·
                refine ⟨29253030922277321715779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 312032329837624764968309 29253030922277321715779)
                ·
                  rfl

theorem cell20_192274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_192274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192274 prefixEnd_192274 := by exact prefixLift 192274
  have htrace : WordTrace (prefixWord ++ tailWord_192274) baseStart_192274 baseEnd_192274 := by
    simpa [prefixWord, tailWord_192274, baseEnd_192274] using wordTrace_append hprefix tailTrace_192274
  have hstable : (prefixWord ++ tailWord_192274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192274).length < 2 ^ (prefixWord ++ tailWord_192274).sum := by decide
  have hdescent : baseEnd_192274 < baseStart_192274 := by decide
  rcases family_descends (prefixWord ++ tailWord_192274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192319 : List Nat := [1, 1, 2, 2, 6, 2, 1, 2, 3]
def baseStart_192319 : Nat := 118140960795 + 192319 * 2 ^ 59
def prefixEnd_192319 : Nat := 4983230072969 + 3 ^ 40 * 192319 * 2
def baseEnd_192319 : Nat := 87779631993011808647153

theorem tailTrace_192319 : CollatzResearch.WordTrace tailWord_192319 prefixEnd_192319 87779631993011808647153 := by
  unfold tailWord_192319
  simp only [CollatzResearch.WordTrace]
  refine ⟨7014450190268583315348011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4676300126845722210232007 7014450190268583315348011)
  ·
    refine ⟨10521675285402874973022017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7014450190268583315348011 10521675285402874973022017)
    ·
      refine ⟨7891256464052156229766513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10521675285402874973022017 7891256464052156229766513)
      ·
        refine ⟨5918442348039117172324885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7891256464052156229766513 5918442348039117172324885)
        ·
          refine ⟨277426985064333617452729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5918442348039117172324885 277426985064333617452729)
          ·
            refine ⟨208070238798250213089547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277426985064333617452729 208070238798250213089547)
            ·
              refine ⟨312105358197375319634321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208070238798250213089547 312105358197375319634321)
              ·
                refine ⟨234079018648031489725741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312105358197375319634321 234079018648031489725741)
                ·
                  refine ⟨87779631993011808647153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234079018648031489725741 87779631993011808647153)
                  ·
                    rfl

theorem cell20_192319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 3].length) (baseStart_192319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192319 prefixEnd_192319 := by exact prefixLift 192319
  have htrace : WordTrace (prefixWord ++ tailWord_192319) baseStart_192319 baseEnd_192319 := by
    simpa [prefixWord, tailWord_192319, baseEnd_192319] using wordTrace_append hprefix tailTrace_192319
  have hstable : (prefixWord ++ tailWord_192319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192319).length < 2 ^ (prefixWord ++ tailWord_192319).sum := by decide
  have hdescent : baseEnd_192319 < baseStart_192319 := by decide
  rcases family_descends (prefixWord ++ tailWord_192319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192323 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 5]
def baseStart_192323 : Nat := 118140960795 + 192323 * 2 ^ 59
def prefixEnd_192323 : Nat := 4983230072969 + 3 ^ 40 * 192323 * 2
def baseEnd_192323 : Nat := 87781457702005572513803

theorem tailTrace_192323 : CollatzResearch.WordTrace tailWord_192323 prefixEnd_192323 87781457702005572513803 := by
  unfold tailWord_192323
  simp only [CollatzResearch.WordTrace]
  refine ⟨7014596082254091998493623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4676397388169394665662415 7014596082254091998493623)
  ·
    refine ⟨10521894123381137997740435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7014596082254091998493623 10521894123381137997740435)
    ·
      refine ⟨15782841185071706996610653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10521894123381137997740435 15782841185071706996610653)
      ·
        refine ⟨5918565444401890123728995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15782841185071706996610653 5918565444401890123728995)
        ·
          refine ⟨8877848166602835185593493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5918565444401890123728995 8877848166602835185593493)
          ·
            refine ⟨416149132809507899324695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8877848166602835185593493 416149132809507899324695)
            ·
              refine ⟨624223699214261848987043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416149132809507899324695 624223699214261848987043)
              ·
                refine ⟨936335548821392773480565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 624223699214261848987043 936335548821392773480565)
                ·
                  refine ⟨87781457702005572513803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 936335548821392773480565 87781457702005572513803)
                  ·
                    rfl

theorem cell20_192323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 5].length) (baseStart_192323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192323 prefixEnd_192323 := by exact prefixLift 192323
  have htrace : WordTrace (prefixWord ++ tailWord_192323) baseStart_192323 baseEnd_192323 := by
    simpa [prefixWord, tailWord_192323, baseEnd_192323] using wordTrace_append hprefix tailTrace_192323
  have hstable : (prefixWord ++ tailWord_192323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192323).length < 2 ^ (prefixWord ++ tailWord_192323).sum := by decide
  have hdescent : baseEnd_192323 < baseStart_192323 := by decide
  rcases family_descends (prefixWord ++ tailWord_192323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192364 : List Nat := [2, 2, 1, 1, 4, 2, 3, 3, 2]
def baseStart_192364 : Nat := 118140960795 + 192364 * 2 ^ 59
def prefixEnd_192364 : Nat := 4983230072969 + 3 ^ 40 * 192364 * 2
def baseEnd_192364 : Nat := 87800171219191652146969

theorem tailTrace_192364 : CollatzResearch.WordTrace tailWord_192364 prefixEnd_192364 87800171219191652146969 := by
  unfold tailWord_192364
  simp only [CollatzResearch.WordTrace]
  refine ⟨3508045737552778000368073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4677394316737037333824097 3508045737552778000368073)
  ·
    refine ⟨2631034303164583500276055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3508045737552778000368073 2631034303164583500276055)
    ·
      refine ⟨3946551454746875250414083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2631034303164583500276055 3946551454746875250414083)
      ·
        refine ⟨5919827182120312875621125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3946551454746875250414083 5919827182120312875621125)
        ·
          refine ⟨1109967596647558664178961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5919827182120312875621125 1109967596647558664178961)
          ·
            refine ⟨832475697485668998134221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1109967596647558664178961 832475697485668998134221)
            ·
              refine ⟨312178386557125874300333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 832475697485668998134221 312178386557125874300333)
              ·
                refine ⟨117066894958922202862625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312178386557125874300333 117066894958922202862625)
                ·
                  refine ⟨87800171219191652146969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117066894958922202862625 87800171219191652146969)
                  ·
                    rfl

theorem cell20_192364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_192364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192364 prefixEnd_192364 := by exact prefixLift 192364
  have htrace : WordTrace (prefixWord ++ tailWord_192364) baseStart_192364 baseEnd_192364 := by
    simpa [prefixWord, tailWord_192364, baseEnd_192364] using wordTrace_append hprefix tailTrace_192364
  have hstable : (prefixWord ++ tailWord_192364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192364).length < 2 ^ (prefixWord ++ tailWord_192364).sum := by decide
  have hdescent : baseEnd_192364 < baseStart_192364 := by decide
  rcases family_descends (prefixWord ++ tailWord_192364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192436 : List Nat := [2, 5, 2, 1, 2, 1, 1, 4, 2]
def baseStart_192436 : Nat := 118140960795 + 192436 * 2 ^ 59
def prefixEnd_192436 : Nat := 4983230072969 + 3 ^ 40 * 192436 * 2
def baseEnd_192436 : Nat := 87833033981079401746675

theorem tailTrace_192436 : CollatzResearch.WordTrace tailWord_192436 prefixEnd_192436 87833033981079401746675 := by
  unfold tailWord_192436
  simp only [CollatzResearch.WordTrace]
  refine ⟨3509358765422356148678581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4679145020563141531571441 3509358765422356148678581)
  ·
    refine ⟨329002384258345888938617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3509358765422356148678581 329002384258345888938617)
    ·
      refine ⟨246751788193759416703963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329002384258345888938617 246751788193759416703963)
      ·
        refine ⟨370127682290639125055945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246751788193759416703963 370127682290639125055945)
        ·
          refine ⟨277595761717979343791959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370127682290639125055945 277595761717979343791959)
          ·
            refine ⟨416393642576969015687939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277595761717979343791959 416393642576969015687939)
            ·
              refine ⟨624590463865453523531909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416393642576969015687939 624590463865453523531909)
              ·
                refine ⟨117110711974772535662233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 624590463865453523531909 117110711974772535662233)
                ·
                  refine ⟨87833033981079401746675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117110711974772535662233 87833033981079401746675)
                  ·
                    rfl

theorem cell20_192436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_192436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192436 prefixEnd_192436 := by exact prefixLift 192436
  have htrace : WordTrace (prefixWord ++ tailWord_192436) baseStart_192436 baseEnd_192436 := by
    simpa [prefixWord, tailWord_192436, baseEnd_192436] using wordTrace_append hprefix tailTrace_192436
  have hstable : (prefixWord ++ tailWord_192436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192436).length < 2 ^ (prefixWord ++ tailWord_192436).sum := by decide
  have hdescent : baseEnd_192436 < baseStart_192436 := by decide
  rcases family_descends (prefixWord ++ tailWord_192436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192520 : List Nat := [2, 1, 3, 2, 1, 2, 1, 4, 4]
def baseStart_192520 : Nat := 118140960795 + 192520 * 2 ^ 59
def prefixEnd_192520 : Nat := 4983230072969 + 3 ^ 40 * 192520 * 2
def baseEnd_192520 : Nat := 87871373869948442946331

theorem tailTrace_192520 : CollatzResearch.WordTrace tailWord_192520 prefixEnd_192520 87871373869948442946331 := by
  unfold tailWord_192520
  simp only [CollatzResearch.WordTrace]
  refine ⟨3510890631270197321707507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4681187508360263095610009 3510890631270197321707507)
  ·
    refine ⟨5266335946905295982561261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3510890631270197321707507 5266335946905295982561261)
    ·
      refine ⟨1974875980089485993460473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5266335946905295982561261 1974875980089485993460473)
      ·
        refine ⟨1481156985067114495095355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1974875980089485993460473 1481156985067114495095355)
        ·
          refine ⟨2221735477600671742643033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1481156985067114495095355 2221735477600671742643033)
          ·
            refine ⟨1666301608200503806982275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2221735477600671742643033 1666301608200503806982275)
            ·
              refine ⟨2499452412300755710473413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1666301608200503806982275 2499452412300755710473413)
              ·
                refine ⟨468647327306391695713765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2499452412300755710473413 468647327306391695713765)
                ·
                  refine ⟨87871373869948442946331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 468647327306391695713765 87871373869948442946331)
                  ·
                    rfl

theorem cell20_192520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_192520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192520 prefixEnd_192520 := by exact prefixLift 192520
  have htrace : WordTrace (prefixWord ++ tailWord_192520) baseStart_192520 baseEnd_192520 := by
    simpa [prefixWord, tailWord_192520, baseEnd_192520] using wordTrace_append hprefix tailTrace_192520
  have hstable : (prefixWord ++ tailWord_192520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192520).length < 2 ^ (prefixWord ++ tailWord_192520).sum := by decide
  have hdescent : baseEnd_192520 < baseStart_192520 := by decide
  rcases family_descends (prefixWord ++ tailWord_192520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192533 : List Nat := [1, 3, 2, 1, 5, 2, 1, 3, 2]
def baseStart_192533 : Nat := 118140960795 + 192533 * 2 ^ 59
def prefixEnd_192533 : Nat := 4983230072969 + 3 ^ 40 * 192533 * 2
def baseEnd_192533 : Nat := 87877307424178175512945

theorem tailTrace_192533 : CollatzResearch.WordTrace tailWord_192533 prefixEnd_192533 87877307424178175512945 := by
  unfold tailWord_192533
  simp only [CollatzResearch.WordTrace]
  refine ⟨7022255411493297863638253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4681503607662198575758835 7022255411493297863638253)
  ·
    refine ⟨2633345779309986698864345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7022255411493297863638253 2633345779309986698864345)
    ·
      refine ⟨1975009334482490024148259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2633345779309986698864345 1975009334482490024148259)
      ·
        refine ⟨2962514001723735036222389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1975009334482490024148259 2962514001723735036222389)
        ·
          refine ⟨277735687661600159645849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2962514001723735036222389 277735687661600159645849)
          ·
            refine ⟨208301765746200119734387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277735687661600159645849 208301765746200119734387)
            ·
              refine ⟨312452648619300179601581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208301765746200119734387 312452648619300179601581)
              ·
                refine ⟨117169743232237567350593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312452648619300179601581 117169743232237567350593)
                ·
                  refine ⟨87877307424178175512945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117169743232237567350593 87877307424178175512945)
                  ·
                    rfl

theorem cell20_192533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_192533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192533 prefixEnd_192533 := by exact prefixLift 192533
  have htrace : WordTrace (prefixWord ++ tailWord_192533) baseStart_192533 baseEnd_192533 := by
    simpa [prefixWord, tailWord_192533, baseEnd_192533] using wordTrace_append hprefix tailTrace_192533
  have hstable : (prefixWord ++ tailWord_192533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192533).length < 2 ^ (prefixWord ++ tailWord_192533).sum := by decide
  have hdescent : baseEnd_192533 < baseStart_192533 := by decide
  rcases family_descends (prefixWord ++ tailWord_192533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192554 : List Nat := [3, 1, 4, 1, 2, 3, 1, 1, 4]
def baseStart_192554 : Nat := 118140960795 + 192554 * 2 ^ 59
def prefixEnd_192554 : Nat := 4983230072969 + 3 ^ 40 * 192554 * 2
def baseEnd_192554 : Nat := 87886892396395435812859

theorem tailTrace_192554 : CollatzResearch.WordTrace tailWord_192554 prefixEnd_192554 87886892396395435812859 := by
  unfold tailWord_192554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1755755336104304612538179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4682014229611478966768477 1755755336104304612538179)
  ·
    refine ⟨2633633004156456918807269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1755755336104304612538179 2633633004156456918807269)
    ·
      refine ⟨493806188279335672276363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2633633004156456918807269 493806188279335672276363)
      ·
        refine ⟨740709282419003508414545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493806188279335672276363 740709282419003508414545)
        ·
          refine ⟨555531961814252631310909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 740709282419003508414545 555531961814252631310909)
          ·
            refine ⟨208324485680344736741591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 555531961814252631310909 208324485680344736741591)
            ·
              refine ⟨312486728520517105112387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208324485680344736741591 312486728520517105112387)
              ·
                refine ⟨468730092780775657668581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312486728520517105112387 468730092780775657668581)
                ·
                  refine ⟨87886892396395435812859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 468730092780775657668581 87886892396395435812859)
                  ·
                    rfl

theorem cell20_192554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_192554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192554 prefixEnd_192554 := by exact prefixLift 192554
  have htrace : WordTrace (prefixWord ++ tailWord_192554) baseStart_192554 baseEnd_192554 := by
    simpa [prefixWord, tailWord_192554, baseEnd_192554] using wordTrace_append hprefix tailTrace_192554
  have hstable : (prefixWord ++ tailWord_192554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192554).length < 2 ^ (prefixWord ++ tailWord_192554).sum := by decide
  have hdescent : baseEnd_192554 < baseStart_192554 := by decide
  rcases family_descends (prefixWord ++ tailWord_192554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192565 : List Nat := [1, 3, 3, 1, 1, 1, 3, 7]
def baseStart_192565 : Nat := 118140960795 + 192565 * 2 ^ 59
def prefixEnd_192565 : Nat := 4983230072969 + 3 ^ 40 * 192565 * 2
def baseEnd_192565 : Nat := 29297304365376095482049

theorem tailTrace_192565 : CollatzResearch.WordTrace tailWord_192565 prefixEnd_192565 29297304365376095482049 := by
  unfold tailWord_192565
  simp only [CollatzResearch.WordTrace]
  refine ⟨7023422547377367328803149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4682281698251578219202099 7023422547377367328803149)
  ·
    refine ⟨2633783455266512748301181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7023422547377367328803149 2633783455266512748301181)
    ·
      refine ⟨987668795724942280612943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2633783455266512748301181 987668795724942280612943)
      ·
        refine ⟨1481503193587413420919415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 987668795724942280612943 1481503193587413420919415)
        ·
          refine ⟨2222254790381120131379123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1481503193587413420919415 2222254790381120131379123)
          ·
            refine ⟨3333382185571680197068685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2222254790381120131379123 3333382185571680197068685)
            ·
              refine ⟨1250018319589380073900757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3333382185571680197068685 1250018319589380073900757)
              ·
                refine ⟨29297304365376095482049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1250018319589380073900757 29297304365376095482049)
                ·
                  rfl

theorem cell20_192565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 7].length) (baseStart_192565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192565 prefixEnd_192565 := by exact prefixLift 192565
  have htrace : WordTrace (prefixWord ++ tailWord_192565) baseStart_192565 baseEnd_192565 := by
    simpa [prefixWord, tailWord_192565, baseEnd_192565] using wordTrace_append hprefix tailTrace_192565
  have hstable : (prefixWord ++ tailWord_192565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192565).length < 2 ^ (prefixWord ++ tailWord_192565).sum := by decide
  have hdescent : baseEnd_192565 < baseStart_192565 := by decide
  rcases family_descends (prefixWord ++ tailWord_192565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192568 : List Nat := [2, 1, 2, 1, 6, 1, 1, 3, 3]
def baseStart_192568 : Nat := 118140960795 + 192568 * 2 ^ 59
def prefixEnd_192568 : Nat := 4983230072969 + 3 ^ 40 * 192568 * 2
def baseEnd_192568 : Nat := 87893282377873609346135

theorem tailTrace_192568 : CollatzResearch.WordTrace tailWord_192568 prefixEnd_192568 87893282377873609346135 := by
  unfold tailWord_192568
  simp only [CollatzResearch.WordTrace]
  refine ⟨3511765983183249420581179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4682354644244332560774905 3511765983183249420581179)
  ·
    refine ⟨5267648974774874130871769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3511765983183249420581179 5267648974774874130871769)
    ·
      refine ⟨3950736731081155598153827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5267648974774874130871769 3950736731081155598153827)
      ·
        refine ⟨5926105096621733397230741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3950736731081155598153827 5926105096621733397230741)
        ·
          refine ⟨277786176404143752995191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5926105096621733397230741 277786176404143752995191)
          ·
            refine ⟨416679264606215629492787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277786176404143752995191 416679264606215629492787)
            ·
              refine ⟨625018896909323444239181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416679264606215629492787 625018896909323444239181)
              ·
                refine ⟨234382086340996291589693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 625018896909323444239181 234382086340996291589693)
                ·
                  refine ⟨87893282377873609346135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234382086340996291589693 87893282377873609346135)
                  ·
                    rfl

theorem cell20_192568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_192568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192568 prefixEnd_192568 := by exact prefixLift 192568
  have htrace : WordTrace (prefixWord ++ tailWord_192568) baseStart_192568 baseEnd_192568 := by
    simpa [prefixWord, tailWord_192568, baseEnd_192568] using wordTrace_append hprefix tailTrace_192568
  have hstable : (prefixWord ++ tailWord_192568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192568).length < 2 ^ (prefixWord ++ tailWord_192568).sum := by decide
  have hdescent : baseEnd_192568 < baseStart_192568 := by decide
  rcases family_descends (prefixWord ++ tailWord_192568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192620 : List Nat := [2, 2, 1, 1, 3, 5, 1, 5]
def baseStart_192620 : Nat := 118140960795 + 192620 * 2 ^ 59
def prefixEnd_192620 : Nat := 4983230072969 + 3 ^ 40 * 192620 * 2
def baseEnd_192620 : Nat := 29305672198264179870863

theorem tailTrace_192620 : CollatzResearch.WordTrace tailWord_192620 prefixEnd_192620 29305672198264179870863 := by
  unfold tailWord_192620
  simp only [CollatzResearch.WordTrace]
  refine ⟨3512714281089055861027657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4683619041452074481370209 3512714281089055861027657)
  ·
    refine ⟨2634535710816791895770743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3512714281089055861027657 2634535710816791895770743)
    ·
      refine ⟨3951803566225187843656115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2634535710816791895770743 3951803566225187843656115)
      ·
        refine ⟨5927705349337781765484173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3951803566225187843656115 5927705349337781765484173)
        ·
          refine ⟨2222889506001668162056565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5927705349337781765484173 2222889506001668162056565)
          ·
            refine ⟨208395891187656390192803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2222889506001668162056565 208395891187656390192803)
            ·
              refine ⟨312593836781484585289205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208395891187656390192803 312593836781484585289205)
              ·
                refine ⟨29305672198264179870863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 312593836781484585289205 29305672198264179870863)
                ·
                  rfl

theorem cell20_192620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_192620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192620 prefixEnd_192620 := by exact prefixLift 192620
  have htrace : WordTrace (prefixWord ++ tailWord_192620) baseStart_192620 baseEnd_192620 := by
    simpa [prefixWord, tailWord_192620, baseEnd_192620] using wordTrace_append hprefix tailTrace_192620
  have hstable : (prefixWord ++ tailWord_192620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192620).length < 2 ^ (prefixWord ++ tailWord_192620).sum := by decide
  have hdescent : baseEnd_192620 < baseStart_192620 := by decide
  rcases family_descends (prefixWord ++ tailWord_192620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192672 : List Nat := [2, 1, 1, 4, 2, 2, 1, 3, 4]
def baseStart_192672 : Nat := 118140960795 + 192672 * 2 ^ 59
def prefixEnd_192672 : Nat := 4983230072969 + 3 ^ 40 * 192672 * 2
def baseEnd_192672 : Nat := 87940750811711469879043

theorem tailTrace_192672 : CollatzResearch.WordTrace tailWord_192672 prefixEnd_192672 87940750811711469879043 := by
  unfold tailWord_192672
  simp only [CollatzResearch.WordTrace]
  refine ⟨3513662578994862301474135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4684883438659816401965513 3513662578994862301474135)
  ·
    refine ⟨5270493868492293452211203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3513662578994862301474135 5270493868492293452211203)
    ·
      refine ⟨7905740802738440178316805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5270493868492293452211203 7905740802738440178316805)
      ·
        refine ⟨1482326400513457533434401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7905740802738440178316805 1482326400513457533434401)
        ·
          refine ⟨1111744800385093150075801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1482326400513457533434401 1111744800385093150075801)
          ·
            refine ⟨833808600288819862556851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1111744800385093150075801 833808600288819862556851)
            ·
              refine ⟨1250712900433229793835277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833808600288819862556851 1250712900433229793835277)
              ·
                refine ⟨469017337662461172688229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1250712900433229793835277 469017337662461172688229)
                ·
                  refine ⟨87940750811711469879043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 469017337662461172688229 87940750811711469879043)
                  ·
                    rfl

theorem cell20_192672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_192672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192672 prefixEnd_192672 := by exact prefixLift 192672
  have htrace : WordTrace (prefixWord ++ tailWord_192672) baseStart_192672 baseEnd_192672 := by
    simpa [prefixWord, tailWord_192672, baseEnd_192672] using wordTrace_append hprefix tailTrace_192672
  have hstable : (prefixWord ++ tailWord_192672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192672).length < 2 ^ (prefixWord ++ tailWord_192672).sum := by decide
  have hdescent : baseEnd_192672 < baseStart_192672 := by decide
  rcases family_descends (prefixWord ++ tailWord_192672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192702 : List Nat := [4, 2, 1, 1, 5, 1, 1, 3, 2]
def baseStart_192702 : Nat := 118140960795 + 192702 * 2 ^ 59
def prefixEnd_192702 : Nat := 4983230072969 + 3 ^ 40 * 192702 * 2
def baseEnd_192702 : Nat := 87954443629164698878921

theorem tailTrace_192702 : CollatzResearch.WordTrace tailWord_192702 prefixEnd_192702 87954443629164698878921 := by
  unfold tailWord_192702
  simp only [CollatzResearch.WordTrace]
  refine ⟨878552418485129965817545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4685612898587359817693573 878552418485129965817545)
  ·
    refine ⟨658914313863847474363159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 878552418485129965817545 658914313863847474363159)
    ·
      refine ⟨988371470795771211544739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 658914313863847474363159 988371470795771211544739)
      ·
        refine ⟨1482557206193656817317109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 988371470795771211544739 1482557206193656817317109)
        ·
          refine ⟨138989738080655326623479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1482557206193656817317109 138989738080655326623479)
          ·
            refine ⟨208484607120982989935219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138989738080655326623479 208484607120982989935219)
            ·
              refine ⟨312726910681474484902829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208484607120982989935219 312726910681474484902829)
              ·
                refine ⟨117272591505552931838561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312726910681474484902829 117272591505552931838561)
                ·
                  refine ⟨87954443629164698878921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117272591505552931838561 87954443629164698878921)
                  ·
                    rfl

theorem cell20_192702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_192702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192702 prefixEnd_192702 := by exact prefixLift 192702
  have htrace : WordTrace (prefixWord ++ tailWord_192702) baseStart_192702 baseEnd_192702 := by
    simpa [prefixWord, tailWord_192702, baseEnd_192702] using wordTrace_append hprefix tailTrace_192702
  have hstable : (prefixWord ++ tailWord_192702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192702).length < 2 ^ (prefixWord ++ tailWord_192702).sum := by decide
  have hdescent : baseEnd_192702 < baseStart_192702 := by decide
  rcases family_descends (prefixWord ++ tailWord_192702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192772 : List Nat := [2, 3, 2, 2, 4, 7]
def baseStart_192772 : Nat := 118140960795 + 192772 * 2 ^ 59
def prefixEnd_192772 : Nat := 4983230072969 + 3 ^ 40 * 192772 * 2
def baseEnd_192772 : Nat := 3258755316168724686863

theorem tailTrace_192772 : CollatzResearch.WordTrace tailWord_192772 prefixEnd_192772 3258755316168724686863 := by
  unfold tailWord_192772
  simp only [CollatzResearch.WordTrace]
  refine ⟨3515486228813720840794285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4687314971751627787725713 3515486228813720840794285)
  ·
    refine ⟨1318307335805145315297857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3515486228813720840794285 1318307335805145315297857)
    ·
      refine ⟨988730501853858986473393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1318307335805145315297857 988730501853858986473393)
      ·
        refine ⟨741547876390394239855045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 988730501853858986473393 741547876390394239855045)
        ·
          refine ⟨139040226823198919972821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 741547876390394239855045 139040226823198919972821)
          ·
            refine ⟨3258755316168724686863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 139040226823198919972821 3258755316168724686863)
            ·
              rfl

theorem cell20_192772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 7].length) (baseStart_192772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192772 prefixEnd_192772 := by exact prefixLift 192772
  have htrace : WordTrace (prefixWord ++ tailWord_192772) baseStart_192772 baseEnd_192772 := by
    simpa [prefixWord, tailWord_192772, baseEnd_192772] using wordTrace_append hprefix tailTrace_192772
  have hstable : (prefixWord ++ tailWord_192772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192772).length < 2 ^ (prefixWord ++ tailWord_192772).sum := by decide
  have hdescent : baseEnd_192772 < baseStart_192772 := by decide
  rcases family_descends (prefixWord ++ tailWord_192772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192775 : List Nat := [1, 1, 4, 5, 1, 1, 2, 2, 3]
def baseStart_192775 : Nat := 118140960795 + 192775 * 2 ^ 59
def prefixEnd_192775 : Nat := 4983230072969 + 3 ^ 40 * 192775 * 2
def baseEnd_192775 : Nat := 87987762818300889445289

theorem tailTrace_192775 : CollatzResearch.WordTrace tailWord_192775 prefixEnd_192775 87987762818300889445289 := by
  unfold tailWord_192775
  simp only [CollatzResearch.WordTrace]
  refine ⟨7031081876616573193947779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4687387917744382129298519 7031081876616573193947779)
  ·
    refine ⟨10546622814924859790921669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7031081876616573193947779 10546622814924859790921669)
    ·
      refine ⟨1977491777798411210797813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10546622814924859790921669 1977491777798411210797813)
      ·
        refine ⟨185389854168601051012295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1977491777798411210797813 185389854168601051012295)
        ·
          refine ⟨278084781252901576518443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185389854168601051012295 278084781252901576518443)
          ·
            refine ⟨417127171879352364777665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278084781252901576518443 417127171879352364777665)
            ·
              refine ⟨312845378909514273583249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417127171879352364777665 312845378909514273583249)
              ·
                refine ⟨234634034182135705187437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312845378909514273583249 234634034182135705187437)
                ·
                  refine ⟨87987762818300889445289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234634034182135705187437 87987762818300889445289)
                  ·
                    rfl

theorem cell20_192775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 3].length) (baseStart_192775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192775 prefixEnd_192775 := by exact prefixLift 192775
  have htrace : WordTrace (prefixWord ++ tailWord_192775) baseStart_192775 baseEnd_192775 := by
    simpa [prefixWord, tailWord_192775, baseEnd_192775] using wordTrace_append hprefix tailTrace_192775
  have hstable : (prefixWord ++ tailWord_192775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192775).length < 2 ^ (prefixWord ++ tailWord_192775).sum := by decide
  have hdescent : baseEnd_192775 < baseStart_192775 := by decide
  rcases family_descends (prefixWord ++ tailWord_192775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192779 : List Nat := [1, 1, 1, 1, 5, 2, 4, 2, 3]
def baseStart_192779 : Nat := 118140960795 + 192779 * 2 ^ 59
def prefixEnd_192779 : Nat := 4983230072969 + 3 ^ 40 * 192779 * 2
def baseEnd_192779 : Nat := 87989588527294653311939

theorem tailTrace_192779 : CollatzResearch.WordTrace tailWord_192779 prefixEnd_192779 87989588527294653311939 := by
  unfold tailWord_192779
  simp only [CollatzResearch.WordTrace]
  refine ⟨7031227768602081877093391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4687485179068054584728927 7031227768602081877093391)
  ·
    refine ⟨10546841652903122815640087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7031227768602081877093391 10546841652903122815640087)
    ·
      refine ⟨15820262479354684223460131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10546841652903122815640087 15820262479354684223460131)
      ·
        refine ⟨23730393719032026335190197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15820262479354684223460131 23730393719032026335190197)
        ·
          refine ⟨2224724411159252468924081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23730393719032026335190197 2224724411159252468924081)
          ·
            refine ⟨1668543308369439351693061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2224724411159252468924081 1668543308369439351693061)
            ·
              refine ⟨312851870319269878442449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1668543308369439351693061 312851870319269878442449)
              ·
                refine ⟨234638902739452408831837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312851870319269878442449 234638902739452408831837)
                ·
                  refine ⟨87989588527294653311939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234638902739452408831837 87989588527294653311939)
                  ·
                    rfl

theorem cell20_192779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 3].length) (baseStart_192779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192779 prefixEnd_192779 := by exact prefixLift 192779
  have htrace : WordTrace (prefixWord ++ tailWord_192779) baseStart_192779 baseEnd_192779 := by
    simpa [prefixWord, tailWord_192779, baseEnd_192779] using wordTrace_append hprefix tailTrace_192779
  have hstable : (prefixWord ++ tailWord_192779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192779).length < 2 ^ (prefixWord ++ tailWord_192779).sum := by decide
  have hdescent : baseEnd_192779 < baseStart_192779 := by decide
  rcases family_descends (prefixWord ++ tailWord_192779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192820 : List Nat := [2, 5, 1, 1, 1, 2, 1, 5, 2]
def baseStart_192820 : Nat := 118140960795 + 192820 * 2 ^ 59
def prefixEnd_192820 : Nat := 4983230072969 + 3 ^ 40 * 192820 * 2
def baseEnd_192820 : Nat := 88008302044480732945105

theorem tailTrace_192820 : CollatzResearch.WordTrace tailWord_192820 prefixEnd_192820 88008302044480732945105 := by
  unfold tailWord_192820
  simp only [CollatzResearch.WordTrace]
  refine ⟨3516361580726772939667957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4688482107635697252890609 3516361580726772939667957)
  ·
    refine ⟨329658898193134963093871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3516361580726772939667957 329658898193134963093871)
    ·
      refine ⟨494488347289702444640807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329658898193134963093871 494488347289702444640807)
      ·
        refine ⟨741732520934553666961211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494488347289702444640807 741732520934553666961211)
        ·
          refine ⟨1112598781401830500441817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741732520934553666961211 1112598781401830500441817)
          ·
            refine ⟨834449086051372875331363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1112598781401830500441817 834449086051372875331363)
            ·
              refine ⟨1251673629077059312997045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834449086051372875331363 1251673629077059312997045)
              ·
                refine ⟨117344402725974310593473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1251673629077059312997045 117344402725974310593473)
                ·
                  refine ⟨88008302044480732945105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117344402725974310593473 88008302044480732945105)
                  ·
                    rfl

theorem cell20_192820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_192820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192820 prefixEnd_192820 := by exact prefixLift 192820
  have htrace : WordTrace (prefixWord ++ tailWord_192820) baseStart_192820 baseEnd_192820 := by
    simpa [prefixWord, tailWord_192820, baseEnd_192820] using wordTrace_append hprefix tailTrace_192820
  have hstable : (prefixWord ++ tailWord_192820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192820).length < 2 ^ (prefixWord ++ tailWord_192820).sum := by decide
  have hdescent : baseEnd_192820 < baseStart_192820 := by decide
  rcases family_descends (prefixWord ++ tailWord_192820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192869 : List Nat := [1, 3, 1, 3, 1, 4, 1, 6]
def baseStart_192869 : Nat := 118140960795 + 192869 * 2 ^ 59
def prefixEnd_192869 : Nat := 4983230072969 + 3 ^ 40 * 192869 * 2
def baseEnd_192869 : Nat := 29343555659884780103857

theorem tailTrace_192869 : CollatzResearch.WordTrace tailWord_192869 prefixEnd_192869 29343555659884780103857 := by
  unfold tailWord_192869
  simp only [CollatzResearch.WordTrace]
  refine ⟨7034510338276027247869661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4689673558850684831913107 7034510338276027247869661)
  ·
    refine ⟨2637941376853510217951123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7034510338276027247869661 2637941376853510217951123)
    ·
      refine ⟨3956912065280265326926685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2637941376853510217951123 3956912065280265326926685)
      ·
        refine ⟨1483842024480099497597507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3956912065280265326926685 1483842024480099497597507)
        ·
          refine ⟨2225763036720149246396261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1483842024480099497597507 2225763036720149246396261)
          ·
            refine ⟨417330569385027983699299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2225763036720149246396261 417330569385027983699299)
            ·
              refine ⟨625995854077541975548949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417330569385027983699299 625995854077541975548949)
              ·
                refine ⟨29343555659884780103857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 625995854077541975548949 29343555659884780103857)
                ·
                  rfl

theorem cell20_192869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 6].length) (baseStart_192869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192869 prefixEnd_192869 := by exact prefixLift 192869
  have htrace : WordTrace (prefixWord ++ tailWord_192869) baseStart_192869 baseEnd_192869 := by
    simpa [prefixWord, tailWord_192869, baseEnd_192869] using wordTrace_append hprefix tailTrace_192869
  have hstable : (prefixWord ++ tailWord_192869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192869).length < 2 ^ (prefixWord ++ tailWord_192869).sum := by decide
  have hdescent : baseEnd_192869 < baseStart_192869 := by decide
  rcases family_descends (prefixWord ++ tailWord_192869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192906 : List Nat := [3, 1, 2, 5, 1, 2, 2, 1, 3]
def baseStart_192906 : Nat := 118140960795 + 192906 * 2 ^ 59
def prefixEnd_192906 : Nat := 4983230072969 + 3 ^ 40 * 192906 * 2
def baseEnd_192906 : Nat := 88047554787846656078087

theorem tailTrace_192906 : CollatzResearch.WordTrace tailWord_192906 prefixEnd_192906 88047554787846656078087 := by
  unfold tailWord_192906
  simp only [CollatzResearch.WordTrace]
  refine ⟨1758964959785495641741643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4690573226094655044644381 1758964959785495641741643)
  ·
    refine ⟨2638447439678243462612465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1758964959785495641741643 2638447439678243462612465)
    ·
      refine ⟨1978835579758682596959349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2638447439678243462612465 1978835579758682596959349)
      ·
        refine ⟨185515835602376493464939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1978835579758682596959349 185515835602376493464939)
        ·
          refine ⟨278273753403564740197409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185515835602376493464939 278273753403564740197409)
          ·
            refine ⟨208705315052673555148057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278273753403564740197409 208705315052673555148057)
            ·
              refine ⟨156528986289505166361043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208705315052673555148057 156528986289505166361043)
              ·
                refine ⟨234793479434257749541565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156528986289505166361043 234793479434257749541565)
                ·
                  refine ⟨88047554787846656078087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234793479434257749541565 88047554787846656078087)
                  ·
                    rfl

theorem cell20_192906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_192906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192906 prefixEnd_192906 := by exact prefixLift 192906
  have htrace : WordTrace (prefixWord ++ tailWord_192906) baseStart_192906 baseEnd_192906 := by
    simpa [prefixWord, tailWord_192906, baseEnd_192906] using wordTrace_append hprefix tailTrace_192906
  have hstable : (prefixWord ++ tailWord_192906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192906).length < 2 ^ (prefixWord ++ tailWord_192906).sum := by decide
  have hdescent : baseEnd_192906 < baseStart_192906 := by decide
  rcases family_descends (prefixWord ++ tailWord_192906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192907 : List Nat := [1, 1, 1, 1, 4, 5, 2, 5]
def baseStart_192907 : Nat := 118140960795 + 192907 * 2 ^ 59
def prefixEnd_192907 : Nat := 4983230072969 + 3 ^ 40 * 192907 * 2
def baseEnd_192907 : Nat := 29349337071698365681583

theorem tailTrace_192907 : CollatzResearch.WordTrace tailWord_192907 prefixEnd_192907 29349337071698365681583 := by
  unfold tailWord_192907
  simp only [CollatzResearch.WordTrace]
  refine ⟨7035896312138359737752975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4690597541425573158501983 7035896312138359737752975)
  ·
    refine ⟨10553844468207539606629463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7035896312138359737752975 10553844468207539606629463)
    ·
      refine ⟨15830766702311309409944195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10553844468207539606629463 15830766702311309409944195)
      ·
        refine ⟨23746150053466964114916293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15830766702311309409944195 23746150053466964114916293)
        ·
          refine ⟨4452403135025055771546805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23746150053466964114916293 4452403135025055771546805)
          ·
            refine ⟨417412793908598978582513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4452403135025055771546805 417412793908598978582513)
            ·
              refine ⟨313059595431449233936885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417412793908598978582513 313059595431449233936885)
              ·
                refine ⟨29349337071698365681583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 313059595431449233936885 29349337071698365681583)
                ·
                  rfl

theorem cell20_192907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 5].length) (baseStart_192907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192907 prefixEnd_192907 := by exact prefixLift 192907
  have htrace : WordTrace (prefixWord ++ tailWord_192907) baseStart_192907 baseEnd_192907 := by
    simpa [prefixWord, tailWord_192907, baseEnd_192907] using wordTrace_append hprefix tailTrace_192907
  have hstable : (prefixWord ++ tailWord_192907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192907).length < 2 ^ (prefixWord ++ tailWord_192907).sum := by decide
  have hdescent : baseEnd_192907 < baseStart_192907 := by decide
  rcases family_descends (prefixWord ++ tailWord_192907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192910 : List Nat := [4, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_192910 : Nat := 118140960795 + 192910 * 2 ^ 59
def prefixEnd_192910 : Nat := 4983230072969 + 3 ^ 40 * 192910 * 2
def baseEnd_192910 : Nat := 88049380496840419944737

theorem tailTrace_192910 : CollatzResearch.WordTrace tailWord_192910 prefixEnd_192910 88049380496840419944737 := by
  unfold tailWord_192910
  simp only [CollatzResearch.WordTrace]
  refine ⟨879500716390936406264023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4690670487418327500074789 879500716390936406264023)
  ·
    refine ⟨1319251074586404609396035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 879500716390936406264023 1319251074586404609396035)
    ·
      refine ⟨1978876611879606914094053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1319251074586404609396035 1978876611879606914094053)
      ·
        refine ⟨371039364727426296392635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1978876611879606914094053 371039364727426296392635)
        ·
          refine ⟨556559047091139444588953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371039364727426296392635 556559047091139444588953)
          ·
            refine ⟨417419285318354583441715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 556559047091139444588953 417419285318354583441715)
            ·
              refine ⟨626128927977531875162573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417419285318354583441715 626128927977531875162573)
              ·
                refine ⟨234798347991574453185965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 626128927977531875162573 234798347991574453185965)
                ·
                  refine ⟨88049380496840419944737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234798347991574453185965 88049380496840419944737)
                  ·
                    rfl

theorem cell20_192910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_192910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192910 prefixEnd_192910 := by exact prefixLift 192910
  have htrace : WordTrace (prefixWord ++ tailWord_192910) baseStart_192910 baseEnd_192910 := by
    simpa [prefixWord, tailWord_192910, baseEnd_192910] using wordTrace_append hprefix tailTrace_192910
  have hstable : (prefixWord ++ tailWord_192910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192910).length < 2 ^ (prefixWord ++ tailWord_192910).sum := by decide
  have hdescent : baseEnd_192910 < baseStart_192910 := by decide
  rcases family_descends (prefixWord ++ tailWord_192910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192921 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 6]
def baseStart_192921 : Nat := 118140960795 + 192921 * 2 ^ 59
def prefixEnd_192921 : Nat := 4983230072969 + 3 ^ 40 * 192921 * 2
def baseEnd_192921 : Nat := 88054401196573270578025

theorem tailTrace_192921 : CollatzResearch.WordTrace tailWord_192921 prefixEnd_192921 88054401196573270578025 := by
  unfold tailWord_192921
  simp only [CollatzResearch.WordTrace]
  refine ⟨7036406934087640128762617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4690937956058426752508411 7036406934087640128762617)
  ·
    refine ⟨5277305200565730096571963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7036406934087640128762617 5277305200565730096571963)
    ·
      refine ⟨7915957800848595144857945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5277305200565730096571963 7915957800848595144857945)
      ·
        refine ⟨5936968350636446358643459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7915957800848595144857945 5936968350636446358643459)
        ·
          refine ⟨8905452525954669537965189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5936968350636446358643459 8905452525954669537965189)
          ·
            refine ⟨1669772348616500538368473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8905452525954669537965189 1669772348616500538368473)
            ·
              refine ⟨1252329261462375403776355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1669772348616500538368473 1252329261462375403776355)
              ·
                refine ⟨1878493892193563105664533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1252329261462375403776355 1878493892193563105664533)
                ·
                  refine ⟨88054401196573270578025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1878493892193563105664533 88054401196573270578025)
                  ·
                    rfl

theorem cell20_192921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_192921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192921 prefixEnd_192921 := by exact prefixLift 192921
  have htrace : WordTrace (prefixWord ++ tailWord_192921) baseStart_192921 baseEnd_192921 := by
    simpa [prefixWord, tailWord_192921, baseEnd_192921] using wordTrace_append hprefix tailTrace_192921
  have hstable : (prefixWord ++ tailWord_192921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192921).length < 2 ^ (prefixWord ++ tailWord_192921).sum := by decide
  have hdescent : baseEnd_192921 < baseStart_192921 := by decide
  rcases family_descends (prefixWord ++ tailWord_192921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192993 : List Nat := [1, 2, 3, 1, 2, 2, 4, 3, 2]
def baseStart_192993 : Nat := 118140960795 + 192993 * 2 ^ 59
def prefixEnd_192993 : Nat := 4983230072969 + 3 ^ 40 * 192993 * 2
def baseEnd_192993 : Nat := 88087263958461020177731

theorem tailTrace_192993 : CollatzResearch.WordTrace tailWord_192993 prefixEnd_192993 88087263958461020177731 := by
  unfold tailWord_192993
  simp only [CollatzResearch.WordTrace]
  refine ⟨7039032989826796425383633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4692688659884530950255755 7039032989826796425383633)
  ·
    refine ⟨5279274742370097319037725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7039032989826796425383633 5279274742370097319037725)
    ·
      refine ⟨1979728028388786494639147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5279274742370097319037725 1979728028388786494639147)
      ·
        refine ⟨2969592042583179741958721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1979728028388786494639147 2969592042583179741958721)
        ·
          refine ⟨2227194031937384806469041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2969592042583179741958721 2227194031937384806469041)
          ·
            refine ⟨1670395523953038604851781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2227194031937384806469041 1670395523953038604851781)
            ·
              refine ⟨313199160741194738409709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1670395523953038604851781 313199160741194738409709)
              ·
                refine ⟨117449685277948026903641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313199160741194738409709 117449685277948026903641)
                ·
                  refine ⟨88087263958461020177731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117449685277948026903641 88087263958461020177731)
                  ·
                    rfl

theorem cell20_192993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 2].length) (baseStart_192993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_192993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_192993 prefixEnd_192993 := by exact prefixLift 192993
  have htrace : WordTrace (prefixWord ++ tailWord_192993) baseStart_192993 baseEnd_192993 := by
    simpa [prefixWord, tailWord_192993, baseEnd_192993] using wordTrace_append hprefix tailTrace_192993
  have hstable : (prefixWord ++ tailWord_192993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192993).length < 2 ^ (prefixWord ++ tailWord_192993).sum := by decide
  have hdescent : baseEnd_192993 < baseStart_192993 := by decide
  rcases family_descends (prefixWord ++ tailWord_192993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193004 : List Nat := [2, 2, 1, 1, 2, 1, 11]
def baseStart_193004 : Nat := 118140960795 + 193004 * 2 ^ 59
def prefixEnd_193004 : Nat := 4983230072969 + 3 ^ 40 * 193004 * 2
def baseEnd_193004 : Nat := 9788031628688207867891

theorem tailTrace_193004 : CollatzResearch.WordTrace tailWord_193004 prefixEnd_193004 9788031628688207867891 := by
  unfold tailWord_193004
  simp only [CollatzResearch.WordTrace]
  refine ⟨3519717096393472652017033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4692956128524630202689377 3519717096393472652017033)
  ·
    refine ⟨2639787822295104489012775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3519717096393472652017033 2639787822295104489012775)
    ·
      refine ⟨3959681733442656733519163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2639787822295104489012775 3959681733442656733519163)
      ·
        refine ⟨5939522600163985100278745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3959681733442656733519163 5939522600163985100278745)
        ·
          refine ⟨4454641950122988825209059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5939522600163985100278745 4454641950122988825209059)
          ·
            refine ⟨6681962925184483237813589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4454641950122988825209059 6681962925184483237813589)
            ·
              refine ⟨9788031628688207867891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6681962925184483237813589 9788031628688207867891)
              ·
                rfl

theorem cell20_193004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 11].length) (baseStart_193004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193004 prefixEnd_193004 := by exact prefixLift 193004
  have htrace : WordTrace (prefixWord ++ tailWord_193004) baseStart_193004 baseEnd_193004 := by
    simpa [prefixWord, tailWord_193004, baseEnd_193004] using wordTrace_append hprefix tailTrace_193004
  have hstable : (prefixWord ++ tailWord_193004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193004).length < 2 ^ (prefixWord ++ tailWord_193004).sum := by decide
  have hdescent : baseEnd_193004 < baseStart_193004 := by decide
  rcases family_descends (prefixWord ++ tailWord_193004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193038 : List Nat := [4, 1, 1, 2, 3, 1, 4, 4]
def baseStart_193038 : Nat := 118140960795 + 193038 * 2 ^ 59
def prefixEnd_193038 : Nat := 4983230072969 + 3 ^ 40 * 193038 * 2
def baseEnd_193038 : Nat := 29369267728213621225849

theorem tailTrace_193038 : CollatzResearch.WordTrace tailWord_193038 prefixEnd_193038 29369267728213621225849 := by
  unfold tailWord_193038
  simp only [CollatzResearch.WordTrace]
  refine ⟨880084284332971138846471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4693782849775846073847845 880084284332971138846471)
  ·
    refine ⟨1320126426499456708269707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 880084284332971138846471 1320126426499456708269707)
    ·
      refine ⟨1980189639749185062404561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1320126426499456708269707 1980189639749185062404561)
      ·
        refine ⟨1485142229811888796803421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1980189639749185062404561 1485142229811888796803421)
        ·
          refine ⟨556928336179458298801283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1485142229811888796803421 556928336179458298801283)
          ·
            refine ⟨835392504269187448201925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556928336179458298801283 835392504269187448201925)
            ·
              refine ⟨156636094550472646537861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 835392504269187448201925 156636094550472646537861)
              ·
                refine ⟨29369267728213621225849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156636094550472646537861 29369267728213621225849)
                ·
                  rfl

theorem cell20_193038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_193038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193038 prefixEnd_193038 := by exact prefixLift 193038
  have htrace : WordTrace (prefixWord ++ tailWord_193038) baseStart_193038 baseEnd_193038 := by
    simpa [prefixWord, tailWord_193038, baseEnd_193038] using wordTrace_append hprefix tailTrace_193038
  have hstable : (prefixWord ++ tailWord_193038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193038).length < 2 ^ (prefixWord ++ tailWord_193038).sum := by decide
  have hdescent : baseEnd_193038 < baseStart_193038 := by decide
  rcases family_descends (prefixWord ++ tailWord_193038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193048 : List Nat := [2, 1, 2, 3, 3, 3, 1, 3, 2]
def baseStart_193048 : Nat := 118140960795 + 193048 * 2 ^ 59
def prefixEnd_193048 : Nat := 4983230072969 + 3 ^ 40 * 193048 * 2
def baseEnd_193048 : Nat := 88112367457125273344173

theorem tailTrace_193048 : CollatzResearch.WordTrace tailWord_193048 prefixEnd_193048 88112367457125273344173 := by
  unfold tailWord_193048
  simp only [CollatzResearch.WordTrace]
  refine ⟨3520519502313770409317899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4694026003085027212423865 3520519502313770409317899)
  ·
    refine ⟨5280779253470655613976849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3520519502313770409317899 5280779253470655613976849)
    ·
      refine ⟨3960584440102991710482637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5280779253470655613976849 3960584440102991710482637)
      ·
        refine ⟨1485219165038621891430989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3960584440102991710482637 1485219165038621891430989)
        ·
          refine ⟨556957186889483209286621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1485219165038621891430989 556957186889483209286621)
          ·
            refine ⟨208858945083556203482483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 556957186889483209286621 208858945083556203482483)
            ·
              refine ⟨313288417625334305223725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208858945083556203482483 313288417625334305223725)
              ·
                refine ⟨117483156609500364458897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313288417625334305223725 117483156609500364458897)
                ·
                  refine ⟨88112367457125273344173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117483156609500364458897 88112367457125273344173)
                  ·
                    rfl

theorem cell20_193048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 2].length) (baseStart_193048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193048 prefixEnd_193048 := by exact prefixLift 193048
  have htrace : WordTrace (prefixWord ++ tailWord_193048) baseStart_193048 baseEnd_193048 := by
    simpa [prefixWord, tailWord_193048, baseEnd_193048] using wordTrace_append hprefix tailTrace_193048
  have hstable : (prefixWord ++ tailWord_193048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193048).length < 2 ^ (prefixWord ++ tailWord_193048).sum := by decide
  have hdescent : baseEnd_193048 < baseStart_193048 := by decide
  rcases family_descends (prefixWord ++ tailWord_193048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193059 : List Nat := [1, 1, 1, 4, 4, 3, 6]
def baseStart_193059 : Nat := 118140960795 + 193059 * 2 ^ 59
def prefixEnd_193059 : Nat := 4983230072969 + 3 ^ 40 * 193059 * 2
def baseEnd_193059 : Nat := 9790820906317569330829

theorem tailTrace_193059 : CollatzResearch.WordTrace tailWord_193059 prefixEnd_193059 9790820906317569330829 := by
  unfold tailWord_193059
  simp only [CollatzResearch.WordTrace]
  refine ⟨7041440207587689697286231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4694293471725126464857487 7041440207587689697286231)
  ·
    refine ⟨10562160311381534545929347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7041440207587689697286231 10562160311381534545929347)
    ·
      refine ⟨15843240467072301818894021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10562160311381534545929347 15843240467072301818894021)
      ·
        refine ⟨2970607587576056591042629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15843240467072301818894021 2970607587576056591042629)
        ·
          refine ⟨556988922670510610820493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2970607587576056591042629 556988922670510610820493)
          ·
            refine ⟨208870846001441479057685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 556988922670510610820493 208870846001441479057685)
            ·
              refine ⟨9790820906317569330829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 208870846001441479057685 9790820906317569330829)
              ·
                rfl

theorem cell20_193059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 6].length) (baseStart_193059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193059 prefixEnd_193059 := by exact prefixLift 193059
  have htrace : WordTrace (prefixWord ++ tailWord_193059) baseStart_193059 baseEnd_193059 := by
    simpa [prefixWord, tailWord_193059, baseEnd_193059] using wordTrace_append hprefix tailTrace_193059
  have hstable : (prefixWord ++ tailWord_193059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193059).length < 2 ^ (prefixWord ++ tailWord_193059).sum := by decide
  have hdescent : baseEnd_193059 < baseStart_193059 := by decide
  rcases family_descends (prefixWord ++ tailWord_193059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193121 : List Nat := [1, 2, 3, 1, 1, 5, 2, 2, 3]
def baseStart_193121 : Nat := 118140960795 + 193121 * 2 ^ 59
def prefixEnd_193121 : Nat := 4983230072969 + 3 ^ 40 * 193121 * 2
def baseEnd_193121 : Nat := 88145686646261463910541

theorem tailTrace_193121 : CollatzResearch.WordTrace tailWord_193121 prefixEnd_193121 88145686646261463910541 := by
  unfold tailWord_193121
  simp only [CollatzResearch.WordTrace]
  refine ⟨7043701533363074286043217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4695801022242049524028811 7043701533363074286043217)
  ·
    refine ⟨5282776150022305714532413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7043701533363074286043217 5282776150022305714532413)
    ·
      refine ⟨1981041056258364642949655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5282776150022305714532413 1981041056258364642949655)
      ·
        refine ⟨2971561584387546964424483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1981041056258364642949655 2971561584387546964424483)
        ·
          refine ⟨4457342376581320446636725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2971561584387546964424483 4457342376581320446636725)
          ·
            refine ⟨417875847804498791872193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4457342376581320446636725 417875847804498791872193)
            ·
              refine ⟨313406885853374093904145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417875847804498791872193 313406885853374093904145)
              ·
                refine ⟨235055164390030570428109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313406885853374093904145 235055164390030570428109)
                ·
                  refine ⟨88145686646261463910541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 235055164390030570428109 88145686646261463910541)
                  ·
                    rfl

theorem cell20_193121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_193121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193121 prefixEnd_193121 := by exact prefixLift 193121
  have htrace : WordTrace (prefixWord ++ tailWord_193121) baseStart_193121 baseEnd_193121 := by
    simpa [prefixWord, tailWord_193121, baseEnd_193121] using wordTrace_append hprefix tailTrace_193121
  have hstable : (prefixWord ++ tailWord_193121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193121).length < 2 ^ (prefixWord ++ tailWord_193121).sum := by decide
  have hdescent : baseEnd_193121 < baseStart_193121 := by decide
  rcases family_descends (prefixWord ++ tailWord_193121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193162 : List Nat := [3, 1, 2, 3, 3, 1, 2, 3, 2]
def baseStart_193162 : Nat := 118140960795 + 193162 * 2 ^ 59
def prefixEnd_193162 : Nat := 4983230072969 + 3 ^ 40 * 193162 * 2
def baseEnd_193162 : Nat := 88164400163447543543707

theorem tailTrace_193162 : CollatzResearch.WordTrace tailWord_193162 prefixEnd_193162 88164400163447543543707 := by
  unfold tailWord_193162
  simp only [CollatzResearch.WordTrace]
  refine ⟨1761299231553634572071435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4696797950809692192190493 1761299231553634572071435)
  ·
    refine ⟨2641948847330451858107153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1761299231553634572071435 2641948847330451858107153)
    ·
      refine ⟨1981461635497838893580365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2641948847330451858107153 1981461635497838893580365)
      ·
        refine ⟨743048113311689585092637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1981461635497838893580365 743048113311689585092637)
        ·
          refine ⟨278643042491883594409739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 743048113311689585092637 278643042491883594409739)
          ·
            refine ⟨417964563737825391614609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278643042491883594409739 417964563737825391614609)
            ·
              refine ⟨313473422803369043710957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417964563737825391614609 313473422803369043710957)
              ·
                refine ⟨117552533551263391391609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313473422803369043710957 117552533551263391391609)
                ·
                  refine ⟨88164400163447543543707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117552533551263391391609 88164400163447543543707)
                  ·
                    rfl

theorem cell20_193162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_193162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193162 prefixEnd_193162 := by exact prefixLift 193162
  have htrace : WordTrace (prefixWord ++ tailWord_193162) baseStart_193162 baseEnd_193162 := by
    simpa [prefixWord, tailWord_193162, baseEnd_193162] using wordTrace_append hprefix tailTrace_193162
  have hstable : (prefixWord ++ tailWord_193162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193162).length < 2 ^ (prefixWord ++ tailWord_193162).sum := by decide
  have hdescent : baseEnd_193162 < baseStart_193162 := by decide
  rcases family_descends (prefixWord ++ tailWord_193162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193207 : List Nat := [1, 1, 3, 1, 7, 1, 2, 4]
def baseStart_193207 : Nat := 118140960795 + 193207 * 2 ^ 59
def prefixEnd_193207 : Nat := 4983230072969 + 3 ^ 40 * 193207 * 2
def baseEnd_193207 : Nat := 29394979796542462347841

theorem tailTrace_193207 : CollatzResearch.WordTrace tailWord_193207 prefixEnd_193207 29394979796542462347841 := by
  unfold tailWord_193207
  simp only [CollatzResearch.WordTrace]
  refine ⟨7046838211051510973673875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4697892140701007315782583 7046838211051510973673875)
  ·
    refine ⟨10570257316577266460510813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7046838211051510973673875 10570257316577266460510813)
    ·
      refine ⟨3963846493716474922691555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10570257316577266460510813 3963846493716474922691555)
      ·
        refine ⟨5945769740574712384037333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3963846493716474922691555 5945769740574712384037333)
        ·
          refine ⟨139353978294719821500875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 5945769740574712384037333 139353978294719821500875)
          ·
            refine ⟨209030967442079732251313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139353978294719821500875 209030967442079732251313)
            ·
              refine ⟨156773225581559799188485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209030967442079732251313 156773225581559799188485)
              ·
                refine ⟨29394979796542462347841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156773225581559799188485 29394979796542462347841)
                ·
                  rfl

theorem cell20_193207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 4].length) (baseStart_193207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193207 prefixEnd_193207 := by exact prefixLift 193207
  have htrace : WordTrace (prefixWord ++ tailWord_193207) baseStart_193207 baseEnd_193207 := by
    simpa [prefixWord, tailWord_193207, baseEnd_193207] using wordTrace_append hprefix tailTrace_193207
  have hstable : (prefixWord ++ tailWord_193207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193207).length < 2 ^ (prefixWord ++ tailWord_193207).sum := by decide
  have hdescent : baseEnd_193207 < baseStart_193207 := by decide
  rcases family_descends (prefixWord ++ tailWord_193207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193249 : List Nat := [1, 2, 3, 1, 4, 2, 2, 5]
def baseStart_193249 : Nat := 118140960795 + 193249 * 2 ^ 59
def prefixEnd_193249 : Nat := 4983230072969 + 3 ^ 40 * 193249 * 2
def baseEnd_193249 : Nat := 29401369778020635881117

theorem tailTrace_193249 : CollatzResearch.WordTrace tailWord_193249 prefixEnd_193249 29401369778020635881117 := by
  unfold tailWord_193249
  simp only [CollatzResearch.WordTrace]
  refine ⟨7048370076899352146702801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4698913384599568097801867 7048370076899352146702801)
  ·
    refine ⟨5286277557674514110027101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7048370076899352146702801 5286277557674514110027101)
    ·
      refine ⟨1982354084127942791260163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5286277557674514110027101 1982354084127942791260163)
      ·
        refine ⟨2973531126191914186890245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1982354084127942791260163 2973531126191914186890245)
        ·
          refine ⟨557537086160983910041921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2973531126191914186890245 557537086160983910041921)
          ·
            refine ⟨418152814620737932531441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 557537086160983910041921 418152814620737932531441)
            ·
              refine ⟨313614610965553449398581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418152814620737932531441 313614610965553449398581)
              ·
                refine ⟨29401369778020635881117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 313614610965553449398581 29401369778020635881117)
                ·
                  rfl

theorem cell20_193249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 5].length) (baseStart_193249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193249 prefixEnd_193249 := by exact prefixLift 193249
  have htrace : WordTrace (prefixWord ++ tailWord_193249) baseStart_193249 baseEnd_193249 := by
    simpa [prefixWord, tailWord_193249, baseEnd_193249] using wordTrace_append hprefix tailTrace_193249
  have hstable : (prefixWord ++ tailWord_193249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193249).length < 2 ^ (prefixWord ++ tailWord_193249).sum := by decide
  have hdescent : baseEnd_193249 < baseStart_193249 := by decide
  rcases family_descends (prefixWord ++ tailWord_193249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193252 : List Nat := [2, 3, 1, 1, 1, 6, 2, 1, 3]
def baseStart_193252 : Nat := 118140960795 + 193252 * 2 ^ 59
def prefixEnd_193252 : Nat := 4983230072969 + 3 ^ 40 * 193252 * 2
def baseEnd_193252 : Nat := 88205478615807230543339

theorem tailTrace_193252 : CollatzResearch.WordTrace tailWord_193252 prefixEnd_193252 88205478615807230543339 := by
  unfold tailWord_193252
  simp only [CollatzResearch.WordTrace]
  refine ⟨3524239747944241829531005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4698986330592322439374673 3524239747944241829531005)
  ·
    refine ⟨1321589905479090686074127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3524239747944241829531005 1321589905479090686074127)
    ·
      refine ⟨1982384858218636029111191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1321589905479090686074127 1982384858218636029111191)
      ·
        refine ⟨2973577287327954043666787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1982384858218636029111191 2973577287327954043666787)
        ·
          refine ⟨4460365930991931065500181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2973577287327954043666787 4460365930991931065500181)
          ·
            refine ⟨209079653015246768695321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4460365930991931065500181 209079653015246768695321)
            ·
              refine ⟨156809739761435076521491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209079653015246768695321 156809739761435076521491)
              ·
                refine ⟨235214609642152614782237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156809739761435076521491 235214609642152614782237)
                ·
                  refine ⟨88205478615807230543339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 235214609642152614782237 88205478615807230543339)
                  ·
                    rfl

theorem cell20_193252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_193252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193252 prefixEnd_193252 := by exact prefixLift 193252
  have htrace : WordTrace (prefixWord ++ tailWord_193252) baseStart_193252 baseEnd_193252 := by
    simpa [prefixWord, tailWord_193252, baseEnd_193252] using wordTrace_append hprefix tailTrace_193252
  have hstable : (prefixWord ++ tailWord_193252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193252).length < 2 ^ (prefixWord ++ tailWord_193252).sum := by decide
  have hdescent : baseEnd_193252 < baseStart_193252 := by decide
  rcases family_descends (prefixWord ++ tailWord_193252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193297 : List Nat := [1, 2, 2, 1, 1, 3, 6, 2, 2]
def baseStart_193297 : Nat := 118140960795 + 193297 * 2 ^ 59
def prefixEnd_193297 : Nat := 4983230072969 + 3 ^ 40 * 193297 * 2
def baseEnd_193297 : Nat := 88226017841987074043155

theorem tailTrace_193297 : CollatzResearch.WordTrace tailWord_193297 prefixEnd_193297 88226017841987074043155 := by
  unfold tailWord_193297
  simp only [CollatzResearch.WordTrace]
  refine ⟨7050120780725456344450145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4700080520483637562966763 7050120780725456344450145)
  ·
    refine ⟨5287590585544092258337609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7050120780725456344450145 5287590585544092258337609)
    ·
      refine ⟨3965692939158069193753207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5287590585544092258337609 3965692939158069193753207)
      ·
        refine ⟨5948539408737103790629811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3965692939158069193753207 5948539408737103790629811)
        ·
          refine ⟨8922809113105655685944717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5948539408737103790629811 8922809113105655685944717)
          ·
            refine ⟨3346053417414620882229269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8922809113105655685944717 3346053417414620882229269)
            ·
              refine ⟨156846253941310353854497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3346053417414620882229269 156846253941310353854497)
              ·
                refine ⟨117634690455982765390873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156846253941310353854497 117634690455982765390873)
                ·
                  refine ⟨88226017841987074043155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117634690455982765390873 88226017841987074043155)
                  ·
                    rfl

theorem cell20_193297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 2].length) (baseStart_193297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193297 prefixEnd_193297 := by exact prefixLift 193297
  have htrace : WordTrace (prefixWord ++ tailWord_193297) baseStart_193297 baseEnd_193297 := by
    simpa [prefixWord, tailWord_193297, baseEnd_193297] using wordTrace_append hprefix tailTrace_193297
  have hstable : (prefixWord ++ tailWord_193297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193297).length < 2 ^ (prefixWord ++ tailWord_193297).sum := by decide
  have hdescent : baseEnd_193297 < baseStart_193297 := by decide
  rcases family_descends (prefixWord ++ tailWord_193297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193301 : List Nat := [1, 3, 2, 1, 2, 2, 2, 3, 4]
def baseStart_193301 : Nat := 118140960795 + 193301 * 2 ^ 59
def prefixEnd_193301 : Nat := 4983230072969 + 3 ^ 40 * 193301 * 2
def baseEnd_193301 : Nat := 88227843550980837909805

theorem tailTrace_193301 : CollatzResearch.WordTrace tailWord_193301 prefixEnd_193301 88227843550980837909805 := by
  unfold tailWord_193301
  simp only [CollatzResearch.WordTrace]
  refine ⟨7050266672710965027595757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4700177781807310018397171 7050266672710965027595757)
  ·
    refine ⟨2643850002266611885348409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7050266672710965027595757 2643850002266611885348409)
    ·
      refine ⟨1982887501699958914011307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2643850002266611885348409 1982887501699958914011307)
      ·
        refine ⟨2974331252549938371016961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1982887501699958914011307 2974331252549938371016961)
        ·
          refine ⟨2230748439412453778262721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2974331252549938371016961 2230748439412453778262721)
          ·
            refine ⟨1673061329559340333697041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2230748439412453778262721 1673061329559340333697041)
            ·
              refine ⟨1254795997169505250272781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1673061329559340333697041 1254795997169505250272781)
              ·
                refine ⟨470548498938564468852293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1254795997169505250272781 470548498938564468852293)
                ·
                  refine ⟨88227843550980837909805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 470548498938564468852293 88227843550980837909805)
                  ·
                    rfl

theorem cell20_193301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_193301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193301 prefixEnd_193301 := by exact prefixLift 193301
  have htrace : WordTrace (prefixWord ++ tailWord_193301) baseStart_193301 baseEnd_193301 := by
    simpa [prefixWord, tailWord_193301, baseEnd_193301] using wordTrace_append hprefix tailTrace_193301
  have hstable : (prefixWord ++ tailWord_193301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193301).length < 2 ^ (prefixWord ++ tailWord_193301).sum := by decide
  have hdescent : baseEnd_193301 < baseStart_193301 := by decide
  rcases family_descends (prefixWord ++ tailWord_193301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193315 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 7]
def baseStart_193315 : Nat := 118140960795 + 193315 * 2 ^ 59
def prefixEnd_193315 : Nat := 4983230072969 + 3 ^ 40 * 193315 * 2
def baseEnd_193315 : Nat := 88234233532459011443081

theorem tailTrace_193315 : CollatzResearch.WordTrace tailWord_193315 prefixEnd_193315 88234233532459011443081 := by
  unfold tailWord_193315
  simp only [CollatzResearch.WordTrace]
  refine ⟨7050777294660245418605399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4700518196440163612403599 7050777294660245418605399)
  ·
    refine ⟨10576165941990368127908099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7050777294660245418605399 10576165941990368127908099)
    ·
      refine ⟨15864248912985552191862149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10576165941990368127908099 15864248912985552191862149)
      ·
        refine ⟨2974546671184791035974153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15864248912985552191862149 2974546671184791035974153)
        ·
          refine ⟨2230910003388593276980615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2974546671184791035974153 2230910003388593276980615)
          ·
            refine ⟨3346365005082889915470923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2230910003388593276980615 3346365005082889915470923)
            ·
              refine ⟨5019547507624334873206385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3346365005082889915470923 5019547507624334873206385)
              ·
                refine ⟨3764660630718251154904789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5019547507624334873206385 3764660630718251154904789)
                ·
                  refine ⟨88234233532459011443081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3764660630718251154904789 88234233532459011443081)
                  ·
                    rfl

theorem cell20_193315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_193315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193315 prefixEnd_193315 := by exact prefixLift 193315
  have htrace : WordTrace (prefixWord ++ tailWord_193315) baseStart_193315 baseEnd_193315 := by
    simpa [prefixWord, tailWord_193315, baseEnd_193315] using wordTrace_append hprefix tailTrace_193315
  have hstable : (prefixWord ++ tailWord_193315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193315).length < 2 ^ (prefixWord ++ tailWord_193315).sum := by decide
  have hdescent : baseEnd_193315 < baseStart_193315 := by decide
  rcases family_descends (prefixWord ++ tailWord_193315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193345 : List Nat := [1, 2, 5, 3, 1, 2, 1, 2, 3]
def baseStart_193345 : Nat := 118140960795 + 193345 * 2 ^ 59
def prefixEnd_193345 : Nat := 4983230072969 + 3 ^ 40 * 193345 * 2
def baseEnd_193345 : Nat := 88247926349912240442959

theorem tailTrace_193345 : CollatzResearch.WordTrace tailWord_193345 prefixEnd_193345 88247926349912240442959 := by
  unfold tailWord_193345
  simp only [CollatzResearch.WordTrace]
  refine ⟨7051871484551560542197489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4701247656367707028131659 7051871484551560542197489)
  ·
    refine ⟨5288903613413670406648117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7051871484551560542197489 5288903613413670406648117)
    ·
      refine ⟨495834713757531600623261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5288903613413670406648117 495834713757531600623261)
      ·
        refine ⟨185938017659074350233723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 495834713757531600623261 185938017659074350233723)
        ·
          refine ⟨278907026488611525350585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185938017659074350233723 278907026488611525350585)
          ·
            refine ⟨209180269866458644012939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278907026488611525350585 209180269866458644012939)
            ·
              refine ⟨313770404799687966019409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209180269866458644012939 313770404799687966019409)
              ·
                refine ⟨235327803599765974514557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313770404799687966019409 235327803599765974514557)
                ·
                  refine ⟨88247926349912240442959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 235327803599765974514557 88247926349912240442959)
                  ·
                    rfl

theorem cell20_193345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 3].length) (baseStart_193345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193345 prefixEnd_193345 := by exact prefixLift 193345
  have htrace : WordTrace (prefixWord ++ tailWord_193345) baseStart_193345 baseEnd_193345 := by
    simpa [prefixWord, tailWord_193345, baseEnd_193345] using wordTrace_append hprefix tailTrace_193345
  have hstable : (prefixWord ++ tailWord_193345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193345).length < 2 ^ (prefixWord ++ tailWord_193345).sum := by decide
  have hdescent : baseEnd_193345 < baseStart_193345 := by decide
  rcases family_descends (prefixWord ++ tailWord_193345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193356 : List Nat := [2, 2, 1, 3, 3, 2, 2, 1, 4]
def baseStart_193356 : Nat := 118140960795 + 193356 * 2 ^ 59
def prefixEnd_193356 : Nat := 4983230072969 + 3 ^ 40 * 193356 * 2
def baseEnd_193356 : Nat := 88252947049645091076247

theorem tailTrace_193356 : CollatzResearch.WordTrace tailWord_193356 prefixEnd_193356 88252947049645091076247 := by
  unfold tailWord_193356
  simp only [CollatzResearch.WordTrace]
  refine ⟨3526136343755854710423961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4701515125007806280565281 3526136343755854710423961)
  ·
    refine ⟨2644602257816891032817971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3526136343755854710423961 2644602257816891032817971)
    ·
      refine ⟨3966903386725336549226957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2644602257816891032817971 3966903386725336549226957)
      ·
        refine ⟨1487588770022001205960109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3966903386725336549226957 1487588770022001205960109)
        ·
          refine ⟨557845788758250452235041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1487588770022001205960109 557845788758250452235041)
          ·
            refine ⟨418384341568687839176281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 557845788758250452235041 418384341568687839176281)
            ·
              refine ⟨313788256176515879382211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418384341568687839176281 313788256176515879382211)
              ·
                refine ⟨470682384264773819073317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313788256176515879382211 470682384264773819073317)
                ·
                  refine ⟨88252947049645091076247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 470682384264773819073317 88252947049645091076247)
                  ·
                    rfl

theorem cell20_193356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_193356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193356 prefixEnd_193356 := by exact prefixLift 193356
  have htrace : WordTrace (prefixWord ++ tailWord_193356) baseStart_193356 baseEnd_193356 := by
    simpa [prefixWord, tailWord_193356, baseEnd_193356] using wordTrace_append hprefix tailTrace_193356
  have hstable : (prefixWord ++ tailWord_193356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193356).length < 2 ^ (prefixWord ++ tailWord_193356).sum := by decide
  have hdescent : baseEnd_193356 < baseStart_193356 := by decide
  rcases family_descends (prefixWord ++ tailWord_193356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193380 : List Nat := [2, 3, 1, 1, 4, 3, 2, 4]
def baseStart_193380 : Nat := 118140960795 + 193380 * 2 ^ 59
def prefixEnd_193380 : Nat := 4983230072969 + 3 ^ 40 * 193380 * 2
def baseEnd_193380 : Nat := 29421300434535891425383

theorem tailTrace_193380 : CollatzResearch.WordTrace tailWord_193380 prefixEnd_193380 29421300434535891425383 := by
  unfold tailWord_193380
  simp only [CollatzResearch.WordTrace]
  refine ⟨3526574019712380759860797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4702098692949841013147729 3526574019712380759860797)
  ·
    refine ⟨1322465257392142784947799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3526574019712380759860797 1322465257392142784947799)
    ·
      refine ⟨1983697886088214177421699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1322465257392142784947799 1983697886088214177421699)
      ·
        refine ⟨2975546829132321266132549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1983697886088214177421699 2975546829132321266132549)
        ·
          refine ⟨557915030462310237399853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2975546829132321266132549 557915030462310237399853)
          ·
            refine ⟨209218136423366339024945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 557915030462310237399853 209218136423366339024945)
            ·
              refine ⟨156913602317524754268709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209218136423366339024945 156913602317524754268709)
              ·
                refine ⟨29421300434535891425383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156913602317524754268709 29421300434535891425383)
                ·
                  rfl

theorem cell20_193380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_193380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193380 prefixEnd_193380 := by exact prefixLift 193380
  have htrace : WordTrace (prefixWord ++ tailWord_193380) baseStart_193380 baseEnd_193380 := by
    simpa [prefixWord, tailWord_193380, baseEnd_193380] using wordTrace_append hprefix tailTrace_193380
  have hstable : (prefixWord ++ tailWord_193380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193380).length < 2 ^ (prefixWord ++ tailWord_193380).sum := by decide
  have hdescent : baseEnd_193380 < baseStart_193380 := by decide
  rcases family_descends (prefixWord ++ tailWord_193380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193411 : List Nat := [1, 1, 1, 3, 4, 1, 5, 2, 2]
def baseStart_193411 : Nat := 118140960795 + 193411 * 2 ^ 59
def prefixEnd_193411 : Nat := 4983230072969 + 3 ^ 40 * 193411 * 2
def baseEnd_193411 : Nat := 88278050548309344242689

theorem tailTrace_193411 : CollatzResearch.WordTrace tailWord_193411 prefixEnd_193411 88278050548309344242689 := by
  unfold tailWord_193411
  simp only [CollatzResearch.WordTrace]
  refine ⟨7054278702312453814100087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4702852468208302542733391 7054278702312453814100087)
  ·
    refine ⟨10581418053468680721150131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7054278702312453814100087 10581418053468680721150131)
    ·
      refine ⟨15872127080203021081725197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10581418053468680721150131 15872127080203021081725197)
      ·
        refine ⟨5952047655076132905646949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15872127080203021081725197 5952047655076132905646949)
        ·
          refine ⟨1116008935326774919808803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5952047655076132905646949 1116008935326774919808803)
          ·
            refine ⟨1674013402990162379713205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116008935326774919808803 1674013402990162379713205)
            ·
              refine ⟨156938756530327723098113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1674013402990162379713205 156938756530327723098113)
              ·
                refine ⟨117704067397745792323585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156938756530327723098113 117704067397745792323585)
                ·
                  refine ⟨88278050548309344242689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117704067397745792323585 88278050548309344242689)
                  ·
                    rfl

theorem cell20_193411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 2].length) (baseStart_193411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193411 prefixEnd_193411 := by exact prefixLift 193411
  have htrace : WordTrace (prefixWord ++ tailWord_193411) baseStart_193411 baseEnd_193411 := by
    simpa [prefixWord, tailWord_193411, baseEnd_193411] using wordTrace_append hprefix tailTrace_193411
  have hstable : (prefixWord ++ tailWord_193411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193411).length < 2 ^ (prefixWord ++ tailWord_193411).sum := by decide
  have hdescent : baseEnd_193411 < baseStart_193411 := by decide
  rcases family_descends (prefixWord ++ tailWord_193411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193462 : List Nat := [5, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_193462 : Nat := 118140960795 + 193462 * 2 ^ 59
def prefixEnd_193462 : Nat := 4983230072969 + 3 ^ 40 * 193462 * 2
def baseEnd_193462 : Nat := 88301328337979833542481

theorem tailTrace_193462 : CollatzResearch.WordTrace tailWord_193462 prefixEnd_193462 88301328337979833542481 := by
  unfold tailWord_193462
  simp only [CollatzResearch.WordTrace]
  refine ⟨441008676570480595262915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4704092550085126349471093 441008676570480595262915)
  ·
    refine ⟨661513014855720892894373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 441008676570480595262915 661513014855720892894373)
    ·
      refine ⟨124033690285447667417695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 661513014855720892894373 124033690285447667417695)
      ·
        refine ⟨186050535428171501126543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124033690285447667417695 186050535428171501126543)
        ·
          refine ⟨279075803142257251689815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186050535428171501126543 279075803142257251689815)
          ·
            refine ⟨418613704713385877534723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279075803142257251689815 418613704713385877534723)
            ·
              refine ⟨627920557070078816302085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418613704713385877534723 627920557070078816302085)
              ·
                refine ⟨117735104450639778056641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 627920557070078816302085 117735104450639778056641)
                ·
                  refine ⟨88301328337979833542481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117735104450639778056641 88301328337979833542481)
                  ·
                    rfl

theorem cell20_193462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_193462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193462 prefixEnd_193462 := by exact prefixLift 193462
  have htrace : WordTrace (prefixWord ++ tailWord_193462) baseStart_193462 baseEnd_193462 := by
    simpa [prefixWord, tailWord_193462, baseEnd_193462] using wordTrace_append hprefix tailTrace_193462
  have hstable : (prefixWord ++ tailWord_193462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193462).length < 2 ^ (prefixWord ++ tailWord_193462).sum := by decide
  have hdescent : baseEnd_193462 < baseStart_193462 := by decide
  rcases family_descends (prefixWord ++ tailWord_193462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193484 : List Nat := [2, 2, 1, 4, 1, 1, 1, 5, 3]
def baseStart_193484 : Nat := 118140960795 + 193484 * 2 ^ 59
def prefixEnd_193484 : Nat := 4983230072969 + 3 ^ 40 * 193484 * 2
def baseEnd_193484 : Nat := 88311369737445534809057

theorem tailTrace_193484 : CollatzResearch.WordTrace tailWord_193484 prefixEnd_193484 88311369737445534809057 := by
  unfold tailWord_193484
  simp only [CollatzResearch.WordTrace]
  refine ⟨3528470615523993640753753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4704627487365324854338337 3528470615523993640753753)
  ·
    refine ⟨2646352961642995230565315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3528470615523993640753753 2646352961642995230565315)
    ·
      refine ⟨3969529442464492845847973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2646352961642995230565315 3969529442464492845847973)
      ·
        refine ⟨744286770462092408596495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3969529442464492845847973 744286770462092408596495)
        ·
          refine ⟨1116430155693138612894743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744286770462092408596495 1116430155693138612894743)
          ·
            refine ⟨1674645233539707919342115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116430155693138612894743 1674645233539707919342115)
            ·
              refine ⟨2511967850309561879013173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1674645233539707919342115 2511967850309561879013173)
              ·
                refine ⟨235496985966521426157485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2511967850309561879013173 235496985966521426157485)
                ·
                  refine ⟨88311369737445534809057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 235496985966521426157485 88311369737445534809057)
                  ·
                    rfl

theorem cell20_193484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_193484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193484 prefixEnd_193484 := by exact prefixLift 193484
  have htrace : WordTrace (prefixWord ++ tailWord_193484) baseStart_193484 baseEnd_193484 := by
    simpa [prefixWord, tailWord_193484, baseEnd_193484] using wordTrace_append hprefix tailTrace_193484
  have hstable : (prefixWord ++ tailWord_193484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193484).length < 2 ^ (prefixWord ++ tailWord_193484).sum := by decide
  have hdescent : baseEnd_193484 < baseStart_193484 := by decide
  rcases family_descends (prefixWord ++ tailWord_193484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193505 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 5]
def baseStart_193505 : Nat := 118140960795 + 193505 * 2 ^ 59
def prefixEnd_193505 : Nat := 4983230072969 + 3 ^ 40 * 193505 * 2
def baseEnd_193505 : Nat := 88320954709662795108971

theorem tailTrace_193505 : CollatzResearch.WordTrace tailWord_193505 prefixEnd_193505 88320954709662795108971 := by
  unfold tailWord_193505
  simp only [CollatzResearch.WordTrace]
  refine ⟨7057707163971907868021969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4705138109314605245347979 7057707163971907868021969)
  ·
    refine ⟨5293280372978930901016477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7057707163971907868021969 5293280372978930901016477)
    ·
      refine ⟨1984980139867099087881179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5293280372978930901016477 1984980139867099087881179)
      ·
        refine ⟨2977470209800648631821769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1984980139867099087881179 2977470209800648631821769)
        ·
          refine ⟨2233102657350486473866327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2977470209800648631821769 2233102657350486473866327)
          ·
            refine ⟨3349653986025729710799491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2233102657350486473866327 3349653986025729710799491)
            ·
              refine ⟨5024480979038594566199237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3349653986025729710799491 5024480979038594566199237)
              ·
                refine ⟨942090183569736481162357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5024480979038594566199237 942090183569736481162357)
                ·
                  refine ⟨88320954709662795108971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 942090183569736481162357 88320954709662795108971)
                  ·
                    rfl

theorem cell20_193505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_193505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193505 prefixEnd_193505 := by exact prefixLift 193505
  have htrace : WordTrace (prefixWord ++ tailWord_193505) baseStart_193505 baseEnd_193505 := by
    simpa [prefixWord, tailWord_193505, baseEnd_193505] using wordTrace_append hprefix tailTrace_193505
  have hstable : (prefixWord ++ tailWord_193505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193505).length < 2 ^ (prefixWord ++ tailWord_193505).sum := by decide
  have hdescent : baseEnd_193505 < baseStart_193505 := by decide
  rcases family_descends (prefixWord ++ tailWord_193505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193518 : List Nat := [4, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_193518 : Nat := 118140960795 + 193518 * 2 ^ 59
def prefixEnd_193518 : Nat := 4983230072969 + 3 ^ 40 * 193518 * 2
def baseEnd_193518 : Nat := 88326888263892527675585

theorem tailTrace_193518 : CollatzResearch.WordTrace tailWord_193518 prefixEnd_193518 88326888263892527675585 := by
  unfold tailWord_193518
  simp only [CollatzResearch.WordTrace]
  refine ⟨882272664115601386030651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4705454208616540725496805 882272664115601386030651)
  ·
    refine ⟨1323408996173402079045977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 882272664115601386030651 1323408996173402079045977)
    ·
      refine ⟨992556747130051559284483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1323408996173402079045977 992556747130051559284483)
      ·
        refine ⟨1488835120695077338926725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 992556747130051559284483 1488835120695077338926725)
        ·
          refine ⟨279156585130327001048761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1488835120695077338926725 279156585130327001048761)
          ·
            refine ⟨209367438847745250786571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279156585130327001048761 209367438847745250786571)
            ·
              refine ⟨314051158271617876179857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209367438847745250786571 314051158271617876179857)
              ·
                refine ⟨235538368703713407134893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314051158271617876179857 235538368703713407134893)
                ·
                  refine ⟨88326888263892527675585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 235538368703713407134893 88326888263892527675585)
                  ·
                    rfl

theorem cell20_193518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_193518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193518 prefixEnd_193518 := by exact prefixLift 193518
  have htrace : WordTrace (prefixWord ++ tailWord_193518) baseStart_193518 baseEnd_193518 := by
    simpa [prefixWord, tailWord_193518, baseEnd_193518] using wordTrace_append hprefix tailTrace_193518
  have hstable : (prefixWord ++ tailWord_193518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193518).length < 2 ^ (prefixWord ++ tailWord_193518).sum := by decide
  have hdescent : baseEnd_193518 < baseStart_193518 := by decide
  rcases family_descends (prefixWord ++ tailWord_193518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193529 : List Nat := [1, 2, 1, 3, 1, 3, 4, 1, 4]
def baseStart_193529 : Nat := 118140960795 + 193529 * 2 ^ 59
def prefixEnd_193529 : Nat := 4983230072969 + 3 ^ 40 * 193529 * 2
def baseEnd_193529 : Nat := 88331908963625378308873

theorem tailTrace_193529 : CollatzResearch.WordTrace tailWord_193529 prefixEnd_193529 88331908963625378308873 := by
  unfold tailWord_193529
  simp only [CollatzResearch.WordTrace]
  refine ⟨7058582515884959966895641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4705721677256639977930427 7058582515884959966895641)
  ·
    refine ⟨5293936886913719975171731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7058582515884959966895641 5293936886913719975171731)
    ·
      refine ⟨7940905330370579962757597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5293936886913719975171731 7940905330370579962757597)
      ·
        refine ⟨2977839498888967486034099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7940905330370579962757597 2977839498888967486034099)
        ·
          refine ⟨4466759248333451229051149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2977839498888967486034099 4466759248333451229051149)
          ·
            refine ⟨1675034718125044210894181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4466759248333451229051149 1675034718125044210894181)
            ·
              refine ⟨314069009648445789542659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1675034718125044210894181 314069009648445789542659)
              ·
                refine ⟨471103514472668684313989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314069009648445789542659 471103514472668684313989)
                ·
                  refine ⟨88331908963625378308873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 471103514472668684313989 88331908963625378308873)
                  ·
                    rfl

theorem cell20_193529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_193529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193529 prefixEnd_193529 := by exact prefixLift 193529
  have htrace : WordTrace (prefixWord ++ tailWord_193529) baseStart_193529 baseEnd_193529 := by
    simpa [prefixWord, tailWord_193529, baseEnd_193529] using wordTrace_append hprefix tailTrace_193529
  have hstable : (prefixWord ++ tailWord_193529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193529).length < 2 ^ (prefixWord ++ tailWord_193529).sum := by decide
  have hdescent : baseEnd_193529 < baseStart_193529 := by decide
  rcases family_descends (prefixWord ++ tailWord_193529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193626 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_193626 : Nat := 118140960795 + 193626 * 2 ^ 59
def prefixEnd_193626 : Nat := 4983230072969 + 3 ^ 40 * 193626 * 2
def baseEnd_193626 : Nat := 88376182406724152075143

theorem tailTrace_193626 : CollatzResearch.WordTrace tailWord_193626 prefixEnd_193626 88376182406724152075143 := by
  unfold tailWord_193626
  simp only [CollatzResearch.WordTrace]
  refine ⟨1765530099133386383294183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4708080264355697022117821 1765530099133386383294183)
  ·
    refine ⟨2648295148700079574941275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1765530099133386383294183 2648295148700079574941275)
    ·
      refine ⟨3972442723050119362411913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2648295148700079574941275 3972442723050119362411913)
      ·
        refine ⟨2979332042287589521808935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3972442723050119362411913 2979332042287589521808935)
        ·
          refine ⟨4468998063431384282713403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2979332042287589521808935 4468998063431384282713403)
          ·
            refine ⟨6703497095147076424070105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4468998063431384282713403 6703497095147076424070105)
            ·
              refine ⟨5027622821360307318052579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6703497095147076424070105 5027622821360307318052579)
              ·
                refine ⟨7541434232040460977078869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5027622821360307318052579 7541434232040460977078869)
                ·
                  refine ⟨88376182406724152075143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7541434232040460977078869 88376182406724152075143)
                  ·
                    rfl

theorem cell20_193626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_193626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193626 prefixEnd_193626 := by exact prefixLift 193626
  have htrace : WordTrace (prefixWord ++ tailWord_193626) baseStart_193626 baseEnd_193626 := by
    simpa [prefixWord, tailWord_193626, baseEnd_193626] using wordTrace_append hprefix tailTrace_193626
  have hstable : (prefixWord ++ tailWord_193626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193626).length < 2 ^ (prefixWord ++ tailWord_193626).sum := by decide
  have hdescent : baseEnd_193626 < baseStart_193626 := by decide
  rcases family_descends (prefixWord ++ tailWord_193626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193629 : List Nat := [1, 4, 4, 1, 2, 8]
def baseStart_193629 : Nat := 118140960795 + 193629 * 2 ^ 59
def prefixEnd_193629 : Nat := 4983230072969 + 3 ^ 40 * 193629 * 2
def baseEnd_193629 : Nat := 3273242655128499073153

theorem tailTrace_193629 : CollatzResearch.WordTrace tailWord_193629 prefixEnd_193629 3273242655128499073153 := by
  unfold tailWord_193629
  simp only [CollatzResearch.WordTrace]
  refine ⟨7062229815522677045535941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4708153210348451363690627 7062229815522677045535941)
  ·
    refine ⟨1324168090410501946037989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7062229815522677045535941 1324168090410501946037989)
    ·
      refine ⟨248281516951969114882123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1324168090410501946037989 248281516951969114882123)
      ·
        refine ⟨372422275427953672323185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248281516951969114882123 372422275427953672323185)
        ·
          refine ⟨279316706570965254242389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372422275427953672323185 279316706570965254242389)
          ·
            refine ⟨3273242655128499073153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 279316706570965254242389 3273242655128499073153)
            ·
              rfl

theorem cell20_193629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 8].length) (baseStart_193629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193629 prefixEnd_193629 := by exact prefixLift 193629
  have htrace : WordTrace (prefixWord ++ tailWord_193629) baseStart_193629 baseEnd_193629 := by
    simpa [prefixWord, tailWord_193629, baseEnd_193629] using wordTrace_append hprefix tailTrace_193629
  have hstable : (prefixWord ++ tailWord_193629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193629).length < 2 ^ (prefixWord ++ tailWord_193629).sum := by decide
  have hdescent : baseEnd_193629 < baseStart_193629 := by decide
  rcases family_descends (prefixWord ++ tailWord_193629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193639 : List Nat := [1, 1, 5, 1, 1, 3, 4, 2, 2]
def baseStart_193639 : Nat := 118140960795 + 193639 * 2 ^ 59
def prefixEnd_193639 : Nat := 4983230072969 + 3 ^ 40 * 193639 * 2
def baseEnd_193639 : Nat := 88382115960953884641757

theorem tailTrace_193639 : CollatzResearch.WordTrace tailWord_193639 prefixEnd_193639 88382115960953884641757 := by
  unfold tailWord_193639
  simp only [CollatzResearch.WordTrace]
  refine ⟨7062594545486448753399971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4708396363657632502266647 7062594545486448753399971)
  ·
    refine ⟨10593891818229673130099957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7062594545486448753399971 10593891818229673130099957)
    ·
      refine ⟨993177357959031855946871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10593891818229673130099957 993177357959031855946871)
      ·
        refine ⟨1489766036938547783920307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 993177357959031855946871 1489766036938547783920307)
        ·
          refine ⟨2234649055407821675880461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1489766036938547783920307 2234649055407821675880461)
          ·
            refine ⟨837993395777933128455173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2234649055407821675880461 837993395777933128455173)
            ·
              refine ⟨157123761708362461585345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 837993395777933128455173 157123761708362461585345)
              ·
                refine ⟨117842821281271846189009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157123761708362461585345 117842821281271846189009)
                ·
                  refine ⟨88382115960953884641757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117842821281271846189009 88382115960953884641757)
                  ·
                    rfl

theorem cell20_193639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 2].length) (baseStart_193639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193639 prefixEnd_193639 := by exact prefixLift 193639
  have htrace : WordTrace (prefixWord ++ tailWord_193639) baseStart_193639 baseEnd_193639 := by
    simpa [prefixWord, tailWord_193639, baseEnd_193639] using wordTrace_append hprefix tailTrace_193639
  have hstable : (prefixWord ++ tailWord_193639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193639).length < 2 ^ (prefixWord ++ tailWord_193639).sum := by decide
  have hdescent : baseEnd_193639 < baseStart_193639 := by decide
  rcases family_descends (prefixWord ++ tailWord_193639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193664 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 6]
def baseStart_193664 : Nat := 118140960795 + 193664 * 2 ^ 59
def prefixEnd_193664 : Nat := 4983230072969 + 3 ^ 40 * 193664 * 2
def baseEnd_193664 : Nat := 88393526642164908808321

theorem tailTrace_193664 : CollatzResearch.WordTrace tailWord_193664 prefixEnd_193664 88393526642164908808321 := by
  unfold tailWord_193664
  simp only [CollatzResearch.WordTrace]
  refine ⟨3531753185197939011530023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4709004246930585348706697 3531753185197939011530023)
  ·
    refine ⟨5297629777796908517295035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3531753185197939011530023 5297629777796908517295035)
    ·
      refine ⟨7946444666695362775942553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5297629777796908517295035 7946444666695362775942553)
      ·
        refine ⟨5959833500021522081956915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7946444666695362775942553 5959833500021522081956915)
        ·
          refine ⟨8939750250032283122935373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5959833500021522081956915 8939750250032283122935373)
          ·
            refine ⟨3352406343762106171100765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8939750250032283122935373 3352406343762106171100765)
            ·
              refine ⟨1257152378910789814162787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3352406343762106171100765 1257152378910789814162787)
              ·
                refine ⟨1885728568366184721244181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1257152378910789814162787 1885728568366184721244181)
                ·
                  refine ⟨88393526642164908808321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1885728568366184721244181 88393526642164908808321)
                  ·
                    rfl

theorem cell20_193664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_193664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193664 prefixEnd_193664 := by exact prefixLift 193664
  have htrace : WordTrace (prefixWord ++ tailWord_193664) baseStart_193664 baseEnd_193664 := by
    simpa [prefixWord, tailWord_193664, baseEnd_193664] using wordTrace_append hprefix tailTrace_193664
  have hstable : (prefixWord ++ tailWord_193664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193664).length < 2 ^ (prefixWord ++ tailWord_193664).sum := by decide
  have hdescent : baseEnd_193664 < baseStart_193664 := by decide
  rcases family_descends (prefixWord ++ tailWord_193664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193688 : List Nat := [2, 1, 2, 4, 2, 2, 7]
def baseStart_193688 : Nat := 118140960795 + 193688 * 2 ^ 59
def prefixEnd_193688 : Nat := 4983230072969 + 3 ^ 40 * 193688 * 2
def baseEnd_193688 : Nat := 9822720099569721334247

theorem tailTrace_193688 : CollatzResearch.WordTrace tailWord_193688 prefixEnd_193688 9822720099569721334247 := by
  unfold tailWord_193688
  simp only [CollatzResearch.WordTrace]
  refine ⟨3532190861154465060966859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4709587814872620081289145 3532190861154465060966859)
  ·
    refine ⟨5298286291731697591450289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3532190861154465060966859 5298286291731697591450289)
    ·
      refine ⟨3973714718798773193587717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5298286291731697591450289 3973714718798773193587717)
      ·
        refine ⟨745071509774769973797697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3973714718798773193587717 745071509774769973797697)
        ·
          refine ⟨558803632331077480348273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 745071509774769973797697 558803632331077480348273)
          ·
            refine ⟨419102724248308110261205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 558803632331077480348273 419102724248308110261205)
            ·
              refine ⟨9822720099569721334247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 419102724248308110261205 9822720099569721334247)
              ·
                rfl

theorem cell20_193688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 7].length) (baseStart_193688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193688 prefixEnd_193688 := by exact prefixLift 193688
  have htrace : WordTrace (prefixWord ++ tailWord_193688) baseStart_193688 baseEnd_193688 := by
    simpa [prefixWord, tailWord_193688, baseEnd_193688] using wordTrace_append hprefix tailTrace_193688
  have hstable : (prefixWord ++ tailWord_193688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193688).length < 2 ^ (prefixWord ++ tailWord_193688).sum := by decide
  have hdescent : baseEnd_193688 < baseStart_193688 := by decide
  rcases family_descends (prefixWord ++ tailWord_193688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193718 : List Nat := [5, 1, 3, 2, 1, 2, 2, 4]
def baseStart_193718 : Nat := 118140960795 + 193718 * 2 ^ 59
def prefixEnd_193718 : Nat := 4983230072969 + 3 ^ 40 * 193718 * 2
def baseEnd_193718 : Nat := 29472724571193573669367

theorem tailTrace_193718 : CollatzResearch.WordTrace tailWord_193718 prefixEnd_193718 29472724571193573669367 := by
  unfold tailWord_193718
  simp only [CollatzResearch.WordTrace]
  refine ⟨441592244512515327845363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4710317274800163497017205 441592244512515327845363)
  ·
    refine ⟨662388366768772991768045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 441592244512515327845363 662388366768772991768045)
    ·
      refine ⟨248395637538289871913017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 662388366768772991768045 248395637538289871913017)
      ·
        refine ⟨186296728153717403934763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248395637538289871913017 186296728153717403934763)
        ·
          refine ⟨279445092230576105902145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186296728153717403934763 279445092230576105902145)
          ·
            refine ⟨209583819172932079426609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279445092230576105902145 209583819172932079426609)
            ·
              refine ⟨157187864379699059569957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209583819172932079426609 157187864379699059569957)
              ·
                refine ⟨29472724571193573669367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157187864379699059569957 29472724571193573669367)
                ·
                  rfl

theorem cell20_193718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_193718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193718 prefixEnd_193718 := by exact prefixLift 193718
  have htrace : WordTrace (prefixWord ++ tailWord_193718) baseStart_193718 baseEnd_193718 := by
    simpa [prefixWord, tailWord_193718, baseEnd_193718] using wordTrace_append hprefix tailTrace_193718
  have hstable : (prefixWord ++ tailWord_193718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193718).length < 2 ^ (prefixWord ++ tailWord_193718).sum := by decide
  have hdescent : baseEnd_193718 < baseStart_193718 := by decide
  rcases family_descends (prefixWord ++ tailWord_193718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193732 : List Nat := [2, 3, 3, 1, 3, 2, 1, 3, 2]
def baseStart_193732 : Nat := 118140960795 + 193732 * 2 ^ 59
def prefixEnd_193732 : Nat := 4983230072969 + 3 ^ 40 * 193732 * 2
def baseEnd_193732 : Nat := 88424563695058894541377

theorem tailTrace_193732 : CollatzResearch.WordTrace tailWord_193732 prefixEnd_193732 88424563695058894541377 := by
  unfold tailWord_193732
  simp only [CollatzResearch.WordTrace]
  refine ⟨3532993267074762818267725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4710657689433017091023633 3532993267074762818267725)
  ·
    refine ⟨1324872475153036056850397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3532993267074762818267725 1324872475153036056850397)
    ·
      refine ⟨496827178182388521318899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1324872475153036056850397 496827178182388521318899)
      ·
        refine ⟨745240767273582781978349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496827178182388521318899 745240767273582781978349)
        ·
          refine ⟨279465287727593543241881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 745240767273582781978349 279465287727593543241881)
          ·
            refine ⟨209598965795695157431411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279465287727593543241881 209598965795695157431411)
            ·
              refine ⟨314398448693542736147117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209598965795695157431411 314398448693542736147117)
              ·
                refine ⟨117899418260078526055169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314398448693542736147117 117899418260078526055169)
                ·
                  refine ⟨88424563695058894541377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117899418260078526055169 88424563695058894541377)
                  ·
                    rfl

theorem cell20_193732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_193732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193732 prefixEnd_193732 := by exact prefixLift 193732
  have htrace : WordTrace (prefixWord ++ tailWord_193732) baseStart_193732 baseEnd_193732 := by
    simpa [prefixWord, tailWord_193732, baseEnd_193732] using wordTrace_append hprefix tailTrace_193732
  have hstable : (prefixWord ++ tailWord_193732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193732).length < 2 ^ (prefixWord ++ tailWord_193732).sum := by decide
  have hdescent : baseEnd_193732 < baseStart_193732 := by decide
  rcases family_descends (prefixWord ++ tailWord_193732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193736 : List Nat := [2, 1, 3, 1, 2, 1, 5, 3, 2]
def baseStart_193736 : Nat := 118140960795 + 193736 * 2 ^ 59
def prefixEnd_193736 : Nat := 4983230072969 + 3 ^ 40 * 193736 * 2
def baseEnd_193736 : Nat := 88426389404052658408027

theorem tailTrace_193736 : CollatzResearch.WordTrace tailWord_193736 prefixEnd_193736 88426389404052658408027 := by
  unfold tailWord_193736
  simp only [CollatzResearch.WordTrace]
  refine ⟨3533066213067517159840531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4710754950756689546454041 3533066213067517159840531)
  ·
    refine ⟨5299599319601275739760797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3533066213067517159840531 5299599319601275739760797)
    ·
      refine ⟨1987349744850478402410299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5299599319601275739760797 1987349744850478402410299)
      ·
        refine ⟨2981024617275717603615449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1987349744850478402410299 2981024617275717603615449)
        ·
          refine ⟨2235768462956788202711587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2981024617275717603615449 2235768462956788202711587)
          ·
            refine ⟨3353652694435182304067381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235768462956788202711587 3353652694435182304067381)
            ·
              refine ⟨314404940103298341006317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3353652694435182304067381 314404940103298341006317)
              ·
                refine ⟨117901852538736877877369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314404940103298341006317 117901852538736877877369)
                ·
                  refine ⟨88426389404052658408027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117901852538736877877369 88426389404052658408027)
                  ·
                    rfl

theorem cell20_193736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 3, 2].length) (baseStart_193736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193736 prefixEnd_193736 := by exact prefixLift 193736
  have htrace : WordTrace (prefixWord ++ tailWord_193736) baseStart_193736 baseEnd_193736 := by
    simpa [prefixWord, tailWord_193736, baseEnd_193736] using wordTrace_append hprefix tailTrace_193736
  have hstable : (prefixWord ++ tailWord_193736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193736).length < 2 ^ (prefixWord ++ tailWord_193736).sum := by decide
  have hdescent : baseEnd_193736 < baseStart_193736 := by decide
  rcases family_descends (prefixWord ++ tailWord_193736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193767 : List Nat := [1, 1, 5, 3, 2, 1, 1, 3, 3]
def baseStart_193767 : Nat := 118140960795 + 193767 * 2 ^ 59
def prefixEnd_193767 : Nat := 4983230072969 + 3 ^ 40 * 193767 * 2
def baseEnd_193767 : Nat := 88440538648754328374567

theorem tailTrace_193767 : CollatzResearch.WordTrace tailWord_193767 prefixEnd_193767 88440538648754328374567 := by
  unfold tailWord_193767
  simp only [CollatzResearch.WordTrace]
  refine ⟨7067263089022726614059555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4711508726015151076039703 7067263089022726614059555)
  ·
    refine ⟨10600894633534089921089333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7067263089022726614059555 10600894633534089921089333)
    ·
      refine ⟨993833871893820930102125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10600894633534089921089333 993833871893820930102125)
      ·
        refine ⟨372687701960182848788297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 993833871893820930102125 372687701960182848788297)
        ·
          refine ⟨279515776470137136591223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372687701960182848788297 279515776470137136591223)
          ·
            refine ⟨419273664705205704886835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279515776470137136591223 419273664705205704886835)
            ·
              refine ⟨628910497057808557330253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419273664705205704886835 628910497057808557330253)
              ·
                refine ⟨235841436396678208998845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 628910497057808557330253 235841436396678208998845)
                ·
                  refine ⟨88440538648754328374567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 235841436396678208998845 88440538648754328374567)
                  ·
                    rfl

theorem cell20_193767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 3].length) (baseStart_193767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193767 prefixEnd_193767 := by exact prefixLift 193767
  have htrace : WordTrace (prefixWord ++ tailWord_193767) baseStart_193767 baseEnd_193767 := by
    simpa [prefixWord, tailWord_193767, baseEnd_193767] using wordTrace_append hprefix tailTrace_193767
  have hstable : (prefixWord ++ tailWord_193767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193767).length < 2 ^ (prefixWord ++ tailWord_193767).sum := by decide
  have hdescent : baseEnd_193767 < baseStart_193767 := by decide
  rcases family_descends (prefixWord ++ tailWord_193767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193785 : List Nat := [1, 2, 1, 3, 1, 1, 3, 8]
def baseStart_193785 : Nat := 118140960795 + 193785 * 2 ^ 59
def prefixEnd_193785 : Nat := 4983230072969 + 3 ^ 40 * 193785 * 2
def baseEnd_193785 : Nat := 29482918113075421924831

theorem tailTrace_193785 : CollatzResearch.WordTrace tailWord_193785 prefixEnd_193785 29482918113075421924831 := by
  unfold tailWord_193785
  simp only [CollatzResearch.WordTrace]
  refine ⟨7067919602957515688214809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4711946401971677125476539 7067919602957515688214809)
  ·
    refine ⟨5300939702218136766161107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7067919602957515688214809 5300939702218136766161107)
    ·
      refine ⟨7951409553327205149241661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5300939702218136766161107 7951409553327205149241661)
      ·
        refine ⟨2981778582497701930965623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7951409553327205149241661 2981778582497701930965623)
        ·
          refine ⟨4472667873746552896448435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2981778582497701930965623 4472667873746552896448435)
          ·
            refine ⟨6709001810619829344672653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4472667873746552896448435 6709001810619829344672653)
            ·
              refine ⟨2515875678982436004252245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6709001810619829344672653 2515875678982436004252245)
              ·
                refine ⟨29482918113075421924831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2515875678982436004252245 29482918113075421924831)
                ·
                  rfl

theorem cell20_193785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 8].length) (baseStart_193785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193785 prefixEnd_193785 := by exact prefixLift 193785
  have htrace : WordTrace (prefixWord ++ tailWord_193785) baseStart_193785 baseEnd_193785 := by
    simpa [prefixWord, tailWord_193785, baseEnd_193785] using wordTrace_append hprefix tailTrace_193785
  have hstable : (prefixWord ++ tailWord_193785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193785).length < 2 ^ (prefixWord ++ tailWord_193785).sum := by decide
  have hdescent : baseEnd_193785 < baseStart_193785 := by decide
  rcases family_descends (prefixWord ++ tailWord_193785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193840 : List Nat := [2, 1, 1, 1, 2, 2, 7, 4]
def baseStart_193840 : Nat := 118140960795 + 193840 * 2 ^ 59
def prefixEnd_193840 : Nat := 4983230072969 + 3 ^ 40 * 193840 * 2
def baseEnd_193840 : Nat := 29491285945963506313645

theorem tailTrace_193840 : CollatzResearch.WordTrace tailWord_193840 prefixEnd_193840 29491285945963506313645 := by
  unfold tailWord_193840
  simp only [CollatzResearch.WordTrace]
  refine ⟨3534962808879130040733487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4713283745172173387644649 3534962808879130040733487)
  ·
    refine ⟨5302444213318695061100231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3534962808879130040733487 5302444213318695061100231)
    ·
      refine ⟨7953666319978042591650347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5302444213318695061100231 7953666319978042591650347)
      ·
        refine ⟨11930499479967063887475521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7953666319978042591650347 11930499479967063887475521)
        ·
          refine ⟨8947874609975297915606641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11930499479967063887475521 8947874609975297915606641)
          ·
            refine ⟨6710905957481473436704981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8947874609975297915606641 6710905957481473436704981)
            ·
              refine ⟨157286858378472033672773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 6710905957481473436704981 157286858378472033672773)
              ·
                refine ⟨29491285945963506313645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157286858378472033672773 29491285945963506313645)
                ·
                  rfl

theorem cell20_193840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_193840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193840 prefixEnd_193840 := by exact prefixLift 193840
  have htrace : WordTrace (prefixWord ++ tailWord_193840) baseStart_193840 baseEnd_193840 := by
    simpa [prefixWord, tailWord_193840, baseEnd_193840] using wordTrace_append hprefix tailTrace_193840
  have hstable : (prefixWord ++ tailWord_193840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193840).length < 2 ^ (prefixWord ++ tailWord_193840).sum := by decide
  have hdescent : baseEnd_193840 < baseStart_193840 := by decide
  rcases family_descends (prefixWord ++ tailWord_193840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193850 : List Nat := [3, 1, 1, 1, 4, 1, 4, 3, 2]
def baseStart_193850 : Nat := 118140960795 + 193850 * 2 ^ 59
def prefixEnd_193850 : Nat := 4983230072969 + 3 ^ 40 * 193850 * 2
def baseEnd_193850 : Nat := 88478422110374928607561

theorem tailTrace_193850 : CollatzResearch.WordTrace tailWord_193850 prefixEnd_193850 88478422110374928607561 := by
  unfold tailWord_193850
  simp only [CollatzResearch.WordTrace]
  refine ⟨1767572586930507947332751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4713526898481354526220669 1767572586930507947332751)
  ·
    refine ⟨2651358880395761920999127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1767572586930507947332751 2651358880395761920999127)
    ·
      refine ⟨3977038320593642881498691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2651358880395761920999127 3977038320593642881498691)
      ·
        refine ⟨5965557480890464322248037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3977038320593642881498691 5965557480890464322248037)
        ·
          refine ⟨1118542027666962060421507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5965557480890464322248037 1118542027666962060421507)
          ·
            refine ⟨1677813041500443090632261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118542027666962060421507 1677813041500443090632261)
            ·
              refine ⟨314589945281333079493549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1677813041500443090632261 314589945281333079493549)
              ·
                refine ⟨117971229480499904810081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314589945281333079493549 117971229480499904810081)
                ·
                  refine ⟨88478422110374928607561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117971229480499904810081 88478422110374928607561)
                  ·
                    rfl

theorem cell20_193850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_193850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193850 prefixEnd_193850 := by exact prefixLift 193850
  have htrace : WordTrace (prefixWord ++ tailWord_193850) baseStart_193850 baseEnd_193850 := by
    simpa [prefixWord, tailWord_193850, baseEnd_193850] using wordTrace_append hprefix tailTrace_193850
  have hstable : (prefixWord ++ tailWord_193850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193850).length < 2 ^ (prefixWord ++ tailWord_193850).sum := by decide
  have hdescent : baseEnd_193850 < baseStart_193850 := by decide
  rcases family_descends (prefixWord ++ tailWord_193850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193860 : List Nat := [2, 3, 4, 1, 1, 3, 1, 2, 3]
def baseStart_193860 : Nat := 118140960795 + 193860 * 2 ^ 59
def prefixEnd_193860 : Nat := 4983230072969 + 3 ^ 40 * 193860 * 2
def baseEnd_193860 : Nat := 88482986382859338274187

theorem tailTrace_193860 : CollatzResearch.WordTrace tailWord_193860 prefixEnd_193860 88482986382859338274187 := by
  unfold tailWord_193860
  simp only [CollatzResearch.WordTrace]
  refine ⟨3535327538842901748597517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4713770051790535664796689 3535327538842901748597517)
  ·
    refine ⟨1325747827066088155724069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3535327538842901748597517 1325747827066088155724069)
    ·
      refine ⟨248577717574891529198263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1325747827066088155724069 248577717574891529198263)
      ·
        refine ⟨372866576362337293797395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248577717574891529198263 372866576362337293797395)
        ·
          refine ⟨559299864543505940696093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372866576362337293797395 559299864543505940696093)
          ·
            refine ⟨209737449203814727761035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 559299864543505940696093 209737449203814727761035)
            ·
              refine ⟨314606173805722091641553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209737449203814727761035 314606173805722091641553)
              ·
                refine ⟨235954630354291568731165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314606173805722091641553 235954630354291568731165)
                ·
                  refine ⟨88482986382859338274187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 235954630354291568731165 88482986382859338274187)
                  ·
                    rfl

theorem cell20_193860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_193860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193860 prefixEnd_193860 := by exact prefixLift 193860
  have htrace : WordTrace (prefixWord ++ tailWord_193860) baseStart_193860 baseEnd_193860 := by
    simpa [prefixWord, tailWord_193860, baseEnd_193860] using wordTrace_append hprefix tailTrace_193860
  have hstable : (prefixWord ++ tailWord_193860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193860).length < 2 ^ (prefixWord ++ tailWord_193860).sum := by decide
  have hdescent : baseEnd_193860 < baseStart_193860 := by decide
  rcases family_descends (prefixWord ++ tailWord_193860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193923 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 5]
def baseStart_193923 : Nat := 118140960795 + 193923 * 2 ^ 59
def prefixEnd_193923 : Nat := 4983230072969 + 3 ^ 40 * 193923 * 2
def baseEnd_193923 : Nat := 88511741299511119173929

theorem tailTrace_193923 : CollatzResearch.WordTrace tailWord_193923 prefixEnd_193923 88511741299511119173929 := by
  unfold tailWord_193923
  simp only [CollatzResearch.WordTrace]
  refine ⟨7072952876457565256738423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4715301917638376837825615 7072952876457565256738423)
  ·
    refine ⟨10609429314686347885107635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7072952876457565256738423 10609429314686347885107635)
    ·
      refine ⟨15914143972029521827661453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10609429314686347885107635 15914143972029521827661453)
      ·
        refine ⟨5967803989511070685373045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15914143972029521827661453 5967803989511070685373045)
        ·
          refine ⟨559481624016662876753723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5967803989511070685373045 559481624016662876753723)
          ·
            refine ⟨839222436024994315130585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559481624016662876753723 839222436024994315130585)
            ·
              refine ⟨629416827018745736347939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839222436024994315130585 629416827018745736347939)
              ·
                refine ⟨944125240528118604521909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 629416827018745736347939 944125240528118604521909)
                ·
                  refine ⟨88511741299511119173929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 944125240528118604521909 88511741299511119173929)
                  ·
                    rfl

theorem cell20_193923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_193923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193923 prefixEnd_193923 := by exact prefixLift 193923
  have htrace : WordTrace (prefixWord ++ tailWord_193923) baseStart_193923 baseEnd_193923 := by
    simpa [prefixWord, tailWord_193923, baseEnd_193923] using wordTrace_append hprefix tailTrace_193923
  have hstable : (prefixWord ++ tailWord_193923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193923).length < 2 ^ (prefixWord ++ tailWord_193923).sum := by decide
  have hdescent : baseEnd_193923 < baseStart_193923 := by decide
  rcases family_descends (prefixWord ++ tailWord_193923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193954 : List Nat := [3, 3, 1, 2, 1, 2, 2, 6]
def baseStart_193954 : Nat := 118140960795 + 193954 * 2 ^ 59
def prefixEnd_193954 : Nat := 4983230072969 + 3 ^ 40 * 193954 * 2
def baseEnd_193954 : Nat := 29508630181404263046823

theorem tailTrace_193954 : CollatzResearch.WordTrace tailWord_193954 prefixEnd_193954 29508630181404263046823 := by
  unfold tailWord_193954
  simp only [CollatzResearch.WordTrace]
  refine ⟨1768520884836314387779229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4716055692896838367411277 1768520884836314387779229)
  ·
    refine ⟨663195331813617895417211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1768520884836314387779229 663195331813617895417211)
    ·
      refine ⟨994792997720426843125817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 663195331813617895417211 994792997720426843125817)
      ·
        refine ⟨746094748290320132344363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 994792997720426843125817 746094748290320132344363)
        ·
          refine ⟨1119142122435480198516545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746094748290320132344363 1119142122435480198516545)
          ·
            refine ⟨839356591826610148887409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1119142122435480198516545 839356591826610148887409)
            ·
              refine ⟨629517443869957611665557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839356591826610148887409 629517443869957611665557)
              ·
                refine ⟨29508630181404263046823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 629517443869957611665557 29508630181404263046823)
                ·
                  rfl

theorem cell20_193954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_193954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193954 prefixEnd_193954 := by exact prefixLift 193954
  have htrace : WordTrace (prefixWord ++ tailWord_193954) baseStart_193954 baseEnd_193954 := by
    simpa [prefixWord, tailWord_193954, baseEnd_193954] using wordTrace_append hprefix tailTrace_193954
  have hstable : (prefixWord ++ tailWord_193954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193954).length < 2 ^ (prefixWord ++ tailWord_193954).sum := by decide
  have hdescent : baseEnd_193954 < baseStart_193954 := by decide
  rcases family_descends (prefixWord ++ tailWord_193954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193999 : List Nat := [1, 1, 2, 1, 1, 4, 4, 3, 3]
def baseStart_193999 : Nat := 118140960795 + 193999 * 2 ^ 59
def prefixEnd_193999 : Nat := 4983230072969 + 3 ^ 40 * 193999 * 2
def baseEnd_193999 : Nat := 88546429770392632640285

theorem tailTrace_193999 : CollatzResearch.WordTrace tailWord_193999 prefixEnd_193999 88546429770392632640285 := by
  unfold tailWord_193999
  simp only [CollatzResearch.WordTrace]
  refine ⟨7075724824182230236505051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4717149882788153491003367 7075724824182230236505051)
  ·
    refine ⟨10613587236273345354757577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7075724824182230236505051 10613587236273345354757577)
    ·
      refine ⟨7960190427205009016068183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10613587236273345354757577 7960190427205009016068183)
      ·
        refine ⟨11940285640807513524102275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7960190427205009016068183 11940285640807513524102275)
        ·
          refine ⟨17910428461211270286153413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11940285640807513524102275 17910428461211270286153413)
          ·
            refine ⟨3358205336477113178653765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17910428461211270286153413 3358205336477113178653765)
            ·
              refine ⟨629663500589458720997581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3358205336477113178653765 629663500589458720997581)
              ·
                refine ⟨236123812721047020374093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 629663500589458720997581 236123812721047020374093)
                ·
                  refine ⟨88546429770392632640285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236123812721047020374093 88546429770392632640285)
                  ·
                    rfl

theorem cell20_193999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 3].length) (baseStart_193999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_193999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_193999 prefixEnd_193999 := by exact prefixLift 193999
  have htrace : WordTrace (prefixWord ++ tailWord_193999) baseStart_193999 baseEnd_193999 := by
    simpa [prefixWord, tailWord_193999, baseEnd_193999] using wordTrace_append hprefix tailTrace_193999
  have hstable : (prefixWord ++ tailWord_193999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193999).length < 2 ^ (prefixWord ++ tailWord_193999).sum := by decide
  have hdescent : baseEnd_193999 < baseStart_193999 := by decide
  rcases family_descends (prefixWord ++ tailWord_193999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194044 : List Nat := [2, 2, 2, 1, 2, 1, 3, 3, 4]
def baseStart_194044 : Nat := 118140960795 + 194044 * 2 ^ 59
def prefixEnd_194044 : Nat := 4983230072969 + 3 ^ 40 * 194044 * 2
def baseEnd_194044 : Nat := 88566968996572476140101

theorem tailTrace_194044 : CollatzResearch.WordTrace tailWord_194044 prefixEnd_194044 88566968996572476140101 := by
  unfold tailWord_194044
  simp only [CollatzResearch.WordTrace]
  refine ⟨3538683054509601460946593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4718244072679468614595457 3538683054509601460946593)
  ·
    refine ⟨2654012290882201095709945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3538683054509601460946593 2654012290882201095709945)
    ·
      refine ⟨1990509218161650821782459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2654012290882201095709945 1990509218161650821782459)
      ·
        refine ⟨2985763827242476232673689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1990509218161650821782459 2985763827242476232673689)
        ·
          refine ⟨2239322870431857174505267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2985763827242476232673689 2239322870431857174505267)
          ·
            refine ⟨3358984305647785761757901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2239322870431857174505267 3358984305647785761757901)
            ·
              refine ⟨1259619114617919660659213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3358984305647785761757901 1259619114617919660659213)
              ·
                refine ⟨472357167981719872747205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1259619114617919660659213 472357167981719872747205)
                ·
                  refine ⟨88566968996572476140101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 472357167981719872747205 88566968996572476140101)
                  ·
                    rfl

theorem cell20_194044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_194044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194044 prefixEnd_194044 := by exact prefixLift 194044
  have htrace : WordTrace (prefixWord ++ tailWord_194044) baseStart_194044 baseEnd_194044 := by
    simpa [prefixWord, tailWord_194044, baseEnd_194044] using wordTrace_append hprefix tailTrace_194044
  have hstable : (prefixWord ++ tailWord_194044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194044).length < 2 ^ (prefixWord ++ tailWord_194044).sum := by decide
  have hdescent : baseEnd_194044 < baseStart_194044 := by decide
  rcases family_descends (prefixWord ++ tailWord_194044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194050 : List Nat := [3, 4, 1, 2, 1, 2, 3, 1, 3]
def baseStart_194050 : Nat := 118140960795 + 194050 * 2 ^ 59
def prefixEnd_194050 : Nat := 4983230072969 + 3 ^ 40 * 194050 * 2
def baseEnd_194050 : Nat := 88569707560063121940077

theorem tailTrace_194050 : CollatzResearch.WordTrace tailWord_194050 prefixEnd_194050 88569707560063121940077 := by
  unfold tailWord_194050
  simp only [CollatzResearch.WordTrace]
  refine ⟨1769396236749366486652901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4718389964664977297741069 1769396236749366486652901)
  ·
    refine ⟨331761794390506216247419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1769396236749366486652901 331761794390506216247419)
    ·
      refine ⟨497642691585759324371129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331761794390506216247419 497642691585759324371129)
      ·
        refine ⟨373232018689319493278347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 497642691585759324371129 373232018689319493278347)
        ·
          refine ⟨559848028033979239917521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373232018689319493278347 559848028033979239917521)
          ·
            refine ⟨419886021025484429938141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 559848028033979239917521 419886021025484429938141)
            ·
              refine ⟨157457257884556661226803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 419886021025484429938141 157457257884556661226803)
              ·
                refine ⟨236185886826834991840205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157457257884556661226803 236185886826834991840205)
                ·
                  refine ⟨88569707560063121940077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236185886826834991840205 88569707560063121940077)
                  ·
                    rfl

theorem cell20_194050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_194050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194050 prefixEnd_194050 := by exact prefixLift 194050
  have htrace : WordTrace (prefixWord ++ tailWord_194050) baseStart_194050 baseEnd_194050 := by
    simpa [prefixWord, tailWord_194050, baseEnd_194050] using wordTrace_append hprefix tailTrace_194050
  have hstable : (prefixWord ++ tailWord_194050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194050).length < 2 ^ (prefixWord ++ tailWord_194050).sum := by decide
  have hdescent : baseEnd_194050 < baseStart_194050 := by decide
  rcases family_descends (prefixWord ++ tailWord_194050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194082 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_194082 : Nat := 118140960795 + 194082 * 2 ^ 59
def prefixEnd_194082 : Nat := 4983230072969 + 3 ^ 40 * 194082 * 2
def baseEnd_194082 : Nat := 88584313232013232873279

theorem tailTrace_194082 : CollatzResearch.WordTrace tailWord_194082 prefixEnd_194082 88584313232013232873279 := by
  unfold tailWord_194082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1769688020720383852944125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4719168055254356941184333 1769688020720383852944125)
  ·
    refine ⟨663633007770143944854047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1769688020720383852944125 663633007770143944854047)
    ·
      refine ⟨995449511655215917281071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 663633007770143944854047 995449511655215917281071)
      ·
        refine ⟨1493174267482823875921607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 995449511655215917281071 1493174267482823875921607)
        ·
          refine ⟨2239761401224235813882411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1493174267482823875921607 2239761401224235813882411)
          ·
            refine ⟨3359642101836353720823617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2239761401224235813882411 3359642101836353720823617)
            ·
              refine ⟨2519731576377265290617713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3359642101836353720823617 2519731576377265290617713)
              ·
                refine ⟨1889798682282948967963285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2519731576377265290617713 1889798682282948967963285)
                ·
                  refine ⟨88584313232013232873279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1889798682282948967963285 88584313232013232873279)
                  ·
                    rfl

theorem cell20_194082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_194082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194082 prefixEnd_194082 := by exact prefixLift 194082
  have htrace : WordTrace (prefixWord ++ tailWord_194082) baseStart_194082 baseEnd_194082 := by
    simpa [prefixWord, tailWord_194082, baseEnd_194082] using wordTrace_append hprefix tailTrace_194082
  have hstable : (prefixWord ++ tailWord_194082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194082).length < 2 ^ (prefixWord ++ tailWord_194082).sum := by decide
  have hdescent : baseEnd_194082 < baseStart_194082 := by decide
  rcases family_descends (prefixWord ++ tailWord_194082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194099 : List Nat := [1, 1, 1, 2, 4, 5, 1, 1, 4]
def baseStart_194099 : Nat := 118140960795 + 194099 * 2 ^ 59
def prefixEnd_194099 : Nat := 4983230072969 + 3 ^ 40 * 194099 * 2
def baseEnd_194099 : Nat := 88592072495236729306543

theorem tailTrace_194099 : CollatzResearch.WordTrace tailWord_194099 prefixEnd_194099 88592072495236729306543 := by
  unfold tailWord_194099
  simp only [CollatzResearch.WordTrace]
  refine ⟨7079372123819947315145351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4719581415879964876763567 7079372123819947315145351)
  ·
    refine ⟨10619058185729920972718027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7079372123819947315145351 10619058185729920972718027)
    ·
      refine ⟨15928587278594881459077041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10619058185729920972718027 15928587278594881459077041)
      ·
        refine ⟨11946440458946161094307781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15928587278594881459077041 11946440458946161094307781)
        ·
          refine ⟨2239957586052405205182709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11946440458946161094307781 2239957586052405205182709)
          ·
            refine ⟨209996023692412987985879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2239957586052405205182709 209996023692412987985879)
            ·
              refine ⟨314994035538619481978819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209996023692412987985879 314994035538619481978819)
              ·
                refine ⟨472491053307929222968229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314994035538619481978819 472491053307929222968229)
                ·
                  refine ⟨88592072495236729306543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 472491053307929222968229 88592072495236729306543)
                  ·
                    rfl

theorem cell20_194099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 4].length) (baseStart_194099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194099 prefixEnd_194099 := by exact prefixLift 194099
  have htrace : WordTrace (prefixWord ++ tailWord_194099) baseStart_194099 baseEnd_194099 := by
    simpa [prefixWord, tailWord_194099, baseEnd_194099] using wordTrace_append hprefix tailTrace_194099
  have hstable : (prefixWord ++ tailWord_194099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194099).length < 2 ^ (prefixWord ++ tailWord_194099).sum := by decide
  have hdescent : baseEnd_194099 < baseStart_194099 := by decide
  rcases family_descends (prefixWord ++ tailWord_194099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194151 : List Nat := [1, 1, 5, 1, 1, 1, 3, 4, 3]
def baseStart_194151 : Nat := 118140960795 + 194151 * 2 ^ 59
def prefixEnd_194151 : Nat := 4983230072969 + 3 ^ 40 * 194151 * 2
def baseEnd_194151 : Nat := 88615806712155659572997

theorem tailTrace_194151 : CollatzResearch.WordTrace tailWord_194151 prefixEnd_194151 88615806712155659572997 := by
  unfold tailWord_194151
  simp only [CollatzResearch.WordTrace]
  refine ⟨7081268719631560196038307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4720845813087706797358871 7081268719631560196038307)
  ·
    refine ⟨10621903079447340294057461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7081268719631560196038307 10621903079447340294057461)
    ·
      refine ⟨995803413698188152567887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10621903079447340294057461 995803413698188152567887)
      ·
        refine ⟨1493705120547282228851831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 995803413698188152567887 1493705120547282228851831)
        ·
          refine ⟨2240557680820923343277747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1493705120547282228851831 2240557680820923343277747)
          ·
            refine ⟨3360836521231385014916621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240557680820923343277747 3360836521231385014916621)
            ·
              refine ⟨1260313695461769380593733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3360836521231385014916621 1260313695461769380593733)
              ·
                refine ⟨236308817899081758861325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1260313695461769380593733 236308817899081758861325)
                ·
                  refine ⟨88615806712155659572997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236308817899081758861325 88615806712155659572997)
                  ·
                    rfl

theorem cell20_194151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 3].length) (baseStart_194151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194151 prefixEnd_194151 := by exact prefixLift 194151
  have htrace : WordTrace (prefixWord ++ tailWord_194151) baseStart_194151 baseEnd_194151 := by
    simpa [prefixWord, tailWord_194151, baseEnd_194151] using wordTrace_append hprefix tailTrace_194151
  have hstable : (prefixWord ++ tailWord_194151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194151).length < 2 ^ (prefixWord ++ tailWord_194151).sum := by decide
  have hdescent : baseEnd_194151 < baseStart_194151 := by decide
  rcases family_descends (prefixWord ++ tailWord_194151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194154 : List Nat := [3, 1, 3, 2, 1, 3, 1, 4, 2]
def baseStart_194154 : Nat := 118140960795 + 194154 * 2 ^ 59
def prefixEnd_194154 : Nat := 4983230072969 + 3 ^ 40 * 194154 * 2
def baseEnd_194154 : Nat := 88617175993900982472985

theorem tailTrace_194154 : CollatzResearch.WordTrace tailWord_194154 prefixEnd_194154 88617175993900982472985 := by
  unfold tailWord_194154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1770344534655172927099379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4720918759080461138931677 1770344534655172927099379)
  ·
    refine ⟨2655516801982759390649069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1770344534655172927099379 2655516801982759390649069)
    ·
      refine ⟨995818800743534771493401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2655516801982759390649069 995818800743534771493401)
      ·
        refine ⟨746864100557651078620051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 995818800743534771493401 746864100557651078620051)
        ·
          refine ⟨1120296150836476617930077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746864100557651078620051 1120296150836476617930077)
          ·
            refine ⟨420111056563678731723779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1120296150836476617930077 420111056563678731723779)
            ·
              refine ⟨630166584845518097585669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420111056563678731723779 630166584845518097585669)
              ·
                refine ⟨118156234658534643297313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 630166584845518097585669 118156234658534643297313)
                ·
                  refine ⟨88617175993900982472985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118156234658534643297313 88617175993900982472985)
                  ·
                    rfl

theorem cell20_194154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_194154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194154 prefixEnd_194154 := by exact prefixLift 194154
  have htrace : WordTrace (prefixWord ++ tailWord_194154) baseStart_194154 baseEnd_194154 := by
    simpa [prefixWord, tailWord_194154, baseEnd_194154] using wordTrace_append hprefix tailTrace_194154
  have hstable : (prefixWord ++ tailWord_194154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194154).length < 2 ^ (prefixWord ++ tailWord_194154).sum := by decide
  have hdescent : baseEnd_194154 < baseStart_194154 := by decide
  rcases family_descends (prefixWord ++ tailWord_194154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194172 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 7]
def baseStart_194172 : Nat := 118140960795 + 194172 * 2 ^ 59
def prefixEnd_194172 : Nat := 4983230072969 + 3 ^ 40 * 194172 * 2
def baseEnd_194172 : Nat := 88625391684372919872911

theorem tailTrace_194172 : CollatzResearch.WordTrace tailWord_194172 prefixEnd_194172 88625391684372919872911 := by
  unfold tailWord_194172
  simp only [CollatzResearch.WordTrace]
  refine ⟨3541017326277740391276385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4721356435036987188368513 3541017326277740391276385)
  ·
    refine ⟨2655762994708305293457289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3541017326277740391276385 2655762994708305293457289)
    ·
      refine ⟨1991822246031228970092967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2655762994708305293457289 1991822246031228970092967)
      ·
        refine ⟨2987733369046843455139451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1991822246031228970092967 2987733369046843455139451)
        ·
          refine ⟨4481600053570265182709177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2987733369046843455139451 4481600053570265182709177)
          ·
            refine ⟨3361200040177698887031883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4481600053570265182709177 3361200040177698887031883)
            ·
              refine ⟨5041800060266548330547825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3361200040177698887031883 5041800060266548330547825)
              ·
                refine ⟨3781350045199911247910869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5041800060266548330547825 3781350045199911247910869)
                ·
                  refine ⟨88625391684372919872911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3781350045199911247910869 88625391684372919872911)
                  ·
                    rfl

theorem cell20_194172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_194172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194172 prefixEnd_194172 := by exact prefixLift 194172
  have htrace : WordTrace (prefixWord ++ tailWord_194172) baseStart_194172 baseEnd_194172 := by
    simpa [prefixWord, tailWord_194172, baseEnd_194172] using wordTrace_append hprefix tailTrace_194172
  have hstable : (prefixWord ++ tailWord_194172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194172).length < 2 ^ (prefixWord ++ tailWord_194172).sum := by decide
  have hdescent : baseEnd_194172 < baseStart_194172 := by decide
  rcases family_descends (prefixWord ++ tailWord_194172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194206 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_194206 : Nat := 118140960795 + 194206 * 2 ^ 59
def prefixEnd_194206 : Nat := 4983230072969 + 3 ^ 40 * 194206 * 2
def baseEnd_194206 : Nat := 88640910210819912739439

theorem tailTrace_194206 : CollatzResearch.WordTrace tailWord_194206 prefixEnd_194206 88640910210819912739439 := by
  unfold tailWord_194206
  simp only [CollatzResearch.WordTrace]
  refine ⟨885409341804038073661309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4722183156288203059526981 885409341804038073661309)
  ·
    refine ⟨332028503176514277622991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 885409341804038073661309 332028503176514277622991)
    ·
      refine ⟨498042754764771416434487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332028503176514277622991 498042754764771416434487)
      ·
        refine ⟨747064132147157124651731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498042754764771416434487 747064132147157124651731)
        ·
          refine ⟨1120596198220735686977597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 747064132147157124651731 1120596198220735686977597)
          ·
            refine ⟨420223574332775882616599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1120596198220735686977597 420223574332775882616599)
            ·
              refine ⟨630335361499163823924899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420223574332775882616599 630335361499163823924899)
              ·
                refine ⟨945503042248745735887349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 630335361499163823924899 945503042248745735887349)
                ·
                  refine ⟨88640910210819912739439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 945503042248745735887349 88640910210819912739439)
                  ·
                    rfl

theorem cell20_194206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_194206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194206 prefixEnd_194206 := by exact prefixLift 194206
  have htrace : WordTrace (prefixWord ++ tailWord_194206) baseStart_194206 baseEnd_194206 := by
    simpa [prefixWord, tailWord_194206, baseEnd_194206] using wordTrace_append hprefix tailTrace_194206
  have hstable : (prefixWord ++ tailWord_194206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194206).length < 2 ^ (prefixWord ++ tailWord_194206).sum := by decide
  have hdescent : baseEnd_194206 < baseStart_194206 := by decide
  rcases family_descends (prefixWord ++ tailWord_194206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194213 : List Nat := [1, 3, 1, 2, 1, 2, 4, 4, 2]
def baseStart_194213 : Nat := 118140960795 + 194213 * 2 ^ 59
def prefixEnd_194213 : Nat := 4983230072969 + 3 ^ 40 * 194213 * 2
def baseEnd_194213 : Nat := 88644105201558999506077

theorem tailTrace_194213 : CollatzResearch.WordTrace tailWord_194213 prefixEnd_194213 88644105201558999506077 := by
  unfold tailWord_194213
  simp only [CollatzResearch.WordTrace]
  refine ⟨7083530045406944784795293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4722353363604629856530195 7083530045406944784795293)
  ·
    refine ⟨2656323767027604294298235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7083530045406944784795293 2656323767027604294298235)
    ·
      refine ⟨3984485650541406441447353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2656323767027604294298235 3984485650541406441447353)
      ·
        refine ⟨2988364237906054831085515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3984485650541406441447353 2988364237906054831085515)
        ·
          refine ⟨4482546356859082246628273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2988364237906054831085515 4482546356859082246628273)
          ·
            refine ⟨3361909767644311684971205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4482546356859082246628273 3361909767644311684971205)
            ·
              refine ⟨630358081433308440932101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3361909767644311684971205 630358081433308440932101)
              ·
                refine ⟨118192140268745332674769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 630358081433308440932101 118192140268745332674769)
                ·
                  refine ⟨88644105201558999506077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118192140268745332674769 88644105201558999506077)
                  ·
                    rfl

theorem cell20_194213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_194213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194213 prefixEnd_194213 := by exact prefixLift 194213
  have htrace : WordTrace (prefixWord ++ tailWord_194213) baseStart_194213 baseEnd_194213 := by
    simpa [prefixWord, tailWord_194213, baseEnd_194213] using wordTrace_append hprefix tailTrace_194213
  have hstable : (prefixWord ++ tailWord_194213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194213).length < 2 ^ (prefixWord ++ tailWord_194213).sum := by decide
  have hdescent : baseEnd_194213 < baseStart_194213 := by decide
  rcases family_descends (prefixWord ++ tailWord_194213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194230 : List Nat := [5, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_194230 : Nat := 118140960795 + 194230 * 2 ^ 59
def prefixEnd_194230 : Nat := 4983230072969 + 3 ^ 40 * 194230 * 2
def baseEnd_194230 : Nat := 88651864464782495939341

theorem tailTrace_194230 : CollatzResearch.WordTrace tailWord_194230 prefixEnd_194230 88651864464782495939341 := by
  unfold tailWord_194230
  simp only [CollatzResearch.WordTrace]
  refine ⟨442759380396584793010259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4722766724230237792109429 442759380396584793010259)
  ·
    refine ⟨664139070594877189515389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 442759380396584793010259 664139070594877189515389)
    ·
      refine ⟨249052151473078946068271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 664139070594877189515389 249052151473078946068271)
      ·
        refine ⟨373578227209618419102407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249052151473078946068271 373578227209618419102407)
        ·
          refine ⟨560367340814427628653611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373578227209618419102407 560367340814427628653611)
          ·
            refine ⟨840551011221641442980417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560367340814427628653611 840551011221641442980417)
            ·
              refine ⟨630413258416231082235313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 840551011221641442980417 630413258416231082235313)
              ·
                refine ⟨472809943812173311676485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630413258416231082235313 472809943812173311676485)
                ·
                  refine ⟨88651864464782495939341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 472809943812173311676485 88651864464782495939341)
                  ·
                    rfl

theorem cell20_194230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_194230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194230 prefixEnd_194230 := by exact prefixLift 194230
  have htrace : WordTrace (prefixWord ++ tailWord_194230) baseStart_194230 baseEnd_194230 := by
    simpa [prefixWord, tailWord_194230, baseEnd_194230] using wordTrace_append hprefix tailTrace_194230
  have hstable : (prefixWord ++ tailWord_194230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194230).length < 2 ^ (prefixWord ++ tailWord_194230).sum := by decide
  have hdescent : baseEnd_194230 < baseStart_194230 := by decide
  rcases family_descends (prefixWord ++ tailWord_194230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194234 : List Nat := [3, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_194234 : Nat := 118140960795 + 194234 * 2 ^ 59
def prefixEnd_194234 : Nat := 4983230072969 + 3 ^ 40 * 194234 * 2
def baseEnd_194234 : Nat := 88653690173776259805991

theorem tailTrace_194234 : CollatzResearch.WordTrace tailWord_194234 prefixEnd_194234 88653690173776259805991 := by
  unfold tailWord_194234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1771073994582716342827439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4722863985553910247539837 1771073994582716342827439)
  ·
    refine ⟨2656610991874074514241159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1771073994582716342827439 2656610991874074514241159)
    ·
      refine ⟨3984916487811111771361739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2656610991874074514241159 3984916487811111771361739)
      ·
        refine ⟨5977374731716667657042609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3984916487811111771361739 5977374731716667657042609)
        ·
          refine ⟨4483031048787500742781957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5977374731716667657042609 4483031048787500742781957)
          ·
            refine ⟨840568321647656389271617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4483031048787500742781957 840568321647656389271617)
            ·
              refine ⟨630426241235742291953713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 840568321647656389271617 630426241235742291953713)
              ·
                refine ⟨472819680926806718965285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630426241235742291953713 472819680926806718965285)
                ·
                  refine ⟨88653690173776259805991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 472819680926806718965285 88653690173776259805991)
                  ·
                    rfl

theorem cell20_194234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_194234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194234 prefixEnd_194234 := by exact prefixLift 194234
  have htrace : WordTrace (prefixWord ++ tailWord_194234) baseStart_194234 baseEnd_194234 := by
    simpa [prefixWord, tailWord_194234, baseEnd_194234] using wordTrace_append hprefix tailTrace_194234
  have hstable : (prefixWord ++ tailWord_194234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194234).length < 2 ^ (prefixWord ++ tailWord_194234).sum := by decide
  have hdescent : baseEnd_194234 < baseStart_194234 := by decide
  rcases family_descends (prefixWord ++ tailWord_194234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194248 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 7]
def baseStart_194248 : Nat := 118140960795 + 194248 * 2 ^ 59
def prefixEnd_194248 : Nat := 4983230072969 + 3 ^ 40 * 194248 * 2
def baseEnd_194248 : Nat := 88660080155254433339267

theorem tailTrace_194248 : CollatzResearch.WordTrace tailWord_194248 prefixEnd_194248 88660080155254433339267 := by
  unfold tailWord_194248
  simp only [CollatzResearch.WordTrace]
  refine ⟨3542403300140072881159699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4723204400186763841546265 3542403300140072881159699)
  ·
    refine ⟨5313604950210109321739549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3542403300140072881159699 5313604950210109321739549)
    ·
      refine ⟨1992601856328790995652331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5313604950210109321739549 1992601856328790995652331)
      ·
        refine ⟨2988902784493186493478497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1992601856328790995652331 2988902784493186493478497)
        ·
          refine ⟨2241677088369889870108873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2988902784493186493478497 2241677088369889870108873)
          ·
            refine ⟨1681257816277417402581655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2241677088369889870108873 1681257816277417402581655)
            ·
              refine ⟨2521886724416126103872483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1681257816277417402581655 2521886724416126103872483)
              ·
                refine ⟨3782830086624189155808725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2521886724416126103872483 3782830086624189155808725)
                ·
                  refine ⟨88660080155254433339267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3782830086624189155808725 88660080155254433339267)
                  ·
                    rfl

theorem cell20_194248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_194248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194248 prefixEnd_194248 := by exact prefixLift 194248
  have htrace : WordTrace (prefixWord ++ tailWord_194248) baseStart_194248 baseEnd_194248 := by
    simpa [prefixWord, tailWord_194248, baseEnd_194248] using wordTrace_append hprefix tailTrace_194248
  have hstable : (prefixWord ++ tailWord_194248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194248).length < 2 ^ (prefixWord ++ tailWord_194248).sum := by decide
  have hdescent : baseEnd_194248 < baseStart_194248 := by decide
  rcases family_descends (prefixWord ++ tailWord_194248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194255 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 6]
def baseStart_194255 : Nat := 118140960795 + 194255 * 2 ^ 59
def prefixEnd_194255 : Nat := 4983230072969 + 3 ^ 40 * 194255 * 2
def baseEnd_194255 : Nat := 88663275145993520105905

theorem tailTrace_194255 : CollatzResearch.WordTrace tailWord_194255 prefixEnd_194255 88663275145993520105905 := by
  unfold tailWord_194255
  simp only [CollatzResearch.WordTrace]
  refine ⟨7085061911254785957824219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4723374607503190638549479 7085061911254785957824219)
  ·
    refine ⟨10627592866882178936736329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7085061911254785957824219 10627592866882178936736329)
    ·
      refine ⟨7970694650161634202552247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10627592866882178936736329 7970694650161634202552247)
      ·
        refine ⟨11956041975242451303828371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7970694650161634202552247 11956041975242451303828371)
        ·
          refine ⟨17934062962863676955742557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11956041975242451303828371 17934062962863676955742557)
          ·
            refine ⟨6725273611073878858403459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17934062962863676955742557 6725273611073878858403459)
            ·
              refine ⟨10087910416610818287605189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6725273611073878858403459 10087910416610818287605189)
              ·
                refine ⟨1891483203114528428925973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10087910416610818287605189 1891483203114528428925973)
                ·
                  refine ⟨88663275145993520105905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1891483203114528428925973 88663275145993520105905)
                  ·
                    rfl

theorem cell20_194255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_194255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194255 prefixEnd_194255 := by exact prefixLift 194255
  have htrace : WordTrace (prefixWord ++ tailWord_194255) baseStart_194255 baseEnd_194255 := by
    simpa [prefixWord, tailWord_194255, baseEnd_194255] using wordTrace_append hprefix tailTrace_194255
  have hstable : (prefixWord ++ tailWord_194255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194255).length < 2 ^ (prefixWord ++ tailWord_194255).sum := by decide
  have hdescent : baseEnd_194255 < baseStart_194255 := by decide
  rcases family_descends (prefixWord ++ tailWord_194255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194258 : List Nat := [3, 2, 2, 2, 2, 3, 6]
def baseStart_194258 : Nat := 118140960795 + 194258 * 2 ^ 59
def prefixEnd_194258 : Nat := 4983230072969 + 3 ^ 40 * 194258 * 2
def baseEnd_194258 : Nat := 9851627158637649222877

theorem tailTrace_194258 : CollatzResearch.WordTrace tailWord_194258 prefixEnd_194258 9851627158637649222877 := by
  unfold tailWord_194258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1771292832560979367545857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4723447553495944980122285 1771292832560979367545857)
  ·
    refine ⟨1328469624420734525659393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1771292832560979367545857 1328469624420734525659393)
    ·
      refine ⟨996352218315550894244545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1328469624420734525659393 996352218315550894244545)
      ·
        refine ⟨747264163736663170683409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 996352218315550894244545 747264163736663170683409)
        ·
          refine ⟨560448122802497378012557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 747264163736663170683409 560448122802497378012557)
          ·
            refine ⟨210168046050936516754709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 560448122802497378012557 210168046050936516754709)
            ·
              refine ⟨9851627158637649222877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 210168046050936516754709 9851627158637649222877)
              ·
                rfl

theorem cell20_194258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 6].length) (baseStart_194258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194258 prefixEnd_194258 := by exact prefixLift 194258
  have htrace : WordTrace (prefixWord ++ tailWord_194258) baseStart_194258 baseEnd_194258 := by
    simpa [prefixWord, tailWord_194258, baseEnd_194258] using wordTrace_append hprefix tailTrace_194258
  have hstable : (prefixWord ++ tailWord_194258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194258).length < 2 ^ (prefixWord ++ tailWord_194258).sum := by decide
  have hdescent : baseEnd_194258 < baseStart_194258 := by decide
  rcases family_descends (prefixWord ++ tailWord_194258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194272 : List Nat := [2, 1, 1, 3, 1, 2, 5, 1, 4]
def baseStart_194272 : Nat := 118140960795 + 194272 * 2 ^ 59
def prefixEnd_194272 : Nat := 4983230072969 + 3 ^ 40 * 194272 * 2
def baseEnd_194272 : Nat := 88671034409217016539169

theorem tailTrace_194272 : CollatzResearch.WordTrace tailWord_194272 prefixEnd_194272 88671034409217016539169 := by
  unfold tailWord_194272
  simp only [CollatzResearch.WordTrace]
  refine ⟨3542840976096598930596535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4723787968128798574128713 3542840976096598930596535)
  ·
    refine ⟨5314261464144898395894803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3542840976096598930596535 5314261464144898395894803)
    ·
      refine ⟨7971392196217347593842205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5314261464144898395894803 7971392196217347593842205)
      ·
        refine ⟨2989272073581505347690827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7971392196217347593842205 2989272073581505347690827)
        ·
          refine ⟨4483908110372258021536241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2989272073581505347690827 4483908110372258021536241)
          ·
            refine ⟨3362931082779193516152181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4483908110372258021536241 3362931082779193516152181)
            ·
              refine ⟨315274789010549392139267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3362931082779193516152181 315274789010549392139267)
              ·
                refine ⟨472912183515824088208901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315274789010549392139267 472912183515824088208901)
                ·
                  refine ⟨88671034409217016539169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 472912183515824088208901 88671034409217016539169)
                  ·
                    rfl

theorem cell20_194272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_194272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194272 prefixEnd_194272 := by exact prefixLift 194272
  have htrace : WordTrace (prefixWord ++ tailWord_194272) baseStart_194272 baseEnd_194272 := by
    simpa [prefixWord, tailWord_194272, baseEnd_194272] using wordTrace_append hprefix tailTrace_194272
  have hstable : (prefixWord ++ tailWord_194272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194272).length < 2 ^ (prefixWord ++ tailWord_194272).sum := by decide
  have hdescent : baseEnd_194272 < baseStart_194272 := by decide
  rcases family_descends (prefixWord ++ tailWord_194272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194282 : List Nat := [3, 1, 3, 1, 1, 1, 6, 1, 3]
def baseStart_194282 : Nat := 118140960795 + 194282 * 2 ^ 59
def prefixEnd_194282 : Nat := 4983230072969 + 3 ^ 40 * 194282 * 2
def baseEnd_194282 : Nat := 88675598681701426205795

theorem tailTrace_194282 : CollatzResearch.WordTrace tailWord_194282 prefixEnd_194282 88675598681701426205795 := by
  unfold tailWord_194282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1771511670539242392264275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4724031121437979712704733 1771511670539242392264275)
  ·
    refine ⟨2657267505808863588396413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1771511670539242392264275 2657267505808863588396413)
    ·
      refine ⟨996475314678323845648655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2657267505808863588396413 996475314678323845648655)
      ·
        refine ⟨1494712972017485768472983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 996475314678323845648655 1494712972017485768472983)
        ·
          refine ⟨2242069458026228652709475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1494712972017485768472983 2242069458026228652709475)
          ·
            refine ⟨3363104187039342979064213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2242069458026228652709475 3363104187039342979064213)
            ·
              refine ⟨157645508767469202143635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3363104187039342979064213 157645508767469202143635)
              ·
                refine ⟨236468263151203803215453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157645508767469202143635 236468263151203803215453)
                ·
                  refine ⟨88675598681701426205795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236468263151203803215453 88675598681701426205795)
                  ·
                    rfl

theorem cell20_194282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_194282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194282 prefixEnd_194282 := by exact prefixLift 194282
  have htrace : WordTrace (prefixWord ++ tailWord_194282) baseStart_194282 baseEnd_194282 := by
    simpa [prefixWord, tailWord_194282, baseEnd_194282] using wordTrace_append hprefix tailTrace_194282
  have hstable : (prefixWord ++ tailWord_194282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194282).length < 2 ^ (prefixWord ++ tailWord_194282).sum := by decide
  have hdescent : baseEnd_194282 < baseStart_194282 := by decide
  rcases family_descends (prefixWord ++ tailWord_194282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194306 : List Nat := [3, 4, 1, 1, 1, 1, 2, 5, 2]
def baseStart_194306 : Nat := 118140960795 + 194306 * 2 ^ 59
def prefixEnd_194306 : Nat := 4983230072969 + 3 ^ 40 * 194306 * 2
def baseEnd_194306 : Nat := 88686552935664009405697

theorem tailTrace_194306 : CollatzResearch.WordTrace tailWord_194306 prefixEnd_194306 88686552935664009405697 := by
  unfold tailWord_194306
  simp only [CollatzResearch.WordTrace]
  refine ⟨1771730508517505416982693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4724614689380014445287181 1771730508517505416982693)
  ·
    refine ⟨332199470347032265684255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1771730508517505416982693 332199470347032265684255)
    ·
      refine ⟨498299205520548398526383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332199470347032265684255 498299205520548398526383)
      ·
        refine ⟨747448808280822597789575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498299205520548398526383 747448808280822597789575)
        ·
          refine ⟨1121173212421233896684363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 747448808280822597789575 1121173212421233896684363)
          ·
            refine ⟨1681759818631850845026545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1121173212421233896684363 1681759818631850845026545)
            ·
              refine ⟨1261319863973888133769909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1681759818631850845026545 1261319863973888133769909)
              ·
                refine ⟨118248737247552012540929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1261319863973888133769909 118248737247552012540929)
                ·
                  refine ⟨88686552935664009405697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118248737247552012540929 88686552935664009405697)
                  ·
                    rfl

theorem cell20_194306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_194306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194306 prefixEnd_194306 := by exact prefixLift 194306
  have htrace : WordTrace (prefixWord ++ tailWord_194306) baseStart_194306 baseEnd_194306 := by
    simpa [prefixWord, tailWord_194306, baseEnd_194306] using wordTrace_append hprefix tailTrace_194306
  have hstable : (prefixWord ++ tailWord_194306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194306).length < 2 ^ (prefixWord ++ tailWord_194306).sum := by decide
  have hdescent : baseEnd_194306 < baseStart_194306 := by decide
  rcases family_descends (prefixWord ++ tailWord_194306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194341 : List Nat := [1, 3, 1, 2, 3, 2, 2, 3, 3]
def baseStart_194341 : Nat := 118140960795 + 194341 * 2 ^ 59
def prefixEnd_194341 : Nat := 4983230072969 + 3 ^ 40 * 194341 * 2
def baseEnd_194341 : Nat := 88702527889359443238887

theorem tailTrace_194341 : CollatzResearch.WordTrace tailWord_194341 prefixEnd_194341 88702527889359443238887 := by
  unfold tailWord_194341
  simp only [CollatzResearch.WordTrace]
  refine ⟨7088198588943222645454877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4725465725962148430303251 7088198588943222645454877)
  ·
    refine ⟨2658074470853708492045579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7088198588943222645454877 2658074470853708492045579)
    ·
      refine ⟨3987111706280562738068369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2658074470853708492045579 3987111706280562738068369)
      ·
        refine ⟨2990333779710422053551277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3987111706280562738068369 2990333779710422053551277)
        ·
          refine ⟨1121375167391408270081729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2990333779710422053551277 1121375167391408270081729)
          ·
            refine ⟨841031375543556202561297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1121375167391408270081729 841031375543556202561297)
            ·
              refine ⟨630773531657667151920973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 841031375543556202561297 630773531657667151920973)
              ·
                refine ⟨236540074371625181970365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 630773531657667151920973 236540074371625181970365)
                ·
                  refine ⟨88702527889359443238887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236540074371625181970365 88702527889359443238887)
                  ·
                    rfl

theorem cell20_194341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_194341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194341 prefixEnd_194341 := by exact prefixLift 194341
  have htrace : WordTrace (prefixWord ++ tailWord_194341) baseStart_194341 baseEnd_194341 := by
    simpa [prefixWord, tailWord_194341, baseEnd_194341] using wordTrace_append hprefix tailTrace_194341
  have hstable : (prefixWord ++ tailWord_194341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194341).length < 2 ^ (prefixWord ++ tailWord_194341).sum := by decide
  have hdescent : baseEnd_194341 < baseStart_194341 := by decide
  rcases family_descends (prefixWord ++ tailWord_194341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194348 : List Nat := [2, 2, 1, 1, 1, 6, 1, 2, 4]
def baseStart_194348 : Nat := 118140960795 + 194348 * 2 ^ 59
def prefixEnd_194348 : Nat := 4983230072969 + 3 ^ 40 * 194348 * 2
def baseEnd_194348 : Nat := 88705722880098530005525

theorem tailTrace_194348 : CollatzResearch.WordTrace tailWord_194348 prefixEnd_194348 88705722880098530005525 := by
  unfold tailWord_194348
  simp only [CollatzResearch.WordTrace]
  refine ⟨3544226949958931420479849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4725635933278575227306465 3544226949958931420479849)
  ·
    refine ⟨2658170212469198565359887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3544226949958931420479849 2658170212469198565359887)
    ·
      refine ⟨3987255318703797848039831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2658170212469198565359887 3987255318703797848039831)
      ·
        refine ⟨5980882978055696772059747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3987255318703797848039831 5980882978055696772059747)
        ·
          refine ⟨8971324467083545158089621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5980882978055696772059747 8971324467083545158089621)
          ·
            refine ⟨420530834394541179285451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8971324467083545158089621 420530834394541179285451)
            ·
              refine ⟨630796251591811768928177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420530834394541179285451 630796251591811768928177)
              ·
                refine ⟨473097188693858826696133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630796251591811768928177 473097188693858826696133)
                ·
                  refine ⟨88705722880098530005525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 473097188693858826696133 88705722880098530005525)
                  ·
                    rfl

theorem cell20_194348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_194348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194348 prefixEnd_194348 := by exact prefixLift 194348
  have htrace : WordTrace (prefixWord ++ tailWord_194348) baseStart_194348 baseEnd_194348 := by
    simpa [prefixWord, tailWord_194348, baseEnd_194348] using wordTrace_append hprefix tailTrace_194348
  have hstable : (prefixWord ++ tailWord_194348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194348).length < 2 ^ (prefixWord ++ tailWord_194348).sum := by decide
  have hdescent : baseEnd_194348 < baseStart_194348 := by decide
  rcases family_descends (prefixWord ++ tailWord_194348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194361 : List Nat := [1, 2, 1, 7, 1, 1, 2, 3, 2]
def baseStart_194361 : Nat := 118140960795 + 194361 * 2 ^ 59
def prefixEnd_194361 : Nat := 4983230072969 + 3 ^ 40 * 194361 * 2
def baseEnd_194361 : Nat := 88711656434328262572139

theorem tailTrace_194361 : CollatzResearch.WordTrace tailWord_194361 prefixEnd_194361 88711656434328262572139 := by
  unfold tailWord_194361
  simp only [CollatzResearch.WordTrace]
  refine ⟨7088928048870766061182937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4725952032580510707455291 7088928048870766061182937)
  ·
    refine ⟨5316696036653074545887203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7088928048870766061182937 5316696036653074545887203)
    ·
      refine ⟨7975044054979611818830805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5316696036653074545887203 7975044054979611818830805)
      ·
        refine ⟨186915095038584652003847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 7975044054979611818830805 186915095038584652003847)
        ·
          refine ⟨280372642557876978005771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186915095038584652003847 280372642557876978005771)
          ·
            refine ⟨420558963836815467008657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280372642557876978005771 420558963836815467008657)
            ·
              refine ⟨315419222877611600256493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420558963836815467008657 315419222877611600256493)
              ·
                refine ⟨118282208579104350096185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 315419222877611600256493 118282208579104350096185)
                ·
                  refine ⟨88711656434328262572139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118282208579104350096185 88711656434328262572139)
                  ·
                    rfl

theorem cell20_194361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 2].length) (baseStart_194361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194361 prefixEnd_194361 := by exact prefixLift 194361
  have htrace : WordTrace (prefixWord ++ tailWord_194361) baseStart_194361 baseEnd_194361 := by
    simpa [prefixWord, tailWord_194361, baseEnd_194361] using wordTrace_append hprefix tailTrace_194361
  have hstable : (prefixWord ++ tailWord_194361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194361).length < 2 ^ (prefixWord ++ tailWord_194361).sum := by decide
  have hdescent : baseEnd_194361 < baseStart_194361 := by decide
  rcases family_descends (prefixWord ++ tailWord_194361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194386 : List Nat := [3, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_194386 : Nat := 118140960795 + 194386 * 2 ^ 59
def prefixEnd_194386 : Nat := 4983230072969 + 3 ^ 40 * 194386 * 2
def baseEnd_194386 : Nat := 88723067115539286738703

theorem tailTrace_194386 : CollatzResearch.WordTrace tailWord_194386 prefixEnd_194386 88723067115539286738703 := by
  unfold tailWord_194386
  simp only [CollatzResearch.WordTrace]
  refine ⟨1772459968445048832710753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4726559915853463553895341 1772459968445048832710753)
  ·
    refine ⟨1329344976333786624533065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1772459968445048832710753 1329344976333786624533065)
    ·
      refine ⟨997008732250339968399799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1329344976333786624533065 997008732250339968399799)
      ·
        refine ⟨1495513098375509952599699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 997008732250339968399799 1495513098375509952599699)
        ·
          refine ⟨2243269647563264928899549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1495513098375509952599699 2243269647563264928899549)
          ·
            refine ⟨841226117836224348337331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2243269647563264928899549 841226117836224348337331)
            ·
              refine ⟨1261839176754336522505997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841226117836224348337331 1261839176754336522505997)
              ·
                refine ⟨473189691282876195939749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1261839176754336522505997 473189691282876195939749)
                ·
                  refine ⟨88723067115539286738703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 473189691282876195939749 88723067115539286738703)
                  ·
                    rfl

theorem cell20_194386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_194386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194386 prefixEnd_194386 := by exact prefixLift 194386
  have htrace : WordTrace (prefixWord ++ tailWord_194386) baseStart_194386 baseEnd_194386 := by
    simpa [prefixWord, tailWord_194386, baseEnd_194386] using wordTrace_append hprefix tailTrace_194386
  have hstable : (prefixWord ++ tailWord_194386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194386).length < 2 ^ (prefixWord ++ tailWord_194386).sum := by decide
  have hdescent : baseEnd_194386 < baseStart_194386 := by decide
  rcases family_descends (prefixWord ++ tailWord_194386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194455 : List Nat := [1, 1, 3, 3, 1, 4, 1, 3, 3]
def baseStart_194455 : Nat := 118140960795 + 194455 * 2 ^ 59
def prefixEnd_194455 : Nat := 4983230072969 + 3 ^ 40 * 194455 * 2
def baseEnd_194455 : Nat := 88754560595681713438421

theorem tailTrace_194455 : CollatzResearch.WordTrace tailWord_194455 prefixEnd_194455 88754560595681713438421 := by
  unfold tailWord_194455
  simp only [CollatzResearch.WordTrace]
  refine ⟨7092356510530220115104819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4728237673686813410069879 7092356510530220115104819)
  ·
    refine ⟨10638534765795330172657229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7092356510530220115104819 10638534765795330172657229)
    ·
      refine ⟨3989450537173248814746461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10638534765795330172657229 3989450537173248814746461)
      ·
        refine ⟨1496043951439968305529923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3989450537173248814746461 1496043951439968305529923)
        ·
          refine ⟨2244065927159952458294885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1496043951439968305529923 2244065927159952458294885)
          ·
            refine ⟨420762361342491085930291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2244065927159952458294885 420762361342491085930291)
            ·
              refine ⟨631143542013736628895437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420762361342491085930291 631143542013736628895437)
              ·
                refine ⟨236678828255151235835789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 631143542013736628895437 236678828255151235835789)
                ·
                  refine ⟨88754560595681713438421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236678828255151235835789 88754560595681713438421)
                  ·
                    rfl

theorem cell20_194455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 3].length) (baseStart_194455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194455 prefixEnd_194455 := by exact prefixLift 194455
  have htrace : WordTrace (prefixWord ++ tailWord_194455) baseStart_194455 baseEnd_194455 := by
    simpa [prefixWord, tailWord_194455, baseEnd_194455] using wordTrace_append hprefix tailTrace_194455
  have hstable : (prefixWord ++ tailWord_194455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194455).length < 2 ^ (prefixWord ++ tailWord_194455).sum := by decide
  have hdescent : baseEnd_194455 < baseStart_194455 := by decide
  rcases family_descends (prefixWord ++ tailWord_194455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194486 : List Nat := [5, 1, 4, 10]
def baseStart_194486 : Nat := 118140960795 + 194486 * 2 ^ 59
def prefixEnd_194486 : Nat := 4983230072969 + 3 ^ 40 * 194486 * 2
def baseEnd_194486 : Nat := 365303332676474828827

theorem tailTrace_194486 : CollatzResearch.WordTrace tailWord_194486 prefixEnd_194486 365303332676474828827 := by
  unfold tailWord_194486
  simp only [CollatzResearch.WordTrace]
  refine ⟨443342948338619525592707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4728991448945274939655541 443342948338619525592707)
  ·
    refine ⟨665014422507929288389061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 443342948338619525592707 665014422507929288389061)
    ·
      refine ⟨124690204220236741572949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 665014422507929288389061 124690204220236741572949)
      ·
        refine ⟨365303332676474828827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 124690204220236741572949 365303332676474828827)
        ·
          rfl

theorem cell20_194486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 10].length) (baseStart_194486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194486 prefixEnd_194486 := by exact prefixLift 194486
  have htrace : WordTrace (prefixWord ++ tailWord_194486) baseStart_194486 baseEnd_194486 := by
    simpa [prefixWord, tailWord_194486, baseEnd_194486] using wordTrace_append hprefix tailTrace_194486
  have hstable : (prefixWord ++ tailWord_194486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194486).length < 2 ^ (prefixWord ++ tailWord_194486).sum := by decide
  have hdescent : baseEnd_194486 < baseStart_194486 := by decide
  rcases family_descends (prefixWord ++ tailWord_194486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194492 : List Nat := [2, 2, 2, 5, 1, 2, 2, 2, 2]
def baseStart_194492 : Nat := 118140960795 + 194492 * 2 ^ 59
def prefixEnd_194492 : Nat := 4983230072969 + 3 ^ 40 * 194492 * 2
def baseEnd_194492 : Nat := 88771448403874029204937

theorem tailTrace_194492 : CollatzResearch.WordTrace tailWord_194492 prefixEnd_194492 88771448403874029204937 := by
  unfold tailWord_194492
  simp only [CollatzResearch.WordTrace]
  refine ⟨3546853005698087717100865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4729137340930783622801153 3546853005698087717100865)
  ·
    refine ⟨2660139754273565787825649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3546853005698087717100865 2660139754273565787825649)
    ·
      refine ⟨1995104815705174340869237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2660139754273565787825649 1995104815705174340869237)
      ·
        refine ⟨187041076472360094456491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1995104815705174340869237 187041076472360094456491)
        ·
          refine ⟨280561614708540141684737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187041076472360094456491 280561614708540141684737)
          ·
            refine ⟨210421211031405106263553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280561614708540141684737 210421211031405106263553)
            ·
              refine ⟨157815908273553829697665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210421211031405106263553 157815908273553829697665)
              ·
                refine ⟨118361931205165372273249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157815908273553829697665 118361931205165372273249)
                ·
                  refine ⟨88771448403874029204937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118361931205165372273249 88771448403874029204937)
                  ·
                    rfl

theorem cell20_194492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_194492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194492 prefixEnd_194492 := by exact prefixLift 194492
  have htrace : WordTrace (prefixWord ++ tailWord_194492) baseStart_194492 baseEnd_194492 := by
    simpa [prefixWord, tailWord_194492, baseEnd_194492] using wordTrace_append hprefix tailTrace_194492
  have hstable : (prefixWord ++ tailWord_194492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194492).length < 2 ^ (prefixWord ++ tailWord_194492).sum := by decide
  have hdescent : baseEnd_194492 < baseStart_194492 := by decide
  rcases family_descends (prefixWord ++ tailWord_194492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194493 : List Nat := [1, 4, 1, 2, 3, 1, 1, 4, 3]
def baseStart_194493 : Nat := 118140960795 + 194493 * 2 ^ 59
def prefixEnd_194493 : Nat := 4983230072969 + 3 ^ 40 * 194493 * 2
def baseEnd_194493 : Nat := 88771904831122470171599

theorem tailTrace_194493 : CollatzResearch.WordTrace tailWord_194493 prefixEnd_194493 88771904831122470171599 := by
  unfold tailWord_194493
  simp only [CollatzResearch.WordTrace]
  refine ⟨7093742484392552604988133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4729161656261701736658755 7093742484392552604988133)
  ·
    refine ⟨1330076715823603613435275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7093742484392552604988133 1330076715823603613435275)
    ·
      refine ⟨1995115073735405420152913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1330076715823603613435275 1995115073735405420152913)
      ·
        refine ⟨1496336305301554065114685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1995115073735405420152913 1496336305301554065114685)
        ·
          refine ⟨561126114488082774418007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1496336305301554065114685 561126114488082774418007)
          ·
            refine ⟨841689171732124161627011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561126114488082774418007 841689171732124161627011)
            ·
              refine ⟨1262533757598186242440517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841689171732124161627011 1262533757598186242440517)
              ·
                refine ⟨236725079549659920457597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1262533757598186242440517 236725079549659920457597)
                ·
                  refine ⟨88771904831122470171599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236725079549659920457597 88771904831122470171599)
                  ·
                    rfl

theorem cell20_194493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_194493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194493 prefixEnd_194493 := by exact prefixLift 194493
  have htrace : WordTrace (prefixWord ++ tailWord_194493) baseStart_194493 baseEnd_194493 := by
    simpa [prefixWord, tailWord_194493, baseEnd_194493] using wordTrace_append hprefix tailTrace_194493
  have hstable : (prefixWord ++ tailWord_194493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194493).length < 2 ^ (prefixWord ++ tailWord_194493).sum := by decide
  have hdescent : baseEnd_194493 < baseStart_194493 := by decide
  rcases family_descends (prefixWord ++ tailWord_194493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194528 : List Nat := [2, 1, 1, 3, 1, 1, 1, 10]
def baseStart_194528 : Nat := 118140960795 + 194528 * 2 ^ 59
def prefixEnd_194528 : Nat := 4983230072969 + 3 ^ 40 * 194528 * 2
def baseEnd_194528 : Nat := 29595959928272634668263

theorem tailTrace_194528 : CollatzResearch.WordTrace tailWord_194528 prefixEnd_194528 29595959928272634668263 := by
  unfold tailWord_194528
  simp only [CollatzResearch.WordTrace]
  refine ⟨3547509519632876791256119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4730012692843835721674825 3547509519632876791256119)
  ·
    refine ⟨5321264279449315186884179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3547509519632876791256119 5321264279449315186884179)
    ·
      refine ⟨7981896419173972780326269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5321264279449315186884179 7981896419173972780326269)
      ·
        refine ⟨2993211157190239792622351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7981896419173972780326269 2993211157190239792622351)
        ·
          refine ⟨4489816735785359688933527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2993211157190239792622351 4489816735785359688933527)
          ·
            refine ⟨6734725103678039533400291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4489816735785359688933527 6734725103678039533400291)
            ·
              refine ⟨10102087655517059300100437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6734725103678039533400291 10102087655517059300100437)
              ·
                refine ⟨29595959928272634668263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10102087655517059300100437 29595959928272634668263)
                ·
                  rfl

theorem cell20_194528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_194528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194528 prefixEnd_194528 := by exact prefixLift 194528
  have htrace : WordTrace (prefixWord ++ tailWord_194528) baseStart_194528 baseEnd_194528 := by
    simpa [prefixWord, tailWord_194528, baseEnd_194528] using wordTrace_append hprefix tailTrace_194528
  have hstable : (prefixWord ++ tailWord_194528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194528).length < 2 ^ (prefixWord ++ tailWord_194528).sum := by decide
  have hdescent : baseEnd_194528 < baseStart_194528 := by decide
  rcases family_descends (prefixWord ++ tailWord_194528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194545 : List Nat := [1, 2, 2, 2, 5, 1, 7]
def baseStart_194545 : Nat := 118140960795 + 194545 * 2 ^ 59
def prefixEnd_194545 : Nat := 4983230072969 + 3 ^ 40 * 194545 * 2
def baseEnd_194545 : Nat := 9866182116449044493117

theorem tailTrace_194545 : CollatzResearch.WordTrace tailWord_194545 prefixEnd_194545 9866182116449044493117 := by
  unfold tailWord_194545
  simp only [CollatzResearch.WordTrace]
  refine ⟨7095639080204165485881089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4730426053469443657254059 7095639080204165485881089)
  ·
    refine ⟨5321729310153124114410817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7095639080204165485881089 5321729310153124114410817)
    ·
      refine ⟨3991296982614843085808113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5321729310153124114410817 3991296982614843085808113)
      ·
        refine ⟨2993472736961132314356085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3991296982614843085808113 2993472736961132314356085)
        ·
          refine ⟨280638069090106154470883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2993472736961132314356085 280638069090106154470883)
          ·
            refine ⟨420957103635159231706325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280638069090106154470883 420957103635159231706325)
            ·
              refine ⟨9866182116449044493117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 420957103635159231706325 9866182116449044493117)
              ·
                rfl

theorem cell20_194545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 7].length) (baseStart_194545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194545 prefixEnd_194545 := by exact prefixLift 194545
  have htrace : WordTrace (prefixWord ++ tailWord_194545) baseStart_194545 baseEnd_194545 := by
    simpa [prefixWord, tailWord_194545, baseEnd_194545] using wordTrace_append hprefix tailTrace_194545
  have hstable : (prefixWord ++ tailWord_194545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194545).length < 2 ^ (prefixWord ++ tailWord_194545).sum := by decide
  have hdescent : baseEnd_194545 < baseStart_194545 := by decide
  rcases family_descends (prefixWord ++ tailWord_194545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194610 : List Nat := [3, 2, 1, 1, 2, 4, 3, 2, 2]
def baseStart_194610 : Nat := 118140960795 + 194610 * 2 ^ 59
def prefixEnd_194610 : Nat := 4983230072969 + 3 ^ 40 * 194610 * 2
def baseEnd_194610 : Nat := 88825306819190063271121

theorem tailTrace_194610 : CollatzResearch.WordTrace tailWord_194610 prefixEnd_194610 88825306819190063271121 := by
  unfold tailWord_194610
  simp only [CollatzResearch.WordTrace]
  refine ⟨1774502456242170396749321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4732006549979121057998189 1774502456242170396749321)
  ·
    refine ⟨1330876842181627797561991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1774502456242170396749321 1330876842181627797561991)
    ·
      refine ⟨1996315263272441696342987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1330876842181627797561991 1996315263272441696342987)
      ·
        refine ⟨2994472894908662544514481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1996315263272441696342987 2994472894908662544514481)
        ·
          refine ⟨2245854671181496908385861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2994472894908662544514481 2245854671181496908385861)
          ·
            refine ⟨421097750846530670322349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2245854671181496908385861 421097750846530670322349)
            ·
              refine ⟨157911656567449001370881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 421097750846530670322349 157911656567449001370881)
              ·
                refine ⟨118433742425586751028161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157911656567449001370881 118433742425586751028161)
                ·
                  refine ⟨88825306819190063271121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118433742425586751028161 88825306819190063271121)
                  ·
                    rfl

theorem cell20_194610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_194610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194610 prefixEnd_194610 := by exact prefixLift 194610
  have htrace : WordTrace (prefixWord ++ tailWord_194610) baseStart_194610 baseEnd_194610 := by
    simpa [prefixWord, tailWord_194610, baseEnd_194610] using wordTrace_append hprefix tailTrace_194610
  have hstable : (prefixWord ++ tailWord_194610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194610).length < 2 ^ (prefixWord ++ tailWord_194610).sum := by decide
  have hdescent : baseEnd_194610 < baseStart_194610 := by decide
  rcases family_descends (prefixWord ++ tailWord_194610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194621 : List Nat := [1, 4, 1, 3, 1, 1, 4, 5]
def baseStart_194621 : Nat := 118140960795 + 194621 * 2 ^ 59
def prefixEnd_194621 : Nat := 4983230072969 + 3 ^ 40 * 194621 * 2
def baseEnd_194621 : Nat := 29610109172974304634803

theorem tailTrace_194621 : CollatzResearch.WordTrace tailWord_194621 prefixEnd_194621 29610109172974304634803 := by
  unfold tailWord_194621
  simp only [CollatzResearch.WordTrace]
  refine ⟨7098411027928830465647717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4732274018619220310431811 7098411027928830465647717)
  ·
    refine ⟨1330952067736655712308947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7098411027928830465647717 1330952067736655712308947)
    ·
      refine ⟨1996428101604983568463421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1330952067736655712308947 1996428101604983568463421)
      ·
        refine ⟨748660538101868838173783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1996428101604983568463421 748660538101868838173783)
        ·
          refine ⟨1122990807152803257260675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 748660538101868838173783 1122990807152803257260675)
          ·
            refine ⟨1684486210729204885891013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1122990807152803257260675 1684486210729204885891013)
            ·
              refine ⟨315841164511725916104565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1684486210729204885891013 315841164511725916104565)
              ·
                refine ⟨29610109172974304634803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 315841164511725916104565 29610109172974304634803)
                ·
                  rfl

theorem cell20_194621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 5].length) (baseStart_194621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194621 prefixEnd_194621 := by exact prefixLift 194621
  have htrace : WordTrace (prefixWord ++ tailWord_194621) baseStart_194621 baseEnd_194621 := by
    simpa [prefixWord, tailWord_194621, baseEnd_194621] using wordTrace_append hprefix tailTrace_194621
  have hstable : (prefixWord ++ tailWord_194621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194621).length < 2 ^ (prefixWord ++ tailWord_194621).sum := by decide
  have hdescent : baseEnd_194621 < baseStart_194621 := by decide
  rcases family_descends (prefixWord ++ tailWord_194621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194624 : List Nat := [2, 1, 1, 2, 2, 6, 2, 1, 3]
def baseStart_194624 : Nat := 118140960795 + 194624 * 2 ^ 59
def prefixEnd_194624 : Nat := 4983230072969 + 3 ^ 40 * 194624 * 2
def baseEnd_194624 : Nat := 88831696800668236804397

theorem tailTrace_194624 : CollatzResearch.WordTrace tailWord_194624 prefixEnd_194624 88831696800668236804397 := by
  unfold tailWord_194624
  simp only [CollatzResearch.WordTrace]
  refine ⟨3549260223458980989003463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4732346964611974652004617 3549260223458980989003463)
  ·
    refine ⟨5323890335188471483505195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3549260223458980989003463 5323890335188471483505195)
    ·
      refine ⟨7985835502782707225257793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5323890335188471483505195 7985835502782707225257793)
      ·
        refine ⟨5989376627087030418943345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7985835502782707225257793 5989376627087030418943345)
        ·
          refine ⟨4492032470315272814207509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5989376627087030418943345 4492032470315272814207509)
          ·
            refine ⟨210564022046028413165977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4492032470315272814207509 210564022046028413165977)
            ·
              refine ⟨157923016534521309874483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210564022046028413165977 157923016534521309874483)
              ·
                refine ⟨236884524801781964811725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157923016534521309874483 236884524801781964811725)
                ·
                  refine ⟨88831696800668236804397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236884524801781964811725 88831696800668236804397)
                  ·
                    rfl

theorem cell20_194624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 3].length) (baseStart_194624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194624 prefixEnd_194624 := by exact prefixLift 194624
  have htrace : WordTrace (prefixWord ++ tailWord_194624) baseStart_194624 baseEnd_194624 := by
    simpa [prefixWord, tailWord_194624, baseEnd_194624] using wordTrace_append hprefix tailTrace_194624
  have hstable : (prefixWord ++ tailWord_194624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194624).length < 2 ^ (prefixWord ++ tailWord_194624).sum := by decide
  have hdescent : baseEnd_194624 < baseStart_194624 := by decide
  rcases family_descends (prefixWord ++ tailWord_194624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194669 : List Nat := [1, 5, 1, 1, 2, 1, 3, 4, 2]
def baseStart_194669 : Nat := 118140960795 + 194669 * 2 ^ 59
def prefixEnd_194669 : Nat := 4983230072969 + 3 ^ 40 * 194669 * 2
def baseEnd_194669 : Nat := 88852236026848080304213

theorem tailTrace_194669 : CollatzResearch.WordTrace tailWord_194669 prefixEnd_194669 88852236026848080304213 := by
  unfold tailWord_194669
  simp only [CollatzResearch.WordTrace]
  refine ⟨7100161731754934663395061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4733441154503289775596707 7100161731754934663395061)
  ·
    refine ⟨665640162352025124693287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7100161731754934663395061 665640162352025124693287)
    ·
      refine ⟨998460243528037687039931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 665640162352025124693287 998460243528037687039931)
      ·
        refine ⟨1497690365292056530559897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 998460243528037687039931 1497690365292056530559897)
        ·
          refine ⟨1123267773969042397919923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1497690365292056530559897 1123267773969042397919923)
          ·
            refine ⟨1684901660953563596879885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123267773969042397919923 1684901660953563596879885)
            ·
              refine ⟨631838122857586348829957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1684901660953563596879885 631838122857586348829957)
              ·
                refine ⟨118469648035797440405617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 631838122857586348829957 118469648035797440405617)
                ·
                  refine ⟨88852236026848080304213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118469648035797440405617 88852236026848080304213)
                  ·
                    rfl

theorem cell20_194669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_194669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194669 prefixEnd_194669 := by exact prefixLift 194669
  have htrace : WordTrace (prefixWord ++ tailWord_194669) baseStart_194669 baseEnd_194669 := by
    simpa [prefixWord, tailWord_194669, baseEnd_194669] using wordTrace_append hprefix tailTrace_194669
  have hstable : (prefixWord ++ tailWord_194669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194669).length < 2 ^ (prefixWord ++ tailWord_194669).sum := by decide
  have hdescent : baseEnd_194669 < baseStart_194669 := by decide
  rcases family_descends (prefixWord ++ tailWord_194669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194673 : List Nat := [1, 2, 2, 2, 1, 1, 4, 3, 4]
def baseStart_194673 : Nat := 118140960795 + 194673 * 2 ^ 59
def prefixEnd_194673 : Nat := 4983230072969 + 3 ^ 40 * 194673 * 2
def baseEnd_194673 : Nat := 88854061735841844170863

theorem tailTrace_194673 : CollatzResearch.WordTrace tailWord_194673 prefixEnd_194673 88854061735841844170863 := by
  unfold tailWord_194673
  simp only [CollatzResearch.WordTrace]
  refine ⟨7100307623740443346540673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4733538415826962231027115 7100307623740443346540673)
  ·
    refine ⟨5325230717805332509905505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7100307623740443346540673 5325230717805332509905505)
    ·
      refine ⟨3993923038353999382429129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5325230717805332509905505 3993923038353999382429129)
      ·
        refine ⟨2995442278765499536821847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3993923038353999382429129 2995442278765499536821847)
        ·
          refine ⟨4493163418148249305232771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2995442278765499536821847 4493163418148249305232771)
          ·
            refine ⟨6739745127222373957849157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4493163418148249305232771 6739745127222373957849157)
            ·
              refine ⟨1263702211354195117096717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6739745127222373957849157 1263702211354195117096717)
              ·
                refine ⟨473888329257823168911269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1263702211354195117096717 473888329257823168911269)
                ·
                  refine ⟨88854061735841844170863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 473888329257823168911269 88854061735841844170863)
                  ·
                    rfl

theorem cell20_194673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_194673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194673 prefixEnd_194673 := by exact prefixLift 194673
  have htrace : WordTrace (prefixWord ++ tailWord_194673) baseStart_194673 baseEnd_194673 := by
    simpa [prefixWord, tailWord_194673, baseEnd_194673] using wordTrace_append hprefix tailTrace_194673
  have hstable : (prefixWord ++ tailWord_194673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194673).length < 2 ^ (prefixWord ++ tailWord_194673).sum := by decide
  have hdescent : baseEnd_194673 < baseStart_194673 := by decide
  rcases family_descends (prefixWord ++ tailWord_194673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194697 : List Nat := [1, 2, 1, 1, 4, 2, 5, 4]
def baseStart_194697 : Nat := 118140960795 + 194697 * 2 ^ 59
def prefixEnd_194697 : Nat := 4983230072969 + 3 ^ 40 * 194697 * 2
def baseEnd_194697 : Nat := 29621671996601475790255

theorem tailTrace_194697 : CollatzResearch.WordTrace tailWord_194697 prefixEnd_194697 29621671996601475790255 := by
  unfold tailWord_194697
  simp only [CollatzResearch.WordTrace]
  refine ⟨7101182975653495445414345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4734121983768996963609563 7101182975653495445414345)
  ·
    refine ⟨5325887231740121584060759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7101182975653495445414345 5325887231740121584060759)
    ·
      refine ⟨7988830847610182376091139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5325887231740121584060759 7988830847610182376091139)
      ·
        refine ⟨11983246271415273564136709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7988830847610182376091139 11983246271415273564136709)
        ·
          refine ⟨2246858675890363793275633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11983246271415273564136709 2246858675890363793275633)
          ·
            refine ⟨1685144006917772844956725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2246858675890363793275633 1685144006917772844956725)
            ·
              refine ⟨157982250648541204214693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1685144006917772844956725 157982250648541204214693)
              ·
                refine ⟨29621671996601475790255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157982250648541204214693 29621671996601475790255)
                ·
                  rfl

theorem cell20_194697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 4].length) (baseStart_194697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194697 prefixEnd_194697 := by exact prefixLift 194697
  have htrace : WordTrace (prefixWord ++ tailWord_194697) baseStart_194697 baseEnd_194697 := by
    simpa [prefixWord, tailWord_194697, baseEnd_194697] using wordTrace_append hprefix tailTrace_194697
  have hstable : (prefixWord ++ tailWord_194697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194697).length < 2 ^ (prefixWord ++ tailWord_194697).sum := by decide
  have hdescent : baseEnd_194697 < baseStart_194697 := by decide
  rcases family_descends (prefixWord ++ tailWord_194697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194721 : List Nat := [1, 2, 3, 3, 1, 2, 3, 2, 3]
def baseStart_194721 : Nat := 118140960795 + 194721 * 2 ^ 59
def prefixEnd_194721 : Nat := 4983230072969 + 3 ^ 40 * 194721 * 2
def baseEnd_194721 : Nat := 88875970243767010570667

theorem tailTrace_194721 : CollatzResearch.WordTrace tailWord_194721 prefixEnd_194721 88875970243767010570667 := by
  unfold tailWord_194721
  simp only [CollatzResearch.WordTrace]
  refine ⟨7102058327566547544288017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4734705551711031696192011 7102058327566547544288017)
  ·
    refine ⟨5326543745674910658216013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7102058327566547544288017 5326543745674910658216013)
    ·
      refine ⟨1997453904628091496831005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5326543745674910658216013 1997453904628091496831005)
      ·
        refine ⟨749045214235534311311627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1997453904628091496831005 749045214235534311311627)
        ·
          refine ⟨1123567821353301466967441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749045214235534311311627 1123567821353301466967441)
          ·
            refine ⟨842675866014976100225581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1123567821353301466967441 842675866014976100225581)
            ·
              refine ⟨316003449755616037584593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 842675866014976100225581 316003449755616037584593)
              ·
                refine ⟨237002587316712028188445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 316003449755616037584593 237002587316712028188445)
                ·
                  refine ⟨88875970243767010570667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237002587316712028188445 88875970243767010570667)
                  ·
                    rfl

theorem cell20_194721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_194721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194721 prefixEnd_194721 := by exact prefixLift 194721
  have htrace : WordTrace (prefixWord ++ tailWord_194721) baseStart_194721 baseEnd_194721 := by
    simpa [prefixWord, tailWord_194721, baseEnd_194721] using wordTrace_append hprefix tailTrace_194721
  have hstable : (prefixWord ++ tailWord_194721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194721).length < 2 ^ (prefixWord ++ tailWord_194721).sum := by decide
  have hdescent : baseEnd_194721 < baseStart_194721 := by decide
  rcases family_descends (prefixWord ++ tailWord_194721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194734 : List Nat := [4, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_194734 : Nat := 118140960795 + 194734 * 2 ^ 59
def prefixEnd_194734 : Nat := 4983230072969 + 3 ^ 40 * 194734 * 2
def baseEnd_194734 : Nat := 88881903797996743137281

theorem tailTrace_194734 : CollatzResearch.WordTrace tailWord_194734 prefixEnd_194734 88881903797996743137281 := by
  unfold tailWord_194734
  simp only [CollatzResearch.WordTrace]
  refine ⟨887816559564931345563907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4735021651012967176340837 887816559564931345563907)
  ·
    refine ⟨1331724839347397018345861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 887816559564931345563907 1331724839347397018345861)
    ·
      refine ⟨249698407377636940939849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1331724839347397018345861 249698407377636940939849)
      ·
        refine ⟨187273805533227705704887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249698407377636940939849 187273805533227705704887)
        ·
          refine ⟨280910708299841558557331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187273805533227705704887 280910708299841558557331)
          ·
            refine ⟨421366062449762337835997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280910708299841558557331 421366062449762337835997)
            ·
              refine ⟨158012273418660876688499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 421366062449762337835997 158012273418660876688499)
              ·
                refine ⟨237018410127991315032749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158012273418660876688499 237018410127991315032749)
                ·
                  refine ⟨88881903797996743137281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237018410127991315032749 88881903797996743137281)
                  ·
                    rfl

theorem cell20_194734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_194734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194734 prefixEnd_194734 := by exact prefixLift 194734
  have htrace : WordTrace (prefixWord ++ tailWord_194734) baseStart_194734 baseEnd_194734 := by
    simpa [prefixWord, tailWord_194734, baseEnd_194734] using wordTrace_append hprefix tailTrace_194734
  have hstable : (prefixWord ++ tailWord_194734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194734).length < 2 ^ (prefixWord ++ tailWord_194734).sum := by decide
  have hdescent : baseEnd_194734 < baseStart_194734 := by decide
  rcases family_descends (prefixWord ++ tailWord_194734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194752 : List Nat := [2, 1, 1, 2, 5, 3, 2, 4]
def baseStart_194752 : Nat := 118140960795 + 194752 * 2 ^ 59
def prefixEnd_194752 : Nat := 4983230072969 + 3 ^ 40 * 194752 * 2
def baseEnd_194752 : Nat := 29630039829489560179069

theorem tailTrace_194752 : CollatzResearch.WordTrace tailWord_194752 prefixEnd_194752 29630039829489560179069 := by
  unfold tailWord_194752
  simp only [CollatzResearch.WordTrace]
  refine ⟨3551594495227119919333255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4735459326969493225777673 3551594495227119919333255)
  ·
    refine ⟨5327391742840679878999883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3551594495227119919333255 5327391742840679878999883)
    ·
      refine ⟨7991087614261019818499825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5327391742840679878999883 7991087614261019818499825)
      ·
        refine ⟨5993315710695764863874869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7991087614261019818499825 5993315710695764863874869)
        ·
          refine ⟨561873347877727955988269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5993315710695764863874869 561873347877727955988269)
          ·
            refine ⟨210702505454147983495601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 561873347877727955988269 210702505454147983495601)
            ·
              refine ⟨158026879090610987621701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210702505454147983495601 158026879090610987621701)
              ·
                refine ⟨29630039829489560179069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158026879090610987621701 29630039829489560179069)
                ·
                  rfl

theorem cell20_194752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_194752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194752 prefixEnd_194752 := by exact prefixLift 194752
  have htrace : WordTrace (prefixWord ++ tailWord_194752) baseStart_194752 baseEnd_194752 := by
    simpa [prefixWord, tailWord_194752, baseEnd_194752] using wordTrace_append hprefix tailTrace_194752
  have hstable : (prefixWord ++ tailWord_194752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194752).length < 2 ^ (prefixWord ++ tailWord_194752).sum := by decide
  have hdescent : baseEnd_194752 < baseStart_194752 := by decide
  rcases family_descends (prefixWord ++ tailWord_194752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194763 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 7]
def baseStart_194763 : Nat := 118140960795 + 194763 * 2 ^ 59
def prefixEnd_194763 : Nat := 4983230072969 + 3 ^ 40 * 194763 * 2
def baseEnd_194763 : Nat := 88895140188201531170495

theorem tailTrace_194763 : CollatzResearch.WordTrace tailWord_194763 prefixEnd_194763 88895140188201531170495 := by
  unfold tailWord_194763
  simp only [CollatzResearch.WordTrace]
  refine ⟨7103590193414388717316943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4735726795609592478211295 7103590193414388717316943)
  ·
    refine ⟨10655385290121583075975415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7103590193414388717316943 10655385290121583075975415)
    ·
      refine ⟨15983077935182374613963123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10655385290121583075975415 15983077935182374613963123)
      ·
        refine ⟨23974616902773561920944685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15983077935182374613963123 23974616902773561920944685)
        ·
          refine ⟨8990481338540085720354257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23974616902773561920944685 8990481338540085720354257)
          ·
            refine ⟨6742861003905064290265693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8990481338540085720354257 6742861003905064290265693)
            ·
              refine ⟨2528572876464399108849635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6742861003905064290265693 2528572876464399108849635)
              ·
                refine ⟨3792859314696598663274453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2528572876464399108849635 3792859314696598663274453)
                ·
                  refine ⟨88895140188201531170495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3792859314696598663274453 88895140188201531170495)
                  ·
                    rfl

theorem cell20_194763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_194763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194763 prefixEnd_194763 := by exact prefixLift 194763
  have htrace : WordTrace (prefixWord ++ tailWord_194763) baseStart_194763 baseEnd_194763 := by
    simpa [prefixWord, tailWord_194763, baseEnd_194763] using wordTrace_append hprefix tailTrace_194763
  have hstable : (prefixWord ++ tailWord_194763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194763).length < 2 ^ (prefixWord ++ tailWord_194763).sum := by decide
  have hdescent : baseEnd_194763 < baseStart_194763 := by decide
  rcases family_descends (prefixWord ++ tailWord_194763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194786 : List Nat := [3, 3, 4, 1, 1, 1, 2, 5]
def baseStart_194786 : Nat := 118140960795 + 194786 * 2 ^ 59
def prefixEnd_194786 : Nat := 4983230072969 + 3 ^ 40 * 194786 * 2
def baseEnd_194786 : Nat := 29635212671638557801245

theorem tailTrace_194786 : CollatzResearch.WordTrace tailWord_194786 prefixEnd_194786 29635212671638557801245 := by
  unfold tailWord_194786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1776107268082765911351053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4736286048220709096936141 1776107268082765911351053)
  ·
    refine ⟨666040225531037216756645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1776107268082765911351053 666040225531037216756645)
    ·
      refine ⟨124882542287069478141871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 666040225531037216756645 124882542287069478141871)
      ·
        refine ⟨187323813430604217212807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124882542287069478141871 187323813430604217212807)
        ·
          refine ⟨280985720145906325819211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187323813430604217212807 280985720145906325819211)
          ·
            refine ⟨421478580218859488728817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280985720145906325819211 421478580218859488728817)
            ·
              refine ⟨316108935164144616546613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421478580218859488728817 316108935164144616546613)
              ·
                refine ⟨29635212671638557801245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 316108935164144616546613 29635212671638557801245)
                ·
                  rfl

theorem cell20_194786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_194786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194786 prefixEnd_194786 := by exact prefixLift 194786
  have htrace : WordTrace (prefixWord ++ tailWord_194786) baseStart_194786 baseEnd_194786 := by
    simpa [prefixWord, tailWord_194786, baseEnd_194786] using wordTrace_append hprefix tailTrace_194786
  have hstable : (prefixWord ++ tailWord_194786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194786).length < 2 ^ (prefixWord ++ tailWord_194786).sum := by decide
  have hdescent : baseEnd_194786 < baseStart_194786 := by decide
  rcases family_descends (prefixWord ++ tailWord_194786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194845 : List Nat := [1, 4, 2, 3, 3, 1, 1, 5]
def baseStart_194845 : Nat := 118140960795 + 194845 * 2 ^ 59
def prefixEnd_194845 : Nat := 4983230072969 + 3 ^ 40 * 194845 * 2
def baseEnd_194845 : Nat := 29644189074191230145609

theorem tailTrace_194845 : CollatzResearch.WordTrace tailWord_194845 prefixEnd_194845 29644189074191230145609 := by
  unfold tailWord_194845
  simp only [CollatzResearch.WordTrace]
  refine ⟨7106580979117316721801989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4737720652744877814534659 7106580979117316721801989)
  ·
    refine ⟨1332483933584496885337873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7106580979117316721801989 1332483933584496885337873)
    ·
      refine ⟨999362950188372664003405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1332483933584496885337873 999362950188372664003405)
      ·
        refine ⟨374761106320639749001277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 999362950188372664003405 374761106320639749001277)
        ·
          refine ⟨140535414870239905875479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374761106320639749001277 140535414870239905875479)
          ·
            refine ⟨210803122305359858813219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140535414870239905875479 210803122305359858813219)
            ·
              refine ⟨316204683458039788219829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210803122305359858813219 316204683458039788219829)
              ·
                refine ⟨29644189074191230145609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 316204683458039788219829 29644189074191230145609)
                ·
                  rfl

theorem cell20_194845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 5].length) (baseStart_194845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194845 prefixEnd_194845 := by exact prefixLift 194845
  have htrace : WordTrace (prefixWord ++ tailWord_194845) baseStart_194845 baseEnd_194845 := by
    simpa [prefixWord, tailWord_194845, baseEnd_194845] using wordTrace_append hprefix tailTrace_194845
  have hstable : (prefixWord ++ tailWord_194845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194845).length < 2 ^ (prefixWord ++ tailWord_194845).sum := by decide
  have hdescent : baseEnd_194845 < baseStart_194845 := by decide
  rcases family_descends (prefixWord ++ tailWord_194845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194866 : List Nat := [3, 2, 1, 1, 5, 1, 3, 4]
def baseStart_194866 : Nat := 118140960795 + 194866 * 2 ^ 59
def prefixEnd_194866 : Nat := 4983230072969 + 3 ^ 40 * 194866 * 2
def baseEnd_194866 : Nat := 29647384064930316912247

theorem tailTrace_194866 : CollatzResearch.WordTrace tailWord_194866 prefixEnd_194866 29647384064930316912247 := by
  unfold tailWord_194866
  simp only [CollatzResearch.WordTrace]
  refine ⟨1776836728010309327079113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4738231274694158205544301 1776836728010309327079113)
  ·
    refine ⟨1332627546007731995309335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1776836728010309327079113 1332627546007731995309335)
    ·
      refine ⟨1998941319011597992964003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1332627546007731995309335 1998941319011597992964003)
      ·
        refine ⟨2998411978517396989446005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1998941319011597992964003 2998411978517396989446005)
        ·
          refine ⟨281101122986005967760563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2998411978517396989446005 281101122986005967760563)
          ·
            refine ⟨421651684479008951640845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281101122986005967760563 421651684479008951640845)
            ·
              refine ⟨158119381679628356865317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 421651684479008951640845 158119381679628356865317)
              ·
                refine ⟨29647384064930316912247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158119381679628356865317 29647384064930316912247)
                ·
                  rfl

theorem cell20_194866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_194866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194866 prefixEnd_194866 := by exact prefixLift 194866
  have htrace : WordTrace (prefixWord ++ tailWord_194866) baseStart_194866 baseEnd_194866 := by
    simpa [prefixWord, tailWord_194866, baseEnd_194866] using wordTrace_append hprefix tailTrace_194866
  have hstable : (prefixWord ++ tailWord_194866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194866).length < 2 ^ (prefixWord ++ tailWord_194866).sum := by decide
  have hdescent : baseEnd_194866 < baseStart_194866 := by decide
  rcases family_descends (prefixWord ++ tailWord_194866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194894 : List Nat := [4, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_194894 : Nat := 118140960795 + 194894 * 2 ^ 59
def prefixEnd_194894 : Nat := 4983230072969 + 3 ^ 40 * 194894 * 2
def baseEnd_194894 : Nat := 88954932157747297803293

theorem tailTrace_194894 : CollatzResearch.WordTrace tailWord_194894 prefixEnd_194894 88954932157747297803293 := by
  unfold tailWord_194894
  simp only [CollatzResearch.WordTrace]
  refine ⟨888546019492474761291967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4738912103959865393557157 888546019492474761291967)
  ·
    refine ⟨1332819029238712141937951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 888546019492474761291967 1332819029238712141937951)
    ·
      refine ⟨1999228543858068212906927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1332819029238712141937951 1999228543858068212906927)
      ·
        refine ⟨2998842815787102319360391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1999228543858068212906927 2998842815787102319360391)
        ·
          refine ⟨4498264223680653479040587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2998842815787102319360391 4498264223680653479040587)
          ·
            refine ⟨6747396335520980218560881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4498264223680653479040587 6747396335520980218560881)
            ·
              refine ⟨5060547251640735163920661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6747396335520980218560881 5060547251640735163920661)
              ·
                refine ⟨237213152420659460808781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5060547251640735163920661 237213152420659460808781)
                ·
                  refine ⟨88954932157747297803293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237213152420659460808781 88954932157747297803293)
                  ·
                    rfl

theorem cell20_194894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_194894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194894 prefixEnd_194894 := by exact prefixLift 194894
  have htrace : WordTrace (prefixWord ++ tailWord_194894) baseStart_194894 baseEnd_194894 := by
    simpa [prefixWord, tailWord_194894, baseEnd_194894] using wordTrace_append hprefix tailTrace_194894
  have hstable : (prefixWord ++ tailWord_194894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194894).length < 2 ^ (prefixWord ++ tailWord_194894).sum := by decide
  have hdescent : baseEnd_194894 < baseStart_194894 := by decide
  rcases family_descends (prefixWord ++ tailWord_194894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194956 : List Nat := [2, 2, 1, 2, 1, 6, 1, 1, 4]
def baseStart_194956 : Nat := 118140960795 + 194956 * 2 ^ 59
def prefixEnd_194956 : Nat := 4983230072969 + 3 ^ 40 * 194956 * 2
def baseEnd_194956 : Nat := 88983230647150637736373

theorem tailTrace_194956 : CollatzResearch.WordTrace tailWord_194956 prefixEnd_194956 88983230647150637736373 := by
  unfold tailWord_194956
  simp only [CollatzResearch.WordTrace]
  refine ⟨3555314740857591339546361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4740419654476788452728481 3555314740857591339546361)
  ·
    refine ⟨2666486055643193504659771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3555314740857591339546361 2666486055643193504659771)
    ·
      refine ⟨3999729083464790256989657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2666486055643193504659771 3999729083464790256989657)
      ·
        refine ⟨2999796812598592692742243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3999729083464790256989657 2999796812598592692742243)
        ·
          refine ⟨4499695218897889039113365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2999796812598592692742243 4499695218897889039113365)
          ·
            refine ⟨210923213385838548708439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4499695218897889039113365 210923213385838548708439)
            ·
              refine ⟨316384820078757823062659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210923213385838548708439 316384820078757823062659)
              ·
                refine ⟨474577230118136734593989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316384820078757823062659 474577230118136734593989)
                ·
                  refine ⟨88983230647150637736373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 474577230118136734593989 88983230647150637736373)
                  ·
                    rfl

theorem cell20_194956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_194956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194956 prefixEnd_194956 := by exact prefixLift 194956
  have htrace : WordTrace (prefixWord ++ tailWord_194956) baseStart_194956 baseEnd_194956 := by
    simpa [prefixWord, tailWord_194956, baseEnd_194956] using wordTrace_append hprefix tailTrace_194956
  have hstable : (prefixWord ++ tailWord_194956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194956).length < 2 ^ (prefixWord ++ tailWord_194956).sum := by decide
  have hdescent : baseEnd_194956 < baseStart_194956 := by decide
  rcases family_descends (prefixWord ++ tailWord_194956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194960 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 10]
def baseStart_194960 : Nat := 118140960795 + 194960 * 2 ^ 59
def prefixEnd_194960 : Nat := 4983230072969 + 3 ^ 40 * 194960 * 2
def baseEnd_194960 : Nat := 88985056356144401603023

theorem tailTrace_194960 : CollatzResearch.WordTrace tailWord_194960 prefixEnd_194960 88985056356144401603023 := by
  unfold tailWord_194960
  simp only [CollatzResearch.WordTrace]
  refine ⟨3555387686850345681119167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4740516915800460908158889 3555387686850345681119167)
  ·
    refine ⟨5333081530275518521678751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3555387686850345681119167 5333081530275518521678751)
    ·
      refine ⟨7999622295413277782518127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5333081530275518521678751 7999622295413277782518127)
      ·
        refine ⟨11999433443119916673777191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7999622295413277782518127 11999433443119916673777191)
        ·
          refine ⟨17999150164679875010665787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11999433443119916673777191 17999150164679875010665787)
          ·
            refine ⟨26998725247019812515998681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17999150164679875010665787 26998725247019812515998681)
            ·
              refine ⟨20249043935264859386999011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26998725247019812515998681 20249043935264859386999011)
              ·
                refine ⟨30373565902897289080498517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20249043935264859386999011 30373565902897289080498517)
                ·
                  refine ⟨88985056356144401603023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 30373565902897289080498517 88985056356144401603023)
                  ·
                    rfl

theorem cell20_194960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_194960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194960 prefixEnd_194960 := by exact prefixLift 194960
  have htrace : WordTrace (prefixWord ++ tailWord_194960) baseStart_194960 baseEnd_194960 := by
    simpa [prefixWord, tailWord_194960, baseEnd_194960] using wordTrace_append hprefix tailTrace_194960
  have hstable : (prefixWord ++ tailWord_194960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194960).length < 2 ^ (prefixWord ++ tailWord_194960).sum := by decide
  have hdescent : baseEnd_194960 < baseStart_194960 := by decide
  rcases family_descends (prefixWord ++ tailWord_194960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194994 : List Nat := [3, 2, 1, 1, 1, 1, 4, 5, 2]
def baseStart_194994 : Nat := 118140960795 + 194994 * 2 ^ 59
def prefixEnd_194994 : Nat := 4983230072969 + 3 ^ 40 * 194994 * 2
def baseEnd_194994 : Nat := 89000574882591394469551

theorem tailTrace_194994 : CollatzResearch.WordTrace tailWord_194994 prefixEnd_194994 89000574882591394469551 := by
  unfold tailWord_194994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1778003863894378792244009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4741343637051676779317357 1778003863894378792244009)
  ·
    refine ⟨1333502897920784094183007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1778003863894378792244009 1333502897920784094183007)
    ·
      refine ⟨2000254346881176141274511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1333502897920784094183007 2000254346881176141274511)
      ·
        refine ⟨3000381520321764211911767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2000254346881176141274511 3000381520321764211911767)
        ·
          refine ⟨4500572280482646317867651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3000381520321764211911767 4500572280482646317867651)
          ·
            refine ⟨6750858420723969476801477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4500572280482646317867651 6750858420723969476801477)
            ·
              refine ⟨1265785953885744276900277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6750858420723969476801477 1265785953885744276900277)
              ·
                refine ⟨118667433176788525959401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1265785953885744276900277 118667433176788525959401)
                ·
                  refine ⟨89000574882591394469551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118667433176788525959401 89000574882591394469551)
                  ·
                    rfl

theorem cell20_194994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_194994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_194994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_194994 prefixEnd_194994 := by exact prefixLift 194994
  have htrace : WordTrace (prefixWord ++ tailWord_194994) baseStart_194994 baseEnd_194994 := by
    simpa [prefixWord, tailWord_194994, baseEnd_194994] using wordTrace_append hprefix tailTrace_194994
  have hstable : (prefixWord ++ tailWord_194994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194994).length < 2 ^ (prefixWord ++ tailWord_194994).sum := by decide
  have hdescent : baseEnd_194994 < baseStart_194994 := by decide
  rcases family_descends (prefixWord ++ tailWord_194994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195039 : List Nat := [1, 1, 2, 3, 3, 3, 3, 4]
def baseStart_195039 : Nat := 118140960795 + 195039 * 2 ^ 59
def prefixEnd_195039 : Nat := 4983230072969 + 3 ^ 40 * 195039 * 2
def baseEnd_195039 : Nat := 29673704702923745989789

theorem tailTrace_195039 : CollatzResearch.WordTrace tailWord_195039 prefixEnd_195039 29673704702923745989789 := by
  unfold tailWord_195039
  simp only [CollatzResearch.WordTrace]
  refine ⟨7113656740414487854364171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4742437826942991902909447 7113656740414487854364171)
  ·
    refine ⟨10670485110621731781546257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7113656740414487854364171 10670485110621731781546257)
    ·
      refine ⟨8002863832966298836159693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10670485110621731781546257 8002863832966298836159693)
      ·
        refine ⟨3001073937362362063559885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8002863832966298836159693 3001073937362362063559885)
        ·
          refine ⟨1125402726510885773834957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3001073937362362063559885 1125402726510885773834957)
          ·
            refine ⟨422026022441582165188109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1125402726510885773834957 422026022441582165188109)
            ·
              refine ⟨158259758415593311945541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 422026022441582165188109 158259758415593311945541)
              ·
                refine ⟨29673704702923745989789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158259758415593311945541 29673704702923745989789)
                ·
                  rfl

theorem cell20_195039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 4].length) (baseStart_195039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195039 prefixEnd_195039 := by exact prefixLift 195039
  have htrace : WordTrace (prefixWord ++ tailWord_195039) baseStart_195039 baseEnd_195039 := by
    simpa [prefixWord, tailWord_195039, baseEnd_195039] using wordTrace_append hprefix tailTrace_195039
  have hstable : (prefixWord ++ tailWord_195039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195039).length < 2 ^ (prefixWord ++ tailWord_195039).sum := by decide
  have hdescent : baseEnd_195039 < baseStart_195039 := by decide
  rcases family_descends (prefixWord ++ tailWord_195039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195104 : List Nat := [2, 1, 1, 6, 2, 2, 1, 3, 2]
def baseStart_195104 : Nat := 118140960795 + 195104 * 2 ^ 59
def prefixEnd_195104 : Nat := 4983230072969 + 3 ^ 40 * 195104 * 2
def baseEnd_195104 : Nat := 89050781879919900802435

theorem tailTrace_195104 : CollatzResearch.WordTrace tailWord_195104 prefixEnd_195104 89050781879919900802435 := by
  unfold tailWord_195104
  simp only [CollatzResearch.WordTrace]
  refine ⟨3558013742589501977740183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4744018323452669303653577 3558013742589501977740183)
  ·
    refine ⟨5337020613884252966610275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3558013742589501977740183 5337020613884252966610275)
    ·
      refine ⟨8005530920826379449915413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5337020613884252966610275 8005530920826379449915413)
      ·
        refine ⟨375259261913736536714785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8005530920826379449915413 375259261913736536714785)
        ·
          refine ⟨281444446435302402536089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375259261913736536714785 281444446435302402536089)
          ·
            refine ⟨211083334826476801902067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281444446435302402536089 211083334826476801902067)
            ·
              refine ⟨316625002239715202853101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211083334826476801902067 316625002239715202853101)
              ·
                refine ⟨118734375839893201069913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316625002239715202853101 118734375839893201069913)
                ·
                  refine ⟨89050781879919900802435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118734375839893201069913 89050781879919900802435)
                  ·
                    rfl

theorem cell20_195104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 2].length) (baseStart_195104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195104 prefixEnd_195104 := by exact prefixLift 195104
  have htrace : WordTrace (prefixWord ++ tailWord_195104) baseStart_195104 baseEnd_195104 := by
    simpa [prefixWord, tailWord_195104, baseEnd_195104] using wordTrace_append hprefix tailTrace_195104
  have hstable : (prefixWord ++ tailWord_195104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195104).length < 2 ^ (prefixWord ++ tailWord_195104).sum := by decide
  have hdescent : baseEnd_195104 < baseStart_195104 := by decide
  rcases family_descends (prefixWord ++ tailWord_195104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195105 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 7]
def baseStart_195105 : Nat := 118140960795 + 195105 * 2 ^ 59
def prefixEnd_195105 : Nat := 4983230072969 + 3 ^ 40 * 195105 * 2
def baseEnd_195105 : Nat := 89051238307168341769097

theorem tailTrace_195105 : CollatzResearch.WordTrace tailWord_195105 prefixEnd_195105 89051238307168341769097 := by
  unfold tailWord_195105
  simp only [CollatzResearch.WordTrace]
  refine ⟨7116063958175381126266769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4744042638783587417511179 7116063958175381126266769)
  ·
    refine ⟨5337047968631535844700077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7116063958175381126266769 5337047968631535844700077)
    ·
      refine ⟨2001392988236825941762529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5337047968631535844700077 2001392988236825941762529)
      ·
        refine ⟨1501044741177619456321897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2001392988236825941762529 1501044741177619456321897)
        ·
          refine ⟨1125783555883214592241423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1501044741177619456321897 1125783555883214592241423)
          ·
            refine ⟨1688675333824821888362135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125783555883214592241423 1688675333824821888362135)
            ·
              refine ⟨2533013000737232832543203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1688675333824821888362135 2533013000737232832543203)
              ·
                refine ⟨3799519501105849248814805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533013000737232832543203 3799519501105849248814805)
                ·
                  refine ⟨89051238307168341769097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3799519501105849248814805 89051238307168341769097)
                  ·
                    rfl

theorem cell20_195105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_195105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195105 prefixEnd_195105 := by exact prefixLift 195105
  have htrace : WordTrace (prefixWord ++ tailWord_195105) baseStart_195105 baseEnd_195105 := by
    simpa [prefixWord, tailWord_195105, baseEnd_195105] using wordTrace_append hprefix tailTrace_195105
  have hstable : (prefixWord ++ tailWord_195105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195105).length < 2 ^ (prefixWord ++ tailWord_195105).sum := by decide
  have hdescent : baseEnd_195105 < baseStart_195105 := by decide
  rcases family_descends (prefixWord ++ tailWord_195105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195111 : List Nat := [1, 1, 7, 2, 2, 1, 6]
def baseStart_195111 : Nat := 118140960795 + 195111 * 2 ^ 59
def prefixEnd_195111 : Nat := 4983230072969 + 3 ^ 40 * 195111 * 2
def baseEnd_195111 : Nat := 9894886318962109729897

theorem tailTrace_195111 : CollatzResearch.WordTrace tailWord_195111 prefixEnd_195111 9894886318962109729897 := by
  unfold tailWord_195111
  simp only [CollatzResearch.WordTrace]
  refine ⟨7116282796153644150985187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4744188530769096100656791 7116282796153644150985187)
  ·
    refine ⟨10674424194230466226477781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7116282796153644150985187 10674424194230466226477781)
    ·
      refine ⟨250181817052276552183073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 10674424194230466226477781 250181817052276552183073)
      ·
        refine ⟨187636362789207414137305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250181817052276552183073 187636362789207414137305)
        ·
          refine ⟨140727272091905560602979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187636362789207414137305 140727272091905560602979)
          ·
            refine ⟨211090908137858340904469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140727272091905560602979 211090908137858340904469)
            ·
              refine ⟨9894886318962109729897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 211090908137858340904469 9894886318962109729897)
              ·
                rfl

theorem cell20_195111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 6].length) (baseStart_195111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195111 prefixEnd_195111 := by exact prefixLift 195111
  have htrace : WordTrace (prefixWord ++ tailWord_195111) baseStart_195111 baseEnd_195111 := by
    simpa [prefixWord, tailWord_195111, baseEnd_195111] using wordTrace_append hprefix tailTrace_195111
  have hstable : (prefixWord ++ tailWord_195111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195111).length < 2 ^ (prefixWord ++ tailWord_195111).sum := by decide
  have hdescent : baseEnd_195111 < baseStart_195111 := by decide
  rcases family_descends (prefixWord ++ tailWord_195111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195125 : List Nat := [1, 3, 3, 1, 1, 2, 5, 2, 2]
def baseStart_195125 : Nat := 118140960795 + 195125 * 2 ^ 59
def prefixEnd_195125 : Nat := 4983230072969 + 3 ^ 40 * 195125 * 2
def baseEnd_195125 : Nat := 89060366852137161102349

theorem tailTrace_195125 : CollatzResearch.WordTrace tailWord_195125 prefixEnd_195125 89060366852137161102349 := by
  unfold tailWord_195125
  simp only [CollatzResearch.WordTrace]
  refine ⟨7116793418102924541994829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4744528945401949694663219 7116793418102924541994829)
  ·
    refine ⟨2668797531788596703248061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7116793418102924541994829 2668797531788596703248061)
    ·
      refine ⟨1000799074420723763718023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2668797531788596703248061 1000799074420723763718023)
      ·
        refine ⟨1501198611631085645577035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1000799074420723763718023 1501198611631085645577035)
        ·
          refine ⟨2251797917446628468365553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1501198611631085645577035 2251797917446628468365553)
          ·
            refine ⟨1688848438084971351274165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2251797917446628468365553 1688848438084971351274165)
            ·
              refine ⟨158329541070466064181953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1688848438084971351274165 158329541070466064181953)
              ·
                refine ⟨118747155802849548136465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158329541070466064181953 118747155802849548136465)
                ·
                  refine ⟨89060366852137161102349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118747155802849548136465 89060366852137161102349)
                  ·
                    rfl

theorem cell20_195125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_195125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195125 prefixEnd_195125 := by exact prefixLift 195125
  have htrace : WordTrace (prefixWord ++ tailWord_195125) baseStart_195125 baseEnd_195125 := by
    simpa [prefixWord, tailWord_195125, baseEnd_195125] using wordTrace_append hprefix tailTrace_195125
  have hstable : (prefixWord ++ tailWord_195125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195125).length < 2 ^ (prefixWord ++ tailWord_195125).sum := by decide
  have hdescent : baseEnd_195125 < baseStart_195125 := by decide
  rcases family_descends (prefixWord ++ tailWord_195125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195170 : List Nat := [3, 3, 2, 3, 2, 7]
def baseStart_195170 : Nat := 118140960795 + 195170 * 2 ^ 59
def prefixEnd_195170 : Nat := 4983230072969 + 3 ^ 40 * 195170 * 2
def baseEnd_195170 : Nat := 3299292817715444614895

theorem tailTrace_195170 : CollatzResearch.WordTrace tailWord_195170 prefixEnd_195170 3299292817715444614895 := by
  unfold tailWord_195170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1779608675734974306845741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4745623135293264818255309 1779608675734974306845741)
  ·
    refine ⟨667353253400615365067153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1779608675734974306845741 667353253400615365067153)
    ·
      refine ⟨500514940050461523800365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 667353253400615365067153 500514940050461523800365)
      ·
        refine ⟨187693102518923071425137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 500514940050461523800365 187693102518923071425137)
        ·
          refine ⟨140769826889192303568853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187693102518923071425137 140769826889192303568853)
          ·
            refine ⟨3299292817715444614895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 140769826889192303568853 3299292817715444614895)
            ·
              rfl

theorem cell20_195170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 7].length) (baseStart_195170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195170 prefixEnd_195170 := by exact prefixLift 195170
  have htrace : WordTrace (prefixWord ++ tailWord_195170) baseStart_195170 baseEnd_195170 := by
    simpa [prefixWord, tailWord_195170, baseEnd_195170] using wordTrace_append hprefix tailTrace_195170
  have hstable : (prefixWord ++ tailWord_195170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195170).length < 2 ^ (prefixWord ++ tailWord_195170).sum := by decide
  have hdescent : baseEnd_195170 < baseStart_195170 := by decide
  rcases family_descends (prefixWord ++ tailWord_195170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195195 : List Nat := [1, 1, 1, 1, 1, 4, 2, 9]
def baseStart_195195 : Nat := 118140960795 + 195195 * 2 ^ 59
def prefixEnd_195195 : Nat := 4983230072969 + 3 ^ 40 * 195195 * 2
def baseEnd_195195 : Nat := 29697438919842676256243

theorem tailTrace_195195 : CollatzResearch.WordTrace tailWord_195195 prefixEnd_195195 29697438919842676256243 := by
  unfold tailWord_195195
  simp only [CollatzResearch.WordTrace]
  refine ⟨7119346527849326497043039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4746231018566217664695359 7119346527849326497043039)
  ·
    refine ⟨10679019791773989745564559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7119346527849326497043039 10679019791773989745564559)
    ·
      refine ⟨16018529687660984618346839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10679019791773989745564559 16018529687660984618346839)
      ·
        refine ⟨24027794531491476927520259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16018529687660984618346839 24027794531491476927520259)
        ·
          refine ⟨36041691797237215391280389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24027794531491476927520259 36041691797237215391280389)
          ·
            refine ⟨6757817211981977885865073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36041691797237215391280389 6757817211981977885865073)
            ·
              refine ⟨5068362908986483414398805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6757817211981977885865073 5068362908986483414398805)
              ·
                refine ⟨29697438919842676256243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5068362908986483414398805 29697438919842676256243)
                ·
                  rfl

theorem cell20_195195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 9].length) (baseStart_195195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195195 prefixEnd_195195 := by exact prefixLift 195195
  have htrace : WordTrace (prefixWord ++ tailWord_195195) baseStart_195195 baseEnd_195195 := by
    simpa [prefixWord, tailWord_195195, baseEnd_195195] using wordTrace_append hprefix tailTrace_195195
  have hstable : (prefixWord ++ tailWord_195195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195195).length < 2 ^ (prefixWord ++ tailWord_195195).sum := by decide
  have hdescent : baseEnd_195195 < baseStart_195195 := by decide
  rcases family_descends (prefixWord ++ tailWord_195195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195205 : List Nat := [1, 3, 1, 1, 4, 3, 1, 2, 4]
def baseStart_195205 : Nat := 118140960795 + 195205 * 2 ^ 59
def prefixEnd_195205 : Nat := 4983230072969 + 3 ^ 40 * 195205 * 2
def baseEnd_195205 : Nat := 89096881032012438435355

theorem tailTrace_195205 : CollatzResearch.WordTrace tailWord_195205 prefixEnd_195205 89096881032012438435355 := by
  unfold tailWord_195205
  simp only [CollatzResearch.WordTrace]
  refine ⟨7119711257813098204907069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4746474171875398803271379 7119711257813098204907069)
  ·
    refine ⟨2669891721679911826840151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7119711257813098204907069 2669891721679911826840151)
    ·
      refine ⟨4004837582519867740260227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2669891721679911826840151 4004837582519867740260227)
      ·
        refine ⟨6007256373779801610390341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4004837582519867740260227 6007256373779801610390341)
        ·
          refine ⟨1126360570083712801948189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6007256373779801610390341 1126360570083712801948189)
          ·
            refine ⟨422385213781392300730571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1126360570083712801948189 422385213781392300730571)
            ·
              refine ⟨633577820672088451095857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422385213781392300730571 633577820672088451095857)
              ·
                refine ⟨475183365504066338321893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 633577820672088451095857 475183365504066338321893)
                ·
                  refine ⟨89096881032012438435355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 475183365504066338321893 89096881032012438435355)
                  ·
                    rfl

theorem cell20_195205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_195205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195205 prefixEnd_195205 := by exact prefixLift 195205
  have htrace : WordTrace (prefixWord ++ tailWord_195205) baseStart_195205 baseEnd_195205 := by
    simpa [prefixWord, tailWord_195205, baseEnd_195205] using wordTrace_append hprefix tailTrace_195205
  have hstable : (prefixWord ++ tailWord_195205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195205).length < 2 ^ (prefixWord ++ tailWord_195205).sum := by decide
  have hdescent : baseEnd_195205 < baseStart_195205 := by decide
  rcases family_descends (prefixWord ++ tailWord_195205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195232 : List Nat := [2, 1, 1, 4, 5, 1, 1, 2, 3]
def baseStart_195232 : Nat := 118140960795 + 195232 * 2 ^ 59
def prefixEnd_195232 : Nat := 4983230072969 + 3 ^ 40 * 195232 * 2
def baseEnd_195232 : Nat := 89109204567720344535245

theorem tailTrace_195232 : CollatzResearch.WordTrace tailWord_195232 prefixEnd_195232 89109204567720344535245 := by
  unfold tailWord_195232
  simp only [CollatzResearch.WordTrace]
  refine ⟨3560348014357640908069975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4747130685810187877426633 3560348014357640908069975)
  ·
    refine ⟨5340522021536461362104963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3560348014357640908069975 5340522021536461362104963)
    ·
      refine ⟨8010783032304692043157445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5340522021536461362104963 8010783032304692043157445)
      ·
        refine ⟨1502021818557129758092021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8010783032304692043157445 1502021818557129758092021)
        ·
          refine ⟨140814545489730914821127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1502021818557129758092021 140814545489730914821127)
          ·
            refine ⟨211221818234596372231691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140814545489730914821127 211221818234596372231691)
            ·
              refine ⟨316832727351894558347537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211221818234596372231691 316832727351894558347537)
              ·
                refine ⟨237624545513920918760653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 316832727351894558347537 237624545513920918760653)
                ·
                  refine ⟨89109204567720344535245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237624545513920918760653 89109204567720344535245)
                  ·
                    rfl

theorem cell20_195232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 3].length) (baseStart_195232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195232 prefixEnd_195232 := by exact prefixLift 195232
  have htrace : WordTrace (prefixWord ++ tailWord_195232) baseStart_195232 baseEnd_195232 := by
    simpa [prefixWord, tailWord_195232, baseEnd_195232] using wordTrace_append hprefix tailTrace_195232
  have hstable : (prefixWord ++ tailWord_195232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195232).length < 2 ^ (prefixWord ++ tailWord_195232).sum := by decide
  have hdescent : baseEnd_195232 < baseStart_195232 := by decide
  rcases family_descends (prefixWord ++ tailWord_195232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195239 : List Nat := [1, 1, 6, 3, 1, 1, 2, 1, 4]
def baseStart_195239 : Nat := 118140960795 + 195239 * 2 ^ 59
def prefixEnd_195239 : Nat := 4983230072969 + 3 ^ 40 * 195239 * 2
def baseEnd_195239 : Nat := 89112399558459431301883

theorem tailTrace_195239 : CollatzResearch.WordTrace tailWord_195239 prefixEnd_195239 89112399558459431301883 := by
  unfold tailWord_195239
  simp only [CollatzResearch.WordTrace]
  refine ⟨7120951339689922011644771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4747300893126614674429847 7120951339689922011644771)
  ·
    refine ⟨10681427009534883017467157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7120951339689922011644771 10681427009534883017467157)
    ·
      refine ⟨500691891071947641443773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10681427009534883017467157 500691891071947641443773)
      ·
        refine ⟨187759459151980365541415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 500691891071947641443773 187759459151980365541415)
        ·
          refine ⟨281639188727970548312123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187759459151980365541415 281639188727970548312123)
          ·
            refine ⟨422458783091955822468185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281639188727970548312123 422458783091955822468185)
            ·
              refine ⟨316844087318966866851139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 422458783091955822468185 316844087318966866851139)
              ·
                refine ⟨475266130978450300276709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316844087318966866851139 475266130978450300276709)
                ·
                  refine ⟨89112399558459431301883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 475266130978450300276709 89112399558459431301883)
                  ·
                    rfl

theorem cell20_195239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 4].length) (baseStart_195239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_195239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_195239 prefixEnd_195239 := by exact prefixLift 195239
  have htrace : WordTrace (prefixWord ++ tailWord_195239) baseStart_195239 baseEnd_195239 := by
    simpa [prefixWord, tailWord_195239, baseEnd_195239] using wordTrace_append hprefix tailTrace_195239
  have hstable : (prefixWord ++ tailWord_195239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195239).length < 2 ^ (prefixWord ++ tailWord_195239).sum := by decide
  have hdescent : baseEnd_195239 < baseStart_195239 := by decide
  rcases family_descends (prefixWord ++ tailWord_195239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
