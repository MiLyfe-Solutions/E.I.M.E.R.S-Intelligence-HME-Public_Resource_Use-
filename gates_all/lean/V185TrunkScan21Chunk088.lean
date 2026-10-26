import V185TrunkScan21Chunk087

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1068302 : List Nat := [4, 1, 1, 2, 1, 3, 9]
def baseStart_1068302 : Nat := 118140960795 + 1068302 * 2 ^ 59
def prefixEnd_1068302 : Nat := 4983230072969 + 3 ^ 40 * 1068302 * 2
def baseEnd_1068302 : Nat := 27089007909115283812937

theorem tailTrace_1068302 : CollatzResearch.WordTrace tailWord_1068302 prefixEnd_1068302 27089007909115283812937 := by
  unfold tailWord_1068302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4870521871966472537625895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25976116650487853534004773 4870521871966472537625895)
  ·
    refine ⟨7305782807949708806438843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4870521871966472537625895 7305782807949708806438843)
    ·
      refine ⟨10958674211924563209658265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7305782807949708806438843 10958674211924563209658265)
      ·
        refine ⟨8219005658943422407243699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10958674211924563209658265 8219005658943422407243699)
        ·
          refine ⟨12328508488415133610865549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8219005658943422407243699 12328508488415133610865549)
          ·
            refine ⟨4623190683155675104074581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12328508488415133610865549 4623190683155675104074581)
            ·
              refine ⟨27089007909115283812937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4623190683155675104074581 27089007909115283812937)
              ·
                rfl

theorem cell21_1068302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 9].length) (baseStart_1068302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068302 prefixEnd_1068302 := by exact prefixLift 1068302
  have htrace : WordTrace (prefixWord ++ tailWord_1068302) baseStart_1068302 baseEnd_1068302 := by
    simpa [prefixWord, tailWord_1068302, baseEnd_1068302] using wordTrace_append hprefix tailTrace_1068302
  have hstable : (prefixWord ++ tailWord_1068302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068302).length < 2 ^ (prefixWord ++ tailWord_1068302).sum := by decide
  have hdescent : baseEnd_1068302 < baseStart_1068302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068319 : List Nat := [1, 1, 2, 4, 4, 1, 2, 6]
def baseStart_1068319 : Nat := 118140960795 + 1068319 * 2 ^ 59
def prefixEnd_1068319 : Nat := 4983230072969 + 3 ^ 40 * 1068319 * 2
def baseEnd_1068319 : Nat := 81268316937883100844355

theorem tailTrace_1068319 : CollatzResearch.WordTrace tailWord_1068319 prefixEnd_1068319 81268316937883100844355 := by
  unfold tailWord_1068319
  simp only [CollatzResearch.WordTrace]
  refine ⟨38964795016670192204376011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25976530011113461469584007 38964795016670192204376011)
  ·
    refine ⟨58447192525005288306564017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38964795016670192204376011 58447192525005288306564017)
    ·
      refine ⟨43835394393753966229923013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58447192525005288306564017 43835394393753966229923013)
      ·
        refine ⟨8219136448828868668110565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43835394393753966229923013 8219136448828868668110565)
        ·
          refine ⟨1541088084155412875270731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8219136448828868668110565 1541088084155412875270731)
          ·
            refine ⟨2311632126233119312906097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1541088084155412875270731 2311632126233119312906097)
            ·
              refine ⟨1733724094674839484679573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2311632126233119312906097 1733724094674839484679573)
              ·
                refine ⟨81268316937883100844355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1733724094674839484679573 81268316937883100844355)
                ·
                  rfl

theorem cell21_1068319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 6].length) (baseStart_1068319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068319 prefixEnd_1068319 := by exact prefixLift 1068319
  have htrace : WordTrace (prefixWord ++ tailWord_1068319) baseStart_1068319 baseEnd_1068319 := by
    simpa [prefixWord, tailWord_1068319, baseEnd_1068319] using wordTrace_append hprefix tailTrace_1068319
  have hstable : (prefixWord ++ tailWord_1068319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068319).length < 2 ^ (prefixWord ++ tailWord_1068319).sum := by decide
  have hdescent : baseEnd_1068319 < baseStart_1068319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068364 : List Nat := [2, 2, 1, 3, 2, 2, 1, 4, 4]
def baseStart_1068364 : Nat := 118140960795 + 1068364 * 2 ^ 59
def prefixEnd_1068364 : Nat := 4983230072969 + 3 ^ 40 * 1068364 * 2
def baseEnd_1068364 : Nat := 243815220426739224282973

theorem tailTrace_1068364 : CollatzResearch.WordTrace tailWord_1068364 prefixEnd_1068364 243815220426739224282973 := by
  unfold tailWord_1068364
  simp only [CollatzResearch.WordTrace]
  refine ⟨19483218150753582444882073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25977624201004776593176097 19483218150753582444882073)
  ·
    refine ⟨14612413613065186833661555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19483218150753582444882073 14612413613065186833661555)
    ·
      refine ⟨21918620419597780250492333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14612413613065186833661555 21918620419597780250492333)
      ·
        refine ⟨8219482657349167593934625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21918620419597780250492333 8219482657349167593934625)
        ·
          refine ⟨6164611993011875695450969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8219482657349167593934625 6164611993011875695450969)
          ·
            refine ⟨4623458994758906771588227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6164611993011875695450969 4623458994758906771588227)
            ·
              refine ⟨6935188492138360157382341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4623458994758906771588227 6935188492138360157382341)
              ·
                refine ⟨1300347842275942529509189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6935188492138360157382341 1300347842275942529509189)
                ·
                  refine ⟨243815220426739224282973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1300347842275942529509189 243815220426739224282973)
                  ·
                    rfl

theorem cell21_1068364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_1068364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068364 prefixEnd_1068364 := by exact prefixLift 1068364
  have htrace : WordTrace (prefixWord ++ tailWord_1068364) baseStart_1068364 baseEnd_1068364 := by
    simpa [prefixWord, tailWord_1068364, baseEnd_1068364] using wordTrace_append hprefix tailTrace_1068364
  have hstable : (prefixWord ++ tailWord_1068364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068364).length < 2 ^ (prefixWord ++ tailWord_1068364).sum := by decide
  have hdescent : baseEnd_1068364 < baseStart_1068364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068378 : List Nat := [3, 1, 1, 2, 1, 2, 5, 6]
def baseStart_1068378 : Nat := 118140960795 + 1068378 * 2 ^ 59
def prefixEnd_1068378 : Nat := 4983230072969 + 3 ^ 40 * 1068378 * 2
def baseEnd_1068378 : Nat := 81272805139159437016537

theorem tailTrace_1068378 : CollatzResearch.WordTrace tailWord_1068378 prefixEnd_1068378 81272805139159437016537 := by
  unfold tailWord_1068378
  simp only [CollatzResearch.WordTrace]
  refine ⟨9741736730864111320193447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25977964615637630187182525 9741736730864111320193447)
  ·
    refine ⟨14612605096296166980290171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9741736730864111320193447 14612605096296166980290171)
    ·
      refine ⟨21918907644444250470435257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14612605096296166980290171 21918907644444250470435257)
      ·
        refine ⟨16439180733333187852826443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21918907644444250470435257 16439180733333187852826443)
        ·
          refine ⟨24658771099999781779239665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16439180733333187852826443 24658771099999781779239665)
          ·
            refine ⟨18494078324999836334429749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24658771099999781779239665 18494078324999836334429749)
            ·
              refine ⟨1733819842968734656352789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18494078324999836334429749 1733819842968734656352789)
              ·
                refine ⟨81272805139159437016537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1733819842968734656352789 81272805139159437016537)
                ·
                  rfl

theorem cell21_1068378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_1068378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068378 prefixEnd_1068378 := by exact prefixLift 1068378
  have htrace : WordTrace (prefixWord ++ tailWord_1068378) baseStart_1068378 baseEnd_1068378 := by
    simpa [prefixWord, tailWord_1068378, baseEnd_1068378] using wordTrace_append hprefix tailTrace_1068378
  have hstable : (prefixWord ++ tailWord_1068378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068378).length < 2 ^ (prefixWord ++ tailWord_1068378).sum := by decide
  have hdescent : baseEnd_1068378 < baseStart_1068378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068446 : List Nat := [4, 3, 1, 2, 3, 1, 2, 5]
def baseStart_1068446 : Nat := 118140960795 + 1068446 * 2 ^ 59
def prefixEnd_1068446 : Nat := 4983230072969 + 3 ^ 40 * 1068446 * 2
def baseEnd_1068446 : Nat := 81277977981308434638713

theorem tailTrace_1068446 : CollatzResearch.WordTrace tailWord_1068446 prefixEnd_1068446 81277977981308434638713 := by
  unfold tailWord_1068446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4871178385901261611781149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25979618058140061929499461 4871178385901261611781149)
  ·
    refine ⟨1826691894712973104417931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4871178385901261611781149 1826691894712973104417931)
    ·
      refine ⟨2740037842069459656626897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1826691894712973104417931 2740037842069459656626897)
      ·
        refine ⟨2055028381552094742470173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2740037842069459656626897 2055028381552094742470173)
        ·
          refine ⟨770635643082035528426315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2055028381552094742470173 770635643082035528426315)
          ·
            refine ⟨1155953464623053292639473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770635643082035528426315 1155953464623053292639473)
            ·
              refine ⟨866965098467289969479605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1155953464623053292639473 866965098467289969479605)
              ·
                refine ⟨81277977981308434638713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 866965098467289969479605 81277977981308434638713)
                ·
                  rfl

theorem cell21_1068446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_1068446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068446 prefixEnd_1068446 := by exact prefixLift 1068446
  have htrace : WordTrace (prefixWord ++ tailWord_1068446) baseStart_1068446 baseEnd_1068446 := by
    simpa [prefixWord, tailWord_1068446, baseEnd_1068446] using wordTrace_append hprefix tailTrace_1068446
  have hstable : (prefixWord ++ tailWord_1068446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068446).length < 2 ^ (prefixWord ++ tailWord_1068446).sum := by decide
  have hdescent : baseEnd_1068446 < baseStart_1068446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068530 : List Nat := [3, 2, 1, 4, 1, 10]
def baseStart_1068530 : Nat := 118140960795 + 1068530 * 2 ^ 59
def prefixEnd_1068530 : Nat := 4983230072969 + 3 ^ 40 * 1068530 * 2
def baseEnd_1068530 : Nat := 9031596440309623130221

theorem tailTrace_1068530 : CollatzResearch.WordTrace tailWord_1068530 prefixEnd_1068530 9031596440309623130221 := by
  unfold tailWord_1068530
  simp only [CollatzResearch.WordTrace]
  refine ⟨9743122704726443810076761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25981660545937183493538029 9743122704726443810076761)
  ·
    refine ⟨7307342028544832857557571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9743122704726443810076761 7307342028544832857557571)
    ·
      refine ⟨10961013042817249286336357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7307342028544832857557571 10961013042817249286336357)
      ·
        refine ⟨2055189945528234241188067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10961013042817249286336357 2055189945528234241188067)
        ·
          refine ⟨3082784918292351361782101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2055189945528234241188067 3082784918292351361782101)
          ·
            refine ⟨9031596440309623130221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3082784918292351361782101 9031596440309623130221)
            ·
              rfl

theorem cell21_1068530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 10].length) (baseStart_1068530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068530 prefixEnd_1068530 := by exact prefixLift 1068530
  have htrace : WordTrace (prefixWord ++ tailWord_1068530) baseStart_1068530 baseEnd_1068530 := by
    simpa [prefixWord, tailWord_1068530, baseEnd_1068530] using wordTrace_append hprefix tailTrace_1068530
  have hstable : (prefixWord ++ tailWord_1068530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068530).length < 2 ^ (prefixWord ++ tailWord_1068530).sum := by decide
  have hdescent : baseEnd_1068530 < baseStart_1068530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068533 : List Nat := [1, 3, 5, 1, 1, 1, 1, 4, 4]
def baseStart_1068533 : Nat := 118140960795 + 1068533 * 2 ^ 59
def prefixEnd_1068533 : Nat := 4983230072969 + 3 ^ 40 * 1068533 * 2
def baseEnd_1068533 : Nat := 243853788529232485965961

theorem tailTrace_1068533 : CollatzResearch.WordTrace tailWord_1068533 prefixEnd_1068533 243853788529232485965961 := by
  unfold tailWord_1068533
  simp only [CollatzResearch.WordTrace]
  refine ⟨38972600237894906752666253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25981733491929937835110835 38972600237894906752666253)
  ·
    refine ⟨14614725089210590032249845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38972600237894906752666253 14614725089210590032249845)
    ·
      refine ⟨1370130477113492815523423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14614725089210590032249845 1370130477113492815523423)
      ·
        refine ⟨2055195715670239223285135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1370130477113492815523423 2055195715670239223285135)
        ·
          refine ⟨3082793573505358834927703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2055195715670239223285135 3082793573505358834927703)
          ·
            refine ⟨4624190360258038252391555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3082793573505358834927703 4624190360258038252391555)
            ·
              refine ⟨6936285540387057378587333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4624190360258038252391555 6936285540387057378587333)
              ·
                refine ⟨1300553538822573258485125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6936285540387057378587333 1300553538822573258485125)
                ·
                  refine ⟨243853788529232485965961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1300553538822573258485125 243853788529232485965961)
                  ·
                    rfl

theorem cell21_1068533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_1068533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068533 prefixEnd_1068533 := by exact prefixLift 1068533
  have htrace : WordTrace (prefixWord ++ tailWord_1068533) baseStart_1068533 baseEnd_1068533 := by
    simpa [prefixWord, tailWord_1068533, baseEnd_1068533] using wordTrace_append hprefix tailTrace_1068533
  have hstable : (prefixWord ++ tailWord_1068533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068533).length < 2 ^ (prefixWord ++ tailWord_1068533).sum := by decide
  have hdescent : baseEnd_1068533 < baseStart_1068533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068578 : List Nat := [3, 3, 1, 1, 1, 1, 3, 5, 3]
def baseStart_1068578 : Nat := 118140960795 + 1068578 * 2 ^ 59
def prefixEnd_1068578 : Nat := 4983230072969 + 3 ^ 40 * 1068578 * 2
def baseEnd_1068578 : Nat := 243864058142322407715869

theorem tailTrace_1068578 : CollatzResearch.WordTrace tailWord_1068578 prefixEnd_1068578 243864058142322407715869 := by
  unfold tailWord_1068578
  simp only [CollatzResearch.WordTrace]
  refine ⟨9743560380682969859513597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25982827681821252958702925 9743560380682969859513597)
  ·
    refine ⟨3653835142756113697317599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9743560380682969859513597 3653835142756113697317599)
    ·
      refine ⟨5480752714134170545976399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3653835142756113697317599 5480752714134170545976399)
      ·
        refine ⟨8221129071201255818964599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5480752714134170545976399 8221129071201255818964599)
        ·
          refine ⟨12331693606801883728446899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8221129071201255818964599 12331693606801883728446899)
          ·
            refine ⟨18497540410202825592670349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12331693606801883728446899 18497540410202825592670349)
            ·
              refine ⟨6936577653826059597251381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18497540410202825592670349 6936577653826059597251381)
              ·
                refine ⟨650304155046193087242317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6936577653826059597251381 650304155046193087242317)
                ·
                  refine ⟨243864058142322407715869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650304155046193087242317 243864058142322407715869)
                  ·
                    rfl

theorem cell21_1068578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_1068578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068578 prefixEnd_1068578 := by exact prefixLift 1068578
  have htrace : WordTrace (prefixWord ++ tailWord_1068578) baseStart_1068578 baseEnd_1068578 := by
    simpa [prefixWord, tailWord_1068578, baseEnd_1068578] using wordTrace_append hprefix tailTrace_1068578
  have hstable : (prefixWord ++ tailWord_1068578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068578).length < 2 ^ (prefixWord ++ tailWord_1068578).sum := by decide
  have hdescent : baseEnd_1068578 < baseStart_1068578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068609 : List Nat := [1, 2, 5, 1, 1, 1, 5, 1, 4]
def baseStart_1068609 : Nat := 118140960795 + 1068609 * 2 ^ 59
def prefixEnd_1068609 : Nat := 4983230072969 + 3 ^ 40 * 1068609 * 2
def baseEnd_1068609 : Nat := 243871132764673242699139

theorem tailTrace_1068609 : CollatzResearch.WordTrace tailWord_1068609 prefixEnd_1068609 243871132764673242699139 := by
  unfold tailWord_1068609
  simp only [CollatzResearch.WordTrace]
  refine ⟨38975372185619571732432881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25983581457079714488288587 38975372185619571732432881)
  ·
    refine ⟨29231529139214678799324661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38975372185619571732432881 29231529139214678799324661)
    ·
      refine ⟨2740455856801376137436687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29231529139214678799324661 2740455856801376137436687)
      ·
        refine ⟨4110683785202064206155031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2740455856801376137436687 4110683785202064206155031)
        ·
          refine ⟨6166025677803096309232547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4110683785202064206155031 6166025677803096309232547)
          ·
            refine ⟨9249038516704644463848821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6166025677803096309232547 9249038516704644463848821)
            ·
              refine ⟨867097360941060418485827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9249038516704644463848821 867097360941060418485827)
              ·
                refine ⟨1300646041411590627728741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867097360941060418485827 1300646041411590627728741)
                ·
                  refine ⟨243871132764673242699139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1300646041411590627728741 243871132764673242699139)
                  ·
                    rfl

theorem cell21_1068609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 4].length) (baseStart_1068609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068609 prefixEnd_1068609 := by exact prefixLift 1068609
  have htrace : WordTrace (prefixWord ++ tailWord_1068609) baseStart_1068609 baseEnd_1068609 := by
    simpa [prefixWord, tailWord_1068609, baseEnd_1068609] using wordTrace_append hprefix tailTrace_1068609
  have hstable : (prefixWord ++ tailWord_1068609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068609).length < 2 ^ (prefixWord ++ tailWord_1068609).sum := by decide
  have hdescent : baseEnd_1068609 < baseStart_1068609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068682 : List Nat := [3, 1, 2, 3, 2, 1, 2, 7]
def baseStart_1068682 : Nat := 118140960795 + 1068682 * 2 ^ 59
def prefixEnd_1068682 : Nat := 4983230072969 + 3 ^ 40 * 1068682 * 2
def baseEnd_1068682 : Nat := 81295930786413779327441

theorem tailTrace_1068682 : CollatzResearch.WordTrace tailWord_1068682 prefixEnd_1068682 81295930786413779327441 := by
  unfold tailWord_1068682
  simp only [CollatzResearch.WordTrace]
  refine ⟨9744508678588776299960075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25985356476236736799893533 9744508678588776299960075)
  ·
    refine ⟨14616763017883164449940113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9744508678588776299960075 14616763017883164449940113)
    ·
      refine ⟨10962572263412373337455085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14616763017883164449940113 10962572263412373337455085)
      ·
        refine ⟨4110964598779640001545657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10962572263412373337455085 4110964598779640001545657)
        ·
          refine ⟨3083223449084730001159243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4110964598779640001545657 3083223449084730001159243)
          ·
            refine ⟨4624835173627095001738865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3083223449084730001159243 4624835173627095001738865)
            ·
              refine ⟨3468626380220321251304149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4624835173627095001738865 3468626380220321251304149)
              ·
                refine ⟨81295930786413779327441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3468626380220321251304149 81295930786413779327441)
                ·
                  rfl

theorem cell21_1068682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_1068682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068682 prefixEnd_1068682 := by exact prefixLift 1068682
  have htrace : WordTrace (prefixWord ++ tailWord_1068682) baseStart_1068682 baseEnd_1068682 := by
    simpa [prefixWord, tailWord_1068682, baseEnd_1068682] using wordTrace_append hprefix tailTrace_1068682
  have hstable : (prefixWord ++ tailWord_1068682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068682).length < 2 ^ (prefixWord ++ tailWord_1068682).sum := by decide
  have hdescent : baseEnd_1068682 < baseStart_1068682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068823 : List Nat := [1, 1, 3, 4, 2, 2, 3, 2, 3]
def baseStart_1068823 : Nat := 118140960795 + 1068823 * 2 ^ 59
def prefixEnd_1068823 : Nat := 4983230072969 + 3 ^ 40 * 1068823 * 2
def baseEnd_1068823 : Nat := 243919970480256426132035

theorem tailTrace_1068823 : CollatzResearch.WordTrace tailWord_1068823 prefixEnd_1068823 243919970480256426132035 := by
  unfold tailWord_1068823
  simp only [CollatzResearch.WordTrace]
  refine ⟨38983177406844286280723123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25988784937896190853815415 38983177406844286280723123)
  ·
    refine ⟨58474766110266429421084685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38983177406844286280723123 58474766110266429421084685)
    ·
      refine ⟨21928037291349911032906757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58474766110266429421084685 21928037291349911032906757)
      ·
        refine ⟨4111506992128108318670017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21928037291349911032906757 4111506992128108318670017)
        ·
          refine ⟨3083630244096081239002513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4111506992128108318670017 3083630244096081239002513)
          ·
            refine ⟨2312722683072060929251885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3083630244096081239002513 2312722683072060929251885)
            ·
              refine ⟨867271006152022848469457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2312722683072060929251885 867271006152022848469457)
              ·
                refine ⟨650453254614017136352093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 867271006152022848469457 650453254614017136352093)
                ·
                  refine ⟨243919970480256426132035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650453254614017136352093 243919970480256426132035)
                  ·
                    rfl

theorem cell21_1068823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 3].length) (baseStart_1068823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068823 prefixEnd_1068823 := by exact prefixLift 1068823
  have htrace : WordTrace (prefixWord ++ tailWord_1068823) baseStart_1068823 baseEnd_1068823 := by
    simpa [prefixWord, tailWord_1068823, baseEnd_1068823] using wordTrace_append hprefix tailTrace_1068823
  have hstable : (prefixWord ++ tailWord_1068823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068823).length < 2 ^ (prefixWord ++ tailWord_1068823).sum := by decide
  have hdescent : baseEnd_1068823 < baseStart_1068823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068834 : List Nat := [3, 3, 1, 1, 2, 1, 4, 6]
def baseStart_1068834 : Nat := 118140960795 + 1068834 * 2 ^ 59
def prefixEnd_1068834 : Nat := 4983230072969 + 3 ^ 40 * 1068834 * 2
def baseEnd_1068834 : Nat := 81307493610040950482893

theorem tailTrace_1068834 : CollatzResearch.WordTrace tailWord_1068834 prefixEnd_1068834 81307493610040950482893 := by
  unfold tailWord_1068834
  simp only [CollatzResearch.WordTrace]
  refine ⟨9745894652451108789843389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25989052406536290106249037 9745894652451108789843389)
  ·
    refine ⟨3654710494669165796191271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9745894652451108789843389 3654710494669165796191271)
    ·
      refine ⟨5482065742003748694286907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3654710494669165796191271 5482065742003748694286907)
      ·
        refine ⟨8223098613005623041430361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5482065742003748694286907 8223098613005623041430361)
        ·
          refine ⟨6167323959754217281072771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8223098613005623041430361 6167323959754217281072771)
          ·
            refine ⟨9250985939631325921609157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6167323959754217281072771 9250985939631325921609157)
            ·
              refine ⟨1734559863680873610301717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9250985939631325921609157 1734559863680873610301717)
              ·
                refine ⟨81307493610040950482893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1734559863680873610301717 81307493610040950482893)
                ·
                  rfl

theorem cell21_1068834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_1068834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068834 prefixEnd_1068834 := by exact prefixLift 1068834
  have htrace : WordTrace (prefixWord ++ tailWord_1068834) baseStart_1068834 baseEnd_1068834 := by
    simpa [prefixWord, tailWord_1068834, baseEnd_1068834] using wordTrace_append hprefix tailTrace_1068834
  have hstable : (prefixWord ++ tailWord_1068834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068834).length < 2 ^ (prefixWord ++ tailWord_1068834).sum := by decide
  have hdescent : baseEnd_1068834 < baseStart_1068834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068837 : List Nat := [1, 3, 1, 2, 3, 4, 2, 1, 4]
def baseStart_1068837 : Nat := 118140960795 + 1068837 * 2 ^ 59
def prefixEnd_1068837 : Nat := 4983230072969 + 3 ^ 40 * 1068837 * 2
def baseEnd_1068837 : Nat := 243923165470995512898673

theorem tailTrace_1068837 : CollatzResearch.WordTrace tailWord_1068837 prefixEnd_1068837 243923165470995512898673 := by
  unfold tailWord_1068837
  simp only [CollatzResearch.WordTrace]
  refine ⟨38983688028793566671732765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25989125352529044447821843 38983688028793566671732765)
  ·
    refine ⟨14618883010797587501899787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38983688028793566671732765 14618883010797587501899787)
    ·
      refine ⟨21928324516196381252849681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14618883010797587501899787 21928324516196381252849681)
      ·
        refine ⟨16446243387147285939637261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21928324516196381252849681 16446243387147285939637261)
        ·
          refine ⟨6167341270180232227363973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16446243387147285939637261 6167341270180232227363973)
          ·
            refine ⟨1156376488158793542630745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6167341270180232227363973 1156376488158793542630745)
            ·
              refine ⟨867282366119095156973059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1156376488158793542630745 867282366119095156973059)
              ·
                refine ⟨1300923549178642735459589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867282366119095156973059 1300923549178642735459589)
                ·
                  refine ⟨243923165470995512898673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1300923549178642735459589 243923165470995512898673)
                  ·
                    rfl

theorem cell21_1068837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_1068837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068837 prefixEnd_1068837 := by exact prefixLift 1068837
  have htrace : WordTrace (prefixWord ++ tailWord_1068837) baseStart_1068837 baseEnd_1068837 := by
    simpa [prefixWord, tailWord_1068837, baseEnd_1068837] using wordTrace_append hprefix tailTrace_1068837
  have hstable : (prefixWord ++ tailWord_1068837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068837).length < 2 ^ (prefixWord ++ tailWord_1068837).sum := by decide
  have hdescent : baseEnd_1068837 < baseStart_1068837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1068882 : List Nat := [3, 2, 2, 1, 1, 4, 1, 4, 3]
def baseStart_1068882 : Nat := 118140960795 + 1068882 * 2 ^ 59
def prefixEnd_1068882 : Nat := 4983230072969 + 3 ^ 40 * 1068882 * 2
def baseEnd_1068882 : Nat := 243933435084085434648581

theorem tailTrace_1068882 : CollatzResearch.WordTrace tailWord_1068882 prefixEnd_1068882 243933435084085434648581 := by
  unfold tailWord_1068882
  simp only [CollatzResearch.WordTrace]
  refine ⟨9746332328407634839280225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25990219542420359571413933 9746332328407634839280225)
  ·
    refine ⟨7309749246305726129460169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9746332328407634839280225 7309749246305726129460169)
    ·
      refine ⟨5482311934729294597095127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7309749246305726129460169 5482311934729294597095127)
      ·
        refine ⟨8223467902093941895642691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5482311934729294597095127 8223467902093941895642691)
        ·
          refine ⟨12335201853140912843464037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8223467902093941895642691 12335201853140912843464037)
          ·
            refine ⟨2312850347463921158149507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12335201853140912843464037 2312850347463921158149507)
            ·
              refine ⟨3469275521195881737224261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2312850347463921158149507 3469275521195881737224261)
              ·
                refine ⟨650489160224227825729549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3469275521195881737224261 650489160224227825729549)
                ·
                  refine ⟨243933435084085434648581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650489160224227825729549 243933435084085434648581)
                  ·
                    rfl

theorem cell21_1068882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_1068882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1068882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1068882 prefixEnd_1068882 := by exact prefixLift 1068882
  have htrace : WordTrace (prefixWord ++ tailWord_1068882) baseStart_1068882 baseEnd_1068882 := by
    simpa [prefixWord, tailWord_1068882, baseEnd_1068882] using wordTrace_append hprefix tailTrace_1068882
  have hstable : (prefixWord ++ tailWord_1068882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1068882).length < 2 ^ (prefixWord ++ tailWord_1068882).sum := by decide
  have hdescent : baseEnd_1068882 < baseStart_1068882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1068882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069045 : List Nat := [1, 3, 5, 12]
def baseStart_1069045 : Nat := 118140960795 + 1069045 * 2 ^ 59
def prefixEnd_1069045 : Nat := 4983230072969 + 3 ^ 40 * 1069045 * 2
def baseEnd_1069045 : Nat := 1003994378209190837167

theorem tailTrace_1069045 : CollatzResearch.WordTrace tailWord_1069045 prefixEnd_1069045 1003994378209190837167 := by
  unfold tailWord_1069045
  simp only [CollatzResearch.WordTrace]
  refine ⟨38991274412040018195304589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25994182941360012130203059 38991274412040018195304589)
  ·
    refine ⟨14621727904515006823239221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38991274412040018195304589 14621727904515006823239221)
    ·
      refine ⟨1370786991048281889678677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14621727904515006823239221 1370786991048281889678677)
      ·
        refine ⟨1003994378209190837167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1370786991048281889678677 1003994378209190837167)
        ·
          rfl

theorem cell21_1069045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 12].length) (baseStart_1069045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069045 prefixEnd_1069045 := by exact prefixLift 1069045
  have htrace : WordTrace (prefixWord ++ tailWord_1069045) baseStart_1069045 baseEnd_1069045 := by
    simpa [prefixWord, tailWord_1069045, baseEnd_1069045] using wordTrace_append hprefix tailTrace_1069045
  have hstable : (prefixWord ++ tailWord_1069045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069045).length < 2 ^ (prefixWord ++ tailWord_1069045).sum := by decide
  have hdescent : baseEnd_1069045 < baseStart_1069045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069059 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 9]
def baseStart_1069059 : Nat := 118140960795 + 1069059 * 2 ^ 59
def prefixEnd_1069059 : Nat := 4983230072969 + 3 ^ 40 * 1069059 * 2
def baseEnd_1069059 : Nat := 243973828895572460198219

theorem tailTrace_1069059 : CollatzResearch.WordTrace tailWord_1069059 prefixEnd_1069059 243973828895572460198219 := by
  unfold tailWord_1069059
  simp only [CollatzResearch.WordTrace]
  refine ⟨38991785033989298586314231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25994523355992865724209487 38991785033989298586314231)
  ·
    refine ⟨58487677550983947879471347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38991785033989298586314231 58487677550983947879471347)
    ·
      refine ⟨87731516326475921819207021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58487677550983947879471347 87731516326475921819207021)
      ·
        refine ⟨32899318622428470682202633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87731516326475921819207021 32899318622428470682202633)
        ·
          refine ⟨24674488966821353011651975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32899318622428470682202633 24674488966821353011651975)
          ·
            refine ⟨37011733450232029517477963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24674488966821353011651975 37011733450232029517477963)
            ·
              refine ⟨55517600175348044276216945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37011733450232029517477963 55517600175348044276216945)
              ·
                refine ⟨41638200131511033207162709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55517600175348044276216945 41638200131511033207162709)
                ·
                  refine ⟨243973828895572460198219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41638200131511033207162709 243973828895572460198219)
                  ·
                    rfl

theorem cell21_1069059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 9].length) (baseStart_1069059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069059 prefixEnd_1069059 := by exact prefixLift 1069059
  have htrace : WordTrace (prefixWord ++ tailWord_1069059) baseStart_1069059 baseEnd_1069059 := by
    simpa [prefixWord, tailWord_1069059, baseEnd_1069059] using wordTrace_append hprefix tailTrace_1069059
  have hstable : (prefixWord ++ tailWord_1069059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069059).length < 2 ^ (prefixWord ++ tailWord_1069059).sum := by decide
  have hdescent : baseEnd_1069059 < baseStart_1069059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069079 : List Nat := [1, 1, 3, 5, 2, 1, 3, 5]
def baseStart_1069079 : Nat := 118140960795 + 1069079 * 2 ^ 59
def prefixEnd_1069079 : Nat := 4983230072969 + 3 ^ 40 * 1069079 * 2
def baseEnd_1069079 : Nat := 81326131056018956621615

theorem tailTrace_1069079 : CollatzResearch.WordTrace tailWord_1069079 prefixEnd_1069079 81326131056018956621615 := by
  unfold tailWord_1069079
  simp only [CollatzResearch.WordTrace]
  refine ⟨38992514493916842002042291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25995009662611228001361527 38992514493916842002042291)
  ·
    refine ⟨58488771740875263003063437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38992514493916842002042291 58488771740875263003063437)
    ·
      refine ⟨21933289402828223626148789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58488771740875263003063437 21933289402828223626148789)
      ·
        refine ⟨2056245881515145964951449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21933289402828223626148789 2056245881515145964951449)
        ·
          refine ⟨1542184411136359473713587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2056245881515145964951449 1542184411136359473713587)
          ·
            refine ⟨2313276616704539210570381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1542184411136359473713587 2313276616704539210570381)
            ·
              refine ⟨867478731264202203963893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2313276616704539210570381 867478731264202203963893)
              ·
                refine ⟨81326131056018956621615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 867478731264202203963893 81326131056018956621615)
                ·
                  rfl

theorem cell21_1069079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 5].length) (baseStart_1069079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069079 prefixEnd_1069079 := by exact prefixLift 1069079
  have htrace : WordTrace (prefixWord ++ tailWord_1069079) baseStart_1069079 baseEnd_1069079 := by
    simpa [prefixWord, tailWord_1069079, baseEnd_1069079] using wordTrace_append hprefix tailTrace_1069079
  have hstable : (prefixWord ++ tailWord_1069079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069079).length < 2 ^ (prefixWord ++ tailWord_1069079).sum := by decide
  have hdescent : baseEnd_1069079 < baseStart_1069079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069093 : List Nat := [1, 3, 1, 2, 2, 3, 1, 5, 3]
def baseStart_1069093 : Nat := 118140960795 + 1069093 * 2 ^ 59
def prefixEnd_1069093 : Nat := 4983230072969 + 3 ^ 40 * 1069093 * 2
def baseEnd_1069093 : Nat := 243981588158795956631483

theorem tailTrace_1069093 : CollatzResearch.WordTrace tailWord_1069093 prefixEnd_1069093 243981588158795956631483 := by
  unfold tailWord_1069093
  simp only [CollatzResearch.WordTrace]
  refine ⟨38993025115866122393051933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25995350077244081595367955 38993025115866122393051933)
  ·
    refine ⟨14622384418449795897394475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38993025115866122393051933 14622384418449795897394475)
    ·
      refine ⟨21933576627674693846091713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14622384418449795897394475 21933576627674693846091713)
      ·
        refine ⟨16450182470756020384568785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21933576627674693846091713 16450182470756020384568785)
        ·
          refine ⟨12337636853067015288426589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16450182470756020384568785 12337636853067015288426589)
          ·
            refine ⟨4626613819900130733159971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12337636853067015288426589 4626613819900130733159971)
            ·
              refine ⟨6939920729850196099739957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4626613819900130733159971 6939920729850196099739957)
              ·
                refine ⟨650617568423455884350621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6939920729850196099739957 650617568423455884350621)
                ·
                  refine ⟨243981588158795956631483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650617568423455884350621 243981588158795956631483)
                  ·
                    rfl

theorem cell21_1069093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_1069093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069093 prefixEnd_1069093 := by exact prefixLift 1069093
  have htrace : WordTrace (prefixWord ++ tailWord_1069093) baseStart_1069093 baseEnd_1069093 := by
    simpa [prefixWord, tailWord_1069093, baseEnd_1069093] using wordTrace_append hprefix tailTrace_1069093
  have hstable : (prefixWord ++ tailWord_1069093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069093).length < 2 ^ (prefixWord ++ tailWord_1069093).sum := by decide
  have hdescent : baseEnd_1069093 < baseStart_1069093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069107 : List Nat := [1, 1, 1, 2, 4, 1, 5, 2, 4]
def baseStart_1069107 : Nat := 118140960795 + 1069107 * 2 ^ 59
def prefixEnd_1069107 : Nat := 4983230072969 + 3 ^ 40 * 1069107 * 2
def baseEnd_1069107 : Nat := 243984783149535043398121

theorem tailTrace_1069107 : CollatzResearch.WordTrace tailWord_1069107 prefixEnd_1069107 243984783149535043398121 := by
  unfold tailWord_1069107
  simp only [CollatzResearch.WordTrace]
  refine ⟨38993535737815402784061575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25995690491876935189374383 38993535737815402784061575)
  ·
    refine ⟨58490303606723104176092363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38993535737815402784061575 58490303606723104176092363)
    ·
      refine ⟨87735455410084656264138545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58490303606723104176092363 87735455410084656264138545)
      ·
        refine ⟨65801591557563492198103909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87735455410084656264138545 65801591557563492198103909)
        ·
          refine ⟨12337798417043154787144483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65801591557563492198103909 12337798417043154787144483)
          ·
            refine ⟨18506697625564732180716725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12337798417043154787144483 18506697625564732180716725)
            ·
              refine ⟨1735002902396693641942193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18506697625564732180716725 1735002902396693641942193)
              ·
                refine ⟨1301252176797520231456645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1735002902396693641942193 1301252176797520231456645)
                ·
                  refine ⟨243984783149535043398121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1301252176797520231456645 243984783149535043398121)
                  ·
                    rfl

theorem cell21_1069107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 4].length) (baseStart_1069107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069107 prefixEnd_1069107 := by exact prefixLift 1069107
  have htrace : WordTrace (prefixWord ++ tailWord_1069107) baseStart_1069107 baseEnd_1069107 := by
    simpa [prefixWord, tailWord_1069107, baseEnd_1069107] using wordTrace_append hprefix tailTrace_1069107
  have hstable : (prefixWord ++ tailWord_1069107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069107).length < 2 ^ (prefixWord ++ tailWord_1069107).sum := by decide
  have hdescent : baseEnd_1069107 < baseStart_1069107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069110 : List Nat := [5, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_1069110 : Nat := 118140960795 + 1069110 * 2 ^ 59
def prefixEnd_1069110 : Nat := 4983230072969 + 3 ^ 40 * 1069110 * 2
def baseEnd_1069110 : Nat := 243985467790407704848115

theorem tailTrace_1069110 : CollatzResearch.WordTrace tailWord_1069110 prefixEnd_1069110 243985467790407704848115 := by
  unfold tailWord_1069110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2437102822300283393526299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25995763437869689530947189 2437102822300283393526299)
  ·
    refine ⟨3655654233450425090289449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2437102822300283393526299 3655654233450425090289449)
    ·
      refine ⟨2741740675087818817717087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3655654233450425090289449 2741740675087818817717087)
      ·
        refine ⟨4112611012631728226575631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2741740675087818817717087 4112611012631728226575631)
        ·
          refine ⟨6168916518947592339863447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4112611012631728226575631 6168916518947592339863447)
          ·
            refine ⟨9253374778421388509795171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6168916518947592339863447 9253374778421388509795171)
            ·
              refine ⟨13880062167632082764692757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9253374778421388509795171 13880062167632082764692757)
              ·
                refine ⟨650627914107753879594973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13880062167632082764692757 650627914107753879594973)
                ·
                  refine ⟨243985467790407704848115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650627914107753879594973 243985467790407704848115)
                  ·
                    rfl

theorem cell21_1069110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_1069110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069110 prefixEnd_1069110 := by exact prefixLift 1069110
  have htrace : WordTrace (prefixWord ++ tailWord_1069110) baseStart_1069110 baseEnd_1069110 := by
    simpa [prefixWord, tailWord_1069110, baseEnd_1069110] using wordTrace_append hprefix tailTrace_1069110
  have hstable : (prefixWord ++ tailWord_1069110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069110).length < 2 ^ (prefixWord ++ tailWord_1069110).sum := by decide
  have hdescent : baseEnd_1069110 < baseStart_1069110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069138 : List Nat := [3, 2, 2, 1, 4, 1, 1, 7]
def baseStart_1069138 : Nat := 118140960795 + 1069138 * 2 ^ 59
def prefixEnd_1069138 : Nat := 4983230072969 + 3 ^ 40 * 1069138 * 2
def baseEnd_1069138 : Nat := 81330619257295292793797

theorem tailTrace_1069138 : CollatzResearch.WordTrace tailWord_1069138 prefixEnd_1069138 81330619257295292793797 := by
  unfold tailWord_1069138
  simp only [CollatzResearch.WordTrace]
  refine ⟨9748666600175773769610017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25996444267135396718960045 9748666600175773769610017)
  ·
    refine ⟨7311499950131830327207513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9748666600175773769610017 7311499950131830327207513)
    ·
      refine ⟨5483624962598872745405635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7311499950131830327207513 5483624962598872745405635)
      ·
        refine ⟨8225437443898309118108453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5483624962598872745405635 8225437443898309118108453)
        ·
          refine ⟨1542269520730932959645335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8225437443898309118108453 1542269520730932959645335)
          ·
            refine ⟨2313404281096399439468003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1542269520730932959645335 2313404281096399439468003)
            ·
              refine ⟨3470106421644599159202005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2313404281096399439468003 3470106421644599159202005)
              ·
                refine ⟨81330619257295292793797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3470106421644599159202005 81330619257295292793797)
                ·
                  rfl

theorem cell21_1069138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_1069138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069138 prefixEnd_1069138 := by exact prefixLift 1069138
  have htrace : WordTrace (prefixWord ++ tailWord_1069138) baseStart_1069138 baseEnd_1069138 := by
    simpa [prefixWord, tailWord_1069138, baseEnd_1069138] using wordTrace_append hprefix tailTrace_1069138
  have hstable : (prefixWord ++ tailWord_1069138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069138).length < 2 ^ (prefixWord ++ tailWord_1069138).sum := by decide
  have hdescent : baseEnd_1069138 < baseStart_1069138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069214 : List Nat := [4, 3, 1, 1, 3, 9]
def baseStart_1069214 : Nat := 118140960795 + 1069214 * 2 ^ 59
def prefixEnd_1069214 : Nat := 4983230072969 + 3 ^ 40 * 1069214 * 2
def baseEnd_1069214 : Nat := 9037377852123208707947

theorem tailTrace_1069214 : CollatzResearch.WordTrace tailWord_1069214 prefixEnd_1069214 9037377852123208707947 := by
  unfold tailWord_1069214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4874679793553470007275837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25998292232285173372137797 4874679793553470007275837)
  ·
    refine ⟨1828004922582551252728439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4874679793553470007275837 1828004922582551252728439)
    ·
      refine ⟨2742007383873826879092659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1828004922582551252728439 2742007383873826879092659)
      ·
        refine ⟨4113011075810740318638989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2742007383873826879092659 4113011075810740318638989)
        ·
          refine ⟨1542379153429027619489621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4113011075810740318638989 1542379153429027619489621)
          ·
            refine ⟨9037377852123208707947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1542379153429027619489621 9037377852123208707947)
            ·
              rfl

theorem cell21_1069214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 9].length) (baseStart_1069214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069214 prefixEnd_1069214 := by exact prefixLift 1069214
  have htrace : WordTrace (prefixWord ++ tailWord_1069214) baseStart_1069214 baseEnd_1069214 := by
    simpa [prefixWord, tailWord_1069214, baseEnd_1069214] using wordTrace_append hprefix tailTrace_1069214
  have hstable : (prefixWord ++ tailWord_1069214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069214).length < 2 ^ (prefixWord ++ tailWord_1069214).sum := by decide
  have hdescent : baseEnd_1069214 < baseStart_1069214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069220 : List Nat := [2, 3, 1, 2, 5, 1, 2, 2, 3]
def baseStart_1069220 : Nat := 118140960795 + 1069220 * 2 ^ 59
def prefixEnd_1069220 : Nat := 4983230072969 + 3 ^ 40 * 1069220 * 2
def baseEnd_1069220 : Nat := 244010571289071958014557

theorem tailTrace_1069220 : CollatzResearch.WordTrace tailWord_1069220 prefixEnd_1069220 244010571289071958014557 := by
  unfold tailWord_1069220
  simp only [CollatzResearch.WordTrace]
  refine ⟨19498828593203011541462557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25998438124270682055283409 19498828593203011541462557)
  ·
    refine ⟨7312060722451129328048459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19498828593203011541462557 7312060722451129328048459)
    ·
      refine ⟨10968091083676693992072689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7312060722451129328048459 10968091083676693992072689)
      ·
        refine ⟨8226068312757520494054517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10968091083676693992072689 8226068312757520494054517)
        ·
          refine ⟨771193904321017546317611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8226068312757520494054517 771193904321017546317611)
          ·
            refine ⟨1156790856481526319476417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771193904321017546317611 1156790856481526319476417)
            ·
              refine ⟨867593142361144739607313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1156790856481526319476417 867593142361144739607313)
              ·
                refine ⟨650694856770858554705485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 867593142361144739607313 650694856770858554705485)
                ·
                  refine ⟨244010571289071958014557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650694856770858554705485 244010571289071958014557)
                  ·
                    rfl

theorem cell21_1069220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_1069220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069220 prefixEnd_1069220 := by exact prefixLift 1069220
  have htrace : WordTrace (prefixWord ++ tailWord_1069220) baseStart_1069220 baseEnd_1069220 := by
    simpa [prefixWord, tailWord_1069220, baseEnd_1069220] using wordTrace_append hprefix tailTrace_1069220
  have hstable : (prefixWord ++ tailWord_1069220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069220).length < 2 ^ (prefixWord ++ tailWord_1069220).sum := by decide
  have hdescent : baseEnd_1069220 < baseStart_1069220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069262 : List Nat := [4, 1, 1, 1, 4, 2, 2, 3, 3]
def baseStart_1069262 : Nat := 118140960795 + 1069262 * 2 ^ 59
def prefixEnd_1069262 : Nat := 4983230072969 + 3 ^ 40 * 1069262 * 2
def baseEnd_1069262 : Nat := 244020156261289218314471

theorem tailTrace_1069262 : CollatzResearch.WordTrace tailWord_1069262 prefixEnd_1069262 244020156261289218314471 := by
  unfold tailWord_1069262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4874898631531733031994255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25999459368169242837302693 4874898631531733031994255)
  ·
    refine ⟨7312347947297599547991383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4874898631531733031994255 7312347947297599547991383)
    ·
      refine ⟨10968521920946399321987075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7312347947297599547991383 10968521920946399321987075)
      ·
        refine ⟨16452782881419598982980613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10968521920946399321987075 16452782881419598982980613)
        ·
          refine ⟨3084896790266174809308865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16452782881419598982980613 3084896790266174809308865)
          ·
            refine ⟨2313672592699631106981649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3084896790266174809308865 2313672592699631106981649)
            ·
              refine ⟨1735254444524723330236237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2313672592699631106981649 1735254444524723330236237)
              ·
                refine ⟨650720416696771248838589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1735254444524723330236237 650720416696771248838589)
                ·
                  refine ⟨244020156261289218314471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650720416696771248838589 244020156261289218314471)
                  ·
                    rfl

theorem cell21_1069262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_1069262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069262 prefixEnd_1069262 := by exact prefixLift 1069262
  have htrace : WordTrace (prefixWord ++ tailWord_1069262) baseStart_1069262 baseEnd_1069262 := by
    simpa [prefixWord, tailWord_1069262, baseEnd_1069262] using wordTrace_append hprefix tailTrace_1069262
  have hstable : (prefixWord ++ tailWord_1069262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069262).length < 2 ^ (prefixWord ++ tailWord_1069262).sum := by decide
  have hdescent : baseEnd_1069262 < baseStart_1069262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069293 : List Nat := [1, 5, 1, 2, 3, 1, 3, 1, 4]
def baseStart_1069293 : Nat := 118140960795 + 1069293 * 2 ^ 59
def prefixEnd_1069293 : Nat := 4983230072969 + 3 ^ 40 * 1069293 * 2
def baseEnd_1069293 : Nat := 244027230883640053297741

theorem tailTrace_1069293 : CollatzResearch.WordTrace tailWord_1069293 prefixEnd_1069293 244027230883640053297741 := by
  unfold tailWord_1069293
  simp only [CollatzResearch.WordTrace]
  refine ⟨39000319715141556550332533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26000213143427704366888355 39000319715141556550332533)
  ·
    refine ⟨3656279973294520926593675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39000319715141556550332533 3656279973294520926593675)
    ·
      refine ⟨5484419959941781389890513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3656279973294520926593675 5484419959941781389890513)
      ·
        refine ⟨4113314969956336042417885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5484419959941781389890513 4113314969956336042417885)
        ·
          refine ⟨1542493113733626015906707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4113314969956336042417885 1542493113733626015906707)
          ·
            refine ⟨2313739670600439023860061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1542493113733626015906707 2313739670600439023860061)
            ·
              refine ⟨867652376475164633947523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2313739670600439023860061 867652376475164633947523)
              ·
                refine ⟨1301478564712746950921285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867652376475164633947523 1301478564712746950921285)
                ·
                  refine ⟨244027230883640053297741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1301478564712746950921285 244027230883640053297741)
                  ·
                    rfl

theorem cell21_1069293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_1069293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069293 prefixEnd_1069293 := by exact prefixLift 1069293
  have htrace : WordTrace (prefixWord ++ tailWord_1069293) baseStart_1069293 baseEnd_1069293 := by
    simpa [prefixWord, tailWord_1069293, baseEnd_1069293] using wordTrace_append hprefix tailTrace_1069293
  have hstable : (prefixWord ++ tailWord_1069293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069293).length < 2 ^ (prefixWord ++ tailWord_1069293).sum := by decide
  have hdescent : baseEnd_1069293 < baseStart_1069293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069321 : List Nat := [1, 2, 1, 1, 3, 4, 3, 3, 3]
def baseStart_1069321 : Nat := 118140960795 + 1069321 * 2 ^ 59
def prefixEnd_1069321 : Nat := 4983230072969 + 3 ^ 40 * 1069321 * 2
def baseEnd_1069321 : Nat := 244033620865118226831017

theorem tailTrace_1069321 : CollatzResearch.WordTrace tailWord_1069321 prefixEnd_1069321 244033620865118226831017 := by
  unfold tailWord_1069321
  simp only [CollatzResearch.WordTrace]
  refine ⟨39001340959040117332351817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26000893972693411554901211 39001340959040117332351817)
  ·
    refine ⟨29251005719280087999263863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39001340959040117332351817 29251005719280087999263863)
    ·
      refine ⟨43876508578920131998895795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29251005719280087999263863 43876508578920131998895795)
      ·
        refine ⟨65814762868380197998343693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43876508578920131998895795 65814762868380197998343693)
        ·
          refine ⟨24680536075642574249378885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65814762868380197998343693 24680536075642574249378885)
          ·
            refine ⟨4627600514182982671758541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24680536075642574249378885 4627600514182982671758541)
            ·
              refine ⟨1735350192818618501909453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4627600514182982671758541 1735350192818618501909453)
              ·
                refine ⟨650756322306981938216045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1735350192818618501909453 650756322306981938216045)
                ·
                  refine ⟨244033620865118226831017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650756322306981938216045 244033620865118226831017)
                  ·
                    rfl

theorem cell21_1069321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 3].length) (baseStart_1069321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069321 prefixEnd_1069321 := by exact prefixLift 1069321
  have htrace : WordTrace (prefixWord ++ tailWord_1069321) baseStart_1069321 baseEnd_1069321 := by
    simpa [prefixWord, tailWord_1069321, baseEnd_1069321] using wordTrace_append hprefix tailTrace_1069321
  have hstable : (prefixWord ++ tailWord_1069321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069321).length < 2 ^ (prefixWord ++ tailWord_1069321).sum := by decide
  have hdescent : baseEnd_1069321 < baseStart_1069321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069338 : List Nat := [3, 1, 1, 3, 5, 1, 1, 1, 5]
def baseStart_1069338 : Nat := 118140960795 + 1069338 * 2 ^ 59
def prefixEnd_1069338 : Nat := 4983230072969 + 3 ^ 40 * 1069338 * 2
def baseEnd_1069338 : Nat := 244037500496729975047649

theorem tailTrace_1069338 : CollatzResearch.WordTrace tailWord_1069338 prefixEnd_1069338 244037500496729975047649 := by
  unfold tailWord_1069338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9750490249994632308930167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26001307333319019490480445 9750490249994632308930167)
  ·
    refine ⟨14625735374991948463395251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9750490249994632308930167 14625735374991948463395251)
    ·
      refine ⟨21938603062487922695092877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14625735374991948463395251 21938603062487922695092877)
      ·
        refine ⟨8226976148432971010659829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21938603062487922695092877 8226976148432971010659829)
        ·
          refine ⟨771279013915591032249359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8226976148432971010659829 771279013915591032249359)
          ·
            refine ⟨1156918520873386548374039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771279013915591032249359 1156918520873386548374039)
            ·
              refine ⟨1735377781310079822561059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1156918520873386548374039 1735377781310079822561059)
              ·
                refine ⟨2603066671965119733841589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1735377781310079822561059 2603066671965119733841589)
                ·
                  refine ⟨244037500496729975047649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2603066671965119733841589 244037500496729975047649)
                  ·
                    rfl

theorem cell21_1069338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_1069338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069338 prefixEnd_1069338 := by exact prefixLift 1069338
  have htrace : WordTrace (prefixWord ++ tailWord_1069338) baseStart_1069338 baseEnd_1069338 := by
    simpa [prefixWord, tailWord_1069338, baseEnd_1069338] using wordTrace_append hprefix tailTrace_1069338
  have hstable : (prefixWord ++ tailWord_1069338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069338).length < 2 ^ (prefixWord ++ tailWord_1069338).sum := by decide
  have hdescent : baseEnd_1069338 < baseStart_1069338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069352 : List Nat := [2, 1, 5, 1, 3, 1, 1, 3, 4]
def baseStart_1069352 : Nat := 118140960795 + 1069352 * 2 ^ 59
def prefixEnd_1069352 : Nat := 4983230072969 + 3 ^ 40 * 1069352 * 2
def baseEnd_1069352 : Nat := 244040695487469061814287

theorem tailTrace_1069352 : CollatzResearch.WordTrace tailWord_1069352 prefixEnd_1069352 244040695487469061814287 := by
  unfold tailWord_1069352
  simp only [CollatzResearch.WordTrace]
  refine ⟨19501235810963904813365155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26001647747951873084486873 19501235810963904813365155)
  ·
    refine ⟨29251853716445857220047733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19501235810963904813365155 29251853716445857220047733)
    ·
      refine ⟨2742361285916799114379475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29251853716445857220047733 2742361285916799114379475)
      ·
        refine ⟨4113541928875198671569213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2742361285916799114379475 4113541928875198671569213)
        ·
          refine ⟨1542578223328199501838455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4113541928875198671569213 1542578223328199501838455)
          ·
            refine ⟨2313867334992299252757683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1542578223328199501838455 2313867334992299252757683)
            ·
              refine ⟨3470801002488448879136525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2313867334992299252757683 3470801002488448879136525)
              ·
                refine ⟨1301550375933168329676197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3470801002488448879136525 1301550375933168329676197)
                ·
                  refine ⟨244040695487469061814287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1301550375933168329676197 244040695487469061814287)
                  ·
                    rfl

theorem cell21_1069352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_1069352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069352 prefixEnd_1069352 := by exact prefixLift 1069352
  have htrace : WordTrace (prefixWord ++ tailWord_1069352) baseStart_1069352 baseEnd_1069352 := by
    simpa [prefixWord, tailWord_1069352, baseEnd_1069352] using wordTrace_append hprefix tailTrace_1069352
  have hstable : (prefixWord ++ tailWord_1069352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069352).length < 2 ^ (prefixWord ++ tailWord_1069352).sum := by decide
  have hdescent : baseEnd_1069352 < baseStart_1069352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069363 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 7]
def baseStart_1069363 : Nat := 118140960795 + 1069363 * 2 ^ 59
def prefixEnd_1069363 : Nat := 4983230072969 + 3 ^ 40 * 1069363 * 2
def baseEnd_1069363 : Nat := 244043205837335487130931

theorem tailTrace_1069363 : CollatzResearch.WordTrace tailWord_1069363 prefixEnd_1069363 244043205837335487130931 := by
  unfold tailWord_1069363
  simp only [CollatzResearch.WordTrace]
  refine ⟨39002872824887958505380743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26001915216591972336920495 39002872824887958505380743)
  ·
    refine ⟨58504309237331937758071115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39002872824887958505380743 58504309237331937758071115)
    ·
      refine ⟨87756463855997906637106673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58504309237331937758071115 87756463855997906637106673)
      ·
        refine ⟨65817347891998429977830005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87756463855997906637106673 65817347891998429977830005)
        ·
          refine ⟨6170376364874852810421563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65817347891998429977830005 6170376364874852810421563)
          ·
            refine ⟨9255564547312279215632345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6170376364874852810421563 9255564547312279215632345)
            ·
              refine ⟨6941673410484209411724259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9255564547312279215632345 6941673410484209411724259)
              ·
                refine ⟨10412510115726314117586389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6941673410484209411724259 10412510115726314117586389)
                ·
                  refine ⟨244043205837335487130931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10412510115726314117586389 244043205837335487130931)
                  ·
                    rfl

theorem cell21_1069363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 7].length) (baseStart_1069363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069363 prefixEnd_1069363 := by exact prefixLift 1069363
  have htrace : WordTrace (prefixWord ++ tailWord_1069363) baseStart_1069363 baseEnd_1069363 := by
    simpa [prefixWord, tailWord_1069363, baseEnd_1069363] using wordTrace_append hprefix tailTrace_1069363
  have hstable : (prefixWord ++ tailWord_1069363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069363).length < 2 ^ (prefixWord ++ tailWord_1069363).sum := by decide
  have hdescent : baseEnd_1069363 < baseStart_1069363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069394 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 6]
def baseStart_1069394 : Nat := 118140960795 + 1069394 * 2 ^ 59
def prefixEnd_1069394 : Nat := 4983230072969 + 3 ^ 40 * 1069394 * 2
def baseEnd_1069394 : Nat := 244050280459686322114201

theorem tailTrace_1069394 : CollatzResearch.WordTrace tailWord_1069394 prefixEnd_1069394 244050280459686322114201 := by
  unfold tailWord_1069394
  simp only [CollatzResearch.WordTrace]
  refine ⟨9751000871943912699939809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26002668991850433866506157 9751000871943912699939809)
  ·
    refine ⟨7313250653957934524954857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9751000871943912699939809 7313250653957934524954857)
    ·
      refine ⟨5484937990468450893716143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7313250653957934524954857 5484937990468450893716143)
      ·
        refine ⟨8227406985702676340574215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5484937990468450893716143 8227406985702676340574215)
        ·
          refine ⟨12341110478554014510861323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8227406985702676340574215 12341110478554014510861323)
          ·
            refine ⟨18511665717831021766291985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12341110478554014510861323 18511665717831021766291985)
            ·
              refine ⟨13883749288373266324718989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18511665717831021766291985 13883749288373266324718989)
              ·
                refine ⟨5206405983139974871769621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13883749288373266324718989 5206405983139974871769621)
                ·
                  refine ⟨244050280459686322114201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5206405983139974871769621 244050280459686322114201)
                  ·
                    rfl

theorem cell21_1069394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_1069394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069394 prefixEnd_1069394 := by exact prefixLift 1069394
  have htrace : WordTrace (prefixWord ++ tailWord_1069394) baseStart_1069394 baseEnd_1069394 := by
    simpa [prefixWord, tailWord_1069394, baseEnd_1069394] using wordTrace_append hprefix tailTrace_1069394
  have hstable : (prefixWord ++ tailWord_1069394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069394).length < 2 ^ (prefixWord ++ tailWord_1069394).sum := by decide
  have hdescent : baseEnd_1069394 < baseStart_1069394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069501 : List Nat := [1, 4, 1, 2, 2, 4, 7]
def baseStart_1069501 : Nat := 118140960795 + 1069501 * 2 ^ 59
def prefixEnd_1069501 : Nat := 4983230072969 + 3 ^ 40 * 1069501 * 2
def baseEnd_1069501 : Nat := 27119411035275323758961

theorem tailTrace_1069501 : CollatzResearch.WordTrace tailWord_1069501 prefixEnd_1069501 27119411035275323758961 := by
  unfold tailWord_1069501
  simp only [CollatzResearch.WordTrace]
  refine ⟨39007906098388008073904357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26005270732258672049269571 39007906098388008073904357)
  ·
    refine ⟨7313982393447751513857067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39007906098388008073904357 7313982393447751513857067)
    ·
      refine ⟨10970973590171627270785601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7313982393447751513857067 10970973590171627270785601)
      ·
        refine ⟨8228230192628720453089201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10970973590171627270785601 8228230192628720453089201)
        ·
          refine ⟨6171172644471540339816901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8228230192628720453089201 6171172644471540339816901)
          ·
            refine ⟨1157094870838413813715669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6171172644471540339816901 1157094870838413813715669)
            ·
              refine ⟨27119411035275323758961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1157094870838413813715669 27119411035275323758961)
              ·
                rfl

theorem cell21_1069501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 7].length) (baseStart_1069501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069501 prefixEnd_1069501 := by exact prefixLift 1069501
  have htrace : WordTrace (prefixWord ++ tailWord_1069501) baseStart_1069501 baseEnd_1069501 := by
    simpa [prefixWord, tailWord_1069501, baseEnd_1069501] using wordTrace_append hprefix tailTrace_1069501
  have hstable : (prefixWord ++ tailWord_1069501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069501).length < 2 ^ (prefixWord ++ tailWord_1069501).sum := by decide
  have hdescent : baseEnd_1069501 < baseStart_1069501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069653 : List Nat := [1, 3, 2, 2, 1, 1, 6, 5]
def baseStart_1069653 : Nat := 118140960795 + 1069653 * 2 ^ 59
def prefixEnd_1069653 : Nat := 4983230072969 + 3 ^ 40 * 1069653 * 2
def baseEnd_1069653 : Nat := 81369795929453142432335

theorem tailTrace_1069653 : CollatzResearch.WordTrace tailWord_1069653 prefixEnd_1069653 81369795929453142432335 := by
  unfold tailWord_1069653
  simp only [CollatzResearch.WordTrace]
  refine ⟨39013449993837338033437613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26008966662558225355625075 39013449993837338033437613)
  ·
    refine ⟨14630043747689001762539105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39013449993837338033437613 14630043747689001762539105)
    ·
      refine ⟨10972532810766751321904329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14630043747689001762539105 10972532810766751321904329)
      ·
        refine ⟨8229399608075063491428247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10972532810766751321904329 8229399608075063491428247)
        ·
          refine ⟨12344099412112595237142371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8229399608075063491428247 12344099412112595237142371)
          ·
            refine ⟨18516149118168892855713557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12344099412112595237142371 18516149118168892855713557)
            ·
              refine ⟨867944489914166852611573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18516149118168892855713557 867944489914166852611573)
              ·
                refine ⟨81369795929453142432335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 867944489914166852611573 81369795929453142432335)
                ·
                  rfl

theorem cell21_1069653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 5].length) (baseStart_1069653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069653 prefixEnd_1069653 := by exact prefixLift 1069653
  have htrace : WordTrace (prefixWord ++ tailWord_1069653) baseStart_1069653 baseEnd_1069653 := by
    simpa [prefixWord, tailWord_1069653, baseEnd_1069653] using wordTrace_append hprefix tailTrace_1069653
  have hstable : (prefixWord ++ tailWord_1069653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069653).length < 2 ^ (prefixWord ++ tailWord_1069653).sum := by decide
  have hdescent : baseEnd_1069653 < baseStart_1069653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069729 : List Nat := [1, 2, 3, 3, 4, 8]
def baseStart_1069729 : Nat := 118140960795 + 1069729 * 2 ^ 59
def prefixEnd_1069729 : Nat := 4983230072969 + 3 ^ 40 * 1069729 * 2
def baseEnd_1069729 : Nat := 9041730815696303112229

theorem tailTrace_1069729 : CollatzResearch.WordTrace tailWord_1069729 prefixEnd_1069729 9041730815696303112229 := by
  unfold tailWord_1069729
  simp only [CollatzResearch.WordTrace]
  refine ⟨39016221941562003013204241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26010814627708002008802827 39016221941562003013204241)
  ·
    refine ⟨29262166456171502259903181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39016221941562003013204241 29262166456171502259903181)
    ·
      refine ⟨10973312421064313347463693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29262166456171502259903181 10973312421064313347463693)
      ·
        refine ⟨4114992157899117505298885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10973312421064313347463693 4114992157899117505298885)
        ·
          refine ⟨771561029606084532243541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4114992157899117505298885 771561029606084532243541)
          ·
            refine ⟨9041730815696303112229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 771561029606084532243541 9041730815696303112229)
            ·
              rfl

theorem cell21_1069729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 8].length) (baseStart_1069729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069729 prefixEnd_1069729 := by exact prefixLift 1069729
  have htrace : WordTrace (prefixWord ++ tailWord_1069729) baseStart_1069729 baseEnd_1069729 := by
    simpa [prefixWord, tailWord_1069729, baseEnd_1069729] using wordTrace_append hprefix tailTrace_1069729
  have hstable : (prefixWord ++ tailWord_1069729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069729).length < 2 ^ (prefixWord ++ tailWord_1069729).sum := by decide
  have hdescent : baseEnd_1069729 < baseStart_1069729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069791 : List Nat := [1, 1, 2, 3, 2, 5, 1, 2, 4]
def baseStart_1069791 : Nat := 118140960795 + 1069791 * 2 ^ 59
def prefixEnd_1069791 : Nat := 4983230072969 + 3 ^ 40 * 1069791 * 2
def baseEnd_1069791 : Nat := 244140881268501853996723

theorem tailTrace_1069791 : CollatzResearch.WordTrace tailWord_1069791 prefixEnd_1069791 244140881268501853996723 := by
  unfold tailWord_1069791
  simp only [CollatzResearch.WordTrace]
  refine ⟨39018483267337387601961227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26012322178224925067974151 39018483267337387601961227)
  ·
    refine ⟨58527724901006081402941841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39018483267337387601961227 58527724901006081402941841)
    ·
      refine ⟨43895793675754561052206381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58527724901006081402941841 43895793675754561052206381)
      ·
        refine ⟨16460922628407960394577393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43895793675754561052206381 16460922628407960394577393)
        ·
          refine ⟨12345691971305970295933045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16460922628407960394577393 12345691971305970295933045)
          ·
            refine ⟨1157408622309934715243723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12345691971305970295933045 1157408622309934715243723)
            ·
              refine ⟨1736112933464902072865585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1157408622309934715243723 1736112933464902072865585)
              ·
                refine ⟨1302084700098676554649189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1736112933464902072865585 1302084700098676554649189)
                ·
                  refine ⟨244140881268501853996723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1302084700098676554649189 244140881268501853996723)
                  ·
                    rfl

theorem cell21_1069791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 4].length) (baseStart_1069791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069791 prefixEnd_1069791 := by exact prefixLift 1069791
  have htrace : WordTrace (prefixWord ++ tailWord_1069791) baseStart_1069791 baseEnd_1069791 := by
    simpa [prefixWord, tailWord_1069791, baseEnd_1069791] using wordTrace_append hprefix tailTrace_1069791
  have hstable : (prefixWord ++ tailWord_1069791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069791).length < 2 ^ (prefixWord ++ tailWord_1069791).sum := by decide
  have hdescent : baseEnd_1069791 < baseStart_1069791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069822 : List Nat := [4, 2, 2, 1, 2, 1, 4, 5]
def baseStart_1069822 : Nat := 118140960795 + 1069822 * 2 ^ 59
def prefixEnd_1069822 : Nat := 4983230072969 + 3 ^ 40 * 1069822 * 2
def baseEnd_1069822 : Nat := 81382651963617562993331

theorem tailTrace_1069822 : CollatzResearch.WordTrace tailWord_1069822 prefixEnd_1069822 81382651963617562993331 := by
  unfold tailWord_1069822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4877451741278134987042465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26013075953483386597559813 4877451741278134987042465)
  ·
    refine ⟨3658088805958601240281849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4877451741278134987042465 3658088805958601240281849)
    ·
      refine ⟨2743566604468950930211387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3658088805958601240281849 2743566604468950930211387)
      ·
        refine ⟨4115349906703426395317081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2743566604468950930211387 4115349906703426395317081)
        ·
          refine ⟨3086512430027569796487811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4115349906703426395317081 3086512430027569796487811)
          ·
            refine ⟨4629768645041354694731717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3086512430027569796487811 4629768645041354694731717)
            ·
              refine ⟨868081620945254005262197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4629768645041354694731717 868081620945254005262197)
              ·
                refine ⟨81382651963617562993331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 868081620945254005262197 81382651963617562993331)
                ·
                  rfl

theorem cell21_1069822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_1069822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069822 prefixEnd_1069822 := by exact prefixLift 1069822
  have htrace : WordTrace (prefixWord ++ tailWord_1069822) baseStart_1069822 baseEnd_1069822 := by
    simpa [prefixWord, tailWord_1069822, baseEnd_1069822] using wordTrace_append hprefix tailTrace_1069822
  have hstable : (prefixWord ++ tailWord_1069822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069822).length < 2 ^ (prefixWord ++ tailWord_1069822).sum := by decide
  have hdescent : baseEnd_1069822 < baseStart_1069822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069833 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 6]
def baseStart_1069833 : Nat := 118140960795 + 1069833 * 2 ^ 59
def prefixEnd_1069833 : Nat := 4983230072969 + 3 ^ 40 * 1069833 * 2
def baseEnd_1069833 : Nat := 244150466240719114296637

theorem tailTrace_1069833 : CollatzResearch.WordTrace tailWord_1069833 prefixEnd_1069833 244150466240719114296637 := by
  unfold tailWord_1069833
  simp only [CollatzResearch.WordTrace]
  refine ⟨39020015133185228774990153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26013343422123485849993435 39020015133185228774990153)
  ·
    refine ⟨29265011349888921581242615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39020015133185228774990153 29265011349888921581242615)
    ·
      refine ⟨43897517024833382371863923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29265011349888921581242615 43897517024833382371863923)
      ·
        refine ⟨65846275537250073557795885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43897517024833382371863923 65846275537250073557795885)
        ·
          refine ⟨24692353326468777584173457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65846275537250073557795885 24692353326468777584173457)
          ·
            refine ⟨18519264994851583188130093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24692353326468777584173457 18519264994851583188130093)
            ·
              refine ⟨6944724373069343695548785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18519264994851583188130093 6944724373069343695548785)
              ·
                refine ⟨5208543279802007771661589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6944724373069343695548785 5208543279802007771661589)
                ·
                  refine ⟨244150466240719114296637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5208543279802007771661589 244150466240719114296637)
                  ·
                    rfl

theorem cell21_1069833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_1069833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069833 prefixEnd_1069833 := by exact prefixLift 1069833
  have htrace : WordTrace (prefixWord ++ tailWord_1069833) baseStart_1069833 baseEnd_1069833 := by
    simpa [prefixWord, tailWord_1069833, baseEnd_1069833] using wordTrace_append hprefix tailTrace_1069833
  have hstable : (prefixWord ++ tailWord_1069833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069833).length < 2 ^ (prefixWord ++ tailWord_1069833).sum := by decide
  have hdescent : baseEnd_1069833 < baseStart_1069833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069850 : List Nat := [3, 1, 1, 3, 2, 1, 2, 4, 4]
def baseStart_1069850 : Nat := 118140960795 + 1069850 * 2 ^ 59
def prefixEnd_1069850 : Nat := 4983230072969 + 3 ^ 40 * 1069850 * 2
def baseEnd_1069850 : Nat := 244154345872330862513269

theorem tailTrace_1069850 : CollatzResearch.WordTrace tailWord_1069850 prefixEnd_1069850 244154345872330862513269 := by
  unfold tailWord_1069850
  simp only [CollatzResearch.WordTrace]
  refine ⟨9755158793530910169589751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26013756782749093785572669 9755158793530910169589751)
  ·
    refine ⟨14632738190296365254384627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9755158793530910169589751 14632738190296365254384627)
    ·
      refine ⟨21949107285444547881576941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14632738190296365254384627 21949107285444547881576941)
      ·
        refine ⟨8230915232041705455591353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21949107285444547881576941 8230915232041705455591353)
        ·
          refine ⟨6173186424031279091693515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8230915232041705455591353 6173186424031279091693515)
          ·
            refine ⟨9259779636046918637540273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6173186424031279091693515 9259779636046918637540273)
            ·
              refine ⟨6944834727035188978155205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9259779636046918637540273 6944834727035188978155205)
              ·
                refine ⟨1302156511319097933404101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6944834727035188978155205 1302156511319097933404101)
                ·
                  refine ⟨244154345872330862513269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1302156511319097933404101 244154345872330862513269)
                  ·
                    rfl

theorem cell21_1069850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_1069850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069850 prefixEnd_1069850 := by exact prefixLift 1069850
  have htrace : WordTrace (prefixWord ++ tailWord_1069850) baseStart_1069850 baseEnd_1069850 := by
    simpa [prefixWord, tailWord_1069850, baseEnd_1069850] using wordTrace_append hprefix tailTrace_1069850
  have hstable : (prefixWord ++ tailWord_1069850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069850).length < 2 ^ (prefixWord ++ tailWord_1069850).sum := by decide
  have hdescent : baseEnd_1069850 < baseStart_1069850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1069991 : List Nat := [1, 1, 6, 1, 4, 1, 2, 5]
def baseStart_1069991 : Nat := 118140960795 + 1069991 * 2 ^ 59
def prefixEnd_1069991 : Nat := 4983230072969 + 3 ^ 40 * 1069991 * 2
def baseEnd_1069991 : Nat := 81395507997781983554327

theorem tailTrace_1069991 : CollatzResearch.WordTrace tailWord_1069991 prefixEnd_1069991 81395507997781983554327 := by
  unfold tailWord_1069991
  simp only [CollatzResearch.WordTrace]
  refine ⟨39025777866612821759241827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26017185244408547839494551 39025777866612821759241827)
  ·
    refine ⟨58538666799919232638862741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39025777866612821759241827 58538666799919232638862741)
    ·
      refine ⟨2744000006246214029946691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58538666799919232638862741 2744000006246214029946691)
      ·
        refine ⟨4116000009369321044920037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2744000006246214029946691 4116000009369321044920037)
        ·
          refine ⟨771750001756747695922507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4116000009369321044920037 771750001756747695922507)
          ·
            refine ⟨1157625002635121543883761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771750001756747695922507 1157625002635121543883761)
            ·
              refine ⟨868218751976341157912821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1157625002635121543883761 868218751976341157912821)
              ·
                refine ⟨81395507997781983554327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 868218751976341157912821 81395507997781983554327)
                ·
                  rfl

theorem cell21_1069991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 5].length) (baseStart_1069991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1069991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1069991 prefixEnd_1069991 := by exact prefixLift 1069991
  have htrace : WordTrace (prefixWord ++ tailWord_1069991) baseStart_1069991 baseEnd_1069991 := by
    simpa [prefixWord, tailWord_1069991, baseEnd_1069991] using wordTrace_append hprefix tailTrace_1069991
  have hstable : (prefixWord ++ tailWord_1069991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1069991).length < 2 ^ (prefixWord ++ tailWord_1069991).sum := by decide
  have hdescent : baseEnd_1069991 < baseStart_1069991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1069991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070016 : List Nat := [2, 1, 1, 2, 3, 5, 7]
def baseStart_1070016 : Nat := 118140960795 + 1070016 * 2 ^ 59
def prefixEnd_1070016 : Nat := 4983230072969 + 3 ^ 40 * 1070016 * 2
def baseEnd_1070016 : Nat := 27132469925994606971807

theorem tailTrace_1070016 : CollatzResearch.WordTrace tailWord_1070016 prefixEnd_1070016 27132469925994606971807 := by
  unfold tailWord_1070016
  simp only [CollatzResearch.WordTrace]
  refine ⟨19513344845761125514450951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26017793127681500685934601 19513344845761125514450951)
  ·
    refine ⟨29270017268641688271676427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19513344845761125514450951 29270017268641688271676427)
    ·
      refine ⟨43905025902962532407514641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29270017268641688271676427 43905025902962532407514641)
      ·
        refine ⟨32928769427221899305635981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43905025902962532407514641 32928769427221899305635981)
        ·
          refine ⟨12348288535208212239613493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32928769427221899305635981 12348288535208212239613493)
          ·
            refine ⟨1157652050175769897463765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12348288535208212239613493 1157652050175769897463765)
            ·
              refine ⟨27132469925994606971807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1157652050175769897463765 27132469925994606971807)
              ·
                rfl

theorem cell21_1070016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 7].length) (baseStart_1070016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070016 prefixEnd_1070016 := by exact prefixLift 1070016
  have htrace : WordTrace (prefixWord ++ tailWord_1070016) baseStart_1070016 baseEnd_1070016 := by
    simpa [prefixWord, tailWord_1070016, baseEnd_1070016] using wordTrace_append hprefix tailTrace_1070016
  have hstable : (prefixWord ++ tailWord_1070016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070016).length < 2 ^ (prefixWord ++ tailWord_1070016).sum := by decide
  have hdescent : baseEnd_1070016 < baseStart_1070016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070036 : List Nat := [2, 4, 1, 2, 1, 4, 2, 1, 4]
def baseStart_1070036 : Nat := 118140960795 + 1070036 * 2 ^ 59
def prefixEnd_1070036 : Nat := 4983230072969 + 3 ^ 40 * 1070036 * 2
def baseEnd_1070036 : Nat := 244196793606435872412889

theorem tailTrace_1070036 : CollatzResearch.WordTrace tailWord_1070036 prefixEnd_1070036 244196793606435872412889 := by
  unfold tailWord_1070036
  simp only [CollatzResearch.WordTrace]
  refine ⟨19513709575724897222314981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26018279434299862963086641 19513709575724897222314981)
  ·
    refine ⟨3658820545448418229184059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19513709575724897222314981 3658820545448418229184059)
    ·
      refine ⟨5488230818172627343776089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3658820545448418229184059 5488230818172627343776089)
      ·
        refine ⟨4116173113629470507832067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5488230818172627343776089 4116173113629470507832067)
        ·
          refine ⟨6174259670444205761748101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4116173113629470507832067 6174259670444205761748101)
          ·
            refine ⟨1157673688208288580327769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6174259670444205761748101 1157673688208288580327769)
            ·
              refine ⟨868255266156216435245827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1157673688208288580327769 868255266156216435245827)
              ·
                refine ⟨1302382899234324652868741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868255266156216435245827 1302382899234324652868741)
                ·
                  refine ⟨244196793606435872412889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1302382899234324652868741 244196793606435872412889)
                  ·
                    rfl

theorem cell21_1070036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_1070036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070036 prefixEnd_1070036 := by exact prefixLift 1070036
  have htrace : WordTrace (prefixWord ++ tailWord_1070036) baseStart_1070036 baseEnd_1070036 := by
    simpa [prefixWord, tailWord_1070036, baseEnd_1070036] using wordTrace_append hprefix tailTrace_1070036
  have hstable : (prefixWord ++ tailWord_1070036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070036).length < 2 ^ (prefixWord ++ tailWord_1070036).sum := by decide
  have hdescent : baseEnd_1070036 < baseStart_1070036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070081 : List Nat := [1, 2, 4, 1, 2, 2, 4, 2, 3]
def baseStart_1070081 : Nat := 118140960795 + 1070081 * 2 ^ 59
def prefixEnd_1070081 : Nat := 4983230072969 + 3 ^ 40 * 1070081 * 2
def baseEnd_1070081 : Nat := 244207063219525794162797

theorem tailTrace_1070081 : CollatzResearch.WordTrace tailWord_1070081 prefixEnd_1070081 244207063219525794162797 := by
  unfold tailWord_1070081
  simp only [CollatzResearch.WordTrace]
  refine ⟨39029060436286767130018097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26019373624191178086678731 39029060436286767130018097)
  ·
    refine ⟨29271795327215075347513573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39029060436286767130018097 29271795327215075347513573)
    ·
      refine ⟨5488461623852826627658795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29271795327215075347513573 5488461623852826627658795)
      ·
        refine ⟨8232692435779239941488193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5488461623852826627658795 8232692435779239941488193)
        ·
          refine ⟨6174519326834429956116145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8232692435779239941488193 6174519326834429956116145)
          ·
            refine ⟨4630889495125822467087109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6174519326834429956116145 4630889495125822467087109)
            ·
              refine ⟨868291780336091712578833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4630889495125822467087109 868291780336091712578833)
              ·
                refine ⟨651218835252068784434125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 868291780336091712578833 651218835252068784434125)
                ·
                  refine ⟨244207063219525794162797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651218835252068784434125 244207063219525794162797)
                  ·
                    rfl

theorem cell21_1070081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 3].length) (baseStart_1070081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070081 prefixEnd_1070081 := by exact prefixLift 1070081
  have htrace : WordTrace (prefixWord ++ tailWord_1070081) baseStart_1070081 baseEnd_1070081 := by
    simpa [prefixWord, tailWord_1070081, baseEnd_1070081] using wordTrace_append hprefix tailTrace_1070081
  have hstable : (prefixWord ++ tailWord_1070081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070081).length < 2 ^ (prefixWord ++ tailWord_1070081).sum := by decide
  have hdescent : baseEnd_1070081 < baseStart_1070081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070092 : List Nat := [2, 2, 1, 2, 3, 2, 3, 6]
def baseStart_1070092 : Nat := 118140960795 + 1070092 * 2 ^ 59
def prefixEnd_1070092 : Nat := 4983230072969 + 3 ^ 40 * 1070092 * 2
def baseEnd_1070092 : Nat := 81403191189797406493147

theorem tailTrace_1070092 : CollatzResearch.WordTrace tailWord_1070092 prefixEnd_1070092 81403191189797406493147 := by
  unfold tailWord_1070092
  simp only [CollatzResearch.WordTrace]
  refine ⟨19514730819623458004334265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26019641092831277339112353 19514730819623458004334265)
  ·
    refine ⟨14636048114717593503250699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19514730819623458004334265 14636048114717593503250699)
    ·
      refine ⟨21954072172076390254876049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14636048114717593503250699 21954072172076390254876049)
      ·
        refine ⟨16465554129057292691157037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21954072172076390254876049 16465554129057292691157037)
        ·
          refine ⟨6174582798396484759183889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16465554129057292691157037 6174582798396484759183889)
          ·
            refine ⟨4630937098797363569387917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6174582798396484759183889 4630937098797363569387917)
            ·
              refine ⟨1736601412049011338520469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4630937098797363569387917 1736601412049011338520469)
              ·
                refine ⟨81403191189797406493147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1736601412049011338520469 81403191189797406493147)
                ·
                  rfl

theorem cell21_1070092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 6].length) (baseStart_1070092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070092 prefixEnd_1070092 := by exact prefixLift 1070092
  have htrace : WordTrace (prefixWord ++ tailWord_1070092) baseStart_1070092 baseEnd_1070092 := by
    simpa [prefixWord, tailWord_1070092, baseEnd_1070092] using wordTrace_append hprefix tailTrace_1070092
  have hstable : (prefixWord ++ tailWord_1070092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070092).length < 2 ^ (prefixWord ++ tailWord_1070092).sum := by decide
  have hdescent : baseEnd_1070092 < baseStart_1070092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070098 : List Nat := [3, 2, 5, 1, 1, 1, 1, 2, 5]
def baseStart_1070098 : Nat := 118140960795 + 1070098 * 2 ^ 59
def prefixEnd_1070098 : Nat := 4983230072969 + 3 ^ 40 * 1070098 * 2
def baseEnd_1070098 : Nat := 244210942851137542379429

theorem tailTrace_1070098 : CollatzResearch.WordTrace tailWord_1070098 prefixEnd_1070098 244210942851137542379429 := by
  unfold tailWord_1070098
  simp only [CollatzResearch.WordTrace]
  refine ⟨9757420119306294758346737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26019786984816786022257965 9757420119306294758346737)
  ·
    refine ⟨7318065089479721068760053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9757420119306294758346737 7318065089479721068760053)
    ·
      refine ⟨686068602138723850196255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7318065089479721068760053 686068602138723850196255)
      ·
        refine ⟨1029102903208085775294383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686068602138723850196255 1029102903208085775294383)
        ·
          refine ⟨1543654354812128662941575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029102903208085775294383 1543654354812128662941575)
          ·
            refine ⟨2315481532218192994412363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1543654354812128662941575 2315481532218192994412363)
            ·
              refine ⟨3473222298327289491618545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2315481532218192994412363 3473222298327289491618545)
              ·
                refine ⟨2604916723745467118713909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3473222298327289491618545 2604916723745467118713909)
                ·
                  refine ⟨244210942851137542379429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2604916723745467118713909 244210942851137542379429)
                  ·
                    rfl

theorem cell21_1070098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_1070098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070098 prefixEnd_1070098 := by exact prefixLift 1070098
  have htrace : WordTrace (prefixWord ++ tailWord_1070098) baseStart_1070098 baseEnd_1070098 := by
    simpa [prefixWord, tailWord_1070098, baseEnd_1070098] using wordTrace_append hprefix tailTrace_1070098
  have hstable : (prefixWord ++ tailWord_1070098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070098).length < 2 ^ (prefixWord ++ tailWord_1070098).sum := by decide
  have hdescent : baseEnd_1070098 < baseStart_1070098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070140 : List Nat := [2, 2, 2, 2, 2, 2, 2, 4, 3]
def baseStart_1070140 : Nat := 118140960795 + 1070140 * 2 ^ 59
def prefixEnd_1070140 : Nat := 4983230072969 + 3 ^ 40 * 1070140 * 2
def baseEnd_1070140 : Nat := 244220527823354802679343

theorem tailTrace_1070140 : CollatzResearch.WordTrace tailWord_1070140 prefixEnd_1070140 244220527823354802679343 := by
  unfold tailWord_1070140
  simp only [CollatzResearch.WordTrace]
  refine ⟨19515606171536510103207937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26020808228715346804277249 19515606171536510103207937)
  ·
    refine ⟨14636704628652382577405953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19515606171536510103207937 14636704628652382577405953)
    ·
      refine ⟨10977528471489286933054465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14636704628652382577405953 10977528471489286933054465)
      ·
        refine ⟨8233146353616965199790849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10977528471489286933054465 8233146353616965199790849)
        ·
          refine ⟨6174859765212723899843137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8233146353616965199790849 6174859765212723899843137)
          ·
            refine ⟨4631144823909542924882353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6174859765212723899843137 4631144823909542924882353)
            ·
              refine ⟨3473358617932157193661765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4631144823909542924882353 3473358617932157193661765)
              ·
                refine ⟨651254740862279473811581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3473358617932157193661765 651254740862279473811581)
                ·
                  refine ⟨244220527823354802679343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651254740862279473811581 244220527823354802679343)
                  ·
                    rfl

theorem cell21_1070140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_1070140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070140 prefixEnd_1070140 := by exact prefixLift 1070140
  have htrace : WordTrace (prefixWord ++ tailWord_1070140) baseStart_1070140 baseEnd_1070140 := by
    simpa [prefixWord, tailWord_1070140, baseEnd_1070140] using wordTrace_append hprefix tailTrace_1070140
  have hstable : (prefixWord ++ tailWord_1070140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070140).length < 2 ^ (prefixWord ++ tailWord_1070140).sum := by decide
  have hdescent : baseEnd_1070140 < baseStart_1070140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070227 : List Nat := [1, 1, 1, 2, 1, 2, 6, 7]
def baseStart_1070227 : Nat := 118140960795 + 1070227 * 2 ^ 59
def prefixEnd_1070227 : Nat := 4983230072969 + 3 ^ 40 * 1070227 * 2
def baseEnd_1070227 : Nat := 81413460802887328243055

theorem tailTrace_1070227 : CollatzResearch.WordTrace tailWord_1070227 prefixEnd_1070227 81413460802887328243055 := by
  unfold tailWord_1070227
  simp only [CollatzResearch.WordTrace]
  refine ⟨39034385493757834064832935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26022923662505222709888623 39034385493757834064832935)
  ·
    refine ⟨58551578240636751097249403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39034385493757834064832935 58551578240636751097249403)
    ·
      refine ⟨87827367360955126645874105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58551578240636751097249403 87827367360955126645874105)
      ·
        refine ⟨65870525520716344984405579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87827367360955126645874105 65870525520716344984405579)
        ·
          refine ⟨98805788281074517476608369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65870525520716344984405579 98805788281074517476608369)
          ·
            refine ⟨74104341210805888107456277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98805788281074517476608369 74104341210805888107456277)
            ·
              refine ⟨3473640994256526005037013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74104341210805888107456277 3473640994256526005037013)
              ·
                refine ⟨81413460802887328243055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3473640994256526005037013 81413460802887328243055)
                ·
                  rfl

theorem cell21_1070227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 7].length) (baseStart_1070227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070227 prefixEnd_1070227 := by exact prefixLift 1070227
  have htrace : WordTrace (prefixWord ++ tailWord_1070227) baseStart_1070227 baseEnd_1070227 := by
    simpa [prefixWord, tailWord_1070227, baseEnd_1070227] using wordTrace_append hprefix tailTrace_1070227
  have hstable : (prefixWord ++ tailWord_1070227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070227).length < 2 ^ (prefixWord ++ tailWord_1070227).sum := by decide
  have hdescent : baseEnd_1070227 < baseStart_1070227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070247 : List Nat := [1, 1, 6, 2, 1, 2, 2, 2, 4]
def baseStart_1070247 : Nat := 118140960795 + 1070247 * 2 ^ 59
def prefixEnd_1070247 : Nat := 4983230072969 + 3 ^ 40 * 1070247 * 2
def baseEnd_1070247 : Nat := 244244946681146394395791

theorem tailTrace_1070247 : CollatzResearch.WordTrace tailWord_1070247 prefixEnd_1070247 244244946681146394395791 := by
  unfold tailWord_1070247
  simp only [CollatzResearch.WordTrace]
  refine ⟨39035114953685377480560995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26023409969123584987040663 39035114953685377480560995)
  ·
    refine ⟨58552672430528066220841493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39035114953685377480560995 58552672430528066220841493)
    ·
      refine ⟨2744656520181003104101945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58552672430528066220841493 2744656520181003104101945)
      ·
        refine ⟨2058492390135752328076459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2744656520181003104101945 2058492390135752328076459)
        ·
          refine ⟨3087738585203628492114689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058492390135752328076459 3087738585203628492114689)
          ·
            refine ⟨2315803938902721369086017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3087738585203628492114689 2315803938902721369086017)
            ·
              refine ⟨1736852954177041026814513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2315803938902721369086017 1736852954177041026814513)
              ·
                refine ⟨1302639715632780770110885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1736852954177041026814513 1302639715632780770110885)
                ·
                  refine ⟨244244946681146394395791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1302639715632780770110885 244244946681146394395791)
                  ·
                    rfl

theorem cell21_1070247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 4].length) (baseStart_1070247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070247 prefixEnd_1070247 := by exact prefixLift 1070247
  have htrace : WordTrace (prefixWord ++ tailWord_1070247) baseStart_1070247 baseEnd_1070247 := by
    simpa [prefixWord, tailWord_1070247, baseEnd_1070247] using wordTrace_append hprefix tailTrace_1070247
  have hstable : (prefixWord ++ tailWord_1070247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070247).length < 2 ^ (prefixWord ++ tailWord_1070247).sum := by decide
  have hdescent : baseEnd_1070247 < baseStart_1070247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070250 : List Nat := [3, 1, 5, 1, 1, 1, 4, 2, 3]
def baseStart_1070250 : Nat := 118140960795 + 1070250 * 2 ^ 59
def prefixEnd_1070250 : Nat := 4983230072969 + 3 ^ 40 * 1070250 * 2
def baseEnd_1070250 : Nat := 244245631322019055845785

theorem tailTrace_1070250 : CollatzResearch.WordTrace tailWord_1070250 prefixEnd_1070250 244245631322019055845785 := by
  unfold tailWord_1070250
  simp only [CollatzResearch.WordTrace]
  refine ⟨9758806093168627248230051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26023482915116339328613469 9758806093168627248230051)
  ·
    refine ⟨14638209139752940872345077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9758806093168627248230051 14638209139752940872345077)
    ·
      refine ⟨1372332106851838206782351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14638209139752940872345077 1372332106851838206782351)
      ·
        refine ⟨2058498160277757310173527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1372332106851838206782351 2058498160277757310173527)
        ·
          refine ⟨3087747240416635965260291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058498160277757310173527 3087747240416635965260291)
          ·
            refine ⟨4631620860624953947890437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3087747240416635965260291 4631620860624953947890437)
            ·
              refine ⟨868428911367178865229457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4631620860624953947890437 868428911367178865229457)
              ·
                refine ⟨651321683525384148922093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 868428911367178865229457 651321683525384148922093)
                ·
                  refine ⟨244245631322019055845785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651321683525384148922093 244245631322019055845785)
                  ·
                    rfl

theorem cell21_1070250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_1070250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070250 prefixEnd_1070250 := by exact prefixLift 1070250
  have htrace : WordTrace (prefixWord ++ tailWord_1070250) baseStart_1070250 baseEnd_1070250 := by
    simpa [prefixWord, tailWord_1070250, baseEnd_1070250] using wordTrace_append hprefix tailTrace_1070250
  have hstable : (prefixWord ++ tailWord_1070250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070250).length < 2 ^ (prefixWord ++ tailWord_1070250).sum := by decide
  have hdescent : baseEnd_1070250 < baseStart_1070250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070337 : List Nat := [1, 2, 4, 1, 1, 5, 2, 5]
def baseStart_1070337 : Nat := 118140960795 + 1070337 * 2 ^ 59
def prefixEnd_1070337 : Nat := 4983230072969 + 3 ^ 40 * 1070337 * 2
def baseEnd_1070337 : Nat := 81421828635775412631869

theorem tailTrace_1070337 : CollatzResearch.WordTrace tailWord_1070337 prefixEnd_1070337 81421828635775412631869 := by
  unfold tailWord_1070337
  simp only [CollatzResearch.WordTrace]
  refine ⟨39038397523359322851337265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26025598348906215234224843 39038397523359322851337265)
  ·
    refine ⟨29278798142519492138502949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39038397523359322851337265 29278798142519492138502949)
    ·
      refine ⟨5489774651722404775969303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29278798142519492138502949 5489774651722404775969303)
      ·
        refine ⟨8234661977583607163953955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5489774651722404775969303 8234661977583607163953955)
        ·
          refine ⟨12351992966375410745930933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8234661977583607163953955 12351992966375410745930933)
          ·
            refine ⟨1157999340597694757431025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12351992966375410745930933 1157999340597694757431025)
            ·
              refine ⟨868499505448271068073269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1157999340597694757431025 868499505448271068073269)
              ·
                refine ⟨81421828635775412631869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 868499505448271068073269 81421828635775412631869)
                ·
                  rfl

theorem cell21_1070337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 5].length) (baseStart_1070337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070337 prefixEnd_1070337 := by exact prefixLift 1070337
  have htrace : WordTrace (prefixWord ++ tailWord_1070337) baseStart_1070337 baseEnd_1070337 := by
    simpa [prefixWord, tailWord_1070337, baseEnd_1070337] using wordTrace_append hprefix tailTrace_1070337
  have hstable : (prefixWord ++ tailWord_1070337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070337).length < 2 ^ (prefixWord ++ tailWord_1070337).sum := by decide
  have hdescent : baseEnd_1070337 < baseStart_1070337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070354 : List Nat := [3, 2, 4, 2, 1, 2, 7]
def baseStart_1070354 : Nat := 118140960795 + 1070354 * 2 ^ 59
def prefixEnd_1070354 : Nat := 4983230072969 + 3 ^ 40 * 1070354 * 2
def baseEnd_1070354 : Nat := 27141040615437554012471

theorem tailTrace_1070354 : CollatzResearch.WordTrace tailWord_1070354 prefixEnd_1070354 27141040615437554012471 := by
  unfold tailWord_1070354
  simp only [CollatzResearch.WordTrace]
  refine ⟨9759754391074433688676529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26026011709531823169804077 9759754391074433688676529)
  ·
    refine ⟨7319815793305825266507397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9759754391074433688676529 7319815793305825266507397)
    ·
      refine ⟨1372465461244842237470137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7319815793305825266507397 1372465461244842237470137)
      ·
        refine ⟨1029349095933631678102603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1372465461244842237470137 1029349095933631678102603)
        ·
          refine ⟨1544023643900447517153905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029349095933631678102603 1544023643900447517153905)
          ·
            refine ⟨1158017732925335637865429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1544023643900447517153905 1158017732925335637865429)
            ·
              refine ⟨27141040615437554012471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1158017732925335637865429 27141040615437554012471)
              ·
                rfl

theorem cell21_1070354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 7].length) (baseStart_1070354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070354 prefixEnd_1070354 := by exact prefixLift 1070354
  have htrace : WordTrace (prefixWord ++ tailWord_1070354) baseStart_1070354 baseEnd_1070354 := by
    simpa [prefixWord, tailWord_1070354, baseEnd_1070354] using wordTrace_append hprefix tailTrace_1070354
  have hstable : (prefixWord ++ tailWord_1070354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070354).length < 2 ^ (prefixWord ++ tailWord_1070354).sum := by decide
  have hdescent : baseEnd_1070354 < baseStart_1070354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070368 : List Nat := [2, 1, 1, 5, 3, 2, 1, 1, 5]
def baseStart_1070368 : Nat := 118140960795 + 1070368 * 2 ^ 59
def prefixEnd_1070368 : Nat := 4983230072969 + 3 ^ 40 * 1070368 * 2
def baseEnd_1070368 : Nat := 244272560529677072878877

theorem tailTrace_1070368 : CollatzResearch.WordTrace tailWord_1070368 prefixEnd_1070368 244272560529677072878877 := by
  unfold tailWord_1070368
  simp only [CollatzResearch.WordTrace]
  refine ⟨19519764093123507572857879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26026352124164676763810505 19519764093123507572857879)
  ·
    refine ⟨29279646139685261359286819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19519764093123507572857879 29279646139685261359286819)
    ·
      refine ⟨43919469209527892038930229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29279646139685261359286819 43919469209527892038930229)
      ·
        refine ⟨4117450238393239878649709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43919469209527892038930229 4117450238393239878649709)
        ·
          refine ⟨1544043839397464954493641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4117450238393239878649709 1544043839397464954493641)
          ·
            refine ⟨1158032879548098715870231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1544043839397464954493641 1158032879548098715870231)
            ·
              refine ⟨1737049319322148073805347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158032879548098715870231 1737049319322148073805347)
              ·
                refine ⟨2605573978983222110708021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1737049319322148073805347 2605573978983222110708021)
                ·
                  refine ⟨244272560529677072878877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2605573978983222110708021 244272560529677072878877)
                  ·
                    rfl

theorem cell21_1070368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 5].length) (baseStart_1070368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070368 prefixEnd_1070368 := by exact prefixLift 1070368
  have htrace : WordTrace (prefixWord ++ tailWord_1070368) baseStart_1070368 baseEnd_1070368 := by
    simpa [prefixWord, tailWord_1070368, baseEnd_1070368] using wordTrace_append hprefix tailTrace_1070368
  have hstable : (prefixWord ++ tailWord_1070368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070368).length < 2 ^ (prefixWord ++ tailWord_1070368).sum := by decide
  have hdescent : baseEnd_1070368 < baseStart_1070368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070413 : List Nat := [1, 6, 1, 3, 1, 9]
def baseStart_1070413 : Nat := 118140960795 + 1070413 * 2 ^ 59
def prefixEnd_1070413 : Nat := 4983230072969 + 3 ^ 40 * 1070413 * 2
def baseEnd_1070413 : Nat := 9047512227509888689955

theorem tailTrace_1070413 : CollatzResearch.WordTrace tailWord_1070413 prefixEnd_1070413 9047512227509888689955 := by
  unfold tailWord_1070413
  simp only [CollatzResearch.WordTrace]
  refine ⟨39041169471083987831103893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26027446314055991887402595 39041169471083987831103893)
  ·
    refine ⟨1830054818957061929582995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39041169471083987831103893 1830054818957061929582995)
    ·
      refine ⟨2745082228435592894374493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1830054818957061929582995 2745082228435592894374493)
      ·
        refine ⟨1029405835663347335390435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2745082228435592894374493 1029405835663347335390435)
        ·
          refine ⟨1544108753495021003085653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029405835663347335390435 1544108753495021003085653)
          ·
            refine ⟨9047512227509888689955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1544108753495021003085653 9047512227509888689955)
            ·
              rfl

theorem cell21_1070413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 9].length) (baseStart_1070413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070413 prefixEnd_1070413 := by exact prefixLift 1070413
  have htrace : WordTrace (prefixWord ++ tailWord_1070413) baseStart_1070413 baseEnd_1070413 := by
    simpa [prefixWord, tailWord_1070413, baseEnd_1070413] using wordTrace_append hprefix tailTrace_1070413
  have hstable : (prefixWord ++ tailWord_1070413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070413).length < 2 ^ (prefixWord ++ tailWord_1070413).sum := by decide
  have hdescent : baseEnd_1070413 < baseStart_1070413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070492 : List Nat := [2, 2, 3, 4, 1, 1, 3, 1, 4]
def baseStart_1070492 : Nat := 118140960795 + 1070492 * 2 ^ 59
def prefixEnd_1070492 : Nat := 4983230072969 + 3 ^ 40 * 1070492 * 2
def baseEnd_1070492 : Nat := 244300859019080412811957

theorem tailTrace_1070492 : CollatzResearch.WordTrace tailWord_1070492 prefixEnd_1070492 244300859019080412811957 := by
  unfold tailWord_1070492
  simp only [CollatzResearch.WordTrace]
  refine ⟨19522025418898892161614865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26029367225198522882153153 19522025418898892161614865)
  ·
    refine ⟨14641519064174169121211149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19522025418898892161614865 14641519064174169121211149)
    ·
      refine ⟨5490569649065313420454181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14641519064174169121211149 5490569649065313420454181)
      ·
        refine ⟨1029481809199746266335159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5490569649065313420454181 1029481809199746266335159)
        ·
          refine ⟨1544222713799619399502739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029481809199746266335159 1544222713799619399502739)
          ·
            refine ⟨2316334070699429099254109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1544222713799619399502739 2316334070699429099254109)
            ·
              refine ⟨868625276512285912220291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2316334070699429099254109 868625276512285912220291)
              ·
                refine ⟨1302937914768428868330437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868625276512285912220291 1302937914768428868330437)
                ·
                  refine ⟨244300859019080412811957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1302937914768428868330437 244300859019080412811957)
                  ·
                    rfl

theorem cell21_1070492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_1070492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070492 prefixEnd_1070492 := by exact prefixLift 1070492
  have htrace : WordTrace (prefixWord ++ tailWord_1070492) baseStart_1070492 baseEnd_1070492 := by
    simpa [prefixWord, tailWord_1070492, baseEnd_1070492] using wordTrace_append hprefix tailTrace_1070492
  have hstable : (prefixWord ++ tailWord_1070492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070492).length < 2 ^ (prefixWord ++ tailWord_1070492).sum := by decide
  have hdescent : baseEnd_1070492 < baseStart_1070492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070517 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 6]
def baseStart_1070517 : Nat := 118140960795 + 1070517 * 2 ^ 59
def prefixEnd_1070517 : Nat := 4983230072969 + 3 ^ 40 * 1070517 * 2
def baseEnd_1070517 : Nat := 244306564359685924895239

theorem tailTrace_1070517 : CollatzResearch.WordTrace tailWord_1070517 prefixEnd_1070517 244306564359685924895239 := by
  unfold tailWord_1070517
  simp only [CollatzResearch.WordTrace]
  refine ⟨39044962662707213592889805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26029975108471475728593203 39044962662707213592889805)
  ·
    refine ⟨14641860998515205097333677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39044962662707213592889805 14641860998515205097333677)
    ·
      refine ⟨5490697874443201911500129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14641860998515205097333677 5490697874443201911500129)
      ·
        refine ⟨4118023405832401433625097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5490697874443201911500129 4118023405832401433625097)
        ·
          refine ⟨3088517554374301075218823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4118023405832401433625097 3088517554374301075218823)
          ·
            refine ⟨4632776331561451612828235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3088517554374301075218823 4632776331561451612828235)
            ·
              refine ⟨6949164497342177419242353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4632776331561451612828235 6949164497342177419242353)
              ·
                refine ⟨5211873373006633064431765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6949164497342177419242353 5211873373006633064431765)
                ·
                  refine ⟨244306564359685924895239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5211873373006633064431765 244306564359685924895239)
                  ·
                    rfl

theorem cell21_1070517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_1070517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070517 prefixEnd_1070517 := by exact prefixLift 1070517
  have htrace : WordTrace (prefixWord ++ tailWord_1070517) baseStart_1070517 baseEnd_1070517 := by
    simpa [prefixWord, tailWord_1070517, baseEnd_1070517] using wordTrace_append hprefix tailTrace_1070517
  have hstable : (prefixWord ++ tailWord_1070517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070517).length < 2 ^ (prefixWord ++ tailWord_1070517).sum := by decide
  have hdescent : baseEnd_1070517 < baseStart_1070517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070655 : List Nat := [1, 1, 2, 2, 3, 3, 2, 4, 3]
def baseStart_1070655 : Nat := 118140960795 + 1070655 * 2 ^ 59
def prefixEnd_1070655 : Nat := 4983230072969 + 3 ^ 40 * 1070655 * 2
def baseEnd_1070655 : Nat := 244338057839828351594957

theorem tailTrace_1070655 : CollatzResearch.WordTrace tailWord_1070655 prefixEnd_1070655 244338057839828351594957 := by
  unfold tailWord_1070655
  simp only [CollatzResearch.WordTrace]
  refine ⟨39049995936207263161413419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26033330624138175440942279 39049995936207263161413419)
  ·
    refine ⟨58574993904310894742120129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39049995936207263161413419 58574993904310894742120129)
    ·
      refine ⟨43931245428233171056590097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58574993904310894742120129 43931245428233171056590097)
      ·
        refine ⟨32948434071174878292442573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43931245428233171056590097 32948434071174878292442573)
        ·
          refine ⟨12355662776690579359665965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32948434071174878292442573 12355662776690579359665965)
          ·
            refine ⟨4633373541258967259874737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12355662776690579359665965 4633373541258967259874737)
            ·
              refine ⟨3475030155944225444906053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4633373541258967259874737 3475030155944225444906053)
              ·
                refine ⟨651568154239542270919885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3475030155944225444906053 651568154239542270919885)
                ·
                  refine ⟨244338057839828351594957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651568154239542270919885 244338057839828351594957)
                  ·
                    rfl

theorem cell21_1070655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 3].length) (baseStart_1070655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070655 prefixEnd_1070655 := by exact prefixLift 1070655
  have htrace : WordTrace (prefixWord ++ tailWord_1070655) baseStart_1070655 baseEnd_1070655 := by
    simpa [prefixWord, tailWord_1070655, baseEnd_1070655] using wordTrace_append hprefix tailTrace_1070655
  have hstable : (prefixWord ++ tailWord_1070655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070655).length < 2 ^ (prefixWord ++ tailWord_1070655).sum := by decide
  have hdescent : baseEnd_1070655 < baseStart_1070655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070697 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 7]
def baseStart_1070697 : Nat := 118140960795 + 1070697 * 2 ^ 59
def prefixEnd_1070697 : Nat := 4983230072969 + 3 ^ 40 * 1070697 * 2
def baseEnd_1070697 : Nat := 244347642812045611894871

theorem tailTrace_1070697 : CollatzResearch.WordTrace tailWord_1070697 prefixEnd_1070697 244347642812045611894871 := by
  unfold tailWord_1070697
  simp only [CollatzResearch.WordTrace]
  refine ⟨39051527802055104334442345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26034351868036736222961563 39051527802055104334442345)
  ·
    refine ⟨29288645851541328250831759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39051527802055104334442345 29288645851541328250831759)
    ·
      refine ⟨43932968777311992376247639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29288645851541328250831759 43932968777311992376247639)
      ·
        refine ⟨65899453165967988564371459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43932968777311992376247639 65899453165967988564371459)
        ·
          refine ⟨98849179748951982846557189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65899453165967988564371459 98849179748951982846557189)
          ·
            refine ⟨18534221202928496783729473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98849179748951982846557189 18534221202928496783729473)
            ·
              refine ⟨13900665902196372587797105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18534221202928496783729473 13900665902196372587797105)
              ·
                refine ⟨10425499426647279440847829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13900665902196372587797105 10425499426647279440847829)
                ·
                  refine ⟨244347642812045611894871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10425499426647279440847829 244347642812045611894871)
                  ·
                    rfl

theorem cell21_1070697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_1070697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070697 prefixEnd_1070697 := by exact prefixLift 1070697
  have htrace : WordTrace (prefixWord ++ tailWord_1070697) baseStart_1070697 baseEnd_1070697 := by
    simpa [prefixWord, tailWord_1070697, baseEnd_1070697] using wordTrace_append hprefix tailTrace_1070697
  have hstable : (prefixWord ++ tailWord_1070697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070697).length < 2 ^ (prefixWord ++ tailWord_1070697).sum := by decide
  have hdescent : baseEnd_1070697 < baseStart_1070697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070807 : List Nat := [1, 1, 3, 2, 1, 3, 4, 3, 3]
def baseStart_1070807 : Nat := 118140960795 + 1070807 * 2 ^ 59
def prefixEnd_1070807 : Nat := 4983230072969 + 3 ^ 40 * 1070807 * 2
def baseEnd_1070807 : Nat := 244372746310709865061313

theorem tailTrace_1070807 : CollatzResearch.WordTrace tailWord_1070807 prefixEnd_1070807 244372746310709865061313 := by
  unfold tailWord_1070807
  simp only [CollatzResearch.WordTrace]
  refine ⟨39055539831656593120946675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26037026554437728747297783 39055539831656593120946675)
  ·
    refine ⟨58583309747484889681420013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39055539831656593120946675 58583309747484889681420013)
    ·
      refine ⟨21968741155306833630532505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58583309747484889681420013 21968741155306833630532505)
      ·
        refine ⟨16476555866480125222899379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21968741155306833630532505 16476555866480125222899379)
        ·
          refine ⟨24714833799720187834349069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16476555866480125222899379 24714833799720187834349069)
          ·
            refine ⟨9268062674895070437880901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24714833799720187834349069 9268062674895070437880901)
            ·
              refine ⟨1737761751542825707102669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9268062674895070437880901 1737761751542825707102669)
              ·
                refine ⟨651660656828559640163501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1737761751542825707102669 651660656828559640163501)
                ·
                  refine ⟨244372746310709865061313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651660656828559640163501 244372746310709865061313)
                  ·
                    rfl

theorem cell21_1070807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 3].length) (baseStart_1070807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070807 prefixEnd_1070807 := by exact prefixLift 1070807
  have htrace : WordTrace (prefixWord ++ tailWord_1070807) baseStart_1070807 baseEnd_1070807 := by
    simpa [prefixWord, tailWord_1070807, baseEnd_1070807] using wordTrace_append hprefix tailTrace_1070807
  have hstable : (prefixWord ++ tailWord_1070807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070807).length < 2 ^ (prefixWord ++ tailWord_1070807).sum := by decide
  have hdescent : baseEnd_1070807 < baseStart_1070807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070852 : List Nat := [2, 3, 2, 2, 1, 2, 4, 5]
def baseStart_1070852 : Nat := 118140960795 + 1070852 * 2 ^ 59
def prefixEnd_1070852 : Nat := 4983230072969 + 3 ^ 40 * 1070852 * 2
def baseEnd_1070852 : Nat := 81461005307933262270407

theorem tailTrace_1070852 : CollatzResearch.WordTrace tailWord_1070852 prefixEnd_1070852 81461005307933262270407 := by
  unfold tailWord_1070852
  simp only [CollatzResearch.WordTrace]
  refine ⟨19528590558246782903167405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26038120744329043870889873 19528590558246782903167405)
  ·
    refine ⟨7323221459342543588687777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19528590558246782903167405 7323221459342543588687777)
    ·
      refine ⟨5492416094506907691515833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7323221459342543588687777 5492416094506907691515833)
      ·
        refine ⟨4119312070880180768636875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5492416094506907691515833 4119312070880180768636875)
        ·
          refine ⟨6178968106320271152955313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4119312070880180768636875 6178968106320271152955313)
          ·
            refine ⟨4634226079740203364716485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6178968106320271152955313 4634226079740203364716485)
            ·
              refine ⟨868917389951288130884341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4634226079740203364716485 868917389951288130884341)
              ·
                refine ⟨81461005307933262270407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 868917389951288130884341 81461005307933262270407)
                ·
                  rfl

theorem cell21_1070852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 5].length) (baseStart_1070852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070852 prefixEnd_1070852 := by exact prefixLift 1070852
  have htrace : WordTrace (prefixWord ++ tailWord_1070852) baseStart_1070852 baseEnd_1070852 := by
    simpa [prefixWord, tailWord_1070852, baseEnd_1070852] using wordTrace_append hprefix tailTrace_1070852
  have hstable : (prefixWord ++ tailWord_1070852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070852).length < 2 ^ (prefixWord ++ tailWord_1070852).sum := by decide
  have hdescent : baseEnd_1070852 < baseStart_1070852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070880 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 6]
def baseStart_1070880 : Nat := 118140960795 + 1070880 * 2 ^ 59
def prefixEnd_1070880 : Nat := 4983230072969 + 3 ^ 40 * 1070880 * 2
def baseEnd_1070880 : Nat := 244389405905277960344497

theorem tailTrace_1070880 : CollatzResearch.WordTrace tailWord_1070880 prefixEnd_1070880 244389405905277960344497 := by
  unfold tailWord_1070880
  simp only [CollatzResearch.WordTrace]
  refine ⟨19529101180196063294177047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26038801573594751058902729 19529101180196063294177047)
  ·
    refine ⟨29293651770294094941265571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19529101180196063294177047 29293651770294094941265571)
    ·
      refine ⟨43940477655441142411898357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29293651770294094941265571 43940477655441142411898357)
      ·
        refine ⟨4119419780197607101115471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43940477655441142411898357 4119419780197607101115471)
        ·
          refine ⟨6179129670296410651673207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4119419780197607101115471 6179129670296410651673207)
          ·
            refine ⟨9268694505444615977509811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6179129670296410651673207 9268694505444615977509811)
            ·
              refine ⟨13903041758166923966264717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9268694505444615977509811 13903041758166923966264717)
              ·
                refine ⟨5213640659312596487349269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13903041758166923966264717 5213640659312596487349269)
                ·
                  refine ⟨244389405905277960344497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5213640659312596487349269 244389405905277960344497)
                  ·
                    rfl

theorem cell21_1070880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_1070880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070880 prefixEnd_1070880 := by exact prefixLift 1070880
  have htrace : WordTrace (prefixWord ++ tailWord_1070880) baseStart_1070880 baseEnd_1070880 := by
    simpa [prefixWord, tailWord_1070880, baseEnd_1070880] using wordTrace_append hprefix tailTrace_1070880
  have hstable : (prefixWord ++ tailWord_1070880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070880).length < 2 ^ (prefixWord ++ tailWord_1070880).sum := by decide
  have hdescent : baseEnd_1070880 < baseStart_1070880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070897 : List Nat := [1, 2, 2, 3, 2, 3, 1, 3, 4]
def baseStart_1070897 : Nat := 118140960795 + 1070897 * 2 ^ 59
def prefixEnd_1070897 : Nat := 4983230072969 + 3 ^ 40 * 1070897 * 2
def baseEnd_1070897 : Nat := 244393285536889708561129

theorem tailTrace_1070897 : CollatzResearch.WordTrace tailWord_1070897 prefixEnd_1070897 244393285536889708561129 := by
  unfold tailWord_1070897
  simp only [CollatzResearch.WordTrace]
  refine ⟨39058822401330538491722945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26039214934220358994481963 39058822401330538491722945)
  ·
    refine ⟨29294116800997903868792209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39058822401330538491722945 29294116800997903868792209)
    ·
      refine ⟨21970587600748427901594157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29294116800997903868792209 21970587600748427901594157)
      ·
        refine ⟨8238970350280660463097809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21970587600748427901594157 8238970350280660463097809)
        ·
          refine ⟨6179227762710495347323357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8238970350280660463097809 6179227762710495347323357)
          ·
            refine ⟨2317210411016435755246259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6179227762710495347323357 2317210411016435755246259)
            ·
              refine ⟨3475815616524653632869389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2317210411016435755246259 3475815616524653632869389)
              ·
                refine ⟨1303430856196745112326021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3475815616524653632869389 1303430856196745112326021)
                ·
                  refine ⟨244393285536889708561129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1303430856196745112326021 244393285536889708561129)
                  ·
                    rfl

theorem cell21_1070897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_1070897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070897 prefixEnd_1070897 := by exact prefixLift 1070897
  have htrace : WordTrace (prefixWord ++ tailWord_1070897) baseStart_1070897 baseEnd_1070897 := by
    simpa [prefixWord, tailWord_1070897, baseEnd_1070897] using wordTrace_append hprefix tailTrace_1070897
  have hstable : (prefixWord ++ tailWord_1070897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070897).length < 2 ^ (prefixWord ++ tailWord_1070897).sum := by decide
  have hdescent : baseEnd_1070897 < baseStart_1070897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070970 : List Nat := [3, 1, 1, 1, 1, 1, 4, 9]
def baseStart_1070970 : Nat := 118140960795 + 1070970 * 2 ^ 59
def prefixEnd_1070970 : Nat := 4983230072969 + 3 ^ 40 * 1070970 * 2
def baseEnd_1070970 : Nat := 81469981710485934614771

theorem tailTrace_1070970 : CollatzResearch.WordTrace tailWord_1070970 prefixEnd_1070970 81469981710485934614771 := by
  unfold tailWord_1070970
  simp only [CollatzResearch.WordTrace]
  refine ⟨9765371232516517989782591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26040989953377381306086909 9765371232516517989782591)
  ·
    refine ⟨14648056848774776984673887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9765371232516517989782591 14648056848774776984673887)
    ·
      refine ⟨21972085273162165477010831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14648056848774776984673887 21972085273162165477010831)
      ·
        refine ⟨32958127909743248215516247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21972085273162165477010831 32958127909743248215516247)
        ·
          refine ⟨49437191864614872323274371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32958127909743248215516247 49437191864614872323274371)
          ·
            refine ⟨74155787796922308484911557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49437191864614872323274371 74155787796922308484911557)
            ·
              refine ⟨13904210211922932840920917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74155787796922308484911557 13904210211922932840920917)
              ·
                refine ⟨81469981710485934614771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13904210211922932840920917 81469981710485934614771)
                ·
                  rfl

theorem cell21_1070970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_1070970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070970 prefixEnd_1070970 := by exact prefixLift 1070970
  have htrace : WordTrace (prefixWord ++ tailWord_1070970) baseStart_1070970 baseEnd_1070970 := by
    simpa [prefixWord, tailWord_1070970, baseEnd_1070970] using wordTrace_append hprefix tailTrace_1070970
  have hstable : (prefixWord ++ tailWord_1070970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070970).length < 2 ^ (prefixWord ++ tailWord_1070970).sum := by decide
  have hdescent : baseEnd_1070970 < baseStart_1070970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1070990 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_1070990 : Nat := 118140960795 + 1070990 * 2 ^ 59
def prefixEnd_1070990 : Nat := 4983230072969 + 3 ^ 40 * 1070990 * 2
def baseEnd_1070990 : Nat := 244414509403942213510939

theorem tailTrace_1070990 : CollatzResearch.WordTrace tailWord_1070990 prefixEnd_1070990 244414509403942213510939 := by
  unfold tailWord_1070990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4882776798749201921857303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26041476259995743583238949 4882776798749201921857303)
  ·
    refine ⟨7324165198123802882785955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4882776798749201921857303 7324165198123802882785955)
    ·
      refine ⟨10986247797185704324178933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7324165198123802882785955 10986247797185704324178933)
      ·
        refine ⟨1029960730986159780391775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10986247797185704324178933 1029960730986159780391775)
        ·
          refine ⟨1544941096479239670587663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029960730986159780391775 1544941096479239670587663)
          ·
            refine ⟨2317411644718859505881495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1544941096479239670587663 2317411644718859505881495)
            ·
              refine ⟨3476117467078289258822243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2317411644718859505881495 3476117467078289258822243)
              ·
                refine ⟨5214176200617433888233365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3476117467078289258822243 5214176200617433888233365)
                ·
                  refine ⟨244414509403942213510939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5214176200617433888233365 244414509403942213510939)
                  ·
                    rfl

theorem cell21_1070990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_1070990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1070990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1070990 prefixEnd_1070990 := by exact prefixLift 1070990
  have htrace : WordTrace (prefixWord ++ tailWord_1070990) baseStart_1070990 baseEnd_1070990 := by
    simpa [prefixWord, tailWord_1070990, baseEnd_1070990] using wordTrace_append hprefix tailTrace_1070990
  have hstable : (prefixWord ++ tailWord_1070990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1070990).length < 2 ^ (prefixWord ++ tailWord_1070990).sum := by decide
  have hdescent : baseEnd_1070990 < baseStart_1070990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1070990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071001 : List Nat := [1, 2, 1, 2, 1, 3, 3, 3, 5]
def baseStart_1071001 : Nat := 118140960795 + 1071001 * 2 ^ 59
def prefixEnd_1071001 : Nat := 4983230072969 + 3 ^ 40 * 1071001 * 2
def baseEnd_1071001 : Nat := 244417019753808638827583

theorem tailTrace_1071001 : CollatzResearch.WordTrace tailWord_1071001 prefixEnd_1071001 244417019753808638827583 := by
  unfold tailWord_1071001
  simp only [CollatzResearch.WordTrace]
  refine ⟨39062615592953764253508857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26041743728635842835672571 39062615592953764253508857)
  ·
    refine ⟨29296961694715323190131643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39062615592953764253508857 29296961694715323190131643)
    ·
      refine ⟨43945442542072984785197465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29296961694715323190131643 43945442542072984785197465)
      ·
        refine ⟨32959081906554738588898099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43945442542072984785197465 32959081906554738588898099)
        ·
          refine ⟨49438622859832107883347149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32959081906554738588898099 49438622859832107883347149)
          ·
            refine ⟨18539483572437040456255181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49438622859832107883347149 18539483572437040456255181)
            ·
              refine ⟨6952306339663890171095693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18539483572437040456255181 6952306339663890171095693)
              ·
                refine ⟨2607114877373958814160885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6952306339663890171095693 2607114877373958814160885)
                ·
                  refine ⟨244417019753808638827583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2607114877373958814160885 244417019753808638827583)
                  ·
                    rfl

theorem cell21_1071001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_1071001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071001 prefixEnd_1071001 := by exact prefixLift 1071001
  have htrace : WordTrace (prefixWord ++ tailWord_1071001) baseStart_1071001 baseEnd_1071001 := by
    simpa [prefixWord, tailWord_1071001, baseEnd_1071001] using wordTrace_append hprefix tailTrace_1071001
  have hstable : (prefixWord ++ tailWord_1071001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071001).length < 2 ^ (prefixWord ++ tailWord_1071001).sum := by decide
  have hdescent : baseEnd_1071001 < baseStart_1071001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071052 : List Nat := [2, 2, 1, 4, 1, 3, 3, 2, 3]
def baseStart_1071052 : Nat := 118140960795 + 1071052 * 2 ^ 59
def prefixEnd_1071052 : Nat := 4983230072969 + 3 ^ 40 * 1071052 * 2
def baseEnd_1071052 : Nat := 244428658648643883477479

theorem tailTrace_1071052 : CollatzResearch.WordTrace tailWord_1071052 prefixEnd_1071052 244428658648643883477479 := by
  unfold tailWord_1071052
  simp only [CollatzResearch.WordTrace]
  refine ⟨19532237857884499981807705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26042983810512666642410273 19532237857884499981807705)
  ·
    refine ⟨14649178393413374986355779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19532237857884499981807705 14649178393413374986355779)
    ·
      refine ⟨21973767590120062479533669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14649178393413374986355779 21973767590120062479533669)
      ·
        refine ⟨4120081423147511714912563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21973767590120062479533669 4120081423147511714912563)
        ·
          refine ⟨6180122134721267572368845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4120081423147511714912563 6180122134721267572368845)
          ·
            refine ⟨2317545800520475339638317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6180122134721267572368845 2317545800520475339638317)
            ·
              refine ⟨869079675195178252364369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2317545800520475339638317 869079675195178252364369)
              ·
                refine ⟨651809756396383689273277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 869079675195178252364369 651809756396383689273277)
                ·
                  refine ⟨244428658648643883477479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651809756396383689273277 244428658648643883477479)
                  ·
                    rfl

theorem cell21_1071052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_1071052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071052 prefixEnd_1071052 := by exact prefixLift 1071052
  have htrace : WordTrace (prefixWord ++ tailWord_1071052) baseStart_1071052 baseEnd_1071052 := by
    simpa [prefixWord, tailWord_1071052, baseEnd_1071052] using wordTrace_append hprefix tailTrace_1071052
  have hstable : (prefixWord ++ tailWord_1071052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071052).length < 2 ^ (prefixWord ++ tailWord_1071052).sum := by decide
  have hdescent : baseEnd_1071052 < baseStart_1071052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071091 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 8]
def baseStart_1071091 : Nat := 118140960795 + 1071091 * 2 ^ 59
def prefixEnd_1071091 : Nat := 4983230072969 + 3 ^ 40 * 1071091 * 2
def baseEnd_1071091 : Nat := 244437558979988482327399

theorem tailTrace_1071091 : CollatzResearch.WordTrace tailWord_1071091 prefixEnd_1071091 244437558979988482327399 := by
  unfold tailWord_1071091
  simp only [CollatzResearch.WordTrace]
  refine ⟨39065898162627709624285127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26043932108418473082856751 39065898162627709624285127)
  ·
    refine ⟨58598847243941564436427691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39065898162627709624285127 58598847243941564436427691)
    ·
      refine ⟨87898270865912346654641537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58598847243941564436427691 87898270865912346654641537)
      ·
        refine ⟨65923703149434259990981153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87898270865912346654641537 65923703149434259990981153)
        ·
          refine ⟨49442777362075694993235865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65923703149434259990981153 49442777362075694993235865)
          ·
            refine ⟨37082083021556771244926899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49442777362075694993235865 37082083021556771244926899)
            ·
              refine ⟨55623124532335156867390349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37082083021556771244926899 55623124532335156867390349)
              ·
                refine ⟨20858671699625683825271381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55623124532335156867390349 20858671699625683825271381)
                ·
                  refine ⟨244437558979988482327399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20858671699625683825271381 244437558979988482327399)
                  ·
                    rfl

theorem cell21_1071091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 8].length) (baseStart_1071091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071091 prefixEnd_1071091 := by exact prefixLift 1071091
  have htrace : WordTrace (prefixWord ++ tailWord_1071091) baseStart_1071091 baseEnd_1071091 := by
    simpa [prefixWord, tailWord_1071091, baseEnd_1071091] using wordTrace_append hprefix tailTrace_1071091
  have hstable : (prefixWord ++ tailWord_1071091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071091).length < 2 ^ (prefixWord ++ tailWord_1071091).sum := by decide
  have hdescent : baseEnd_1071091 < baseStart_1071091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071111 : List Nat := [1, 1, 4, 3, 1, 3, 1, 4, 3]
def baseStart_1071111 : Nat := 118140960795 + 1071111 * 2 ^ 59
def prefixEnd_1071111 : Nat := 4983230072969 + 3 ^ 40 * 1071111 * 2
def baseEnd_1071111 : Nat := 244442123252472891994025

theorem tailTrace_1071111 : CollatzResearch.WordTrace tailWord_1071111 prefixEnd_1071111 244442123252472891994025 := by
  unfold tailWord_1071111
  simp only [CollatzResearch.WordTrace]
  refine ⟨39066627622555253040013187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26044418415036835360008791 39066627622555253040013187)
  ·
    refine ⟨58599941433832879560019781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39066627622555253040013187 58599941433832879560019781)
    ·
      refine ⟨10987489018843664917503709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58599941433832879560019781 10987489018843664917503709)
      ·
        refine ⟨4120308382066374344063891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10987489018843664917503709 4120308382066374344063891)
        ·
          refine ⟨6180462573099561516095837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4120308382066374344063891 6180462573099561516095837)
          ·
            refine ⟨2317673464912335568535939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6180462573099561516095837 2317673464912335568535939)
            ·
              refine ⟨3476510197368503352803909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2317673464912335568535939 3476510197368503352803909)
              ·
                refine ⟨651845662006594378650733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3476510197368503352803909 651845662006594378650733)
                ·
                  refine ⟨244442123252472891994025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651845662006594378650733 244442123252472891994025)
                  ·
                    rfl

theorem cell21_1071111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 3].length) (baseStart_1071111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071111 prefixEnd_1071111 := by exact prefixLift 1071111
  have htrace : WordTrace (prefixWord ++ tailWord_1071111) baseStart_1071111 baseEnd_1071111 := by
    simpa [prefixWord, tailWord_1071111, baseEnd_1071111] using wordTrace_append hprefix tailTrace_1071111
  have hstable : (prefixWord ++ tailWord_1071111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071111).length < 2 ^ (prefixWord ++ tailWord_1071111).sum := by decide
  have hdescent : baseEnd_1071111 < baseStart_1071111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071139 : List Nat := [1, 1, 1, 4, 3, 1, 5, 5]
def baseStart_1071139 : Nat := 118140960795 + 1071139 * 2 ^ 59
def prefixEnd_1071139 : Nat := 4983230072969 + 3 ^ 40 * 1071139 * 2
def baseEnd_1071139 : Nat := 81482837744650355175767

theorem tailTrace_1071139 : CollatzResearch.WordTrace tailWord_1071139 prefixEnd_1071139 81482837744650355175767 := by
  unfold tailWord_1071139
  simp only [CollatzResearch.WordTrace]
  refine ⟨39067648866453813822032471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26045099244302542548021647 39067648866453813822032471)
  ·
    refine ⟨58601473299680720733048707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39067648866453813822032471 58601473299680720733048707)
    ·
      refine ⟨87902209949521081099573061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58601473299680720733048707 87902209949521081099573061)
      ·
        refine ⟨16481664365535202706169949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87902209949521081099573061 16481664365535202706169949)
        ·
          refine ⟨6180624137075701014813731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16481664365535202706169949 6180624137075701014813731)
          ·
            refine ⟨9270936205613551522220597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6180624137075701014813731 9270936205613551522220597)
            ·
              refine ⟨869150269276270455208181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9270936205613551522220597 869150269276270455208181)
              ·
                refine ⟨81482837744650355175767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 869150269276270455208181 81482837744650355175767)
                ·
                  rfl

theorem cell21_1071139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 5].length) (baseStart_1071139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071139 prefixEnd_1071139 := by exact prefixLift 1071139
  have htrace : WordTrace (prefixWord ++ tailWord_1071139) baseStart_1071139 baseEnd_1071139 := by
    simpa [prefixWord, tailWord_1071139, baseEnd_1071139] using wordTrace_append hprefix tailTrace_1071139
  have hstable : (prefixWord ++ tailWord_1071139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071139).length < 2 ^ (prefixWord ++ tailWord_1071139).sum := by decide
  have hdescent : baseEnd_1071139 < baseStart_1071139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071156 : List Nat := [2, 5, 1, 2, 2, 1, 8]
def baseStart_1071156 : Nat := 118140960795 + 1071156 * 2 ^ 59
def prefixEnd_1071156 : Nat := 4983230072969 + 3 ^ 40 * 1071156 * 2
def baseEnd_1071156 : Nat := 27161376985062534860437

theorem tailTrace_1071156 : CollatzResearch.WordTrace tailWord_1071156 prefixEnd_1071156 27161376985062534860437 := by
  unfold tailWord_1071156
  simp only [CollatzResearch.WordTrace]
  refine ⟨19534134453696112862700661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26045512604928150483600881 19534134453696112862700661)
  ·
    refine ⟨1831325105034010580878187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19534134453696112862700661 1831325105034010580878187)
    ·
      refine ⟨2746987657551015871317281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1831325105034010580878187 2746987657551015871317281)
      ·
        refine ⟨2060240743163261903487961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2746987657551015871317281 2060240743163261903487961)
        ·
          refine ⟨1545180557372446427615971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2060240743163261903487961 1545180557372446427615971)
          ·
            refine ⟨2317770836058669641423957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1545180557372446427615971 2317770836058669641423957)
            ·
              refine ⟨27161376985062534860437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2317770836058669641423957 27161376985062534860437)
              ·
                rfl

theorem cell21_1071156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 8].length) (baseStart_1071156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071156 prefixEnd_1071156 := by exact prefixLift 1071156
  have htrace : WordTrace (prefixWord ++ tailWord_1071156) baseStart_1071156 baseEnd_1071156 := by
    simpa [prefixWord, tailWord_1071156, baseEnd_1071156] using wordTrace_append hprefix tailTrace_1071156
  have hstable : (prefixWord ++ tailWord_1071156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071156).length < 2 ^ (prefixWord ++ tailWord_1071156).sum := by decide
  have hdescent : baseEnd_1071156 < baseStart_1071156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071190 : List Nat := [5, 2, 2, 1, 1, 3, 2, 5]
def baseStart_1071190 : Nat := 118140960795 + 1071190 * 2 ^ 59
def prefixEnd_1071190 : Nat := 4983230072969 + 3 ^ 40 * 1071190 * 2
def baseEnd_1071190 : Nat := 81486717376262103392399

theorem tailTrace_1071190 : CollatzResearch.WordTrace tailWord_1071190 prefixEnd_1071190 81486717376262103392399 := by
  unfold tailWord_1071190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2441844311829315595758689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26046339326179366354759349 2441844311829315595758689)
  ·
    refine ⟨1831383233871986696819017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2441844311829315595758689 1831383233871986696819017)
    ·
      refine ⟨1373537425403990022614263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1831383233871986696819017 1373537425403990022614263)
      ·
        refine ⟨2060306138105985033921395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1373537425403990022614263 2060306138105985033921395)
        ·
          refine ⟨3090459207158977550882093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2060306138105985033921395 3090459207158977550882093)
          ·
            refine ⟨1158922202684616581580785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3090459207158977550882093 1158922202684616581580785)
            ·
              refine ⟨869191652013462436185589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1158922202684616581580785 869191652013462436185589)
              ·
                refine ⟨81486717376262103392399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 869191652013462436185589 81486717376262103392399)
                ·
                  rfl

theorem cell21_1071190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_1071190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071190 prefixEnd_1071190 := by exact prefixLift 1071190
  have htrace : WordTrace (prefixWord ++ tailWord_1071190) baseStart_1071190 baseEnd_1071190 := by
    simpa [prefixWord, tailWord_1071190, baseEnd_1071190] using wordTrace_append hprefix tailTrace_1071190
  have hstable : (prefixWord ++ tailWord_1071190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071190).length < 2 ^ (prefixWord ++ tailWord_1071190).sum := by decide
  have hdescent : baseEnd_1071190 < baseStart_1071190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071277 : List Nat := [1, 5, 2, 1, 2, 1, 1, 4, 4]
def baseStart_1071277 : Nat := 118140960795 + 1071277 * 2 ^ 59
def prefixEnd_1071277 : Nat := 4983230072969 + 3 ^ 40 * 1071277 * 2
def baseEnd_1071277 : Nat := 244480006714093492227019

theorem tailTrace_1071277 : CollatzResearch.WordTrace tailWord_1071277 prefixEnd_1071277 244480006714093492227019 := by
  unfold tailWord_1071277
  simp only [CollatzResearch.WordTrace]
  refine ⟨39072682139953863390556085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26048454759969242260370723 39072682139953863390556085)
  ·
    refine ⟨3663063950620674692864633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39072682139953863390556085 3663063950620674692864633)
    ·
      refine ⟨2747297962965506019648475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3663063950620674692864633 2747297962965506019648475)
      ·
        refine ⟨4120946944448259029472713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2747297962965506019648475 4120946944448259029472713)
        ·
          refine ⟨3090710208336194272104535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4120946944448259029472713 3090710208336194272104535)
          ·
            refine ⟨4636065312504291408156803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3090710208336194272104535 4636065312504291408156803)
            ·
              refine ⟨6954097968756437112235205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4636065312504291408156803 6954097968756437112235205)
              ·
                refine ⟨1303893369141831958544101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6954097968756437112235205 1303893369141831958544101)
                ·
                  refine ⟨244480006714093492227019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1303893369141831958544101 244480006714093492227019)
                  ·
                    rfl

theorem cell21_1071277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_1071277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071277 prefixEnd_1071277 := by exact prefixLift 1071277
  have htrace : WordTrace (prefixWord ++ tailWord_1071277) baseStart_1071277 baseEnd_1071277 := by
    simpa [prefixWord, tailWord_1071277, baseEnd_1071277] using wordTrace_append hprefix tailTrace_1071277
  have hstable : (prefixWord ++ tailWord_1071277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071277).length < 2 ^ (prefixWord ++ tailWord_1071277).sum := by decide
  have hdescent : baseEnd_1071277 < baseStart_1071277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071319 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 6]
def baseStart_1071319 : Nat := 118140960795 + 1071319 * 2 ^ 59
def prefixEnd_1071319 : Nat := 4983230072969 + 3 ^ 40 * 1071319 * 2
def baseEnd_1071319 : Nat := 244489591686310752526933

theorem tailTrace_1071319 : CollatzResearch.WordTrace tailWord_1071319 prefixEnd_1071319 244489591686310752526933 := by
  unfold tailWord_1071319
  simp only [CollatzResearch.WordTrace]
  refine ⟨39074214005801704563585011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26049476003867803042390007 39074214005801704563585011)
  ·
    refine ⟨58611321008702556845377517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39074214005801704563585011 58611321008702556845377517)
    ·
      refine ⟨21979245378263458817016569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58611321008702556845377517 21979245378263458817016569)
      ·
        refine ⟨16484434033697594112762427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21979245378263458817016569 16484434033697594112762427)
        ·
          refine ⟨24726651050546391169143641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16484434033697594112762427 24726651050546391169143641)
          ·
            refine ⟨18544988287909793376857731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24726651050546391169143641 18544988287909793376857731)
            ·
              refine ⟨27817482431864690065286597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18544988287909793376857731 27817482431864690065286597)
              ·
                refine ⟨5215777955974629387241237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27817482431864690065286597 5215777955974629387241237)
                ·
                  refine ⟨244489591686310752526933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5215777955974629387241237 244489591686310752526933)
                  ·
                    rfl

theorem cell21_1071319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 6].length) (baseStart_1071319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071319 prefixEnd_1071319 := by exact prefixLift 1071319
  have htrace : WordTrace (prefixWord ++ tailWord_1071319) baseStart_1071319 baseEnd_1071319 := by
    simpa [prefixWord, tailWord_1071319, baseEnd_1071319] using wordTrace_append hprefix tailTrace_1071319
  have hstable : (prefixWord ++ tailWord_1071319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071319).length < 2 ^ (prefixWord ++ tailWord_1071319).sum := by decide
  have hdescent : baseEnd_1071319 < baseStart_1071319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071322 : List Nat := [3, 1, 1, 2, 2, 1, 3, 5, 3]
def baseStart_1071322 : Nat := 118140960795 + 1071322 * 2 ^ 59
def prefixEnd_1071322 : Nat := 4983230072969 + 3 ^ 40 * 1071322 * 2
def baseEnd_1071322 : Nat := 244490276327183413976927

theorem tailTrace_1071322 : CollatzResearch.WordTrace tailWord_1071322 prefixEnd_1071322 244490276327183413976927 := by
  unfold tailWord_1071322
  simp only [CollatzResearch.WordTrace]
  refine ⟨9768580856197709018986055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26049548949860557383962813 9768580856197709018986055)
  ·
    refine ⟨14652871284296563528479083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9768580856197709018986055 14652871284296563528479083)
    ·
      refine ⟨21979306926444845292718625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14652871284296563528479083 21979306926444845292718625)
      ·
        refine ⟨16484480194833633969538969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21979306926444845292718625 16484480194833633969538969)
        ·
          refine ⟨12363360146125225477154227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16484480194833633969538969 12363360146125225477154227)
          ·
            refine ⟨18545040219187838215731341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12363360146125225477154227 18545040219187838215731341)
            ·
              refine ⟨6954390082195439330899253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18545040219187838215731341 6954390082195439330899253)
              ·
                refine ⟨651974070205822437271805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6954390082195439330899253 651974070205822437271805)
                ·
                  refine ⟨244490276327183413976927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 651974070205822437271805 244490276327183413976927)
                  ·
                    rfl

theorem cell21_1071322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_1071322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071322 prefixEnd_1071322 := by exact prefixLift 1071322
  have htrace : WordTrace (prefixWord ++ tailWord_1071322) baseStart_1071322 baseEnd_1071322 := by
    simpa [prefixWord, tailWord_1071322, baseEnd_1071322] using wordTrace_append hprefix tailTrace_1071322
  have hstable : (prefixWord ++ tailWord_1071322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071322).length < 2 ^ (prefixWord ++ tailWord_1071322).sum := by decide
  have hdescent : baseEnd_1071322 < baseStart_1071322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071336 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 6]
def baseStart_1071336 : Nat := 118140960795 + 1071336 * 2 ^ 59
def prefixEnd_1071336 : Nat := 4983230072969 + 3 ^ 40 * 1071336 * 2
def baseEnd_1071336 : Nat := 244493471317922500743565

theorem tailTrace_1071336 : CollatzResearch.WordTrace tailWord_1071336 prefixEnd_1071336 244493471317922500743565 := by
  unfold tailWord_1071336
  simp only [CollatzResearch.WordTrace]
  refine ⟨19537417023370058233476931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26049889364493410977969241 19537417023370058233476931)
  ·
    refine ⟨29306125535055087350215397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19537417023370058233476931 29306125535055087350215397)
    ·
      refine ⟨5494898537822828878165387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29306125535055087350215397 5494898537822828878165387)
      ·
        refine ⟨8242347806734243317248081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5494898537822828878165387 8242347806734243317248081)
        ·
          refine ⟨6181760855050682487936061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8242347806734243317248081 6181760855050682487936061)
          ·
            refine ⟨2318160320644005932976023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6181760855050682487936061 2318160320644005932976023)
            ·
              refine ⟨3477240480966008899464035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2318160320644005932976023 3477240480966008899464035)
              ·
                refine ⟨5215860721449013349196053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477240480966008899464035 5215860721449013349196053)
                ·
                  refine ⟨244493471317922500743565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5215860721449013349196053 244493471317922500743565)
                  ·
                    rfl

theorem cell21_1071336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_1071336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071336 prefixEnd_1071336 := by exact prefixLift 1071336
  have htrace : WordTrace (prefixWord ++ tailWord_1071336) baseStart_1071336 baseEnd_1071336 := by
    simpa [prefixWord, tailWord_1071336, baseEnd_1071336] using wordTrace_append hprefix tailTrace_1071336
  have hstable : (prefixWord ++ tailWord_1071336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071336).length < 2 ^ (prefixWord ++ tailWord_1071336).sum := by decide
  have hdescent : baseEnd_1071336 < baseStart_1071336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071395 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 6]
def baseStart_1071395 : Nat := 118140960795 + 1071395 * 2 ^ 59
def prefixEnd_1071395 : Nat := 4983230072969 + 3 ^ 40 * 1071395 * 2
def baseEnd_1071395 : Nat := 244506935921751509260111

theorem tailTrace_1071395 : CollatzResearch.WordTrace tailWord_1071395 prefixEnd_1071395 244506935921751509260111 := by
  unfold tailWord_1071395
  simp only [CollatzResearch.WordTrace]
  refine ⟨39076985953526369543351639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26051323969017579695567759 39076985953526369543351639)
  ·
    refine ⟨58615478930289554315027459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39076985953526369543351639 58615478930289554315027459)
    ·
      refine ⟨87923218395434331472541189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58615478930289554315027459 87923218395434331472541189)
      ·
        refine ⟨16485603449143937151101473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87923218395434331472541189 16485603449143937151101473)
        ·
          refine ⟨12364202586857952863326105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16485603449143937151101473 12364202586857952863326105)
          ·
            refine ⟨9273151940143464647494579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12364202586857952863326105 9273151940143464647494579)
            ·
              refine ⟨13909727910215196971241869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9273151940143464647494579 13909727910215196971241869)
              ·
                refine ⟨5216147966330698864215701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13909727910215196971241869 5216147966330698864215701)
                ·
                  refine ⟨244506935921751509260111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5216147966330698864215701 244506935921751509260111)
                  ·
                    rfl

theorem cell21_1071395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 6].length) (baseStart_1071395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071395 prefixEnd_1071395 := by exact prefixLift 1071395
  have htrace : WordTrace (prefixWord ++ tailWord_1071395) baseStart_1071395 baseEnd_1071395 := by
    simpa [prefixWord, tailWord_1071395, baseEnd_1071395] using wordTrace_append hprefix tailTrace_1071395
  have hstable : (prefixWord ++ tailWord_1071395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071395).length < 2 ^ (prefixWord ++ tailWord_1071395).sum := by decide
  have hdescent : baseEnd_1071395 < baseStart_1071395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071491 : List Nat := [1, 1, 1, 3, 6, 1, 2, 3, 3]
def baseStart_1071491 : Nat := 118140960795 + 1071491 * 2 ^ 59
def prefixEnd_1071491 : Nat := 4983230072969 + 3 ^ 40 * 1071491 * 2
def baseEnd_1071491 : Nat := 244528844429676675659915

theorem tailTrace_1071491 : CollatzResearch.WordTrace tailWord_1071491 prefixEnd_1071491 244528844429676675659915 := by
  unfold tailWord_1071491
  simp only [CollatzResearch.WordTrace]
  refine ⟨39080487361178577938846327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26053658240785718625897551 39080487361178577938846327)
  ·
    refine ⟨58620731041767866908269491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39080487361178577938846327 58620731041767866908269491)
    ·
      refine ⟨87931096562651800362404237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58620731041767866908269491 87931096562651800362404237)
      ·
        refine ⟨32974161210994425135901589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87931096562651800362404237 32974161210994425135901589)
        ·
          refine ⟨1545663806765363678245387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32974161210994425135901589 1545663806765363678245387)
          ·
            refine ⟨2318495710148045517368081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1545663806765363678245387 2318495710148045517368081)
            ·
              refine ⟨1738871782611034138026061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2318495710148045517368081 1738871782611034138026061)
              ·
                refine ⟨652076918479137801759773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1738871782611034138026061 652076918479137801759773)
                ·
                  refine ⟨244528844429676675659915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 652076918479137801759773 244528844429676675659915)
                  ·
                    rfl

theorem cell21_1071491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 3].length) (baseStart_1071491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071491 prefixEnd_1071491 := by exact prefixLift 1071491
  have htrace : WordTrace (prefixWord ++ tailWord_1071491) baseStart_1071491 baseEnd_1071491 := by
    simpa [prefixWord, tailWord_1071491, baseEnd_1071491] using wordTrace_append hprefix tailTrace_1071491
  have hstable : (prefixWord ++ tailWord_1071491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071491).length < 2 ^ (prefixWord ++ tailWord_1071491).sum := by decide
  have hdescent : baseEnd_1071491 < baseStart_1071491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071553 : List Nat := [1, 2, 7, 1, 1, 2, 7]
def baseStart_1071553 : Nat := 118140960795 + 1071553 * 2 ^ 59
def prefixEnd_1071553 : Nat := 4983230072969 + 3 ^ 40 * 1071553 * 2
def baseEnd_1071553 : Nat := 27171443741597593958495

theorem tailTrace_1071553 : CollatzResearch.WordTrace tailWord_1071553 prefixEnd_1071553 27171443741597593958495 := by
  unfold tailWord_1071553
  simp only [CollatzResearch.WordTrace]
  refine ⟨39082748686953962527603313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26055165791302641685068875 39082748686953962527603313)
  ·
    refine ⟨29312061515215471895702485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39082748686953962527603313 29312061515215471895702485)
    ·
      refine ⟨687001441762862622555527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 29312061515215471895702485 687001441762862622555527)
      ·
        refine ⟨1030502162644293933833291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687001441762862622555527 1030502162644293933833291)
        ·
          refine ⟨1545753243966440900749937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1030502162644293933833291 1545753243966440900749937)
          ·
            refine ⟨1159314932974830675562453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1545753243966440900749937 1159314932974830675562453)
            ·
              refine ⟨27171443741597593958495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1159314932974830675562453 27171443741597593958495)
              ·
                rfl

theorem cell21_1071553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 7].length) (baseStart_1071553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071553 prefixEnd_1071553 := by exact prefixLift 1071553
  have htrace : WordTrace (prefixWord ++ tailWord_1071553) baseStart_1071553 baseEnd_1071553 := by
    simpa [prefixWord, tailWord_1071553, baseEnd_1071553] using wordTrace_append hprefix tailTrace_1071553
  have hstable : (prefixWord ++ tailWord_1071553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071553).length < 2 ^ (prefixWord ++ tailWord_1071553).sum := by decide
  have hdescent : baseEnd_1071553 < baseStart_1071553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071561 : List Nat := [1, 2, 1, 1, 2, 1, 13]
def baseStart_1071561 : Nat := 118140960795 + 1071561 * 2 ^ 59
def prefixEnd_1071561 : Nat := 4983230072969 + 3 ^ 40 * 1071561 * 2
def baseEnd_1071561 : Nat := 27171646598152456610345

theorem tailTrace_1071561 : CollatzResearch.WordTrace tailWord_1071561 prefixEnd_1071561 27171646598152456610345 := by
  unfold tailWord_1071561
  simp only [CollatzResearch.WordTrace]
  refine ⟨39083040470924979893894537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26055360313949986595929691 39083040470924979893894537)
  ·
    refine ⟨29312280353193734920420903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39083040470924979893894537 29312280353193734920420903)
    ·
      refine ⟨43968420529790602380631355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29312280353193734920420903 43968420529790602380631355)
      ·
        refine ⟨65952630794685903570947033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43968420529790602380631355 65952630794685903570947033)
        ·
          refine ⟨49464473096014427678210275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65952630794685903570947033 49464473096014427678210275)
          ·
            refine ⟨74196709644021641517315413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49464473096014427678210275 74196709644021641517315413)
            ·
              refine ⟨27171646598152456610345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 74196709644021641517315413 27171646598152456610345)
              ·
                rfl

theorem cell21_1071561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 13].length) (baseStart_1071561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071561 prefixEnd_1071561 := by exact prefixLift 1071561
  have htrace : WordTrace (prefixWord ++ tailWord_1071561) baseStart_1071561 baseEnd_1071561 := by
    simpa [prefixWord, tailWord_1071561, baseEnd_1071561] using wordTrace_append hprefix tailTrace_1071561
  have hstable : (prefixWord ++ tailWord_1071561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071561).length < 2 ^ (prefixWord ++ tailWord_1071561).sum := by decide
  have hdescent : baseEnd_1071561 < baseStart_1071561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071578 : List Nat := [3, 1, 1, 2, 3, 1, 4, 6]
def baseStart_1071578 : Nat := 118140960795 + 1071578 * 2 ^ 59
def prefixEnd_1071578 : Nat := 4983230072969 + 3 ^ 40 * 1071578 * 2
def baseEnd_1071578 : Nat := 81516233004994619236579

theorem tailTrace_1071578 : CollatzResearch.WordTrace tailWord_1071578 prefixEnd_1071578 81516233004994619236579 := by
  unfold tailWord_1071578
  simp only [CollatzResearch.WordTrace]
  refine ⟨9770915127965847949315847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26055773674575594531508925 9770915127965847949315847)
  ·
    refine ⟨14656372691948771923973771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9770915127965847949315847 14656372691948771923973771)
    ·
      refine ⟨21984559037923157885960657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14656372691948771923973771 21984559037923157885960657)
      ·
        refine ⟨16488419278442368414470493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21984559037923157885960657 16488419278442368414470493)
        ·
          refine ⟨6183157229415888155426435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16488419278442368414470493 6183157229415888155426435)
          ·
            refine ⟨9274735844123832233139653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6183157229415888155426435 9274735844123832233139653)
            ·
              refine ⟨1739012970773218543713685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9274735844123832233139653 1739012970773218543713685)
              ·
                refine ⟨81516233004994619236579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1739012970773218543713685 81516233004994619236579)
                ·
                  rfl

theorem cell21_1071578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_1071578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071578 prefixEnd_1071578 := by exact prefixLift 1071578
  have htrace : WordTrace (prefixWord ++ tailWord_1071578) baseStart_1071578 baseEnd_1071578 := by
    simpa [prefixWord, tailWord_1071578, baseEnd_1071578] using wordTrace_append hprefix tailTrace_1071578
  have hstable : (prefixWord ++ tailWord_1071578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071578).length < 2 ^ (prefixWord ++ tailWord_1071578).sum := by decide
  have hdescent : baseEnd_1071578 < baseStart_1071578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071618 : List Nat := [3, 4, 1, 2, 3, 1, 2, 2, 3]
def baseStart_1071618 : Nat := 118140960795 + 1071618 * 2 ^ 59
def prefixEnd_1071618 : Nat := 4983230072969 + 3 ^ 40 * 1071618 * 2
def baseEnd_1071618 : Nat := 244557827559952677042989

theorem tailTrace_1071618 : CollatzResearch.WordTrace tailWord_1071618 prefixEnd_1071618 244557827559952677042989 := by
  unfold tailWord_1071618
  simp only [CollatzResearch.WordTrace]
  refine ⟨9771279857929619657179877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26056746287812319085813005 9771279857929619657179877)
  ·
    refine ⟨1832114973361803685721227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9771279857929619657179877 1832114973361803685721227)
    ·
      refine ⟨2748172460042705528581841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1832114973361803685721227 2748172460042705528581841)
      ·
        refine ⟨2061129345032029146436381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2748172460042705528581841 2061129345032029146436381)
        ·
          refine ⟨772923504387010929913643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2061129345032029146436381 772923504387010929913643)
          ·
            refine ⟨1159385256580516394870465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772923504387010929913643 1159385256580516394870465)
            ·
              refine ⟨869538942435387296152849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1159385256580516394870465 869538942435387296152849)
              ·
                refine ⟨652154206826540472114637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 869538942435387296152849 652154206826540472114637)
                ·
                  refine ⟨244557827559952677042989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 652154206826540472114637 244557827559952677042989)
                  ·
                    rfl

theorem cell21_1071618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_1071618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071618 prefixEnd_1071618 := by exact prefixLift 1071618
  have htrace : WordTrace (prefixWord ++ tailWord_1071618) baseStart_1071618 baseEnd_1071618 := by
    simpa [prefixWord, tailWord_1071618, baseEnd_1071618] using wordTrace_append hprefix tailTrace_1071618
  have hstable : (prefixWord ++ tailWord_1071618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071618).length < 2 ^ (prefixWord ++ tailWord_1071618).sum := by decide
  have hdescent : baseEnd_1071618 < baseStart_1071618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071626 : List Nat := [3, 1, 2, 2, 2, 1, 3, 4, 3]
def baseStart_1071626 : Nat := 118140960795 + 1071626 * 2 ^ 59
def prefixEnd_1071626 : Nat := 4983230072969 + 3 ^ 40 * 1071626 * 2
def baseEnd_1071626 : Nat := 244559653268946440909639

theorem tailTrace_1071626 : CollatzResearch.WordTrace tailWord_1071626 prefixEnd_1071626 244559653268946440909639 := by
  unfold tailWord_1071626
  simp only [CollatzResearch.WordTrace]
  refine ⟨9771352803922373998752683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26056940810459663996673821 9771352803922373998752683)
  ·
    refine ⟨14657029205883560998129025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9771352803922373998752683 14657029205883560998129025)
    ·
      refine ⟨10992771904412670748596769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14657029205883560998129025 10992771904412670748596769)
      ·
        refine ⟨8244578928309503061447577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10992771904412670748596769 8244578928309503061447577)
        ·
          refine ⟨6183434196232127296085683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8244578928309503061447577 6183434196232127296085683)
          ·
            refine ⟨9275151294348190944128525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6183434196232127296085683 9275151294348190944128525)
            ·
              refine ⟨3478181735380571604048197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9275151294348190944128525 3478181735380571604048197)
              ·
                refine ⟨652159075383857175759037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3478181735380571604048197 652159075383857175759037)
                ·
                  refine ⟨244559653268946440909639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 652159075383857175759037 244559653268946440909639)
                  ·
                    rfl

theorem cell21_1071626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_1071626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071626 prefixEnd_1071626 := by exact prefixLift 1071626
  have htrace : WordTrace (prefixWord ++ tailWord_1071626) baseStart_1071626 baseEnd_1071626 := by
    simpa [prefixWord, tailWord_1071626, baseEnd_1071626] using wordTrace_append hprefix tailTrace_1071626
  have hstable : (prefixWord ++ tailWord_1071626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071626).length < 2 ^ (prefixWord ++ tailWord_1071626).sum := by decide
  have hdescent : baseEnd_1071626 < baseStart_1071626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071629 : List Nat := [1, 7, 1, 1, 1, 3, 1, 6]
def baseStart_1071629 : Nat := 118140960795 + 1071629 * 2 ^ 59
def prefixEnd_1071629 : Nat := 4983230072969 + 3 ^ 40 * 1071629 * 2
def baseEnd_1071629 : Nat := 81520112636606367453211

theorem tailTrace_1071629 : CollatzResearch.WordTrace tailWord_1071629 prefixEnd_1071629 81520112636606367453211 := by
  unfold tailWord_1071629
  simp only [CollatzResearch.WordTrace]
  refine ⟨39085520634678627507369941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26057013756452418338246627 39085520634678627507369941)
  ·
    refine ⟨916066889875280332203983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 39085520634678627507369941 916066889875280332203983)
    ·
      refine ⟨1374100334812920498305975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 916066889875280332203983 1374100334812920498305975)
      ·
        refine ⟨2061150502219380747458963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1374100334812920498305975 2061150502219380747458963)
        ·
          refine ⟨3091725753329071121188445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2061150502219380747458963 3091725753329071121188445)
          ·
            refine ⟨1159397157498401670445667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3091725753329071121188445 1159397157498401670445667)
            ·
              refine ⟨1739095736247602505668501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159397157498401670445667 1739095736247602505668501)
              ·
                refine ⟨81520112636606367453211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1739095736247602505668501 81520112636606367453211)
                ·
                  rfl

theorem cell21_1071629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 6].length) (baseStart_1071629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071629 prefixEnd_1071629 := by exact prefixLift 1071629
  have htrace : WordTrace (prefixWord ++ tailWord_1071629) baseStart_1071629 baseEnd_1071629 := by
    simpa [prefixWord, tailWord_1071629, baseEnd_1071629] using wordTrace_append hprefix tailTrace_1071629
  have hstable : (prefixWord ++ tailWord_1071629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071629).length < 2 ^ (prefixWord ++ tailWord_1071629).sum := by decide
  have hdescent : baseEnd_1071629 < baseStart_1071629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071640 : List Nat := [2, 1, 2, 3, 3, 1, 2, 3, 4]
def baseStart_1071640 : Nat := 118140960795 + 1071640 * 2 ^ 59
def prefixEnd_1071640 : Nat := 4983230072969 + 3 ^ 40 * 1071640 * 2
def baseEnd_1071640 : Nat := 244562848259685527676277

theorem tailTrace_1071640 : CollatzResearch.WordTrace tailWord_1071640 prefixEnd_1071640 244562848259685527676277 := by
  unfold tailWord_1071640
  simp only [CollatzResearch.WordTrace]
  refine ⟨19542960918819388193010187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26057281225092517590680249 19542960918819388193010187)
  ·
    refine ⟨29314441378229082289515281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19542960918819388193010187 29314441378229082289515281)
    ·
      refine ⟨21985831033671811717136461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29314441378229082289515281 21985831033671811717136461)
      ·
        refine ⟨8244686637626929393926173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21985831033671811717136461 8244686637626929393926173)
        ·
          refine ⟨3091757489110098522722315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8244686637626929393926173 3091757489110098522722315)
          ·
            refine ⟨4637636233665147784083473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3091757489110098522722315 4637636233665147784083473)
            ·
              refine ⟨3478227175248860838062605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4637636233665147784083473 3478227175248860838062605)
              ·
                refine ⟨1304335190718322814273477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3478227175248860838062605 1304335190718322814273477)
                ·
                  refine ⟨244562848259685527676277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1304335190718322814273477 244562848259685527676277)
                  ·
                    rfl

theorem cell21_1071640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_1071640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071640 prefixEnd_1071640 := by exact prefixLift 1071640
  have htrace : WordTrace (prefixWord ++ tailWord_1071640) baseStart_1071640 baseEnd_1071640 := by
    simpa [prefixWord, tailWord_1071640, baseEnd_1071640] using wordTrace_append hprefix tailTrace_1071640
  have hstable : (prefixWord ++ tailWord_1071640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071640).length < 2 ^ (prefixWord ++ tailWord_1071640).sum := by decide
  have hdescent : baseEnd_1071640 < baseStart_1071640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071685 : List Nat := [1, 3, 1, 1, 1, 6, 2, 1, 5]
def baseStart_1071685 : Nat := 118140960795 + 1071685 * 2 ^ 59
def prefixEnd_1071685 : Nat := 4983230072969 + 3 ^ 40 * 1071685 * 2
def baseEnd_1071685 : Nat := 244573117872775449426185

theorem tailTrace_1071685 : CollatzResearch.WordTrace tailWord_1071685 prefixEnd_1071685 244573117872775449426185 := by
  unfold tailWord_1071685
  simp only [CollatzResearch.WordTrace]
  refine ⟨39087563122475749071408509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26058375414983832714272339 39087563122475749071408509)
  ·
    refine ⟨14657836170928405901778191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39087563122475749071408509 14657836170928405901778191)
    ·
      refine ⟨21986754256392608852667287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14657836170928405901778191 21986754256392608852667287)
      ·
        refine ⟨32980131384588913279000931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21986754256392608852667287 32980131384588913279000931)
        ·
          refine ⟨49470197076883369918501397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32980131384588913279000931 49470197076883369918501397)
          ·
            refine ⟨2318915487978907964929753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49470197076883369918501397 2318915487978907964929753)
            ·
              refine ⟨1739186615984180973697315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2318915487978907964929753 1739186615984180973697315)
              ·
                refine ⟨2608779923976271460545973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1739186615984180973697315 2608779923976271460545973)
                ·
                  refine ⟨244573117872775449426185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2608779923976271460545973 244573117872775449426185)
                  ·
                    rfl

theorem cell21_1071685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_1071685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071685 prefixEnd_1071685 := by exact prefixLift 1071685
  have htrace : WordTrace (prefixWord ++ tailWord_1071685) baseStart_1071685 baseEnd_1071685 := by
    simpa [prefixWord, tailWord_1071685, baseEnd_1071685] using wordTrace_append hprefix tailTrace_1071685
  have hstable : (prefixWord ++ tailWord_1071685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071685).length < 2 ^ (prefixWord ++ tailWord_1071685).sum := by decide
  have hdescent : baseEnd_1071685 < baseStart_1071685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071795 : List Nat := [1, 1, 1, 2, 3, 6, 2, 2, 3]
def baseStart_1071795 : Nat := 118140960795 + 1071795 * 2 ^ 59
def prefixEnd_1071795 : Nat := 4983230072969 + 3 ^ 40 * 1071795 * 2
def baseEnd_1071795 : Nat := 244598221371439702592627

theorem tailTrace_1071795 : CollatzResearch.WordTrace tailWord_1071795 prefixEnd_1071795 244598221371439702592627 := by
  unfold tailWord_1071795
  simp only [CollatzResearch.WordTrace]
  refine ⟨39091575152077237857912839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26061050101384825238608559 39091575152077237857912839)
  ·
    refine ⟨58637362728115856786869259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39091575152077237857912839 58637362728115856786869259)
    ·
      refine ⟨87956044092173785180303889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58637362728115856786869259 87956044092173785180303889)
      ·
        refine ⟨65967033069130338885227917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87956044092173785180303889 65967033069130338885227917)
        ·
          refine ⟨24737637400923877081960469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65967033069130338885227917 24737637400923877081960469)
          ·
            refine ⟨1159576753168306738216897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24737637400923877081960469 1159576753168306738216897)
            ·
              refine ⟨869682564876230053662673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1159576753168306738216897 869682564876230053662673)
              ·
                refine ⟨652261923657172540247005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 869682564876230053662673 652261923657172540247005)
                ·
                  refine ⟨244598221371439702592627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 652261923657172540247005 244598221371439702592627)
                  ·
                    rfl

theorem cell21_1071795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 3].length) (baseStart_1071795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071795 prefixEnd_1071795 := by exact prefixLift 1071795
  have htrace : WordTrace (prefixWord ++ tailWord_1071795) baseStart_1071795 baseEnd_1071795 := by
    simpa [prefixWord, tailWord_1071795, baseEnd_1071795] using wordTrace_append hprefix tailTrace_1071795
  have hstable : (prefixWord ++ tailWord_1071795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071795).length < 2 ^ (prefixWord ++ tailWord_1071795).sum := by decide
  have hdescent : baseEnd_1071795 < baseStart_1071795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071854 : List Nat := [4, 1, 2, 1, 1, 3, 2, 4, 3]
def baseStart_1071854 : Nat := 118140960795 + 1071854 * 2 ^ 59
def prefixEnd_1071854 : Nat := 4983230072969 + 3 ^ 40 * 1071854 * 2
def baseEnd_1071854 : Nat := 244611685975268711109173

theorem tailTrace_1071854 : CollatzResearch.WordTrace tailWord_1071854 prefixEnd_1071854 244611685975268711109173 := by
  unfold tailWord_1071854
  simp only [CollatzResearch.WordTrace]
  refine ⟨4886715882357936366788827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26062484705908993956207077 4886715882357936366788827)
  ·
    refine ⟨7330073823536904550183241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4886715882357936366788827 7330073823536904550183241)
    ·
      refine ⟨5497555367652678412637431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7330073823536904550183241 5497555367652678412637431)
      ·
        refine ⟨8246333051479017618956147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5497555367652678412637431 8246333051479017618956147)
        ·
          refine ⟨12369499577218526428434221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8246333051479017618956147 12369499577218526428434221)
          ·
            refine ⟨4638562341456947410662833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12369499577218526428434221 4638562341456947410662833)
            ·
              refine ⟨3478921756092710557997125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4638562341456947410662833 3478921756092710557997125)
              ·
                refine ⟨652297829267383229624461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3478921756092710557997125 652297829267383229624461)
                ·
                  refine ⟨244611685975268711109173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 652297829267383229624461 244611685975268711109173)
                  ·
                    rfl

theorem cell21_1071854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_1071854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071854 prefixEnd_1071854 := by exact prefixLift 1071854
  have htrace : WordTrace (prefixWord ++ tailWord_1071854) baseStart_1071854 baseEnd_1071854 := by
    simpa [prefixWord, tailWord_1071854, baseEnd_1071854] using wordTrace_append hprefix tailTrace_1071854
  have hstable : (prefixWord ++ tailWord_1071854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071854).length < 2 ^ (prefixWord ++ tailWord_1071854).sum := by decide
  have hdescent : baseEnd_1071854 < baseStart_1071854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071927 : List Nat := [1, 1, 3, 1, 2, 1, 5, 3, 4]
def baseStart_1071927 : Nat := 118140960795 + 1071927 * 2 ^ 59
def prefixEnd_1071927 : Nat := 4983230072969 + 3 ^ 40 * 1071927 * 2
def baseEnd_1071927 : Nat := 244628345569836806392357

theorem tailTrace_1071927 : CollatzResearch.WordTrace tailWord_1071927 prefixEnd_1071927 244628345569836806392357 := by
  unfold tailWord_1071927
  simp only [CollatzResearch.WordTrace]
  refine ⟨39096389587599024401718035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26064259725066016267812023 39096389587599024401718035)
  ·
    refine ⟨58644584381398536602577053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39096389587599024401718035 58644584381398536602577053)
    ·
      refine ⟨21991719143024451225966395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58644584381398536602577053 21991719143024451225966395)
      ·
        refine ⟨32987578714536676838949593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21991719143024451225966395 32987578714536676838949593)
        ·
          refine ⟨24740684035902507629212195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32987578714536676838949593 24740684035902507629212195)
          ·
            refine ⟨37111026053853761443818293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24740684035902507629212195 37111026053853761443818293)
            ·
              refine ⟨3479158692548790135357965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37111026053853761443818293 3479158692548790135357965)
              ·
                refine ⟨1304684509705796300759237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3479158692548790135357965 1304684509705796300759237)
                ·
                  refine ⟨244628345569836806392357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1304684509705796300759237 244628345569836806392357)
                  ·
                    rfl

theorem cell21_1071927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 4].length) (baseStart_1071927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071927 prefixEnd_1071927 := by exact prefixLift 1071927
  have htrace : WordTrace (prefixWord ++ tailWord_1071927) baseStart_1071927 baseEnd_1071927 := by
    simpa [prefixWord, tailWord_1071927, baseEnd_1071927] using wordTrace_append hprefix tailTrace_1071927
  have hstable : (prefixWord ++ tailWord_1071927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071927).length < 2 ^ (prefixWord ++ tailWord_1071927).sum := by decide
  have hdescent : baseEnd_1071927 < baseStart_1071927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071964 : List Nat := [2, 2, 4, 2, 1, 3, 2, 2, 3]
def baseStart_1071964 : Nat := 118140960795 + 1071964 * 2 ^ 59
def prefixEnd_1071964 : Nat := 4983230072969 + 3 ^ 40 * 1071964 * 2
def baseEnd_1071964 : Nat := 244636789473932964275615

theorem tailTrace_1071964 : CollatzResearch.WordTrace tailWord_1071964 prefixEnd_1071964 244636789473932964275615 := by
  unfold tailWord_1071964
  simp only [CollatzResearch.WordTrace]
  refine ⟨19548869544232489860407473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26065159392309986480543297 19548869544232489860407473)
  ·
    refine ⟨14661652158174367395305605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19548869544232489860407473 14661652158174367395305605)
    ·
      refine ⟨2749059779657693886619801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14661652158174367395305605 2749059779657693886619801)
      ·
        refine ⟨2061794834743270414964851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2749059779657693886619801 2061794834743270414964851)
        ·
          refine ⟨3092692252114905622447277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2061794834743270414964851 3092692252114905622447277)
          ·
            refine ⟨1159759594543089608417729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3092692252114905622447277 1159759594543089608417729)
            ·
              refine ⟨869819695907317206313297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1159759594543089608417729 869819695907317206313297)
              ·
                refine ⟨652364771930487904734973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 869819695907317206313297 652364771930487904734973)
                ·
                  refine ⟨244636789473932964275615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 652364771930487904734973 244636789473932964275615)
                  ·
                    rfl

theorem cell21_1071964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_1071964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071964 prefixEnd_1071964 := by exact prefixLift 1071964
  have htrace : WordTrace (prefixWord ++ tailWord_1071964) baseStart_1071964 baseEnd_1071964 := by
    simpa [prefixWord, tailWord_1071964, baseEnd_1071964] using wordTrace_append hprefix tailTrace_1071964
  have hstable : (prefixWord ++ tailWord_1071964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071964).length < 2 ^ (prefixWord ++ tailWord_1071964).sum := by decide
  have hdescent : baseEnd_1071964 < baseStart_1071964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1071989 : List Nat := [1, 3, 4, 1, 1, 3, 1, 2, 5]
def baseStart_1071989 : Nat := 118140960795 + 1071989 * 2 ^ 59
def prefixEnd_1071989 : Nat := 4983230072969 + 3 ^ 40 * 1071989 * 2
def baseEnd_1071989 : Nat := 244642494814538476358897

theorem tailTrace_1071989 : CollatzResearch.WordTrace tailWord_1071989 prefixEnd_1071989 244642494814538476358897 := by
  unfold tailWord_1071989
  simp only [CollatzResearch.WordTrace]
  refine ⟨39098650913374408990475021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26065767275582939326983347 39098650913374408990475021)
  ·
    refine ⟨14661994092515403371428133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39098650913374408990475021 14661994092515403371428133)
    ·
      refine ⟨2749123892346638132142775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14661994092515403371428133 2749123892346638132142775)
      ·
        refine ⟨4123685838519957198214163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2749123892346638132142775 4123685838519957198214163)
        ·
          refine ⟨6185528757779935797321245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4123685838519957198214163 6185528757779935797321245)
          ·
            refine ⟨2319573284167475923995467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6185528757779935797321245 2319573284167475923995467)
            ·
              refine ⟨3479359926251213885993201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2319573284167475923995467 3479359926251213885993201)
              ·
                refine ⟨2609519944688410414494901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3479359926251213885993201 2609519944688410414494901)
                ·
                  refine ⟨244642494814538476358897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2609519944688410414494901 244642494814538476358897)
                  ·
                    rfl

theorem cell21_1071989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_1071989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1071989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1071989 prefixEnd_1071989 := by exact prefixLift 1071989
  have htrace : WordTrace (prefixWord ++ tailWord_1071989) baseStart_1071989 baseEnd_1071989 := by
    simpa [prefixWord, tailWord_1071989, baseEnd_1071989] using wordTrace_append hprefix tailTrace_1071989
  have hstable : (prefixWord ++ tailWord_1071989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1071989).length < 2 ^ (prefixWord ++ tailWord_1071989).sum := by decide
  have hdescent : baseEnd_1071989 < baseStart_1071989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1071989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072068 : List Nat := [2, 3, 3, 3, 2, 1, 7]
def baseStart_1072068 : Nat := 118140960795 + 1072068 * 2 ^ 59
def prefixEnd_1072068 : Nat := 4983230072969 + 3 ^ 40 * 1072068 * 2
def baseEnd_1072068 : Nat := 27184502632316877171341

theorem tailTrace_1072068 : CollatzResearch.WordTrace tailWord_1072068 prefixEnd_1072068 27184502632316877171341 := by
  unfold tailWord_1072068
  simp only [CollatzResearch.WordTrace]
  refine ⟨19550766140044102741300429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26067688186725470321733905 19550766140044102741300429)
  ·
    refine ⟨7331537302516538527987661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19550766140044102741300429 7331537302516538527987661)
    ·
      refine ⟨2749326488443701947995373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7331537302516538527987661 2749326488443701947995373)
      ·
        refine ⟨1030997433166388230498265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2749326488443701947995373 1030997433166388230498265)
        ·
          refine ⟨773248074874791172873699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1030997433166388230498265 773248074874791172873699)
          ·
            refine ⟨1159872112312186759310549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773248074874791172873699 1159872112312186759310549)
            ·
              refine ⟨27184502632316877171341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1159872112312186759310549 27184502632316877171341)
              ·
                rfl

theorem cell21_1072068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 7].length) (baseStart_1072068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1072068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1072068 prefixEnd_1072068 := by exact prefixLift 1072068
  have htrace : WordTrace (prefixWord ++ tailWord_1072068) baseStart_1072068 baseEnd_1072068 := by
    simpa [prefixWord, tailWord_1072068, baseEnd_1072068] using wordTrace_append hprefix tailTrace_1072068
  have hstable : (prefixWord ++ tailWord_1072068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072068).length < 2 ^ (prefixWord ++ tailWord_1072068).sum := by decide
  have hdescent : baseEnd_1072068 < baseStart_1072068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072082 : List Nat := [3, 2, 2, 3, 1, 3, 1, 1, 5]
def baseStart_1072082 : Nat := 118140960795 + 1072082 * 2 ^ 59
def prefixEnd_1072082 : Nat := 4983230072969 + 3 ^ 40 * 1072082 * 2
def baseEnd_1072082 : Nat := 244663718681590981308707

theorem tailTrace_1072082 : CollatzResearch.WordTrace tailWord_1072082 prefixEnd_1072082 244663718681590981308707 := by
  unfold tailWord_1072082
  simp only [CollatzResearch.WordTrace]
  refine ⟨9775510725509371468402625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26068028601358323915740333 9775510725509371468402625)
  ·
    refine ⟨7331633044132028601301969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9775510725509371468402625 7331633044132028601301969)
    ·
      refine ⟨5498724783099021450976477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7331633044132028601301969 5498724783099021450976477)
      ·
        refine ⟨2062021793662133044116179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5498724783099021450976477 2062021793662133044116179)
        ·
          refine ⟨3093032690493199566174269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2062021793662133044116179 3093032690493199566174269)
          ·
            refine ⟨1159887258934949837315351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3093032690493199566174269 1159887258934949837315351)
            ·
              refine ⟨1739830888402424755973027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159887258934949837315351 1739830888402424755973027)
              ·
                refine ⟨2609746332603637133959541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1739830888402424755973027 2609746332603637133959541)
                ·
                  refine ⟨244663718681590981308707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2609746332603637133959541 244663718681590981308707)
                  ·
                    rfl

theorem cell21_1072082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_1072082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1072082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1072082 prefixEnd_1072082 := by exact prefixLift 1072082
  have htrace : WordTrace (prefixWord ++ tailWord_1072082) baseStart_1072082 baseEnd_1072082 := by
    simpa [prefixWord, tailWord_1072082, baseEnd_1072082] using wordTrace_append hprefix tailTrace_1072082
  have hstable : (prefixWord ++ tailWord_1072082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072082).length < 2 ^ (prefixWord ++ tailWord_1072082).sum := by decide
  have hdescent : baseEnd_1072082 < baseStart_1072082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072130 : List Nat := [3, 4, 1, 3, 1, 1, 2, 2, 4]
def baseStart_1072130 : Nat := 118140960795 + 1072130 * 2 ^ 59
def prefixEnd_1072130 : Nat := 4983230072969 + 3 ^ 40 * 1072130 * 2
def baseEnd_1072130 : Nat := 244674672935553564508609

theorem tailTrace_1072130 : CollatzResearch.WordTrace tailWord_1072130 prefixEnd_1072130 244674672935553564508609 := by
  unfold tailWord_1072130
  simp only [CollatzResearch.WordTrace]
  refine ⟨9775948401465897517839461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26069195737242393380905229 9775948401465897517839461)
  ·
    refine ⟨1832990325274855784594899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9775948401465897517839461 1832990325274855784594899)
    ·
      refine ⟨2749485487912283676892349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1832990325274855784594899 2749485487912283676892349)
      ·
        refine ⟨1031057057967106378834631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2749485487912283676892349 1031057057967106378834631)
        ·
          refine ⟨1546585586950659568251947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1031057057967106378834631 1546585586950659568251947)
          ·
            refine ⟨2319878380425989352377921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1546585586950659568251947 2319878380425989352377921)
            ·
              refine ⟨1739908785319492014283441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2319878380425989352377921 1739908785319492014283441)
              ·
                refine ⟨1304931588989619010712581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1739908785319492014283441 1304931588989619010712581)
                ·
                  refine ⟨244674672935553564508609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1304931588989619010712581 244674672935553564508609)
                  ·
                    rfl

theorem cell21_1072130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_1072130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1072130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1072130 prefixEnd_1072130 := by exact prefixLift 1072130
  have htrace : WordTrace (prefixWord ++ tailWord_1072130) baseStart_1072130 baseEnd_1072130 := by
    simpa [prefixWord, tailWord_1072130, baseEnd_1072130] using wordTrace_append hprefix tailTrace_1072130
  have hstable : (prefixWord ++ tailWord_1072130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072130).length < 2 ^ (prefixWord ++ tailWord_1072130).sum := by decide
  have hdescent : baseEnd_1072130 < baseStart_1072130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072183 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 9]
def baseStart_1072183 : Nat := 118140960795 + 1072183 * 2 ^ 59
def prefixEnd_1072183 : Nat := 4983230072969 + 3 ^ 40 * 1072183 * 2
def baseEnd_1072183 : Nat := 244686768257637250125167

theorem tailTrace_1072183 : CollatzResearch.WordTrace tailWord_1072183 prefixEnd_1072183 244686768257637250125167 := by
  unfold tailWord_1072183
  simp only [CollatzResearch.WordTrace]
  refine ⟨39105726674671580123037203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26070484449781053415358135 39105726674671580123037203)
  ·
    refine ⟨58658590012007370184555805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39105726674671580123037203 58658590012007370184555805)
    ·
      refine ⟨21996971254502763819208427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58658590012007370184555805 21996971254502763819208427)
      ·
        refine ⟨32995456881754145728812641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21996971254502763819208427 32995456881754145728812641)
        ·
          refine ⟨24746592661315609296609481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32995456881754145728812641 24746592661315609296609481)
          ·
            refine ⟨18559944495986706972457111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24746592661315609296609481 18559944495986706972457111)
            ·
              refine ⟨27839916743980060458685667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18559944495986706972457111 27839916743980060458685667)
              ·
                refine ⟨41759875115970090688028501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27839916743980060458685667 41759875115970090688028501)
                ·
                  refine ⟨244686768257637250125167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41759875115970090688028501 244686768257637250125167)
                  ·
                    rfl

theorem cell21_1072183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 9].length) (baseStart_1072183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1072183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1072183 prefixEnd_1072183 := by exact prefixLift 1072183
  have htrace : WordTrace (prefixWord ++ tailWord_1072183) baseStart_1072183 baseEnd_1072183 := by
    simpa [prefixWord, tailWord_1072183, baseEnd_1072183] using wordTrace_append hprefix tailTrace_1072183
  have hstable : (prefixWord ++ tailWord_1072183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072183).length < 2 ^ (prefixWord ++ tailWord_1072183).sum := by decide
  have hdescent : baseEnd_1072183 < baseStart_1072183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072200 : List Nat := [2, 1, 3, 1, 1, 1, 6, 1, 5]
def baseStart_1072200 : Nat := 118140960795 + 1072200 * 2 ^ 59
def prefixEnd_1072200 : Nat := 4983230072969 + 3 ^ 40 * 1072200 * 2
def baseEnd_1072200 : Nat := 244690647889248998341799

theorem tailTrace_1072200 : CollatzResearch.WordTrace tailWord_1072200 prefixEnd_1072200 244690647889248998341799 := by
  unfold tailWord_1072200
  simp only [CollatzResearch.WordTrace]
  refine ⟨19553173357804996013203027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26070897810406661350937369 19553173357804996013203027)
  ·
    refine ⟨29329760036707494019804541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19553173357804996013203027 29329760036707494019804541)
    ·
      refine ⟨10998660013765310257426703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29329760036707494019804541 10998660013765310257426703)
      ·
        refine ⟨16497990020647965386140055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10998660013765310257426703 16497990020647965386140055)
        ·
          refine ⟨24746985030971948079210083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16497990020647965386140055 24746985030971948079210083)
          ·
            refine ⟨37120477546457922118815125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24746985030971948079210083 37120477546457922118815125)
            ·
              refine ⟨1740022384990215099319459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37120477546457922118815125 1740022384990215099319459)
              ·
                refine ⟨2610033577485322648979189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1740022384990215099319459 2610033577485322648979189)
                ·
                  refine ⟨244690647889248998341799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2610033577485322648979189 244690647889248998341799)
                  ·
                    rfl

theorem cell21_1072200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_1072200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1072200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1072200 prefixEnd_1072200 := by exact prefixLift 1072200
  have htrace : WordTrace (prefixWord ++ tailWord_1072200) baseStart_1072200 baseEnd_1072200 := by
    simpa [prefixWord, tailWord_1072200, baseEnd_1072200] using wordTrace_append hprefix tailTrace_1072200
  have hstable : (prefixWord ++ tailWord_1072200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072200).length < 2 ^ (prefixWord ++ tailWord_1072200).sum := by decide
  have hdescent : baseEnd_1072200 < baseStart_1072200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072234 : List Nat := [3, 1, 3, 2, 2, 1, 3, 3, 3]
def baseStart_1072234 : Nat := 118140960795 + 1072234 * 2 ^ 59
def prefixEnd_1072234 : Nat := 4983230072969 + 3 ^ 40 * 1072234 * 2
def baseEnd_1072234 : Nat := 244698407152472494775063

theorem tailTrace_1072234 : CollatzResearch.WordTrace tailWord_1072234 prefixEnd_1072234 244698407152472494775063 := by
  unfold tailWord_1072234
  simp only [CollatzResearch.WordTrace]
  refine ⟨9776896699371703958285939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26071724531657877222095837 9776896699371703958285939)
  ·
    refine ⟨14665345049057555937428909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9776896699371703958285939 14665345049057555937428909)
    ·
      refine ⟨5499504393396583476535841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14665345049057555937428909 5499504393396583476535841)
      ·
        refine ⟨4124628295047437607401881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5499504393396583476535841 4124628295047437607401881)
        ·
          refine ⟨3093471221285578205551411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4124628295047437607401881 3093471221285578205551411)
          ·
            refine ⟨4640206831928367308327117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3093471221285578205551411 4640206831928367308327117)
            ·
              refine ⟨1740077561973137740622669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4640206831928367308327117 1740077561973137740622669)
              ·
                refine ⟨652529085739926652733501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1740077561973137740622669 652529085739926652733501)
                ·
                  refine ⟨244698407152472494775063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 652529085739926652733501 244698407152472494775063)
                  ·
                    rfl

theorem cell21_1072234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_1072234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1072234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1072234 prefixEnd_1072234 := by exact prefixLift 1072234
  have htrace : WordTrace (prefixWord ++ tailWord_1072234) baseStart_1072234 baseEnd_1072234 := by
    simpa [prefixWord, tailWord_1072234, baseEnd_1072234] using wordTrace_append hprefix tailTrace_1072234
  have hstable : (prefixWord ++ tailWord_1072234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072234).length < 2 ^ (prefixWord ++ tailWord_1072234).sum := by decide
  have hdescent : baseEnd_1072234 < baseStart_1072234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072338 : List Nat := [3, 2, 2, 2, 1, 1, 5, 5]
def baseStart_1072338 : Nat := 118140960795 + 1072338 * 2 ^ 59
def prefixEnd_1072338 : Nat := 4983230072969 + 3 ^ 40 * 1072338 * 2
def baseEnd_1072338 : Nat := 81574047123130475013839

theorem tailTrace_1072338 : CollatzResearch.WordTrace tailWord_1072338 prefixEnd_1072338 81574047123130475013839 := by
  unfold tailWord_1072338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9777844997277510398732417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26074253326073361063286445 9777844997277510398732417)
  ·
    refine ⟨7333383747958132799049313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9777844997277510398732417 7333383747958132799049313)
    ·
      refine ⟨5500037810968599599286985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7333383747958132799049313 5500037810968599599286985)
      ·
        refine ⟨4125028358226449699465239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5500037810968599599286985 4125028358226449699465239)
        ·
          refine ⟨6187542537339674549197859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4125028358226449699465239 6187542537339674549197859)
          ·
            refine ⟨9281313806009511823796789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6187542537339674549197859 9281313806009511823796789)
            ·
              refine ⟨870123169313391733480949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9281313806009511823796789 870123169313391733480949)
              ·
                refine ⟨81574047123130475013839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 870123169313391733480949 81574047123130475013839)
                ·
                  rfl

theorem cell21_1072338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_1072338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1072338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1072338 prefixEnd_1072338 := by exact prefixLift 1072338
  have htrace : WordTrace (prefixWord ++ tailWord_1072338) baseStart_1072338 baseEnd_1072338 := by
    simpa [prefixWord, tailWord_1072338, baseEnd_1072338] using wordTrace_append hprefix tailTrace_1072338
  have hstable : (prefixWord ++ tailWord_1072338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072338).length < 2 ^ (prefixWord ++ tailWord_1072338).sum := by decide
  have hdescent : baseEnd_1072338 < baseStart_1072338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072611 : List Nat := [1, 1, 1, 6, 2, 2, 1, 3, 4]
def baseStart_1072611 : Nat := 118140960795 + 1072611 * 2 ^ 59
def prefixEnd_1072611 : Nat := 4983230072969 + 3 ^ 40 * 1072611 * 2
def baseEnd_1072611 : Nat := 244784443688803616990959

theorem tailTrace_1072611 : CollatzResearch.WordTrace tailWord_1072611 prefixEnd_1072611 244784443688803616990959 := by
  unfold tailWord_1072611
  simp only [CollatzResearch.WordTrace]
  refine ⟨39121337117121009219617687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26080891411414006146411791 39121337117121009219617687)
  ·
    refine ⟨58682005675681513829426531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39121337117121009219617687 58682005675681513829426531)
    ·
      refine ⟨88023008513522270744139797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58682005675681513829426531 88023008513522270744139797)
      ·
        refine ⟨4126078524071356441131553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88023008513522270744139797 4126078524071356441131553)
        ·
          refine ⟨3094558893053517330848665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4126078524071356441131553 3094558893053517330848665)
          ·
            refine ⟨2320919169790137998136499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3094558893053517330848665 2320919169790137998136499)
            ·
              refine ⟨3481378754685206997204749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2320919169790137998136499 3481378754685206997204749)
              ·
                refine ⟨1305517033006952623951781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3481378754685206997204749 1305517033006952623951781)
                ·
                  refine ⟨244784443688803616990959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1305517033006952623951781 244784443688803616990959)
                  ·
                    rfl

theorem cell21_1072611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 4].length) (baseStart_1072611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1072611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1072611 prefixEnd_1072611 := by exact prefixLift 1072611
  have htrace : WordTrace (prefixWord ++ tailWord_1072611) baseStart_1072611 baseEnd_1072611 := by
    simpa [prefixWord, tailWord_1072611, baseEnd_1072611] using wordTrace_append hprefix tailTrace_1072611
  have hstable : (prefixWord ++ tailWord_1072611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072611).length < 2 ^ (prefixWord ++ tailWord_1072611).sum := by decide
  have hdescent : baseEnd_1072611 < baseStart_1072611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072701 : List Nat := [1, 4, 1, 3, 3, 1, 8]
def baseStart_1072701 : Nat := 118140960795 + 1072701 * 2 ^ 59
def prefixEnd_1072701 : Nat := 4983230072969 + 3 ^ 40 * 1072701 * 2
def baseEnd_1072701 : Nat := 27200553657220384498975

theorem tailTrace_1072701 : CollatzResearch.WordTrace tailWord_1072701 prefixEnd_1072701 27200553657220384498975 := by
  unfold tailWord_1072701
  simp only [CollatzResearch.WordTrace]
  refine ⟨39124619686794954590393957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26083079791196636393595971 39124619686794954590393957)
  ·
    refine ⟨7335866191274053985698867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39124619686794954590393957 7335866191274053985698867)
    ·
      refine ⟨11003799286911080978548301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7335866191274053985698867 11003799286911080978548301)
      ·
        refine ⟨4126424732591655366955613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11003799286911080978548301 4126424732591655366955613)
        ·
          refine ⟨1547409274721870762608355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4126424732591655366955613 1547409274721870762608355)
          ·
            refine ⟨2321113912082806143912533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1547409274721870762608355 2321113912082806143912533)
            ·
              refine ⟨27200553657220384498975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2321113912082806143912533 27200553657220384498975)
              ·
                rfl

theorem cell21_1072701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 8].length) (baseStart_1072701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1072701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1072701 prefixEnd_1072701 := by exact prefixLift 1072701
  have htrace : WordTrace (prefixWord ++ tailWord_1072701) baseStart_1072701 baseEnd_1072701 := by
    simpa [prefixWord, tailWord_1072701, baseEnd_1072701] using wordTrace_append hprefix tailTrace_1072701
  have hstable : (prefixWord ++ tailWord_1072701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072701).length < 2 ^ (prefixWord ++ tailWord_1072701).sum := by decide
  have hdescent : baseEnd_1072701 < baseStart_1072701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072732 : List Nat := [2, 2, 4, 1, 2, 1, 2, 2, 5]
def baseStart_1072732 : Nat := 118140960795 + 1072732 * 2 ^ 59
def prefixEnd_1072732 : Nat := 4983230072969 + 3 ^ 40 * 1072732 * 2
def baseEnd_1072732 : Nat := 244812057537334295474045

theorem tailTrace_1072732 : CollatzResearch.WordTrace tailWord_1072732 prefixEnd_1072732 244812057537334295474045 := by
  unfold tailWord_1072732
  simp only [CollatzResearch.WordTrace]
  refine ⟨19562875174841323442386225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26083833566455097923181633 19562875174841323442386225)
  ·
    refine ⟨14672156381130992581789669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19562875174841323442386225 14672156381130992581789669)
    ·
      refine ⟨2751029321462061109085563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14672156381130992581789669 2751029321462061109085563)
      ·
        refine ⟨4126543982193091663628345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2751029321462061109085563 4126543982193091663628345)
        ·
          refine ⟨3094907986644818747721259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4126543982193091663628345 3094907986644818747721259)
          ·
            refine ⟨4642361979967228121581889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3094907986644818747721259 4642361979967228121581889)
            ·
              refine ⟨3481771484975421091186417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4642361979967228121581889 3481771484975421091186417)
              ·
                refine ⟨2611328613731565818389813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3481771484975421091186417 2611328613731565818389813)
                ·
                  refine ⟨244812057537334295474045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2611328613731565818389813 244812057537334295474045)
                  ·
                    rfl

theorem cell21_1072732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_1072732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1072732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1072732 prefixEnd_1072732 := by exact prefixLift 1072732
  have htrace : WordTrace (prefixWord ++ tailWord_1072732) baseStart_1072732 baseEnd_1072732 := by
    simpa [prefixWord, tailWord_1072732, baseEnd_1072732] using wordTrace_append hprefix tailTrace_1072732
  have hstable : (prefixWord ++ tailWord_1072732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072732).length < 2 ^ (prefixWord ++ tailWord_1072732).sum := by decide
  have hdescent : baseEnd_1072732 < baseStart_1072732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072746 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 6]
def baseStart_1072746 : Nat := 118140960795 + 1072746 * 2 ^ 59
def prefixEnd_1072746 : Nat := 4983230072969 + 3 ^ 40 * 1072746 * 2
def baseEnd_1072746 : Nat := 244815252528073382240683

theorem tailTrace_1072746 : CollatzResearch.WordTrace tailWord_1072746 prefixEnd_1072746 244815252528073382240683 := by
  unfold tailWord_1072746
  simp only [CollatzResearch.WordTrace]
  refine ⟨9781565242907981818945523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26084173981087951517188061 9781565242907981818945523)
  ·
    refine ⟨14672347864361972728418285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9781565242907981818945523 14672347864361972728418285)
    ·
      refine ⟨5502130449135739773156857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14672347864361972728418285 5502130449135739773156857)
      ·
        refine ⟨4126597836851804829867643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5502130449135739773156857 4126597836851804829867643)
        ·
          refine ⟨6189896755277707244801465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4126597836851804829867643 6189896755277707244801465)
          ·
            refine ⟨4642422566458280433601099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6189896755277707244801465 4642422566458280433601099)
            ·
              refine ⟨6963633849687420650401649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4642422566458280433601099 6963633849687420650401649)
              ·
                refine ⟨5222725387265565487801237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6963633849687420650401649 5222725387265565487801237)
                ·
                  refine ⟨244815252528073382240683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5222725387265565487801237 244815252528073382240683)
                  ·
                    rfl

theorem cell21_1072746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_1072746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1072746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1072746 prefixEnd_1072746 := by exact prefixLift 1072746
  have htrace : WordTrace (prefixWord ++ tailWord_1072746) baseStart_1072746 baseEnd_1072746 := by
    simpa [prefixWord, tailWord_1072746, baseEnd_1072746] using wordTrace_append hprefix tailTrace_1072746
  have hstable : (prefixWord ++ tailWord_1072746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072746).length < 2 ^ (prefixWord ++ tailWord_1072746).sum := by decide
  have hdescent : baseEnd_1072746 < baseStart_1072746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072805 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 8]
def baseStart_1072805 : Nat := 118140960795 + 1072805 * 2 ^ 59
def prefixEnd_1072805 : Nat := 4983230072969 + 3 ^ 40 * 1072805 * 2
def baseEnd_1072805 : Nat := 244828717131902390757229

theorem tailTrace_1072805 : CollatzResearch.WordTrace tailWord_1072805 prefixEnd_1072805 244828717131902390757229 := by
  unfold tailWord_1072805
  simp only [CollatzResearch.WordTrace]
  refine ⟨39128412878418180352179869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26085608585612120234786579 39128412878418180352179869)
  ·
    refine ⟨14673154829406817632067451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39128412878418180352179869 14673154829406817632067451)
    ·
      refine ⟨22009732244110226448101177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14673154829406817632067451 22009732244110226448101177)
      ·
        refine ⟨16507299183082669836075883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22009732244110226448101177 16507299183082669836075883)
        ·
          refine ⟨24760948774624004754113825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16507299183082669836075883 24760948774624004754113825)
          ·
            refine ⟨18570711580968003565585369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24760948774624004754113825 18570711580968003565585369)
            ·
              refine ⟨13928033685726002674189027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18570711580968003565585369 13928033685726002674189027)
              ·
                refine ⟨20892050528589004011283541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13928033685726002674189027 20892050528589004011283541)
                ·
                  refine ⟨244828717131902390757229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20892050528589004011283541 244828717131902390757229)
                  ·
                    rfl

theorem cell21_1072805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_1072805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1072805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1072805 prefixEnd_1072805 := by exact prefixLift 1072805
  have htrace : WordTrace (prefixWord ++ tailWord_1072805) baseStart_1072805 baseEnd_1072805 := by
    simpa [prefixWord, tailWord_1072805, baseEnd_1072805] using wordTrace_append hprefix tailTrace_1072805
  have hstable : (prefixWord ++ tailWord_1072805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072805).length < 2 ^ (prefixWord ++ tailWord_1072805).sum := by decide
  have hdescent : baseEnd_1072805 < baseStart_1072805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072825 : List Nat := [1, 2, 1, 4, 1, 1, 6, 2, 3]
def baseStart_1072825 : Nat := 118140960795 + 1072825 * 2 ^ 59
def prefixEnd_1072825 : Nat := 4983230072969 + 3 ^ 40 * 1072825 * 2
def baseEnd_1072825 : Nat := 244833281404386800423855

theorem tailTrace_1072825 : CollatzResearch.WordTrace tailWord_1072825 prefixEnd_1072825 244833281404386800423855 := by
  unfold tailWord_1072825
  simp only [CollatzResearch.WordTrace]
  refine ⟨39129142338345723767907929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26086094892230482511938619 39129142338345723767907929)
  ·
    refine ⟨29346856753759292825930947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39129142338345723767907929 29346856753759292825930947)
    ·
      refine ⟨44020285130638939238896421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29346856753759292825930947 44020285130638939238896421)
      ·
        refine ⟨8253803461994801107293079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44020285130638939238896421 8253803461994801107293079)
        ·
          refine ⟨12380705192992201660939619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8253803461994801107293079 12380705192992201660939619)
          ·
            refine ⟨18571057789488302491409429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12380705192992201660939619 18571057789488302491409429)
            ·
              refine ⟨870518333882264179284817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18571057789488302491409429 870518333882264179284817)
              ·
                refine ⟨652888750411698134463613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 870518333882264179284817 652888750411698134463613)
                ·
                  refine ⟨244833281404386800423855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 652888750411698134463613 244833281404386800423855)
                  ·
                    rfl

theorem cell21_1072825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 3].length) (baseStart_1072825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1072825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1072825 prefixEnd_1072825 := by exact prefixLift 1072825
  have htrace : WordTrace (prefixWord ++ tailWord_1072825) baseStart_1072825 baseEnd_1072825 := by
    simpa [prefixWord, tailWord_1072825, baseEnd_1072825] using wordTrace_append hprefix tailTrace_1072825
  have hstable : (prefixWord ++ tailWord_1072825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072825).length < 2 ^ (prefixWord ++ tailWord_1072825).sum := by decide
  have hdescent : baseEnd_1072825 < baseStart_1072825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072949 : List Nat := [1, 3, 3, 1, 5, 1, 2, 1, 4]
def baseStart_1072949 : Nat := 118140960795 + 1072949 * 2 ^ 59
def prefixEnd_1072949 : Nat := 4983230072969 + 3 ^ 40 * 1072949 * 2
def baseEnd_1072949 : Nat := 244861579893790140356935

theorem tailTrace_1072949 : CollatzResearch.WordTrace tailWord_1072949 prefixEnd_1072949 244861579893790140356935 := by
  unfold tailWord_1072949
  simp only [CollatzResearch.WordTrace]
  refine ⟨39133664989896492945421901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26089109993264328630281267 39133664989896492945421901)
  ·
    refine ⟨14675124371211184854533213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39133664989896492945421901 14675124371211184854533213)
    ·
      refine ⟨5503171639204194320449955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14675124371211184854533213 5503171639204194320449955)
      ·
        refine ⟨8254757458806291480674933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5503171639204194320449955 8254757458806291480674933)
        ·
          refine ⟨773883511763089826313275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8254757458806291480674933 773883511763089826313275)
          ·
            refine ⟨1160825267644634739469913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773883511763089826313275 1160825267644634739469913)
            ·
              refine ⟨870618950733476054602435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1160825267644634739469913 870618950733476054602435)
              ·
                refine ⟨1305928426100214081903653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 870618950733476054602435 1305928426100214081903653)
                ·
                  refine ⟨244861579893790140356935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1305928426100214081903653 244861579893790140356935)
                  ·
                    rfl

theorem cell21_1072949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_1072949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1072949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1072949 prefixEnd_1072949 := by exact prefixLift 1072949
  have htrace : WordTrace (prefixWord ++ tailWord_1072949) baseStart_1072949 baseEnd_1072949 := by
    simpa [prefixWord, tailWord_1072949, baseEnd_1072949] using wordTrace_append hprefix tailTrace_1072949
  have hstable : (prefixWord ++ tailWord_1072949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072949).length < 2 ^ (prefixWord ++ tailWord_1072949).sum := by decide
  have hdescent : baseEnd_1072949 < baseStart_1072949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072988 : List Nat := [2, 2, 4, 2, 11]
def baseStart_1072988 : Nat := 118140960795 + 1072988 * 2 ^ 59
def prefixEnd_1072988 : Nat := 4983230072969 + 3 ^ 40 * 1072988 * 2
def baseEnd_1072988 : Nat := 3023092348458453570455

theorem tailTrace_1072988 : CollatzResearch.WordTrace tailWord_1072988 prefixEnd_1072988 3023092348458453570455 := by
  unfold tailWord_1072988
  simp only [CollatzResearch.WordTrace]
  refine ⟨19567543718377601303045809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26090058291170135070727745 19567543718377601303045809)
  ·
    refine ⟨14675657788783200977284357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19567543718377601303045809 14675657788783200977284357)
    ·
      refine ⟨2751685835396850183240817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14675657788783200977284357 2751685835396850183240817)
      ·
        refine ⟨2063764376547637637430613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2751685835396850183240817 2063764376547637637430613)
        ·
          refine ⟨3023092348458453570455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2063764376547637637430613 3023092348458453570455)
          ·
            rfl

theorem cell21_1072988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 11].length) (baseStart_1072988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1072988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1072988 prefixEnd_1072988 := by exact prefixLift 1072988
  have htrace : WordTrace (prefixWord ++ tailWord_1072988) baseStart_1072988 baseEnd_1072988 := by
    simpa [prefixWord, tailWord_1072988, baseEnd_1072988] using wordTrace_append hprefix tailTrace_1072988
  have hstable : (prefixWord ++ tailWord_1072988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072988).length < 2 ^ (prefixWord ++ tailWord_1072988).sum := by decide
  have hdescent : baseEnd_1072988 < baseStart_1072988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1072994 : List Nat := [3, 3, 2, 1, 2, 1, 4, 2, 3]
def baseStart_1072994 : Nat := 118140960795 + 1072994 * 2 ^ 59
def prefixEnd_1072994 : Nat := 4983230072969 + 3 ^ 40 * 1072994 * 2
def baseEnd_1072994 : Nat := 244871849506880062106843

theorem tailTrace_1072994 : CollatzResearch.WordTrace tailWord_1072994 prefixEnd_1072994 244871849506880062106843 := by
  unfold tailWord_1072994
  simp only [CollatzResearch.WordTrace]
  refine ⟨9783826568683366407702509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26090204183155643753873357 9783826568683366407702509)
  ·
    refine ⟨3668934963256262402888441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9783826568683366407702509 3668934963256262402888441)
    ·
      refine ⟨2751701222442196802166331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3668934963256262402888441 2751701222442196802166331)
      ·
        refine ⟨4127551833663295203249497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2751701222442196802166331 4127551833663295203249497)
        ·
          refine ⟨3095663875247471402437123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4127551833663295203249497 3095663875247471402437123)
          ·
            refine ⟨4643495812871207103655685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3095663875247471402437123 4643495812871207103655685)
            ·
              refine ⟨870655464913351331935441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4643495812871207103655685 870655464913351331935441)
              ·
                refine ⟨652991598685013498951581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 870655464913351331935441 652991598685013498951581)
                ·
                  refine ⟨244871849506880062106843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 652991598685013498951581 244871849506880062106843)
                  ·
                    rfl

theorem cell21_1072994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_1072994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1072994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1072994 prefixEnd_1072994 := by exact prefixLift 1072994
  have htrace : WordTrace (prefixWord ++ tailWord_1072994) baseStart_1072994 baseEnd_1072994 := by
    simpa [prefixWord, tailWord_1072994, baseEnd_1072994] using wordTrace_append hprefix tailTrace_1072994
  have hstable : (prefixWord ++ tailWord_1072994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1072994).length < 2 ^ (prefixWord ++ tailWord_1072994).sum := by decide
  have hdescent : baseEnd_1072994 < baseStart_1072994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1072994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073033 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 6]
def baseStart_1073033 : Nat := 118140960795 + 1073033 * 2 ^ 59
def prefixEnd_1073033 : Nat := 4983230072969 + 3 ^ 40 * 1073033 * 2
def baseEnd_1073033 : Nat := 244880749838224660956763

theorem tailTrace_1073033 : CollatzResearch.WordTrace tailWord_1073033 prefixEnd_1073033 244880749838224660956763 := by
  unfold tailWord_1073033
  simp only [CollatzResearch.WordTrace]
  refine ⟨39136728721592175291479753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26091152481061450194319835 39136728721592175291479753)
  ·
    refine ⟨29352546541194131468609815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39136728721592175291479753 29352546541194131468609815)
    ·
      refine ⟨44028819811791197202914723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29352546541194131468609815 44028819811791197202914723)
      ·
        refine ⟨66043229717686795804372085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44028819811791197202914723 66043229717686795804372085)
        ·
          refine ⟨6191552786033137106659883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66043229717686795804372085 6191552786033137106659883)
          ·
            refine ⟨9287329179049705659989825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6191552786033137106659883 9287329179049705659989825)
            ·
              refine ⟨6965496884287279244992369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9287329179049705659989825 6965496884287279244992369)
              ·
                refine ⟨5224122663215459433744277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6965496884287279244992369 5224122663215459433744277)
                ·
                  refine ⟨244880749838224660956763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5224122663215459433744277 244880749838224660956763)
                  ·
                    rfl

theorem cell21_1073033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_1073033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073033 prefixEnd_1073033 := by exact prefixLift 1073033
  have htrace : WordTrace (prefixWord ++ tailWord_1073033) baseStart_1073033 baseEnd_1073033 := by
    simpa [prefixWord, tailWord_1073033, baseEnd_1073033] using wordTrace_append hprefix tailTrace_1073033
  have hstable : (prefixWord ++ tailWord_1073033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073033).length < 2 ^ (prefixWord ++ tailWord_1073033).sum := by decide
  have hdescent : baseEnd_1073033 < baseStart_1073033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073050 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 6]
def baseStart_1073050 : Nat := 118140960795 + 1073050 * 2 ^ 59
def prefixEnd_1073050 : Nat := 4983230072969 + 3 ^ 40 * 1073050 * 2
def baseEnd_1073050 : Nat := 244884629469836409173395

theorem tailTrace_1073050 : CollatzResearch.WordTrace tailWord_1073050 prefixEnd_1073050 244884629469836409173395 := by
  unfold tailWord_1073050
  simp only [CollatzResearch.WordTrace]
  refine ⟨9784337190632646798712151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26091565841687058129899069 9784337190632646798712151)
  ·
    refine ⟨14676505785948970198068227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9784337190632646798712151 14676505785948970198068227)
    ·
      refine ⟨22014758678923455297102341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14676505785948970198068227 22014758678923455297102341)
      ·
        refine ⟨4127767252298147868206689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22014758678923455297102341 4127767252298147868206689)
        ·
          refine ⟨3095825439223610901155017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4127767252298147868206689 3095825439223610901155017)
          ·
            refine ⟨2321869079417708175866263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3095825439223610901155017 2321869079417708175866263)
            ·
              refine ⟨3482803619126562263799395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2321869079417708175866263 3482803619126562263799395)
              ·
                refine ⟨5224205428689843395699093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3482803619126562263799395 5224205428689843395699093)
                ·
                  refine ⟨244884629469836409173395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5224205428689843395699093 244884629469836409173395)
                  ·
                    rfl

theorem cell21_1073050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_1073050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073050 prefixEnd_1073050 := by exact prefixLift 1073050
  have htrace : WordTrace (prefixWord ++ tailWord_1073050) baseStart_1073050 baseEnd_1073050 := by
    simpa [prefixWord, tailWord_1073050, baseEnd_1073050] using wordTrace_append hprefix tailTrace_1073050
  have hstable : (prefixWord ++ tailWord_1073050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073050).length < 2 ^ (prefixWord ++ tailWord_1073050).sum := by decide
  have hdescent : baseEnd_1073050 < baseStart_1073050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073188 : List Nat := [2, 3, 1, 4, 2, 1, 1, 2, 5]
def baseStart_1073188 : Nat := 118140960795 + 1073188 * 2 ^ 59
def prefixEnd_1073188 : Nat := 4983230072969 + 3 ^ 40 * 1073188 * 2
def baseEnd_1073188 : Nat := 244916122949978835873113

theorem tailTrace_1073188 : CollatzResearch.WordTrace tailWord_1073188 prefixEnd_1073188 244916122949978835873113 := by
  unfold tailWord_1073188
  simp only [CollatzResearch.WordTrace]
  refine ⟨19571191018015318381686109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26094921357353757842248145 19571191018015318381686109)
  ·
    refine ⟨7339196631755744393132291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19571191018015318381686109 7339196631755744393132291)
    ·
      refine ⟨11008794947633616589698437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7339196631755744393132291 11008794947633616589698437)
      ·
        refine ⟨2064149052681303110568457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11008794947633616589698437 2064149052681303110568457)
        ·
          refine ⟨1548111789510977332926343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2064149052681303110568457 1548111789510977332926343)
          ·
            refine ⟨2322167684266465999389515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1548111789510977332926343 2322167684266465999389515)
            ·
              refine ⟨3483251526399698999084273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2322167684266465999389515 3483251526399698999084273)
              ·
                refine ⟨2612438644799774249313205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3483251526399698999084273 2612438644799774249313205)
                ·
                  refine ⟨244916122949978835873113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2612438644799774249313205 244916122949978835873113)
                  ·
                    rfl

theorem cell21_1073188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_1073188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073188 prefixEnd_1073188 := by exact prefixLift 1073188
  have htrace : WordTrace (prefixWord ++ tailWord_1073188) baseStart_1073188 baseEnd_1073188 := by
    simpa [prefixWord, tailWord_1073188, baseEnd_1073188] using wordTrace_append hprefix tailTrace_1073188
  have hstable : (prefixWord ++ tailWord_1073188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073188).length < 2 ^ (prefixWord ++ tailWord_1073188).sum := by decide
  have hdescent : baseEnd_1073188 < baseStart_1073188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073261 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 8]
def baseStart_1073261 : Nat := 118140960795 + 1073261 * 2 ^ 59
def prefixEnd_1073261 : Nat := 4983230072969 + 3 ^ 40 * 1073261 * 2
def baseEnd_1073261 : Nat := 244932782544546931156297

theorem tailTrace_1073261 : CollatzResearch.WordTrace tailWord_1073261 prefixEnd_1073261 244932782544546931156297 := by
  unfold tailWord_1073261
  simp only [CollatzResearch.WordTrace]
  refine ⟨39145044564766170230779637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26096696376510780153853091 39145044564766170230779637)
  ·
    refine ⟨3669847927946828459135591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39145044564766170230779637 3669847927946828459135591)
    ·
      refine ⟨5504771891920242688703387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3669847927946828459135591 5504771891920242688703387)
      ·
        refine ⟨8257157837880364033055081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5504771891920242688703387 8257157837880364033055081)
        ·
          refine ⟨6192868378410273024791311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8257157837880364033055081 6192868378410273024791311)
          ·
            refine ⟨9289302567615409537186967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6192868378410273024791311 9289302567615409537186967)
            ·
              refine ⟨13933953851423114305780451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9289302567615409537186967 13933953851423114305780451)
              ·
                refine ⟨20900930777134671458670677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13933953851423114305780451 20900930777134671458670677)
                ·
                  refine ⟨244932782544546931156297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20900930777134671458670677 244932782544546931156297)
                  ·
                    rfl

theorem cell21_1073261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_1073261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073261 prefixEnd_1073261 := by exact prefixLift 1073261
  have htrace : WordTrace (prefixWord ++ tailWord_1073261) baseStart_1073261 baseEnd_1073261 := by
    simpa [prefixWord, tailWord_1073261, baseEnd_1073261] using wordTrace_append hprefix tailTrace_1073261
  have hstable : (prefixWord ++ tailWord_1073261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073261).length < 2 ^ (prefixWord ++ tailWord_1073261).sum := by decide
  have hdescent : baseEnd_1073261 < baseStart_1073261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073264 : List Nat := [2, 1, 1, 1, 5, 2, 3, 3, 3]
def baseStart_1073264 : Nat := 118140960795 + 1073264 * 2 ^ 59
def prefixEnd_1073264 : Nat := 4983230072969 + 3 ^ 40 * 1073264 * 2
def baseEnd_1073264 : Nat := 244933467185419592606291

theorem tailTrace_1073264 : CollatzResearch.WordTrace tailWord_1073264 prefixEnd_1073264 244933467185419592606291 := by
  unfold tailWord_1073264
  simp only [CollatzResearch.WordTrace]
  refine ⟨19572576991877650871569423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26096769322503534495425897 19572576991877650871569423)
  ·
    refine ⟨29358865487816476307354135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19572576991877650871569423 29358865487816476307354135)
    ·
      refine ⟨44038298231724714461031203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29358865487816476307354135 44038298231724714461031203)
      ·
        refine ⟨66057447347587071691546805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44038298231724714461031203 66057447347587071691546805)
        ·
          refine ⟨6192885688836287971082513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66057447347587071691546805 6192885688836287971082513)
          ·
            refine ⟨4644664266627215978311885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6192885688836287971082513 4644664266627215978311885)
            ·
              refine ⟨1741749099985205991866957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4644664266627215978311885 1741749099985205991866957)
              ·
                refine ⟨653155912494452246950109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1741749099985205991866957 653155912494452246950109)
                ·
                  refine ⟨244933467185419592606291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 653155912494452246950109 244933467185419592606291)
                  ·
                    rfl

theorem cell21_1073264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 3].length) (baseStart_1073264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073264 prefixEnd_1073264 := by exact prefixLift 1073264
  have htrace : WordTrace (prefixWord ++ tailWord_1073264) baseStart_1073264 baseEnd_1073264 := by
    simpa [prefixWord, tailWord_1073264, baseEnd_1073264] using wordTrace_append hprefix tailTrace_1073264
  have hstable : (prefixWord ++ tailWord_1073264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073264).length < 2 ^ (prefixWord ++ tailWord_1073264).sum := by decide
  have hdescent : baseEnd_1073264 < baseStart_1073264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073281 : List Nat := [1, 2, 4, 2, 4, 1, 1, 1, 5]
def baseStart_1073281 : Nat := 118140960795 + 1073281 * 2 ^ 59
def prefixEnd_1073281 : Nat := 4983230072969 + 3 ^ 40 * 1073281 * 2
def baseEnd_1073281 : Nat := 244937346817031340822923

theorem tailTrace_1073281 : CollatzResearch.WordTrace tailWord_1073281 prefixEnd_1073281 244937346817031340822923 := by
  unfold tailWord_1073281
  simp only [CollatzResearch.WordTrace]
  refine ⟨39145774024693713646507697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26097182683129142431005131 39145774024693713646507697)
  ·
    refine ⟨29359330518520285234880773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39145774024693713646507697 29359330518520285234880773)
    ·
      refine ⟨5504874472222553481540145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29359330518520285234880773 5504874472222553481540145)
      ·
        refine ⟨4128655854166915111155109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5504874472222553481540145 4128655854166915111155109)
        ·
          refine ⟨774122972656296583341583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4128655854166915111155109 774122972656296583341583)
          ·
            refine ⟨1161184458984444875012375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774122972656296583341583 1161184458984444875012375)
            ·
              refine ⟨1741776688476667312518563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1161184458984444875012375 1741776688476667312518563)
              ·
                refine ⟨2612665032715000968777845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1741776688476667312518563 2612665032715000968777845)
                ·
                  refine ⟨244937346817031340822923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2612665032715000968777845 244937346817031340822923)
                  ·
                    rfl

theorem cell21_1073281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 5].length) (baseStart_1073281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073281 prefixEnd_1073281 := by exact prefixLift 1073281
  have htrace : WordTrace (prefixWord ++ tailWord_1073281) baseStart_1073281 baseEnd_1073281 := by
    simpa [prefixWord, tailWord_1073281, baseEnd_1073281] using wordTrace_append hprefix tailTrace_1073281
  have hstable : (prefixWord ++ tailWord_1073281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073281).length < 2 ^ (prefixWord ++ tailWord_1073281).sum := by decide
  have hdescent : baseEnd_1073281 < baseStart_1073281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073326 : List Nat := [4, 1, 4, 2, 2, 8]
def baseStart_1073326 : Nat := 118140960795 + 1073326 * 2 ^ 59
def prefixEnd_1073326 : Nat := 4983230072969 + 3 ^ 40 * 1073326 * 2
def baseEnd_1073326 : Nat := 9072133941856343058253

theorem tailTrace_1073326 : CollatzResearch.WordTrace tailWord_1073326 prefixEnd_1073326 9072133941856343058253 := by
  unfold tailWord_1073326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4893426913691335791486979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26098276873020457554597221 4893426913691335791486979)
  ·
    refine ⟨7340140370537003687230469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4893426913691335791486979 7340140370537003687230469)
    ·
      refine ⟨1376276319475688191355713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7340140370537003687230469 1376276319475688191355713)
      ·
        refine ⟨1032207239606766143516785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1376276319475688191355713 1032207239606766143516785)
        ·
          refine ⟨774155429705074607637589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1032207239606766143516785 774155429705074607637589)
          ·
            refine ⟨9072133941856343058253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 774155429705074607637589 9072133941856343058253)
            ·
              rfl

theorem cell21_1073326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 8].length) (baseStart_1073326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073326 prefixEnd_1073326 := by exact prefixLift 1073326
  have htrace : WordTrace (prefixWord ++ tailWord_1073326) baseStart_1073326 baseEnd_1073326 := by
    simpa [prefixWord, tailWord_1073326, baseEnd_1073326] using wordTrace_append hprefix tailTrace_1073326
  have hstable : (prefixWord ++ tailWord_1073326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073326).length < 2 ^ (prefixWord ++ tailWord_1073326).sum := by decide
  have hdescent : baseEnd_1073326 < baseStart_1073326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073444 : List Nat := [2, 3, 1, 3, 1, 4, 7]
def baseStart_1073444 : Nat := 118140960795 + 1073444 * 2 ^ 59
def prefixEnd_1073444 : Nat := 4983230072969 + 3 ^ 40 * 1073444 * 2
def baseEnd_1073444 : Nat := 27219393959753253289547

theorem tailTrace_1073444 : CollatzResearch.WordTrace tailWord_1073444 prefixEnd_1073444 27219393959753253289547 := by
  unfold tailWord_1073444
  simp only [CollatzResearch.WordTrace]
  refine ⟨19575859561551596242345693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26101146082068794989794257 19575859561551596242345693)
  ·
    refine ⟨7340947335581848590879635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19575859561551596242345693 7340947335581848590879635)
    ·
      refine ⟨11011421003372772886319453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7340947335581848590879635 11011421003372772886319453)
      ·
        refine ⟨4129282876264789832369795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11011421003372772886319453 4129282876264789832369795)
        ·
          refine ⟨6193924314397184748554693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4129282876264789832369795 6193924314397184748554693)
          ·
            refine ⟨1161360808949472140354005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6193924314397184748554693 1161360808949472140354005)
            ·
              refine ⟨27219393959753253289547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1161360808949472140354005 27219393959753253289547)
              ·
                rfl

theorem cell21_1073444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 7].length) (baseStart_1073444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073444 prefixEnd_1073444 := by exact prefixLift 1073444
  have htrace : WordTrace (prefixWord ++ tailWord_1073444) baseStart_1073444 baseEnd_1073444 := by
    simpa [prefixWord, tailWord_1073444, baseEnd_1073444] using wordTrace_append hprefix tailTrace_1073444
  have hstable : (prefixWord ++ tailWord_1073444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073444).length < 2 ^ (prefixWord ++ tailWord_1073444).sum := by decide
  have hdescent : baseEnd_1073444 < baseStart_1073444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073450 : List Nat := [3, 1, 4, 2, 2, 1, 3, 2, 3]
def baseStart_1073450 : Nat := 118140960795 + 1073450 * 2 ^ 59
def prefixEnd_1073450 : Nat := 4983230072969 + 3 ^ 40 * 1073450 * 2
def baseEnd_1073450 : Nat := 244975914919524602505911

theorem tailTrace_1073450 : CollatzResearch.WordTrace tailWord_1073450 prefixEnd_1073450 244975914919524602505911 := by
  unfold tailWord_1073450
  simp only [CollatzResearch.WordTrace]
  refine ⟨9787984490270363877352451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26101291974054303672939869 9787984490270363877352451)
  ·
    refine ⟨14681976735405545816028677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9787984490270363877352451 14681976735405545816028677)
    ·
      refine ⟨2752870637888539840505377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14681976735405545816028677 2752870637888539840505377)
      ·
        refine ⟨2064652978416404880379033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2752870637888539840505377 2064652978416404880379033)
        ·
          refine ⟨1548489733812303660284275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2064652978416404880379033 1548489733812303660284275)
          ·
            refine ⟨2322734600718455490426413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1548489733812303660284275 2322734600718455490426413)
            ·
              refine ⟨871025475269420808909905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2322734600718455490426413 871025475269420808909905)
              ·
                refine ⟨653269106452065606682429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 871025475269420808909905 653269106452065606682429)
                ·
                  refine ⟨244975914919524602505911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 653269106452065606682429 244975914919524602505911)
                  ·
                    rfl

theorem cell21_1073450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_1073450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073450 prefixEnd_1073450 := by exact prefixLift 1073450
  have htrace : WordTrace (prefixWord ++ tailWord_1073450) baseStart_1073450 baseEnd_1073450 := by
    simpa [prefixWord, tailWord_1073450, baseEnd_1073450] using wordTrace_append hprefix tailTrace_1073450
  have hstable : (prefixWord ++ tailWord_1073450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073450).length < 2 ^ (prefixWord ++ tailWord_1073450).sum := by decide
  have hdescent : baseEnd_1073450 < baseStart_1073450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073472 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 8]
def baseStart_1073472 : Nat := 118140960795 + 1073472 * 2 ^ 59
def prefixEnd_1073472 : Nat := 4983230072969 + 3 ^ 40 * 1073472 * 2
def baseEnd_1073472 : Nat := 244980935619257453139199

theorem tailTrace_1073472 : CollatzResearch.WordTrace tailWord_1073472 prefixEnd_1073472 244980935619257453139199 := by
  unfold tailWord_1073472
  simp only [CollatzResearch.WordTrace]
  refine ⟨19576370183500876633355335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26101826911334502177807113 19576370183500876633355335)
  ·
    refine ⟨29364555275251314950033003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19576370183500876633355335 29364555275251314950033003)
    ·
      refine ⟨44046832912876972425049505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29364555275251314950033003 44046832912876972425049505)
      ·
        refine ⟨33035124684657729318787129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44046832912876972425049505 33035124684657729318787129)
        ·
          refine ⟨24776343513493296989090347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33035124684657729318787129 24776343513493296989090347)
          ·
            refine ⟨37164515270239945483635521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24776343513493296989090347 37164515270239945483635521)
            ·
              refine ⟨27873386452679959112726641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37164515270239945483635521 27873386452679959112726641)
              ·
                refine ⟨20905039839509969334544981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27873386452679959112726641 20905039839509969334544981)
                ·
                  refine ⟨244980935619257453139199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20905039839509969334544981 244980935619257453139199)
                  ·
                    rfl

theorem cell21_1073472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_1073472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073472 prefixEnd_1073472 := by exact prefixLift 1073472
  have htrace : WordTrace (prefixWord ++ tailWord_1073472) baseStart_1073472 baseEnd_1073472 := by
    simpa [prefixWord, tailWord_1073472, baseEnd_1073472] using wordTrace_append hprefix tailTrace_1073472
  have hstable : (prefixWord ++ tailWord_1073472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073472).length < 2 ^ (prefixWord ++ tailWord_1073472).sum := by decide
  have hdescent : baseEnd_1073472 < baseStart_1073472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073506 : List Nat := [3, 3, 2, 1, 1, 2, 1, 4, 4]
def baseStart_1073506 : Nat := 118140960795 + 1073506 * 2 ^ 59
def prefixEnd_1073506 : Nat := 4983230072969 + 3 ^ 40 * 1073506 * 2
def baseEnd_1073506 : Nat := 244988694882480949572463

theorem tailTrace_1073506 : CollatzResearch.WordTrace tailWord_1073506 prefixEnd_1073506 244988694882480949572463 := by
  unfold tailWord_1073506
  simp only [CollatzResearch.WordTrace]
  refine ⟨9788495112219644268362093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26102653632585718048965581 9788495112219644268362093)
  ·
    refine ⟨3670685667082366600635785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9788495112219644268362093 3670685667082366600635785)
    ·
      refine ⟨2753014250311774950476839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3670685667082366600635785 2753014250311774950476839)
      ·
        refine ⟨4129521375467662425715259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2753014250311774950476839 4129521375467662425715259)
        ·
          refine ⟨6194282063201493638572889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4129521375467662425715259 6194282063201493638572889)
          ·
            refine ⟨4645711547401120228929667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6194282063201493638572889 4645711547401120228929667)
            ·
              refine ⟨6968567321101680343394501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4645711547401120228929667 6968567321101680343394501)
              ·
                refine ⟨1306606372706565064386469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6968567321101680343394501 1306606372706565064386469)
                ·
                  refine ⟨244988694882480949572463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1306606372706565064386469 244988694882480949572463)
                  ·
                    rfl

theorem cell21_1073506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_1073506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073506 prefixEnd_1073506 := by exact prefixLift 1073506
  have htrace : WordTrace (prefixWord ++ tailWord_1073506) baseStart_1073506 baseEnd_1073506 := by
    simpa [prefixWord, tailWord_1073506, baseEnd_1073506] using wordTrace_append hprefix tailTrace_1073506
  have hstable : (prefixWord ++ tailWord_1073506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073506).length < 2 ^ (prefixWord ++ tailWord_1073506).sum := by decide
  have hdescent : baseEnd_1073506 < baseStart_1073506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073509 : List Nat := [1, 3, 1, 3, 1, 5, 2, 2, 3]
def baseStart_1073509 : Nat := 118140960795 + 1073509 * 2 ^ 59
def prefixEnd_1073509 : Nat := 4983230072969 + 3 ^ 40 * 1073509 * 2
def baseEnd_1073509 : Nat := 244989379523353611022457

theorem tailTrace_1073509 : CollatzResearch.WordTrace tailWord_1073509 prefixEnd_1073509 244989379523353611022457 := by
  unfold tailWord_1073509
  simp only [CollatzResearch.WordTrace]
  refine ⟨39154089867867708585807581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26102726578578472390538387 39154089867867708585807581)
  ·
    refine ⟨14682783700450390719677843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39154089867867708585807581 14682783700450390719677843)
    ·
      refine ⟨22024175550675586079516765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14682783700450390719677843 22024175550675586079516765)
      ·
        refine ⟨8259065831503344779818787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22024175550675586079516765 8259065831503344779818787)
        ·
          refine ⟨12388598747255017169728181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8259065831503344779818787 12388598747255017169728181)
          ·
            refine ⟨1161431132555157859662017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12388598747255017169728181 1161431132555157859662017)
            ·
              refine ⟨871073349416368394746513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1161431132555157859662017 871073349416368394746513)
              ·
                refine ⟨653305012062276296059885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 871073349416368394746513 653305012062276296059885)
                ·
                  refine ⟨244989379523353611022457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 653305012062276296059885 244989379523353611022457)
                  ·
                    rfl

theorem cell21_1073509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_1073509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073509 prefixEnd_1073509 := by exact prefixLift 1073509
  have htrace : WordTrace (prefixWord ++ tailWord_1073509) baseStart_1073509 baseEnd_1073509 := by
    simpa [prefixWord, tailWord_1073509, baseEnd_1073509] using wordTrace_append hprefix tailTrace_1073509
  have hstable : (prefixWord ++ tailWord_1073509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073509).length < 2 ^ (prefixWord ++ tailWord_1073509).sum := by decide
  have hdescent : baseEnd_1073509 < baseStart_1073509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073520 : List Nat := [2, 1, 1, 1, 4, 5, 1, 6]
def baseStart_1073520 : Nat := 118140960795 + 1073520 * 2 ^ 59
def prefixEnd_1073520 : Nat := 4983230072969 + 3 ^ 40 * 1073520 * 2
def baseEnd_1073520 : Nat := 81663963291073345446367

theorem tailTrace_1073520 : CollatzResearch.WordTrace tailWord_1073520 prefixEnd_1073520 81663963291073345446367 := by
  unfold tailWord_1073520
  simp only [CollatzResearch.WordTrace]
  refine ⟨19577245535413928732229007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26102994047218571642972009 19577245535413928732229007)
  ·
    refine ⟨29365868303120893098343511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19577245535413928732229007 29365868303120893098343511)
    ·
      refine ⟨44048802454681339647515267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29365868303120893098343511 44048802454681339647515267)
      ·
        refine ⟨66073203682022009471272901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44048802454681339647515267 66073203682022009471272901)
        ·
          refine ⟨12388725690379126775863669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66073203682022009471272901 12388725690379126775863669)
          ·
            refine ⟨1161443033473043135237219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12388725690379126775863669 1161443033473043135237219)
            ·
              refine ⟨1742164550209564702855829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1161443033473043135237219 1742164550209564702855829)
              ·
                refine ⟨81663963291073345446367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1742164550209564702855829 81663963291073345446367)
                ·
                  rfl

theorem cell21_1073520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 6].length) (baseStart_1073520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073520 prefixEnd_1073520 := by exact prefixLift 1073520
  have htrace : WordTrace (prefixWord ++ tailWord_1073520) baseStart_1073520 baseEnd_1073520 := by
    simpa [prefixWord, tailWord_1073520, baseEnd_1073520] using wordTrace_append hprefix tailTrace_1073520
  have hstable : (prefixWord ++ tailWord_1073520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073520).length < 2 ^ (prefixWord ++ tailWord_1073520).sum := by decide
  have hdescent : baseEnd_1073520 < baseStart_1073520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073537 : List Nat := [1, 2, 4, 3, 1, 2, 3, 5]
def baseStart_1073537 : Nat := 118140960795 + 1073537 * 2 ^ 59
def prefixEnd_1073537 : Nat := 4983230072969 + 3 ^ 40 * 1073537 * 2
def baseEnd_1073537 : Nat := 81665256501610594851911

theorem tailTrace_1073537 : CollatzResearch.WordTrace tailWord_1073537 prefixEnd_1073537 81665256501610594851911 := by
  unfold tailWord_1073537
  simp only [CollatzResearch.WordTrace]
  refine ⟨39155111111766269367826865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26103407407844179578551243 39155111111766269367826865)
  ·
    refine ⟨29366333333824702025870149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39155111111766269367826865 29366333333824702025870149)
    ·
      refine ⟨5506187500092131629850653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29366333333824702025870149 5506187500092131629850653)
      ·
        refine ⟨2064820312534549361193995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5506187500092131629850653 2064820312534549361193995)
        ·
          refine ⟨3097230468801824041790993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2064820312534549361193995 3097230468801824041790993)
          ·
            refine ⟨2322922851601368031343245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3097230468801824041790993 2322922851601368031343245)
            ·
              refine ⟨871096069350513011753717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2322922851601368031343245 871096069350513011753717)
              ·
                refine ⟨81665256501610594851911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 871096069350513011753717 81665256501610594851911)
                ·
                  rfl

theorem cell21_1073537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 5].length) (baseStart_1073537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073537 prefixEnd_1073537 := by exact prefixLift 1073537
  have htrace : WordTrace (prefixWord ++ tailWord_1073537) baseStart_1073537 baseEnd_1073537 := by
    simpa [prefixWord, tailWord_1073537, baseEnd_1073537] using wordTrace_append hprefix tailTrace_1073537
  have hstable : (prefixWord ++ tailWord_1073537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073537).length < 2 ^ (prefixWord ++ tailWord_1073537).sum := by decide
  have hdescent : baseEnd_1073537 < baseStart_1073537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073588 : List Nat := [2, 5, 2, 2, 2, 1, 2, 5]
def baseStart_1073588 : Nat := 118140960795 + 1073588 * 2 ^ 59
def prefixEnd_1073588 : Nat := 4983230072969 + 3 ^ 40 * 1073588 * 2
def baseEnd_1073588 : Nat := 81669136133222343068543

theorem tailTrace_1073588 : CollatzResearch.WordTrace tailWord_1073588 prefixEnd_1073588 81669136133222343068543 := by
  unfold tailWord_1073588
  simp only [CollatzResearch.WordTrace]
  refine ⟨19578485617290752538966709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26104647489721003385288945 19578485617290752538966709)
  ·
    refine ⟨1835483026621008050528129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19578485617290752538966709 1835483026621008050528129)
    ·
      refine ⟨1376612269965756037896097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1835483026621008050528129 1376612269965756037896097)
      ·
        refine ⟨1032459202474317028422073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1376612269965756037896097 1032459202474317028422073)
        ·
          refine ⟨774344401855737771316555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1032459202474317028422073 774344401855737771316555)
          ·
            refine ⟨1161516602783606656974833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774344401855737771316555 1161516602783606656974833)
            ·
              refine ⟨871137452087704992731125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1161516602783606656974833 871137452087704992731125)
              ·
                refine ⟨81669136133222343068543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 871137452087704992731125 81669136133222343068543)
                ·
                  rfl

theorem cell21_1073588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 5].length) (baseStart_1073588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073588 prefixEnd_1073588 := by exact prefixLift 1073588
  have htrace : WordTrace (prefixWord ++ tailWord_1073588) baseStart_1073588 baseEnd_1073588 := by
    simpa [prefixWord, tailWord_1073588, baseEnd_1073588] using wordTrace_append hprefix tailTrace_1073588
  have hstable : (prefixWord ++ tailWord_1073588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073588).length < 2 ^ (prefixWord ++ tailWord_1073588).sum := by decide
  have hdescent : baseEnd_1073588 < baseStart_1073588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073596 : List Nat := [2, 2, 2, 4, 1, 2, 1, 7]
def baseStart_1073596 : Nat := 118140960795 + 1073596 * 2 ^ 59
def prefixEnd_1073596 : Nat := 4983230072969 + 3 ^ 40 * 1073596 * 2
def baseEnd_1073596 : Nat := 81669744702886931024093

theorem tailTrace_1073596 : CollatzResearch.WordTrace tailWord_1073596 prefixEnd_1073596 81669744702886931024093 := by
  unfold tailWord_1073596
  simp only [CollatzResearch.WordTrace]
  refine ⟨19578631509276261222112321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26104842012368348296149761 19578631509276261222112321)
  ·
    refine ⟨14683973631957195916584241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19578631509276261222112321 14683973631957195916584241)
    ·
      refine ⟨11012980223967896937438181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14683973631957195916584241 11012980223967896937438181)
      ·
        refine ⟨2064933791993980675769659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11012980223967896937438181 2064933791993980675769659)
        ·
          refine ⟨3097400687990971013654489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2064933791993980675769659 3097400687990971013654489)
          ·
            refine ⟨2323050515993228260240867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3097400687990971013654489 2323050515993228260240867)
            ·
              refine ⟨3484575773989842390361301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2323050515993228260240867 3484575773989842390361301)
              ·
                refine ⟨81669744702886931024093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3484575773989842390361301 81669744702886931024093)
                ·
                  rfl

theorem cell21_1073596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 7].length) (baseStart_1073596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073596 prefixEnd_1073596 := by exact prefixLift 1073596
  have htrace : WordTrace (prefixWord ++ tailWord_1073596) baseStart_1073596 baseEnd_1073596 := by
    simpa [prefixWord, tailWord_1073596, baseEnd_1073596] using wordTrace_append hprefix tailTrace_1073596
  have hstable : (prefixWord ++ tailWord_1073596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073596).length < 2 ^ (prefixWord ++ tailWord_1073596).sum := by decide
  have hdescent : baseEnd_1073596 < baseStart_1073596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073765 : List Nat := [1, 3, 1, 3, 4, 2, 2, 5]
def baseStart_1073765 : Nat := 118140960795 + 1073765 * 2 ^ 59
def prefixEnd_1073765 : Nat := 4983230072969 + 3 ^ 40 * 1073765 * 2
def baseEnd_1073765 : Nat := 81682600737051351585089

theorem tailTrace_1073765 : CollatzResearch.WordTrace tailWord_1073765 prefixEnd_1073765 81682600737051351585089 := by
  unfold tailWord_1073765
  simp only [CollatzResearch.WordTrace]
  refine ⟨39163426954940264307126749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26108951303293509538084499 39163426954940264307126749)
  ·
    refine ⟨14686285108102599115172531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39163426954940264307126749 14686285108102599115172531)
    ·
      refine ⟨22029427662153898672758797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14686285108102599115172531 22029427662153898672758797)
      ·
        refine ⟨8261035373307712002284549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22029427662153898672758797 8261035373307712002284549)
        ·
          refine ⟨1548944132495196000428353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8261035373307712002284549 1548944132495196000428353)
          ·
            refine ⟨1161708099371397000321265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1548944132495196000428353 1161708099371397000321265)
            ·
              refine ⟨871281074528547750240949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1161708099371397000321265 871281074528547750240949)
              ·
                refine ⟨81682600737051351585089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 871281074528547750240949 81682600737051351585089)
                ·
                  rfl

theorem cell21_1073765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 5].length) (baseStart_1073765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073765 prefixEnd_1073765 := by exact prefixLift 1073765
  have htrace : WordTrace (prefixWord ++ tailWord_1073765) baseStart_1073765 baseEnd_1073765 := by
    simpa [prefixWord, tailWord_1073765, baseEnd_1073765] using wordTrace_append hprefix tailTrace_1073765
  have hstable : (prefixWord ++ tailWord_1073765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073765).length < 2 ^ (prefixWord ++ tailWord_1073765).sum := by decide
  have hdescent : baseEnd_1073765 < baseStart_1073765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073793 : List Nat := [1, 2, 4, 2, 1, 1, 2, 4, 4]
def baseStart_1073793 : Nat := 118140960795 + 1073793 * 2 ^ 59
def prefixEnd_1073793 : Nat := 4983230072969 + 3 ^ 40 * 1073793 * 2
def baseEnd_1073793 : Nat := 245054192192632228288543

theorem tailTrace_1073793 : CollatzResearch.WordTrace tailWord_1073793 prefixEnd_1073793 245054192192632228288543 := by
  unfold tailWord_1073793
  simp only [CollatzResearch.WordTrace]
  refine ⟨39164448198838825089146033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26109632132559216726097355 39164448198838825089146033)
  ·
    refine ⟨29373336149129118816859525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39164448198838825089146033 29373336149129118816859525)
    ·
      refine ⟨5507500527961709778161161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29373336149129118816859525 5507500527961709778161161)
      ·
        refine ⟨4130625395971282333620871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5507500527961709778161161 4130625395971282333620871)
        ·
          refine ⟨6195938093956923500431307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4130625395971282333620871 6195938093956923500431307)
          ·
            refine ⟨9293907140935385250646961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6195938093956923500431307 9293907140935385250646961)
            ·
              refine ⟨6970430355701538937985221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9293907140935385250646961 6970430355701538937985221)
              ·
                refine ⟨1306955691694038550872229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6970430355701538937985221 1306955691694038550872229)
                ·
                  refine ⟨245054192192632228288543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1306955691694038550872229 245054192192632228288543)
                  ·
                    rfl

theorem cell21_1073793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_1073793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073793 prefixEnd_1073793 := by exact prefixLift 1073793
  have htrace : WordTrace (prefixWord ++ tailWord_1073793) baseStart_1073793 baseEnd_1073793 := by
    simpa [prefixWord, tailWord_1073793, baseEnd_1073793] using wordTrace_append hprefix tailTrace_1073793
  have hstable : (prefixWord ++ tailWord_1073793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073793).length < 2 ^ (prefixWord ++ tailWord_1073793).sum := by decide
  have hdescent : baseEnd_1073793 < baseStart_1073793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073810 : List Nat := [3, 2, 3, 1, 2, 2, 1, 3, 4]
def baseStart_1073810 : Nat := 118140960795 + 1073810 * 2 ^ 59
def prefixEnd_1073810 : Nat := 4983230072969 + 3 ^ 40 * 1073810 * 2
def baseEnd_1073810 : Nat := 245058071824243976505175

theorem tailTrace_1073810 : CollatzResearch.WordTrace tailWord_1073810 prefixEnd_1073810 245058071824243976505175 := by
  unfold tailWord_1073810
  simp only [CollatzResearch.WordTrace]
  refine ⟨9791267059944309248128721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26110045493184824661676589 9791267059944309248128721)
  ·
    refine ⟨7343450294958231936096541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9791267059944309248128721 7343450294958231936096541)
    ·
      refine ⟨2753793860609336976036203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7343450294958231936096541 2753793860609336976036203)
      ·
        refine ⟨4130690790914005464054305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2753793860609336976036203 4130690790914005464054305)
        ·
          refine ⟨3098018093185504098040729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4130690790914005464054305 3098018093185504098040729)
          ·
            refine ⟨2323513569889128073530547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3098018093185504098040729 2323513569889128073530547)
            ·
              refine ⟨3485270354833692110295821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2323513569889128073530547 3485270354833692110295821)
              ·
                refine ⟨1306976383062634541360933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3485270354833692110295821 1306976383062634541360933)
                ·
                  refine ⟨245058071824243976505175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1306976383062634541360933 245058071824243976505175)
                  ·
                    rfl

theorem cell21_1073810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_1073810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073810 prefixEnd_1073810 := by exact prefixLift 1073810
  have htrace : WordTrace (prefixWord ++ tailWord_1073810) baseStart_1073810 baseEnd_1073810 := by
    simpa [prefixWord, tailWord_1073810, baseEnd_1073810] using wordTrace_append hprefix tailTrace_1073810
  have hstable : (prefixWord ++ tailWord_1073810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073810).length < 2 ^ (prefixWord ++ tailWord_1073810).sum := by decide
  have hdescent : baseEnd_1073810 < baseStart_1073810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073855 : List Nat := [1, 1, 2, 2, 2, 5, 1, 4, 3]
def baseStart_1073855 : Nat := 118140960795 + 1073855 * 2 ^ 59
def prefixEnd_1073855 : Nat := 4983230072969 + 3 ^ 40 * 1073855 * 2
def baseEnd_1073855 : Nat := 245068341437333898255083

theorem tailTrace_1073855 : CollatzResearch.WordTrace tailWord_1073855 prefixEnd_1073855 245068341437333898255083 := by
  unfold tailWord_1073855
  simp only [CollatzResearch.WordTrace]
  refine ⟨39166709524614209677903019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26111139683076139785268679 39166709524614209677903019)
  ·
    refine ⟨58750064286921314516854529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39166709524614209677903019 58750064286921314516854529)
    ·
      refine ⟨44062548215190985887640897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58750064286921314516854529 44062548215190985887640897)
      ·
        refine ⟨33046911161393239415730673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44062548215190985887640897 33046911161393239415730673)
        ·
          refine ⟨24785183371044929561798005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33046911161393239415730673 24785183371044929561798005)
          ·
            refine ⟨2323610941035462146418563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24785183371044929561798005 2323610941035462146418563)
            ·
              refine ⟨3485416411553193219627845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2323610941035462146418563 3485416411553193219627845)
              ·
                refine ⟨653515577166223728680221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3485416411553193219627845 653515577166223728680221)
                ·
                  refine ⟨245068341437333898255083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 653515577166223728680221 245068341437333898255083)
                  ·
                    rfl

theorem cell21_1073855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 3].length) (baseStart_1073855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073855 prefixEnd_1073855 := by exact prefixLift 1073855
  have htrace : WordTrace (prefixWord ++ tailWord_1073855) baseStart_1073855 baseEnd_1073855 := by
    simpa [prefixWord, tailWord_1073855, baseEnd_1073855] using wordTrace_append hprefix tailTrace_1073855
  have hstable : (prefixWord ++ tailWord_1073855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073855).length < 2 ^ (prefixWord ++ tailWord_1073855).sum := by decide
  have hdescent : baseEnd_1073855 < baseStart_1073855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073948 : List Nat := [2, 2, 3, 1, 1, 5, 1, 3, 3]
def baseStart_1073948 : Nat := 118140960795 + 1073948 * 2 ^ 59
def prefixEnd_1073948 : Nat := 4983230072969 + 3 ^ 40 * 1073948 * 2
def baseEnd_1073948 : Nat := 245089565304386403204893

theorem tailTrace_1073948 : CollatzResearch.WordTrace tailWord_1073948 prefixEnd_1073948 245089565304386403204893 := by
  unfold tailWord_1073948
  simp only [CollatzResearch.WordTrace]
  refine ⟨19585050756638643280519249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26113401008851524374025665 19585050756638643280519249)
  ·
    refine ⟨14688788067478982460389437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19585050756638643280519249 14688788067478982460389437)
    ·
      refine ⟨5508295525304618422646039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14688788067478982460389437 5508295525304618422646039)
      ·
        refine ⟨8262443287956927633969059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5508295525304618422646039 8262443287956927633969059)
        ·
          refine ⟨12393664931935391450953589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8262443287956927633969059 12393664931935391450953589)
          ·
            refine ⟨1161906087368942948526899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12393664931935391450953589 1161906087368942948526899)
            ·
              refine ⟨1742859131053414422790349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1161906087368942948526899 1742859131053414422790349)
              ·
                refine ⟨653572174145030408546381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1742859131053414422790349 653572174145030408546381)
                ·
                  refine ⟨245089565304386403204893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 653572174145030408546381 245089565304386403204893)
                  ·
                    rfl

theorem cell21_1073948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_1073948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073948 prefixEnd_1073948 := by exact prefixLift 1073948
  have htrace : WordTrace (prefixWord ++ tailWord_1073948) baseStart_1073948 baseEnd_1073948 := by
    simpa [prefixWord, tailWord_1073948, baseEnd_1073948] using wordTrace_append hprefix tailTrace_1073948
  have hstable : (prefixWord ++ tailWord_1073948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073948).length < 2 ^ (prefixWord ++ tailWord_1073948).sum := by decide
  have hdescent : baseEnd_1073948 < baseStart_1073948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1073965 : List Nat := [1, 5, 3, 2, 1, 2, 1, 1, 5]
def baseStart_1073965 : Nat := 118140960795 + 1073965 * 2 ^ 59
def prefixEnd_1073965 : Nat := 4983230072969 + 3 ^ 40 * 1073965 * 2
def baseEnd_1073965 : Nat := 245093444935998151421525

theorem tailTrace_1073965 : CollatzResearch.WordTrace tailWord_1073965 prefixEnd_1073965 245093444935998151421525 := by
  unfold tailWord_1073965
  simp only [CollatzResearch.WordTrace]
  refine ⟨39170721554215698464407349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26113814369477132309604899 39170721554215698464407349)
  ·
    refine ⟨3672255145707721731038189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39170721554215698464407349 3672255145707721731038189)
    ·
      refine ⟨1377095679640395649139321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3672255145707721731038189 1377095679640395649139321)
      ·
        refine ⟨1032821759730296736854491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1377095679640395649139321 1032821759730296736854491)
        ·
          refine ⟨1549232639595445105281737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1032821759730296736854491 1549232639595445105281737)
          ·
            refine ⟨1161924479696583828961303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1549232639595445105281737 1161924479696583828961303)
            ·
              refine ⟨1742886719544875743441955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1161924479696583828961303 1742886719544875743441955)
              ·
                refine ⟨2614330079317313615162933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1742886719544875743441955 2614330079317313615162933)
                ·
                  refine ⟨245093444935998151421525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2614330079317313615162933 245093444935998151421525)
                  ·
                    rfl

theorem cell21_1073965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_1073965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1073965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1073965 prefixEnd_1073965 := by exact prefixLift 1073965
  have htrace : WordTrace (prefixWord ++ tailWord_1073965) baseStart_1073965 baseEnd_1073965 := by
    simpa [prefixWord, tailWord_1073965, baseEnd_1073965] using wordTrace_append hprefix tailTrace_1073965
  have hstable : (prefixWord ++ tailWord_1073965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1073965).length < 2 ^ (prefixWord ++ tailWord_1073965).sum := by decide
  have hdescent : baseEnd_1073965 < baseStart_1073965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1073965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074024 : List Nat := [2, 1, 4, 2, 1, 2, 4, 2, 3]
def baseStart_1074024 : Nat := 118140960795 + 1074024 * 2 ^ 59
def prefixEnd_1074024 : Nat := 4983230072969 + 3 ^ 40 * 1074024 * 2
def baseEnd_1074024 : Nat := 245106909539827159938071

theorem tailTrace_1074024 : CollatzResearch.WordTrace tailWord_1074024 prefixEnd_1074024 245106909539827159938071 := by
  unfold tailWord_1074024
  simp only [CollatzResearch.WordTrace]
  refine ⟨19586436730500975770402563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26115248974001301027203417 19586436730500975770402563)
  ·
    refine ⟨29379655095751463655603845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19586436730500975770402563 29379655095751463655603845)
    ·
      refine ⟨5508685330453399435425721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29379655095751463655603845 5508685330453399435425721)
      ·
        refine ⟨4131513997840049576569291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5508685330453399435425721 4131513997840049576569291)
        ·
          refine ⟨6197270996760074364853937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4131513997840049576569291 6197270996760074364853937)
          ·
            refine ⟨4647953247570055773640453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6197270996760074364853937 4647953247570055773640453)
            ·
              refine ⟨871491233919385457557585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4647953247570055773640453 871491233919385457557585)
              ·
                refine ⟨653618425439539093168189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 871491233919385457557585 653618425439539093168189)
                ·
                  refine ⟨245106909539827159938071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 653618425439539093168189 245106909539827159938071)
                  ·
                    rfl

theorem cell21_1074024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 3].length) (baseStart_1074024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074024 prefixEnd_1074024 := by exact prefixLift 1074024
  have htrace : WordTrace (prefixWord ++ tailWord_1074024) baseStart_1074024 baseEnd_1074024 := by
    simpa [prefixWord, tailWord_1074024, baseEnd_1074024] using wordTrace_append hprefix tailTrace_1074024
  have hstable : (prefixWord ++ tailWord_1074024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074024).length < 2 ^ (prefixWord ++ tailWord_1074024).sum := by decide
  have hdescent : baseEnd_1074024 < baseStart_1074024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074038 : List Nat := [5, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_1074038 : Nat := 118140960795 + 1074038 * 2 ^ 59
def prefixEnd_1074038 : Nat := 4983230072969 + 3 ^ 40 * 1074038 * 2
def baseEnd_1074038 : Nat := 245110104530566246704709

theorem tailTrace_1074038 : CollatzResearch.WordTrace tailWord_1074038 prefixEnd_1074038 245110104530566246704709 := by
  unfold tailWord_1074038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2448336505184451995738423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26115589388634154621209845 2448336505184451995738423)
  ·
    refine ⟨3672504757776677993607635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2448336505184451995738423 3672504757776677993607635)
    ·
      refine ⟨5508757136665016990411453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3672504757776677993607635 5508757136665016990411453)
      ·
        refine ⟨2065783926249381371404295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5508757136665016990411453 2065783926249381371404295)
        ·
          refine ⟨3098675889374072057106443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2065783926249381371404295 3098675889374072057106443)
          ·
            refine ⟨4648013834061108085659665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3098675889374072057106443 4648013834061108085659665)
            ·
              refine ⟨3486010375545831064244749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4648013834061108085659665 3486010375545831064244749)
              ·
                refine ⟨1307253890829686649091781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3486010375545831064244749 1307253890829686649091781)
                ·
                  refine ⟨245110104530566246704709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1307253890829686649091781 245110104530566246704709)
                  ·
                    rfl

theorem cell21_1074038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_1074038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074038 prefixEnd_1074038 := by exact prefixLift 1074038
  have htrace : WordTrace (prefixWord ++ tailWord_1074038) baseStart_1074038 baseEnd_1074038 := by
    simpa [prefixWord, tailWord_1074038, baseEnd_1074038] using wordTrace_append hprefix tailTrace_1074038
  have hstable : (prefixWord ++ tailWord_1074038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074038).length < 2 ^ (prefixWord ++ tailWord_1074038).sum := by decide
  have hdescent : baseEnd_1074038 < baseStart_1074038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074204 : List Nat := [2, 2, 3, 1, 4, 2, 1, 6]
def baseStart_1074204 : Nat := 118140960795 + 1074204 * 2 ^ 59
def prefixEnd_1074204 : Nat := 4983230072969 + 3 ^ 40 * 1074204 * 2
def baseEnd_1074204 : Nat := 81715995997395615645901

theorem tailTrace_1074204 : CollatzResearch.WordTrace tailWord_1074204 prefixEnd_1074204 81715995997395615645901 := by
  unfold tailWord_1074204
  simp only [CollatzResearch.WordTrace]
  refine ⟨19589719300174921141178833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26119625733566561521571777 19589719300174921141178833)
  ·
    refine ⟨14692289475131190855884125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19589719300174921141178833 14692289475131190855884125)
    ·
      refine ⟨5509608553174196570956547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14692289475131190855884125 5509608553174196570956547)
      ·
        refine ⟨8264412829761294856434821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5509608553174196570956547 8264412829761294856434821)
        ·
          refine ⟨1549577405580242785581529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8264412829761294856434821 1549577405580242785581529)
          ·
            refine ⟨1162183054185182089186147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1549577405580242785581529 1162183054185182089186147)
            ·
              refine ⟨1743274581277773133779221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1162183054185182089186147 1743274581277773133779221)
              ·
                refine ⟨81715995997395615645901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1743274581277773133779221 81715995997395615645901)
                ·
                  rfl

theorem cell21_1074204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 6].length) (baseStart_1074204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074204 prefixEnd_1074204 := by exact prefixLift 1074204
  have htrace : WordTrace (prefixWord ++ tailWord_1074204) baseStart_1074204 baseEnd_1074204 := by
    simpa [prefixWord, tailWord_1074204, baseEnd_1074204] using wordTrace_append hprefix tailTrace_1074204
  have hstable : (prefixWord ++ tailWord_1074204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074204).length < 2 ^ (prefixWord ++ tailWord_1074204).sum := by decide
  have hdescent : baseEnd_1074204 < baseStart_1074204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074277 : List Nat := [1, 3, 1, 3, 2, 1, 1, 4, 5]
def baseStart_1074277 : Nat := 118140960795 + 1074277 * 2 ^ 59
def prefixEnd_1074277 : Nat := 4983230072969 + 3 ^ 40 * 1074277 * 2
def baseEnd_1074277 : Nat := 245164647586754942220887

theorem tailTrace_1074277 : CollatzResearch.WordTrace tailWord_1074277 prefixEnd_1074277 245164647586754942220887 := by
  unfold tailWord_1074277
  simp only [CollatzResearch.WordTrace]
  refine ⟨39182101129085375749765085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26121400752723583833176723 39182101129085375749765085)
  ·
    refine ⟨14693287923407015906161907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39182101129085375749765085 14693287923407015906161907)
    ·
      refine ⟨22039931885110523859242861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14693287923407015906161907 22039931885110523859242861)
      ·
        refine ⟨8264974456916446447216073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22039931885110523859242861 8264974456916446447216073)
        ·
          refine ⟨6198730842687334835412055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8264974456916446447216073 6198730842687334835412055)
          ·
            refine ⟨9298096264031002253118083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6198730842687334835412055 9298096264031002253118083)
            ·
              refine ⟨13947144396046503379677125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9298096264031002253118083 13947144396046503379677125)
              ·
                refine ⟨2615089574258719383689461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13947144396046503379677125 2615089574258719383689461)
                ·
                  refine ⟨245164647586754942220887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2615089574258719383689461 245164647586754942220887)
                  ·
                    rfl

theorem cell21_1074277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_1074277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074277 prefixEnd_1074277 := by exact prefixLift 1074277
  have htrace : WordTrace (prefixWord ++ tailWord_1074277) baseStart_1074277 baseEnd_1074277 := by
    simpa [prefixWord, tailWord_1074277, baseEnd_1074277] using wordTrace_append hprefix tailTrace_1074277
  have hstable : (prefixWord ++ tailWord_1074277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074277).length < 2 ^ (prefixWord ++ tailWord_1074277).sum := by decide
  have hdescent : baseEnd_1074277 < baseStart_1074277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074280 : List Nat := [2, 1, 4, 4, 1, 1, 1, 7]
def baseStart_1074280 : Nat := 118140960795 + 1074280 * 2 ^ 59
def prefixEnd_1074280 : Nat := 4983230072969 + 3 ^ 40 * 1074280 * 2
def baseEnd_1074280 : Nat := 81721777409209201223627

theorem tailTrace_1074280 : CollatzResearch.WordTrace tailWord_1074280 prefixEnd_1074280 81721777409209201223627 := by
  unfold tailWord_1074280
  simp only [CollatzResearch.WordTrace]
  refine ⟨19591105274037253631062147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26121473698716338174749529 19591105274037253631062147)
  ·
    refine ⟨29386657911055880446593221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19591105274037253631062147 29386657911055880446593221)
    ·
      refine ⟨5509998358322977583736229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29386657911055880446593221 5509998358322977583736229)
      ·
        refine ⟨1033124692185558296950543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5509998358322977583736229 1033124692185558296950543)
        ·
          refine ⟨1549687038278337445425815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1033124692185558296950543 1549687038278337445425815)
          ·
            refine ⟨2324530557417506168138723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1549687038278337445425815 2324530557417506168138723)
            ·
              refine ⟨3486795836126259252208085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2324530557417506168138723 3486795836126259252208085)
              ·
                refine ⟨81721777409209201223627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3486795836126259252208085 81721777409209201223627)
                ·
                  rfl

theorem cell21_1074280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 7].length) (baseStart_1074280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074280 prefixEnd_1074280 := by exact prefixLift 1074280
  have htrace : WordTrace (prefixWord ++ tailWord_1074280) baseStart_1074280 baseEnd_1074280 := by
    simpa [prefixWord, tailWord_1074280, baseEnd_1074280] using wordTrace_append hprefix tailTrace_1074280
  have hstable : (prefixWord ++ tailWord_1074280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074280).length < 2 ^ (prefixWord ++ tailWord_1074280).sum := by decide
  have hdescent : baseEnd_1074280 < baseStart_1074280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074308 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 6]
def baseStart_1074308 : Nat := 118140960795 + 1074308 * 2 ^ 59
def prefixEnd_1074308 : Nat := 4983230072969 + 3 ^ 40 * 1074308 * 2
def baseEnd_1074308 : Nat := 245171722209105777204157

theorem tailTrace_1074308 : CollatzResearch.WordTrace tailWord_1074308 prefixEnd_1074308 245171722209105777204157 := by
  unfold tailWord_1074308
  simp only [CollatzResearch.WordTrace]
  refine ⟨19591615895986534022071789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26122154527982045362762385 19591615895986534022071789)
  ·
    refine ⟨7346855960994950258276921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19591615895986534022071789 7346855960994950258276921)
    ·
      refine ⟨5510141970746212693707691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7346855960994950258276921 5510141970746212693707691)
      ·
        refine ⟨8265212956119319040561537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5510141970746212693707691 8265212956119319040561537)
        ·
          refine ⟨6198909717089489280421153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8265212956119319040561537 6198909717089489280421153)
          ·
            refine ⟨4649182287817116960315865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6198909717089489280421153 4649182287817116960315865)
            ·
              refine ⟨3486886715862837720236899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4649182287817116960315865 3486886715862837720236899)
              ·
                refine ⟨5230330073794256580355349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3486886715862837720236899 5230330073794256580355349)
                ·
                  refine ⟨245171722209105777204157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5230330073794256580355349 245171722209105777204157)
                  ·
                    rfl

theorem cell21_1074308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_1074308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074308 prefixEnd_1074308 := by exact prefixLift 1074308
  have htrace : WordTrace (prefixWord ++ tailWord_1074308) baseStart_1074308 baseEnd_1074308 := by
    simpa [prefixWord, tailWord_1074308, baseEnd_1074308] using wordTrace_append hprefix tailTrace_1074308
  have hstable : (prefixWord ++ tailWord_1074308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074308).length < 2 ^ (prefixWord ++ tailWord_1074308).sum := by decide
  have hdescent : baseEnd_1074308 < baseStart_1074308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074367 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 6]
def baseStart_1074367 : Nat := 118140960795 + 1074367 * 2 ^ 59
def prefixEnd_1074367 : Nat := 4983230072969 + 3 ^ 40 * 1074367 * 2
def baseEnd_1074367 : Nat := 245185186812934785720703

theorem tailTrace_1074367 : CollatzResearch.WordTrace tailWord_1074367 prefixEnd_1074367 245185186812934785720703 := by
  unfold tailWord_1074367
  simp only [CollatzResearch.WordTrace]
  refine ⟨39185383698759321120541355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26123589132506214080360903 39185383698759321120541355)
  ·
    refine ⟨58778075548138981680812033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39185383698759321120541355 58778075548138981680812033)
    ·
      refine ⟨44083556661104236260609025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58778075548138981680812033 44083556661104236260609025)
      ·
        refine ⟨33062667495828177195456769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44083556661104236260609025 33062667495828177195456769)
        ·
          refine ⟨24797000621871132896592577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33062667495828177195456769 24797000621871132896592577)
          ·
            refine ⟨18597750466403349672444433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24797000621871132896592577 18597750466403349672444433)
            ·
              refine ⟨13948312849802512254333325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18597750466403349672444433 13948312849802512254333325)
              ·
                refine ⟨5230617318675942095374997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13948312849802512254333325 5230617318675942095374997)
                ·
                  refine ⟨245185186812934785720703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5230617318675942095374997 245185186812934785720703)
                  ·
                    rfl

theorem cell21_1074367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 6].length) (baseStart_1074367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074367 prefixEnd_1074367 := by exact prefixLift 1074367
  have htrace : WordTrace (prefixWord ++ tailWord_1074367) baseStart_1074367 baseEnd_1074367 := by
    simpa [prefixWord, tailWord_1074367, baseEnd_1074367] using wordTrace_append hprefix tailTrace_1074367
  have hstable : (prefixWord ++ tailWord_1074367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074367).length < 2 ^ (prefixWord ++ tailWord_1074367).sum := by decide
  have hdescent : baseEnd_1074367 < baseStart_1074367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074418 : List Nat := [3, 2, 1, 3, 3, 2, 1, 2, 4]
def baseStart_1074418 : Nat := 118140960795 + 1074418 * 2 ^ 59
def prefixEnd_1074418 : Nat := 4983230072969 + 3 ^ 40 * 1074418 * 2
def baseEnd_1074418 : Nat := 245196825707770030370599

theorem tailTrace_1074418 : CollatzResearch.WordTrace tailWord_1074418 prefixEnd_1074418 245196825707770030370599 := by
  unfold tailWord_1074418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9796810955393639207661977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26124829214383037887098605 9796810955393639207661977)
  ·
    refine ⟨7347608216545229405746483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9796810955393639207661977 7347608216545229405746483)
    ·
      refine ⟨11021412324817844108619725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7347608216545229405746483 11021412324817844108619725)
      ·
        refine ⟨4133029621806691540732397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11021412324817844108619725 4133029621806691540732397)
        ·
          refine ⟨1549886108177509327774649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4133029621806691540732397 1549886108177509327774649)
          ·
            refine ⟨1162414581133131995830987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1549886108177509327774649 1162414581133131995830987)
            ·
              refine ⟨1743621871699697993746481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1162414581133131995830987 1743621871699697993746481)
              ·
                refine ⟨1307716403774773495309861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1743621871699697993746481 1307716403774773495309861)
                ·
                  refine ⟨245196825707770030370599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1307716403774773495309861 245196825707770030370599)
                  ·
                    rfl

theorem cell21_1074418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_1074418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074418 prefixEnd_1074418 := by exact prefixLift 1074418
  have htrace : WordTrace (prefixWord ++ tailWord_1074418) baseStart_1074418 baseEnd_1074418 := by
    simpa [prefixWord, tailWord_1074418, baseEnd_1074418] using wordTrace_append hprefix tailTrace_1074418
  have hstable : (prefixWord ++ tailWord_1074418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074418).length < 2 ^ (prefixWord ++ tailWord_1074418).sum := by decide
  have hdescent : baseEnd_1074418 < baseStart_1074418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074477 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 6]
def baseStart_1074477 : Nat := 118140960795 + 1074477 * 2 ^ 59
def prefixEnd_1074477 : Nat := 4983230072969 + 3 ^ 40 * 1074477 * 2
def baseEnd_1074477 : Nat := 245210290311599038887145

theorem tailTrace_1074477 : CollatzResearch.WordTrace tailWord_1074477 prefixEnd_1074477 245210290311599038887145 := by
  unfold tailWord_1074477
  simp only [CollatzResearch.WordTrace]
  refine ⟨39189395728360809907045685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26126263818907206604697123 39189395728360809907045685)
  ·
    refine ⟨3674005849533825928785533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39189395728360809907045685 3674005849533825928785533)
    ·
      refine ⟨1377752193575184723294575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3674005849533825928785533 1377752193575184723294575)
      ·
        refine ⟨2066628290362777084941863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1377752193575184723294575 2066628290362777084941863)
        ·
          refine ⟨3099942435544165627412795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2066628290362777084941863 3099942435544165627412795)
          ·
            refine ⟨4649913653316248441119193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3099942435544165627412795 4649913653316248441119193)
            ·
              refine ⟨3487435239987186330839395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4649913653316248441119193 3487435239987186330839395)
              ·
                refine ⟨5231152859980779496259093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3487435239987186330839395 5231152859980779496259093)
                ·
                  refine ⟨245210290311599038887145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5231152859980779496259093 245210290311599038887145)
                  ·
                    rfl

theorem cell21_1074477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_1074477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074477 prefixEnd_1074477 := by exact prefixLift 1074477
  have htrace : WordTrace (prefixWord ++ tailWord_1074477) baseStart_1074477 baseEnd_1074477 := by
    simpa [prefixWord, tailWord_1074477, baseEnd_1074477] using wordTrace_append hprefix tailTrace_1074477
  have hstable : (prefixWord ++ tailWord_1074477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074477).length < 2 ^ (prefixWord ++ tailWord_1074477).sum := by decide
  have hdescent : baseEnd_1074477 < baseStart_1074477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074525 : List Nat := [1, 4, 5, 1, 2, 8]
def baseStart_1074525 : Nat := 118140960795 + 1074525 * 2 ^ 59
def prefixEnd_1074525 : Nat := 4983230072969 + 3 ^ 40 * 1074525 * 2
def baseEnd_1074525 : Nat := 9082268317243023040261

theorem tailTrace_1074525 : CollatzResearch.WordTrace tailWord_1074525 prefixEnd_1074525 9082268317243023040261 := by
  unfold tailWord_1074525
  simp only [CollatzResearch.WordTrace]
  refine ⟨39191146432186914104793029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26127430954791276069862019 39191146432186914104793029)
  ·
    refine ⟨7348339956035046394648693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39191146432186914104793029 7348339956035046394648693)
    ·
      refine ⟨688906870878285599498315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7348339956035046394648693 688906870878285599498315)
      ·
        refine ⟨1033360306317428399247473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688906870878285599498315 1033360306317428399247473)
        ·
          refine ⟨775020229738071299435605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1033360306317428399247473 775020229738071299435605)
          ·
            refine ⟨9082268317243023040261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 775020229738071299435605 9082268317243023040261)
            ·
              rfl

theorem cell21_1074525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 8].length) (baseStart_1074525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074525 prefixEnd_1074525 := by exact prefixLift 1074525
  have htrace : WordTrace (prefixWord ++ tailWord_1074525) baseStart_1074525 baseEnd_1074525 := by
    simpa [prefixWord, tailWord_1074525, baseEnd_1074525] using wordTrace_append hprefix tailTrace_1074525
  have hstable : (prefixWord ++ tailWord_1074525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074525).length < 2 ^ (prefixWord ++ tailWord_1074525).sum := by decide
  have hdescent : baseEnd_1074525 < baseStart_1074525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074567 : List Nat := [1, 1, 4, 2, 2, 3, 3, 5]
def baseStart_1074567 : Nat := 118140960795 + 1074567 * 2 ^ 59
def prefixEnd_1074567 : Nat := 4983230072969 + 3 ^ 40 * 1074567 * 2
def baseEnd_1074567 : Nat := 81743609845926294128987

theorem tailTrace_1074567 : CollatzResearch.WordTrace tailWord_1074567 prefixEnd_1074567 81743609845926294128987 := by
  unfold tailWord_1074567
  simp only [CollatzResearch.WordTrace]
  refine ⟨39192678298034755277821955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26128452198689836851881303 39192678298034755277821955)
  ·
    refine ⟨58789017447052132916732933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39192678298034755277821955 58789017447052132916732933)
    ·
      refine ⟨11022940771322274921887425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58789017447052132916732933 11022940771322274921887425)
      ·
        refine ⟨8267205578491706191415569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11022940771322274921887425 8267205578491706191415569)
        ·
          refine ⟨6200404183868779643561677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8267205578491706191415569 6200404183868779643561677)
          ·
            refine ⟨2325151568950792366335629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6200404183868779643561677 2325151568950792366335629)
            ·
              refine ⟨871931838356547137375861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2325151568950792366335629 871931838356547137375861)
              ·
                refine ⟨81743609845926294128987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 871931838356547137375861 81743609845926294128987)
                ·
                  rfl

theorem cell21_1074567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 5].length) (baseStart_1074567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074567 prefixEnd_1074567 := by exact prefixLift 1074567
  have htrace : WordTrace (prefixWord ++ tailWord_1074567) baseStart_1074567 baseEnd_1074567 := by
    simpa [prefixWord, tailWord_1074567, baseEnd_1074567] using wordTrace_append hprefix tailTrace_1074567
  have hstable : (prefixWord ++ tailWord_1074567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074567).length < 2 ^ (prefixWord ++ tailWord_1074567).sum := by decide
  have hdescent : baseEnd_1074567 < baseStart_1074567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074595 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 6]
def baseStart_1074595 : Nat := 118140960795 + 1074595 * 2 ^ 59
def prefixEnd_1074595 : Nat := 4983230072969 + 3 ^ 40 * 1074595 * 2
def baseEnd_1074595 : Nat := 245237219519257055920237

theorem tailTrace_1074595 : CollatzResearch.WordTrace tailWord_1074595 prefixEnd_1074595 245237219519257055920237 := by
  unfold tailWord_1074595
  simp only [CollatzResearch.WordTrace]
  refine ⟨39193699541933316059841239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26129133027955544039894159 39193699541933316059841239)
  ·
    refine ⟨58790549312899974089761859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39193699541933316059841239 58790549312899974089761859)
    ·
      refine ⟨88185823969349961134642789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58790549312899974089761859 88185823969349961134642789)
      ·
        refine ⟨16534841994253117712745523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88185823969349961134642789 16534841994253117712745523)
        ·
          refine ⟨24802262991379676569118285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16534841994253117712745523 24802262991379676569118285)
          ·
            refine ⟨9300848621767378713419357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24802262991379676569118285 9300848621767378713419357)
            ·
              refine ⟨3487818233162767017532259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9300848621767378713419357 3487818233162767017532259)
              ·
                refine ⟨5231727349744150526298389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3487818233162767017532259 5231727349744150526298389)
                ·
                  refine ⟨245237219519257055920237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5231727349744150526298389 245237219519257055920237)
                  ·
                    rfl

theorem cell21_1074595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 6].length) (baseStart_1074595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074595 prefixEnd_1074595 := by exact prefixLift 1074595
  have htrace : WordTrace (prefixWord ++ tailWord_1074595) baseStart_1074595 baseEnd_1074595 := by
    simpa [prefixWord, tailWord_1074595, baseEnd_1074595] using wordTrace_append hprefix tailTrace_1074595
  have hstable : (prefixWord ++ tailWord_1074595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074595).length < 2 ^ (prefixWord ++ tailWord_1074595).sum := by decide
  have hdescent : baseEnd_1074595 < baseStart_1074595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074657 : List Nat := [1, 2, 3, 1, 2, 3, 3, 1, 5]
def baseStart_1074657 : Nat := 118140960795 + 1074657 * 2 ^ 59
def prefixEnd_1074657 : Nat := 4983230072969 + 3 ^ 40 * 1074657 * 2
def baseEnd_1074657 : Nat := 245251368763958725886777

theorem tailTrace_1074657 : CollatzResearch.WordTrace tailWord_1074657 prefixEnd_1074657 245251368763958725886777 := by
  unfold tailWord_1074657
  simp only [CollatzResearch.WordTrace]
  refine ⟨39195960867708700648598225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26130640578472467099065483 39195960867708700648598225)
  ·
    refine ⟨29396970650781525486448669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39195960867708700648598225 29396970650781525486448669)
    ·
      refine ⟨11023863994043072057418251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29396970650781525486448669 11023863994043072057418251)
      ·
        refine ⟨16535795991064608086127377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11023863994043072057418251 16535795991064608086127377)
        ·
          refine ⟨12401846993298456064595533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16535795991064608086127377 12401846993298456064595533)
          ·
            refine ⟨4650692622486921024223325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12401846993298456064595533 4650692622486921024223325)
            ·
              refine ⟨1744009733432595384083747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4650692622486921024223325 1744009733432595384083747)
              ·
                refine ⟨2616014600148893076125621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1744009733432595384083747 2616014600148893076125621)
                ·
                  refine ⟨245251368763958725886777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2616014600148893076125621 245251368763958725886777)
                  ·
                    rfl

theorem cell21_1074657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_1074657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074657 prefixEnd_1074657 := by exact prefixLift 1074657
  have htrace : WordTrace (prefixWord ++ tailWord_1074657) baseStart_1074657 baseEnd_1074657 := by
    simpa [prefixWord, tailWord_1074657, baseEnd_1074657] using wordTrace_append hprefix tailTrace_1074657
  have hstable : (prefixWord ++ tailWord_1074657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074657).length < 2 ^ (prefixWord ++ tailWord_1074657).sum := by decide
  have hdescent : baseEnd_1074657 < baseStart_1074657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074702 : List Nat := [4, 1, 1, 2, 4, 9]
def baseStart_1074702 : Nat := 118140960795 + 1074702 * 2 ^ 59
def prefixEnd_1074702 : Nat := 4983230072969 + 3 ^ 40 * 1074702 * 2
def baseEnd_1074702 : Nat := 9083764384335135097655

theorem tailTrace_1074702 : CollatzResearch.WordTrace tailWord_1074702 prefixEnd_1074702 9083764384335135097655 := by
  unfold tailWord_1074702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4899700269068209166748295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26131734768363782222657573 4899700269068209166748295)
  ·
    refine ⟨7349550403602313750122443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4899700269068209166748295 7349550403602313750122443)
    ·
      refine ⟨11024325605403470625183665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7349550403602313750122443 11024325605403470625183665)
      ·
        refine ⟨8268244204052602968887749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11024325605403470625183665 8268244204052602968887749)
        ·
          refine ⟨1550295788259863056666453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8268244204052602968887749 1550295788259863056666453)
          ·
            refine ⟨9083764384335135097655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1550295788259863056666453 9083764384335135097655)
            ·
              rfl

theorem cell21_1074702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 9].length) (baseStart_1074702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074702 prefixEnd_1074702 := by exact prefixLift 1074702
  have htrace : WordTrace (prefixWord ++ tailWord_1074702) baseStart_1074702 baseEnd_1074702 := by
    simpa [prefixWord, tailWord_1074702, baseEnd_1074702] using wordTrace_append hprefix tailTrace_1074702
  have hstable : (prefixWord ++ tailWord_1074702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074702).length < 2 ^ (prefixWord ++ tailWord_1074702).sum := by decide
  have hdescent : baseEnd_1074702 < baseStart_1074702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074708 : List Nat := [2, 4, 3, 1, 2, 1, 1, 4, 3]
def baseStart_1074708 : Nat := 118140960795 + 1074708 * 2 ^ 59
def prefixEnd_1074708 : Nat := 4983230072969 + 3 ^ 40 * 1074708 * 2
def baseEnd_1074708 : Nat := 245263007658793970536673

theorem tailTrace_1074708 : CollatzResearch.WordTrace tailWord_1074708 prefixEnd_1074708 245263007658793970536673 := by
  unfold tailWord_1074708
  simp only [CollatzResearch.WordTrace]
  refine ⟨19598910495261968179352389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26131880660349290905803185 19598910495261968179352389)
  ·
    refine ⟨3674795717861619033628573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19598910495261968179352389 3674795717861619033628573)
    ·
      refine ⟨1378048394198107137610715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3674795717861619033628573 1378048394198107137610715)
      ·
        refine ⟨2067072591297160706416073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1378048394198107137610715 2067072591297160706416073)
        ·
          refine ⟨1550304443472870529812055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2067072591297160706416073 1550304443472870529812055)
          ·
            refine ⟨2325456665209305794718083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550304443472870529812055 2325456665209305794718083)
            ·
              refine ⟨3488184997813958692077125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2325456665209305794718083 3488184997813958692077125)
              ·
                refine ⟨654034687090117254764461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3488184997813958692077125 654034687090117254764461)
                ·
                  refine ⟨245263007658793970536673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 654034687090117254764461 245263007658793970536673)
                  ·
                    rfl

theorem cell21_1074708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_1074708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074708 prefixEnd_1074708 := by exact prefixLift 1074708
  have htrace : WordTrace (prefixWord ++ tailWord_1074708) baseStart_1074708 baseEnd_1074708 := by
    simpa [prefixWord, tailWord_1074708, baseEnd_1074708] using wordTrace_append hprefix tailTrace_1074708
  have hstable : (prefixWord ++ tailWord_1074708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074708).length < 2 ^ (prefixWord ++ tailWord_1074708).sum := by decide
  have hdescent : baseEnd_1074708 < baseStart_1074708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074764 : List Nat := [2, 2, 1, 3, 1, 3, 3, 2, 4]
def baseStart_1074764 : Nat := 118140960795 + 1074764 * 2 ^ 59
def prefixEnd_1074764 : Nat := 4983230072969 + 3 ^ 40 * 1074764 * 2
def baseEnd_1074764 : Nat := 245275787621750317603225

theorem tailTrace_1074764 : CollatzResearch.WordTrace tailWord_1074764 prefixEnd_1074764 245275787621750317603225 := by
  unfold tailWord_1074764
  simp only [CollatzResearch.WordTrace]
  refine ⟨19599931739160528961371673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26133242318880705281828897 19599931739160528961371673)
  ·
    refine ⟨14699948804370396721028755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19599931739160528961371673 14699948804370396721028755)
    ·
      refine ⟨22049923206555595081543133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14699948804370396721028755 22049923206555595081543133)
      ·
        refine ⟨8268721202458348155578675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22049923206555595081543133 8268721202458348155578675)
        ·
          refine ⟨12403081803687522233368013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8268721202458348155578675 12403081803687522233368013)
          ·
            refine ⟨4651155676382820837513005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12403081803687522233368013 4651155676382820837513005)
            ·
              refine ⟨1744183378643557814067377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4651155676382820837513005 1744183378643557814067377)
              ·
                refine ⟨1308137533982668360550533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1744183378643557814067377 1308137533982668360550533)
                ·
                  refine ⟨245275787621750317603225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1308137533982668360550533 245275787621750317603225)
                  ·
                    rfl

theorem cell21_1074764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_1074764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074764 prefixEnd_1074764 := by exact prefixLift 1074764
  have htrace : WordTrace (prefixWord ++ tailWord_1074764) baseStart_1074764 baseEnd_1074764 := by
    simpa [prefixWord, tailWord_1074764, baseEnd_1074764] using wordTrace_append hprefix tailTrace_1074764
  have hstable : (prefixWord ++ tailWord_1074764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074764).length < 2 ^ (prefixWord ++ tailWord_1074764).sum := by decide
  have hdescent : baseEnd_1074764 < baseStart_1074764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074823 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 6]
def baseStart_1074823 : Nat := 118140960795 + 1074823 * 2 ^ 59
def prefixEnd_1074823 : Nat := 4983230072969 + 3 ^ 40 * 1074823 * 2
def baseEnd_1074823 : Nat := 245289252225579326119771

theorem tailTrace_1074823 : CollatzResearch.WordTrace tailWord_1074823 prefixEnd_1074823 245289252225579326119771 := by
  unfold tailWord_1074823
  simp only [CollatzResearch.WordTrace]
  refine ⟨39202015385107310999141123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26134676923404873999427415 39202015385107310999141123)
  ·
    refine ⟨58803023077660966498711685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39202015385107310999141123 58803023077660966498711685)
    ·
      refine ⟨11025566827061431218508441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58803023077660966498711685 11025566827061431218508441)
      ·
        refine ⟨8269175120296073413881331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11025566827061431218508441 8269175120296073413881331)
        ·
          refine ⟨12403762680444110120821997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8269175120296073413881331 12403762680444110120821997)
          ·
            refine ⟨4651411005166541295308249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12403762680444110120821997 4651411005166541295308249)
            ·
              refine ⟨3488558253874905971481187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4651411005166541295308249 3488558253874905971481187)
              ·
                refine ⟨5232837380812358957221781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3488558253874905971481187 5232837380812358957221781)
                ·
                  refine ⟨245289252225579326119771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5232837380812358957221781 245289252225579326119771)
                  ·
                    rfl

theorem cell21_1074823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 6].length) (baseStart_1074823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074823 prefixEnd_1074823 := by exact prefixLift 1074823
  have htrace : WordTrace (prefixWord ++ tailWord_1074823) baseStart_1074823 baseEnd_1074823 := by
    simpa [prefixWord, tailWord_1074823, baseEnd_1074823] using wordTrace_append hprefix tailTrace_1074823
  have hstable : (prefixWord ++ tailWord_1074823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074823).length < 2 ^ (prefixWord ++ tailWord_1074823).sum := by decide
  have hdescent : baseEnd_1074823 < baseStart_1074823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074826 : List Nat := [3, 1, 2, 3, 2, 3, 1, 1, 5]
def baseStart_1074826 : Nat := 118140960795 + 1074826 * 2 ^ 59
def prefixEnd_1074826 : Nat := 4983230072969 + 3 ^ 40 * 1074826 * 2
def baseEnd_1074826 : Nat := 245289936866451987569765

theorem tailTrace_1074826 : CollatzResearch.WordTrace tailWord_1074826 prefixEnd_1074826 245289936866451987569765 := by
  unfold tailWord_1074826
  simp only [CollatzResearch.WordTrace]
  refine ⟨9800531201024110627875083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26134749869397628341000221 9800531201024110627875083)
  ·
    refine ⟨14700796801536165941812625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9800531201024110627875083 14700796801536165941812625)
    ·
      refine ⟨11025597601152124456359469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14700796801536165941812625 11025597601152124456359469)
      ·
        refine ⟨4134599100432046671134801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11025597601152124456359469 4134599100432046671134801)
        ·
          refine ⟨3100949325324035003351101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4134599100432046671134801 3100949325324035003351101)
          ·
            refine ⟨1162855996996513126256663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3100949325324035003351101 1162855996996513126256663)
            ·
              refine ⟨1744283995494769689384995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1162855996996513126256663 1744283995494769689384995)
              ·
                refine ⟨2616425993242154534077493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1744283995494769689384995 2616425993242154534077493)
                ·
                  refine ⟨245289936866451987569765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2616425993242154534077493 245289936866451987569765)
                  ·
                    rfl

theorem cell21_1074826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_1074826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074826 prefixEnd_1074826 := by exact prefixLift 1074826
  have htrace : WordTrace (prefixWord ++ tailWord_1074826) baseStart_1074826 baseEnd_1074826 := by
    simpa [prefixWord, tailWord_1074826, baseEnd_1074826] using wordTrace_append hprefix tailTrace_1074826
  have hstable : (prefixWord ++ tailWord_1074826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074826).length < 2 ^ (prefixWord ++ tailWord_1074826).sum := by decide
  have hdescent : baseEnd_1074826 < baseStart_1074826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074840 : List Nat := [2, 1, 2, 4, 1, 3, 1, 3, 4]
def baseStart_1074840 : Nat := 118140960795 + 1074840 * 2 ^ 59
def prefixEnd_1074840 : Nat := 4983230072969 + 3 ^ 40 * 1074840 * 2
def baseEnd_1074840 : Nat := 245293131857191074336403

theorem tailTrace_1074840 : CollatzResearch.WordTrace tailWord_1074840 prefixEnd_1074840 245293131857191074336403 := by
  unfold tailWord_1074840
  simp only [CollatzResearch.WordTrace]
  refine ⟨19601317713022861451254987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26135090284030481935006649 19601317713022861451254987)
  ·
    refine ⟨29401976569534292176882481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19601317713022861451254987 29401976569534292176882481)
    ·
      refine ⟨22051482427150719132661861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29401976569534292176882481 22051482427150719132661861)
      ·
        refine ⟨4134652955090759837374099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22051482427150719132661861 4134652955090759837374099)
        ·
          refine ⟨6201979432636139756061149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4134652955090759837374099 6201979432636139756061149)
          ·
            refine ⟨2325742287238552408522931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6201979432636139756061149 2325742287238552408522931)
            ·
              refine ⟨3488613430857828612784397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2325742287238552408522931 3488613430857828612784397)
              ·
                refine ⟨1308230036571685729794149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3488613430857828612784397 1308230036571685729794149)
                ·
                  refine ⟨245293131857191074336403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1308230036571685729794149 245293131857191074336403)
                  ·
                    rfl

theorem cell21_1074840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_1074840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074840 prefixEnd_1074840 := by exact prefixLift 1074840
  have htrace : WordTrace (prefixWord ++ tailWord_1074840) baseStart_1074840 baseEnd_1074840 := by
    simpa [prefixWord, tailWord_1074840, baseEnd_1074840] using wordTrace_append hprefix tailTrace_1074840
  have hstable : (prefixWord ++ tailWord_1074840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074840).length < 2 ^ (prefixWord ++ tailWord_1074840).sum := by decide
  have hdescent : baseEnd_1074840 < baseStart_1074840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074885 : List Nat := [1, 3, 1, 1, 1, 1, 2, 8, 3]
def baseStart_1074885 : Nat := 118140960795 + 1074885 * 2 ^ 59
def prefixEnd_1074885 : Nat := 4983230072969 + 3 ^ 40 * 1074885 * 2
def baseEnd_1074885 : Nat := 245303401470280996086311

theorem tailTrace_1074885 : CollatzResearch.WordTrace tailWord_1074885 prefixEnd_1074885 245303401470280996086311 := by
  unfold tailWord_1074885
  simp only [CollatzResearch.WordTrace]
  refine ⟨39204276710882695587898109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26136184473921797058598739 39204276710882695587898109)
  ·
    refine ⟨14701603766581010845461791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39204276710882695587898109 14701603766581010845461791)
    ·
      refine ⟨22052405649871516268192687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14701603766581010845461791 22052405649871516268192687)
      ·
        refine ⟨33078608474807274402289031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22052405649871516268192687 33078608474807274402289031)
        ·
          refine ⟨49617912712210911603433547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33078608474807274402289031 49617912712210911603433547)
          ·
            refine ⟨74426869068316367405150321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49617912712210911603433547 74426869068316367405150321)
            ·
              refine ⟨55820151801237275553862741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74426869068316367405150321 55820151801237275553862741)
              ·
                refine ⟨654142403920749322896829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 55820151801237275553862741 654142403920749322896829)
                ·
                  refine ⟨245303401470280996086311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 654142403920749322896829 245303401470280996086311)
                  ·
                    rfl

theorem cell21_1074885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_1074885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074885 prefixEnd_1074885 := by exact prefixLift 1074885
  have htrace : WordTrace (prefixWord ++ tailWord_1074885) baseStart_1074885 baseEnd_1074885 := by
    simpa [prefixWord, tailWord_1074885, baseEnd_1074885] using wordTrace_append hprefix tailTrace_1074885
  have hstable : (prefixWord ++ tailWord_1074885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074885).length < 2 ^ (prefixWord ++ tailWord_1074885).sum := by decide
  have hdescent : baseEnd_1074885 < baseStart_1074885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1074995 : List Nat := [1, 1, 1, 2, 7, 1, 3, 2, 3]
def baseStart_1074995 : Nat := 118140960795 + 1074995 * 2 ^ 59
def prefixEnd_1074995 : Nat := 4983230072969 + 3 ^ 40 * 1074995 * 2
def baseEnd_1074995 : Nat := 245328504968945249252753

theorem tailTrace_1074995 : CollatzResearch.WordTrace tailWord_1074995 prefixEnd_1074995 245328504968945249252753 := by
  unfold tailWord_1074995
  simp only [CollatzResearch.WordTrace]
  refine ⟨39208288740484184374402439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26138859160322789582934959 39208288740484184374402439)
  ·
    refine ⟨58812433110726276561603659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39208288740484184374402439 58812433110726276561603659)
    ·
      refine ⟨88218649666089414842405489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58812433110726276561603659 88218649666089414842405489)
      ·
        refine ⟨66163987249567061131804117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88218649666089414842405489 66163987249567061131804117)
        ·
          refine ⟨1550718451161727995276659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 66163987249567061131804117 1550718451161727995276659)
          ·
            refine ⟨2326077676742591992914989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550718451161727995276659 2326077676742591992914989)
            ·
              refine ⟨872279128778471997343121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2326077676742591992914989 872279128778471997343121)
              ·
                refine ⟨654209346583853998007341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 872279128778471997343121 654209346583853998007341)
                ·
                  refine ⟨245328504968945249252753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 654209346583853998007341 245328504968945249252753)
                  ·
                    rfl

theorem cell21_1074995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 3].length) (baseStart_1074995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1074995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1074995 prefixEnd_1074995 := by exact prefixLift 1074995
  have htrace : WordTrace (prefixWord ++ tailWord_1074995) baseStart_1074995 baseEnd_1074995 := by
    simpa [prefixWord, tailWord_1074995, baseEnd_1074995] using wordTrace_append hprefix tailTrace_1074995
  have hstable : (prefixWord ++ tailWord_1074995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1074995).length < 2 ^ (prefixWord ++ tailWord_1074995).sum := by decide
  have hdescent : baseEnd_1074995 < baseStart_1074995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1074995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075006 : List Nat := [4, 2, 1, 2, 2, 1, 1, 8]
def baseStart_1075006 : Nat := 118140960795 + 1075006 * 2 ^ 59
def prefixEnd_1075006 : Nat := 4983230072969 + 3 ^ 40 * 1075006 * 2
def baseEnd_1075006 : Nat := 81777005106270558189799

theorem tailTrace_1075006 : CollatzResearch.WordTrace tailWord_1075006 prefixEnd_1075006 81777005106270558189799 := by
  unfold tailWord_1075006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4901086242930541656631609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26139126628962888835368581 4901086242930541656631609)
  ·
    refine ⟨3675814682197906242473707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4901086242930541656631609 3675814682197906242473707)
    ·
      refine ⟨5513722023296859363710561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3675814682197906242473707 5513722023296859363710561)
      ·
        refine ⟨4135291517472644522782921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5513722023296859363710561 4135291517472644522782921)
        ·
          refine ⟨3101468638104483392087191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4135291517472644522782921 3101468638104483392087191)
          ·
            refine ⟨4652202957156725088130787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3101468638104483392087191 4652202957156725088130787)
            ·
              refine ⟨6978304435735087632196181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4652202957156725088130787 6978304435735087632196181)
              ·
                refine ⟨81777005106270558189799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6978304435735087632196181 81777005106270558189799)
                ·
                  rfl

theorem cell21_1075006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_1075006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1075006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1075006 prefixEnd_1075006 := by exact prefixLift 1075006
  have htrace : WordTrace (prefixWord ++ tailWord_1075006) baseStart_1075006 baseEnd_1075006 := by
    simpa [prefixWord, tailWord_1075006, baseEnd_1075006] using wordTrace_append hprefix tailTrace_1075006
  have hstable : (prefixWord ++ tailWord_1075006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075006).length < 2 ^ (prefixWord ++ tailWord_1075006).sum := by decide
  have hdescent : baseEnd_1075006 < baseStart_1075006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075164 : List Nat := [2, 2, 6, 1, 1, 2, 1, 1, 5]
def baseStart_1075164 : Nat := 118140960795 + 1075164 * 2 ^ 59
def prefixEnd_1075164 : Nat := 4983230072969 + 3 ^ 40 * 1075164 * 2
def baseEnd_1075164 : Nat := 245367073071438510935741

theorem tailTrace_1075164 : CollatzResearch.WordTrace tailWord_1075164 prefixEnd_1075164 245367073071438510935741 := by
  unfold tailWord_1075164
  simp only [CollatzResearch.WordTrace]
  refine ⟨19607226338435963118652273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26142968451247950824869697 19607226338435963118652273)
  ·
    refine ⟨14705419753826972338989205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19607226338435963118652273 14705419753826972338989205)
    ·
      refine ⟨689316550960639328390119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14705419753826972338989205 689316550960639328390119)
      ·
        refine ⟨1033974826440958992585179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 689316550960639328390119 1033974826440958992585179)
        ·
          refine ⟨1550962239661438488877769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1033974826440958992585179 1550962239661438488877769)
          ·
            refine ⟨1163221679746078866658327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1550962239661438488877769 1163221679746078866658327)
            ·
              refine ⟨1744832519619118299987491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1163221679746078866658327 1744832519619118299987491)
              ·
                refine ⟨2617248779428677449981237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1744832519619118299987491 2617248779428677449981237)
                ·
                  refine ⟨245367073071438510935741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2617248779428677449981237 245367073071438510935741)
                  ·
                    rfl

theorem cell21_1075164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_1075164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1075164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1075164 prefixEnd_1075164 := by exact prefixLift 1075164
  have htrace : WordTrace (prefixWord ++ tailWord_1075164) baseStart_1075164 baseEnd_1075164 := by
    simpa [prefixWord, tailWord_1075164, baseEnd_1075164] using wordTrace_append hprefix tailTrace_1075164
  have hstable : (prefixWord ++ tailWord_1075164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075164).length < 2 ^ (prefixWord ++ tailWord_1075164).sum := by decide
  have hdescent : baseEnd_1075164 < baseStart_1075164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075248 : List Nat := [2, 1, 1, 1, 2, 6, 1, 2, 5]
def baseStart_1075248 : Nat := 118140960795 + 1075248 * 2 ^ 59
def prefixEnd_1075248 : Nat := 4983230072969 + 3 ^ 40 * 1075248 * 2
def baseEnd_1075248 : Nat := 245386243015873031535569

theorem tailTrace_1075248 : CollatzResearch.WordTrace tailWord_1075248 prefixEnd_1075248 245386243015873031535569 := by
  unfold tailWord_1075248
  simp only [CollatzResearch.WordTrace]
  refine ⟨19608758204283804291681199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26145010939045072388908265 19608758204283804291681199)
  ·
    refine ⟨29413137306425706437521799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19608758204283804291681199 29413137306425706437521799)
    ·
      refine ⟨44119705959638559656282699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29413137306425706437521799 44119705959638559656282699)
      ·
        refine ⟨66179558939457839484424049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44119705959638559656282699 66179558939457839484424049)
        ·
          refine ⟨49634669204593379613318037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66179558939457839484424049 49634669204593379613318037)
          ·
            refine ⟨2326625118965314669374283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49634669204593379613318037 2326625118965314669374283)
            ·
              refine ⟨3489937678447972004061425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2326625118965314669374283 3489937678447972004061425)
              ·
                refine ⟨2617453258835979003046069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3489937678447972004061425 2617453258835979003046069)
                ·
                  refine ⟨245386243015873031535569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2617453258835979003046069 245386243015873031535569)
                  ·
                    rfl

theorem cell21_1075248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_1075248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1075248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1075248 prefixEnd_1075248 := by exact prefixLift 1075248
  have htrace : WordTrace (prefixWord ++ tailWord_1075248) baseStart_1075248 baseEnd_1075248 := by
    simpa [prefixWord, tailWord_1075248, baseEnd_1075248] using wordTrace_append hprefix tailTrace_1075248
  have hstable : (prefixWord ++ tailWord_1075248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075248).length < 2 ^ (prefixWord ++ tailWord_1075248).sum := by decide
  have hdescent : baseEnd_1075248 < baseStart_1075248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075296 : List Nat := [2, 1, 1, 3, 2, 4, 3, 1, 4]
def baseStart_1075296 : Nat := 118140960795 + 1075296 * 2 ^ 59
def prefixEnd_1075296 : Nat := 4983230072969 + 3 ^ 40 * 1075296 * 2
def baseEnd_1075296 : Nat := 245397197269835614735471

theorem tailTrace_1075296 : CollatzResearch.WordTrace tailWord_1075296 prefixEnd_1075296 245397197269835614735471 := by
  unfold tailWord_1075296
  simp only [CollatzResearch.WordTrace]
  refine ⟨19609633556196856390554871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26146178074929141854073161 19609633556196856390554871)
  ·
    refine ⟨29414450334295284585832307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19609633556196856390554871 29414450334295284585832307)
    ·
      refine ⟨44121675501442926878748461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29414450334295284585832307 44121675501442926878748461)
      ·
        refine ⟨16545628313041097579530673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44121675501442926878748461 16545628313041097579530673)
        ·
          refine ⟨12409221234780823184648005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16545628313041097579530673 12409221234780823184648005)
          ·
            refine ⟨2326728981521404347121501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12409221234780823184648005 2326728981521404347121501)
            ·
              refine ⟨872523368070526630170563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2326728981521404347121501 872523368070526630170563)
              ·
                refine ⟨1308785052105789945255845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872523368070526630170563 1308785052105789945255845)
                ·
                  refine ⟨245397197269835614735471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1308785052105789945255845 245397197269835614735471)
                  ·
                    rfl

theorem cell21_1075296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 4].length) (baseStart_1075296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1075296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1075296 prefixEnd_1075296 := by exact prefixLift 1075296
  have htrace : WordTrace (prefixWord ++ tailWord_1075296) baseStart_1075296 baseEnd_1075296 := by
    simpa [prefixWord, tailWord_1075296, baseEnd_1075296] using wordTrace_append hprefix tailTrace_1075296
  have hstable : (prefixWord ++ tailWord_1075296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075296).length < 2 ^ (prefixWord ++ tailWord_1075296).sum := by decide
  have hdescent : baseEnd_1075296 < baseStart_1075296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075420 : List Nat := [2, 2, 5, 2, 1, 1, 3, 5]
def baseStart_1075420 : Nat := 118140960795 + 1075420 * 2 ^ 59
def prefixEnd_1075420 : Nat := 4983230072969 + 3 ^ 40 * 1075420 * 2
def baseEnd_1075420 : Nat := 81808498586412984889517

theorem tailTrace_1075420 : CollatzResearch.WordTrace tailWord_1075420 prefixEnd_1075420 81808498586412984889517 := by
  unfold tailWord_1075420
  simp only [CollatzResearch.WordTrace]
  refine ⟨19611894881972240979311857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26149193175962987972415809 19611894881972240979311857)
  ·
    refine ⟨14708921161479180734483893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19611894881972240979311857 14708921161479180734483893)
    ·
      refine ⟨1378961358888673193857865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14708921161479180734483893 1378961358888673193857865)
      ·
        refine ⟨1034221019166504895393399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1378961358888673193857865 1034221019166504895393399)
        ·
          refine ⟨1551331528749757343090099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034221019166504895393399 1551331528749757343090099)
          ·
            refine ⟨2326997293124636014635149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551331528749757343090099 2326997293124636014635149)
            ·
              refine ⟨872623984921738505488181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2326997293124636014635149 872623984921738505488181)
              ·
                refine ⟨81808498586412984889517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 872623984921738505488181 81808498586412984889517)
                ·
                  rfl

theorem cell21_1075420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 5].length) (baseStart_1075420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1075420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1075420 prefixEnd_1075420 := by exact prefixLift 1075420
  have htrace : WordTrace (prefixWord ++ tailWord_1075420) baseStart_1075420 baseEnd_1075420 := by
    simpa [prefixWord, tailWord_1075420, baseEnd_1075420] using wordTrace_append hprefix tailTrace_1075420
  have hstable : (prefixWord ++ tailWord_1075420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075420).length < 2 ^ (prefixWord ++ tailWord_1075420).sum := by decide
  have hdescent : baseEnd_1075420 < baseStart_1075420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075580 : List Nat := [2, 2, 2, 1, 1, 1, 2, 10]
def baseStart_1075580 : Nat := 118140960795 + 1075580 * 2 ^ 59
def prefixEnd_1075580 : Nat := 4983230072969 + 3 ^ 40 * 1075580 * 2
def baseEnd_1075580 : Nat := 81820669979704744000519

theorem tailTrace_1075580 : CollatzResearch.WordTrace tailWord_1075580 prefixEnd_1075580 81820669979704744000519 := by
  unfold tailWord_1075580
  simp only [CollatzResearch.WordTrace]
  refine ⟨19614812721682414642224097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26153083628909886189632129 19614812721682414642224097)
  ·
    refine ⟨14711109541261810981668073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19614812721682414642224097 14711109541261810981668073)
    ·
      refine ⟨11033332155946358236251055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14711109541261810981668073 11033332155946358236251055)
      ·
        refine ⟨16549998233919537354376583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11033332155946358236251055 16549998233919537354376583)
        ·
          refine ⟨24824997350879306031564875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16549998233919537354376583 24824997350879306031564875)
          ·
            refine ⟨37237496026318959047347313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24824997350879306031564875 37237496026318959047347313)
            ·
              refine ⟨27928122019739219285510485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37237496026318959047347313 27928122019739219285510485)
              ·
                refine ⟨81820669979704744000519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27928122019739219285510485 81820669979704744000519)
                ·
                  rfl

theorem cell21_1075580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 10].length) (baseStart_1075580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1075580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1075580 prefixEnd_1075580 := by exact prefixLift 1075580
  have htrace : WordTrace (prefixWord ++ tailWord_1075580) baseStart_1075580 baseEnd_1075580 := by
    simpa [prefixWord, tailWord_1075580, baseEnd_1075580] using wordTrace_append hprefix tailTrace_1075580
  have hstable : (prefixWord ++ tailWord_1075580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075580).length < 2 ^ (prefixWord ++ tailWord_1075580).sum := by decide
  have hdescent : baseEnd_1075580 < baseStart_1075580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075586 : List Nat := [3, 4, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1075586 : Nat := 118140960795 + 1075586 * 2 ^ 59
def prefixEnd_1075586 : Nat := 4983230072969 + 3 ^ 40 * 1075586 * 2
def baseEnd_1075586 : Nat := 245463379220859554901545

theorem tailTrace_1075586 : CollatzResearch.WordTrace tailWord_1075586 prefixEnd_1075586 245463379220859554901545 := by
  unfold tailWord_1075586
  simp only [CollatzResearch.WordTrace]
  refine ⟨9807461070335773077291653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26153229520895394872777741 9807461070335773077291653)
  ·
    refine ⟨1838898950687957451992185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9807461070335773077291653 1838898950687957451992185)
    ·
      refine ⟨1379174213015968088994139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1838898950687957451992185 1379174213015968088994139)
      ·
        refine ⟨2068761319523952133491209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1379174213015968088994139 2068761319523952133491209)
        ·
          refine ⟨1551570989642964100118407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2068761319523952133491209 1551570989642964100118407)
          ·
            refine ⟨2327356484464446150177611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551570989642964100118407 2327356484464446150177611)
            ·
              refine ⟨3491034726696669225266417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2327356484464446150177611 3491034726696669225266417)
              ·
                refine ⟨2618276045022501918949813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3491034726696669225266417 2618276045022501918949813)
                ·
                  refine ⟨245463379220859554901545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2618276045022501918949813 245463379220859554901545)
                  ·
                    rfl

theorem cell21_1075586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1075586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1075586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1075586 prefixEnd_1075586 := by exact prefixLift 1075586
  have htrace : WordTrace (prefixWord ++ tailWord_1075586) baseStart_1075586 baseEnd_1075586 := by
    simpa [prefixWord, tailWord_1075586, baseEnd_1075586] using wordTrace_append hprefix tailTrace_1075586
  have hstable : (prefixWord ++ tailWord_1075586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075586).length < 2 ^ (prefixWord ++ tailWord_1075586).sum := by decide
  have hdescent : baseEnd_1075586 < baseStart_1075586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075614 : List Nat := [4, 3, 1, 2, 1, 2, 8]
def baseStart_1075614 : Nat := 118140960795 + 1075614 * 2 ^ 59
def prefixEnd_1075614 : Nat := 4983230072969 + 3 ^ 40 * 1075614 * 2
def baseEnd_1075614 : Nat := 27274418800259747603869

theorem tailTrace_1075614 : CollatzResearch.WordTrace tailWord_1075614 prefixEnd_1075614 27274418800259747603869 := by
  unfold tailWord_1075614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4903858190655206636398237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26153910350161102060790597 4903858190655206636398237)
  ·
    refine ⟨1838946821495702488649339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4903858190655206636398237 1838946821495702488649339)
    ·
      refine ⟨2758420232243553732974009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1838946821495702488649339 2758420232243553732974009)
      ·
        refine ⟨2068815174182665299730507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2758420232243553732974009 2068815174182665299730507)
        ·
          refine ⟨3103222761273997949595761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2068815174182665299730507 3103222761273997949595761)
          ·
            refine ⟨2327417070955498462196821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3103222761273997949595761 2327417070955498462196821)
            ·
              refine ⟨27274418800259747603869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2327417070955498462196821 27274418800259747603869)
              ·
                rfl

theorem cell21_1075614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 8].length) (baseStart_1075614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1075614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1075614 prefixEnd_1075614 := by exact prefixLift 1075614
  have htrace : WordTrace (prefixWord ++ tailWord_1075614) baseStart_1075614 baseEnd_1075614 := by
    simpa [prefixWord, tailWord_1075614, baseEnd_1075614] using wordTrace_append hprefix tailTrace_1075614
  have hstable : (prefixWord ++ tailWord_1075614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075614).length < 2 ^ (prefixWord ++ tailWord_1075614).sum := by decide
  have hdescent : baseEnd_1075614 < baseStart_1075614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075617 : List Nat := [1, 2, 3, 5, 1, 2, 1, 2, 4]
def baseStart_1075617 : Nat := 118140960795 + 1075617 * 2 ^ 59
def prefixEnd_1075617 : Nat := 4983230072969 + 3 ^ 40 * 1075617 * 2
def baseEnd_1075617 : Nat := 245470453843210389884815

theorem tailTrace_1075617 : CollatzResearch.WordTrace tailWord_1075617 prefixEnd_1075617 245470453843210389884815 := by
  unfold tailWord_1075617
  simp only [CollatzResearch.WordTrace]
  refine ⟨39230974944230784603545105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26153983296153856402363403 39230974944230784603545105)
  ·
    refine ⟨29423231208173088452658829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39230974944230784603545105 29423231208173088452658829)
    ·
      refine ⟨11033711703064908169747061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29423231208173088452658829 11033711703064908169747061)
      ·
        refine ⟨1034410472162335140913787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11033711703064908169747061 1034410472162335140913787)
        ·
          refine ⟨1551615708243502711370681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034410472162335140913787 1551615708243502711370681)
          ·
            refine ⟨1163711781182627033528011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1551615708243502711370681 1163711781182627033528011)
            ·
              refine ⟨1745567671773940550292017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1163711781182627033528011 1745567671773940550292017)
              ·
                refine ⟨1309175753830455412719013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1745567671773940550292017 1309175753830455412719013)
                ·
                  refine ⟨245470453843210389884815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1309175753830455412719013 245470453843210389884815)
                  ·
                    rfl

theorem cell21_1075617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 4].length) (baseStart_1075617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1075617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1075617 prefixEnd_1075617 := by exact prefixLift 1075617
  have htrace : WordTrace (prefixWord ++ tailWord_1075617) baseStart_1075617 baseEnd_1075617 := by
    simpa [prefixWord, tailWord_1075617, baseEnd_1075617] using wordTrace_append hprefix tailTrace_1075617
  have hstable : (prefixWord ++ tailWord_1075617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075617).length < 2 ^ (prefixWord ++ tailWord_1075617).sum := by decide
  have hdescent : baseEnd_1075617 < baseStart_1075617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075642 : List Nat := [3, 1, 1, 1, 2, 1, 1, 7, 4]
def baseStart_1075642 : Nat := 118140960795 + 1075642 * 2 ^ 59
def prefixEnd_1075642 : Nat := 4983230072969 + 3 ^ 40 * 1075642 * 2
def baseEnd_1075642 : Nat := 245476159183815901968097

theorem tailTrace_1075642 : CollatzResearch.WordTrace tailWord_1075642 prefixEnd_1075642 245476159183815901968097 := by
  unfold tailWord_1075642
  simp only [CollatzResearch.WordTrace]
  refine ⟨9807971692285053468301295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26154591179426809248803453 9807971692285053468301295)
  ·
    refine ⟨14711957538427580202451943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9807971692285053468301295 14711957538427580202451943)
    ·
      refine ⟨22067936307641370303677915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14711957538427580202451943 22067936307641370303677915)
      ·
        refine ⟨33101904461462055455516873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22067936307641370303677915 33101904461462055455516873)
        ·
          refine ⟨24826428346096541591637655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33101904461462055455516873 24826428346096541591637655)
          ·
            refine ⟨37239642519144812387456483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24826428346096541591637655 37239642519144812387456483)
            ·
              refine ⟨55859463778717218581184725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37239642519144812387456483 55859463778717218581184725)
              ·
                refine ⟨1309206182313684810496517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 55859463778717218581184725 1309206182313684810496517)
                ·
                  refine ⟨245476159183815901968097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1309206182313684810496517 245476159183815901968097)
                  ·
                    rfl

theorem cell21_1075642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_1075642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1075642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1075642 prefixEnd_1075642 := by exact prefixLift 1075642
  have htrace : WordTrace (prefixWord ++ tailWord_1075642) baseStart_1075642 baseEnd_1075642 := by
    simpa [prefixWord, tailWord_1075642, baseEnd_1075642] using wordTrace_append hprefix tailTrace_1075642
  have hstable : (prefixWord ++ tailWord_1075642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075642).length < 2 ^ (prefixWord ++ tailWord_1075642).sum := by decide
  have hdescent : baseEnd_1075642 < baseStart_1075642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075693 : List Nat := [1, 5, 1, 3, 1, 3, 2, 1, 4]
def baseStart_1075693 : Nat := 118140960795 + 1075693 * 2 ^ 59
def prefixEnd_1075693 : Nat := 4983230072969 + 3 ^ 40 * 1075693 * 2
def baseEnd_1075693 : Nat := 245487798078651146617993

theorem tailTrace_1075693 : CollatzResearch.WordTrace tailWord_1075693 prefixEnd_1075693 245487798078651146617993 := by
  unfold tailWord_1075693
  simp only [CollatzResearch.WordTrace]
  refine ⟨39233746891955449583311733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26155831261303633055541155 39233746891955449583311733)
  ·
    refine ⟨3678163771120823398435475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39233746891955449583311733 3678163771120823398435475)
    ·
      refine ⟨5517245656681235097653213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3678163771120823398435475 5517245656681235097653213)
      ·
        refine ⟨2068967121255463161619955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5517245656681235097653213 2068967121255463161619955)
        ·
          refine ⟨3103450681883194742429933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2068967121255463161619955 3103450681883194742429933)
          ·
            refine ⟨1163794005706198028411225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3103450681883194742429933 1163794005706198028411225)
            ·
              refine ⟨872845504279648521308419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1163794005706198028411225 872845504279648521308419)
              ·
                refine ⟨1309268256419472781962629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872845504279648521308419 1309268256419472781962629)
                ·
                  refine ⟨245487798078651146617993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1309268256419472781962629 245487798078651146617993)
                  ·
                    rfl

theorem cell21_1075693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_1075693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1075693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1075693 prefixEnd_1075693 := by exact prefixLift 1075693
  have htrace : WordTrace (prefixWord ++ tailWord_1075693) baseStart_1075693 baseEnd_1075693 := by
    simpa [prefixWord, tailWord_1075693, baseEnd_1075693] using wordTrace_append hprefix tailTrace_1075693
  have hstable : (prefixWord ++ tailWord_1075693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075693).length < 2 ^ (prefixWord ++ tailWord_1075693).sum := by decide
  have hdescent : baseEnd_1075693 < baseStart_1075693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075763 : List Nat := [1, 1, 1, 2, 4, 2, 3, 2, 5]
def baseStart_1075763 : Nat := 118140960795 + 1075763 * 2 ^ 59
def prefixEnd_1075763 : Nat := 4983230072969 + 3 ^ 40 * 1075763 * 2
def baseEnd_1075763 : Nat := 245503773032346580451183

theorem tailTrace_1075763 : CollatzResearch.WordTrace tailWord_1075763 prefixEnd_1075763 245503773032346580451183 := by
  unfold tailWord_1075763
  simp only [CollatzResearch.WordTrace]
  refine ⟨39236300001701851538359943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26157533334467901025573295 39236300001701851538359943)
  ·
    refine ⟨58854450002552777307539915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39236300001701851538359943 58854450002552777307539915)
    ·
      refine ⟨88281675003829165961309873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58854450002552777307539915 88281675003829165961309873)
      ·
        refine ⟨66211256252871874470982405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88281675003829165961309873 66211256252871874470982405)
        ·
          refine ⟨12414610547413476463309201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66211256252871874470982405 12414610547413476463309201)
          ·
            refine ⟨9310957910560107347481901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12414610547413476463309201 9310957910560107347481901)
            ·
              refine ⟨3491609216460040255305713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9310957910560107347481901 3491609216460040255305713)
              ·
                refine ⟨2618706912345030191479285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3491609216460040255305713 2618706912345030191479285)
                ·
                  refine ⟨245503773032346580451183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2618706912345030191479285 245503773032346580451183)
                  ·
                    rfl

theorem cell21_1075763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 5].length) (baseStart_1075763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1075763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1075763 prefixEnd_1075763 := by exact prefixLift 1075763
  have htrace : WordTrace (prefixWord ++ tailWord_1075763) baseStart_1075763 baseEnd_1075763 := by
    simpa [prefixWord, tailWord_1075763, baseEnd_1075763] using wordTrace_append hprefix tailTrace_1075763
  have hstable : (prefixWord ++ tailWord_1075763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075763).length < 2 ^ (prefixWord ++ tailWord_1075763).sum := by decide
  have hdescent : baseEnd_1075763 < baseStart_1075763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075794 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 6]
def baseStart_1075794 : Nat := 118140960795 + 1075794 * 2 ^ 59
def prefixEnd_1075794 : Nat := 4983230072969 + 3 ^ 40 * 1075794 * 2
def baseEnd_1075794 : Nat := 245510847654697415434453

theorem tailTrace_1075794 : CollatzResearch.WordTrace tailWord_1075794 prefixEnd_1075794 245510847654697415434453 := by
  unfold tailWord_1075794
  simp only [CollatzResearch.WordTrace]
  refine ⟨9809357666147385958184609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26158287109726362555158957 9809357666147385958184609)
  ·
    refine ⟨7357018249610539468638457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9809357666147385958184609 7357018249610539468638457)
    ·
      refine ⟨5517763687207904601478843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7357018249610539468638457 5517763687207904601478843)
      ·
        refine ⟨8276645530811856902218265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5517763687207904601478843 8276645530811856902218265)
        ·
          refine ⟨6207484148108892676663699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8276645530811856902218265 6207484148108892676663699)
          ·
            refine ⟨9311226222163339014995549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6207484148108892676663699 9311226222163339014995549)
            ·
              refine ⟨3491709833311252130623331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9311226222163339014995549 3491709833311252130623331)
              ·
                refine ⟨5237564749966878195934997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3491709833311252130623331 5237564749966878195934997)
                ·
                  refine ⟨245510847654697415434453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5237564749966878195934997 245510847654697415434453)
                  ·
                    rfl

theorem cell21_1075794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_1075794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1075794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1075794 prefixEnd_1075794 := by exact prefixLift 1075794
  have htrace : WordTrace (prefixWord ++ tailWord_1075794) baseStart_1075794 baseEnd_1075794 := by
    simpa [prefixWord, tailWord_1075794, baseEnd_1075794] using wordTrace_append hprefix tailTrace_1075794
  have hstable : (prefixWord ++ tailWord_1075794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075794).length < 2 ^ (prefixWord ++ tailWord_1075794).sum := by decide
  have hdescent : baseEnd_1075794 < baseStart_1075794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075811 : List Nat := [1, 1, 1, 5, 1, 2, 5, 1, 4]
def baseStart_1075811 : Nat := 118140960795 + 1075811 * 2 ^ 59
def prefixEnd_1075811 : Nat := 4983230072969 + 3 ^ 40 * 1075811 * 2
def baseEnd_1075811 : Nat := 245514727286309163651085

theorem tailTrace_1075811 : CollatzResearch.WordTrace tailWord_1075811 prefixEnd_1075811 245514727286309163651085 := by
  unfold tailWord_1075811
  simp only [CollatzResearch.WordTrace]
  refine ⟨39238050705527955736107287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26158700470351970490738191 39238050705527955736107287)
  ·
    refine ⟨58857076058291933604160931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39238050705527955736107287 58857076058291933604160931)
    ·
      refine ⟨88285614087437900406241397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58857076058291933604160931 88285614087437900406241397)
      ·
        refine ⟨8276776320697303163085131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88285614087437900406241397 8276776320697303163085131)
        ·
          refine ⟨12415164481045954744627697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8276776320697303163085131 12415164481045954744627697)
          ·
            refine ⟨9311373360784466058470773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12415164481045954744627697 9311373360784466058470773)
            ·
              refine ⟨872941252573543692981635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9311373360784466058470773 872941252573543692981635)
              ·
                refine ⟨1309411878860315539472453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872941252573543692981635 1309411878860315539472453)
                ·
                  refine ⟨245514727286309163651085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1309411878860315539472453 245514727286309163651085)
                  ·
                    rfl

theorem cell21_1075811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 4].length) (baseStart_1075811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1075811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1075811 prefixEnd_1075811 := by exact prefixLift 1075811
  have htrace : WordTrace (prefixWord ++ tailWord_1075811) baseStart_1075811 baseEnd_1075811 := by
    simpa [prefixWord, tailWord_1075811, baseEnd_1075811] using wordTrace_append hprefix tailTrace_1075811
  have hstable : (prefixWord ++ tailWord_1075811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075811).length < 2 ^ (prefixWord ++ tailWord_1075811).sum := by decide
  have hdescent : baseEnd_1075811 < baseStart_1075811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075932 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 7]
def baseStart_1075932 : Nat := 118140960795 + 1075932 * 2 ^ 59
def prefixEnd_1075932 : Nat := 4983230072969 + 3 ^ 40 * 1075932 * 2
def baseEnd_1075932 : Nat := 245542341134839842134171

theorem tailTrace_1075932 : CollatzResearch.WordTrace tailWord_1075932 prefixEnd_1075932 245542341134839842134171 := by
  unfold tailWord_1075932
  simp only [CollatzResearch.WordTrace]
  refine ⟨19621231969044796700631025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26161642625393062267508033 19621231969044796700631025)
  ·
    refine ⟨14715923976783597525473269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19621231969044796700631025 14715923976783597525473269)
    ·
      refine ⟨1379617872823462268013119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14715923976783597525473269 1379617872823462268013119)
      ·
        refine ⟨2069426809235193402019679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1379617872823462268013119 2069426809235193402019679)
        ·
          refine ⟨3104140213852790103029519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2069426809235193402019679 3104140213852790103029519)
          ·
            refine ⟨4656210320779185154544279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3104140213852790103029519 4656210320779185154544279)
            ·
              refine ⟨6984315481168777731816419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4656210320779185154544279 6984315481168777731816419)
              ·
                refine ⟨10476473221753166597724629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6984315481168777731816419 10476473221753166597724629)
                ·
                  refine ⟨245542341134839842134171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10476473221753166597724629 245542341134839842134171)
                  ·
                    rfl

theorem cell21_1075932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_1075932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1075932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1075932 prefixEnd_1075932 := by exact prefixLift 1075932
  have htrace : WordTrace (prefixWord ++ tailWord_1075932) baseStart_1075932 baseEnd_1075932 := by
    simpa [prefixWord, tailWord_1075932, baseEnd_1075932] using wordTrace_append hprefix tailTrace_1075932
  have hstable : (prefixWord ++ tailWord_1075932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075932).length < 2 ^ (prefixWord ++ tailWord_1075932).sum := by decide
  have hdescent : baseEnd_1075932 < baseStart_1075932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1075949 : List Nat := [1, 5, 1, 2, 1, 1, 4, 3, 3]
def baseStart_1075949 : Nat := 118140960795 + 1075949 * 2 ^ 59
def prefixEnd_1075949 : Nat := 4983230072969 + 3 ^ 40 * 1075949 * 2
def baseEnd_1075949 : Nat := 245546220766451590350803

theorem tailTrace_1075949 : CollatzResearch.WordTrace tailWord_1075949 prefixEnd_1075949 245546220766451590350803 := by
  unfold tailWord_1075949
  simp only [CollatzResearch.WordTrace]
  refine ⟨39243083979028005304630901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26162055986018670203087267 39243083979028005304630901)
  ·
    refine ⟨3679039123033875497309147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39243083979028005304630901 3679039123033875497309147)
    ·
      refine ⟨5518558684550813245963721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3679039123033875497309147 5518558684550813245963721)
      ·
        refine ⟨4138919013413109934472791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5518558684550813245963721 4138919013413109934472791)
        ·
          refine ⟨6208378520119664901709187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4138919013413109934472791 6208378520119664901709187)
          ·
            refine ⟨9312567780179497352563781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6208378520119664901709187 9312567780179497352563781)
            ·
              refine ⟨1746106458783655753605709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9312567780179497352563781 1746106458783655753605709)
              ·
                refine ⟨654789922043870907602141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1746106458783655753605709 654789922043870907602141)
                ·
                  refine ⟨245546220766451590350803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 654789922043870907602141 245546220766451590350803)
                  ·
                    rfl

theorem cell21_1075949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_1075949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1075949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1075949 prefixEnd_1075949 := by exact prefixLift 1075949
  have htrace : WordTrace (prefixWord ++ tailWord_1075949) baseStart_1075949 baseEnd_1075949 := by
    simpa [prefixWord, tailWord_1075949, baseEnd_1075949] using wordTrace_append hprefix tailTrace_1075949
  have hstable : (prefixWord ++ tailWord_1075949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1075949).length < 2 ^ (prefixWord ++ tailWord_1075949).sum := by decide
  have hdescent : baseEnd_1075949 < baseStart_1075949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1075949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076005 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 8]
def baseStart_1076005 : Nat := 118140960795 + 1076005 * 2 ^ 59
def prefixEnd_1076005 : Nat := 4983230072969 + 3 ^ 40 * 1076005 * 2
def baseEnd_1076005 : Nat := 245559000729407937417355

theorem tailTrace_1076005 : CollatzResearch.WordTrace tailWord_1076005 prefixEnd_1076005 245559000729407937417355 := by
  unfold tailWord_1076005
  simp only [CollatzResearch.WordTrace]
  refine ⟨39245126466825126868669469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26163417644550084579112979 39245126466825126868669469)
  ·
    refine ⟨14716922425059422575751051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39245126466825126868669469 14716922425059422575751051)
    ·
      refine ⟨22075383637589133863626577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14716922425059422575751051 22075383637589133863626577)
      ·
        refine ⟨16556537728191850397719933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22075383637589133863626577 16556537728191850397719933)
        ·
          refine ⟨6208701648071943899144975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16556537728191850397719933 6208701648071943899144975)
          ·
            refine ⟨9313052472107915848717463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6208701648071943899144975 9313052472107915848717463)
            ·
              refine ⟨13969578708161873773076195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9313052472107915848717463 13969578708161873773076195)
              ·
                refine ⟨20954368062242810659614293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13969578708161873773076195 20954368062242810659614293)
                ·
                  refine ⟨245559000729407937417355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20954368062242810659614293 245559000729407937417355)
                  ·
                    rfl

theorem cell21_1076005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_1076005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076005 prefixEnd_1076005 := by exact prefixLift 1076005
  have htrace : WordTrace (prefixWord ++ tailWord_1076005) baseStart_1076005 baseEnd_1076005 := by
    simpa [prefixWord, tailWord_1076005, baseEnd_1076005] using wordTrace_append hprefix tailTrace_1076005
  have hstable : (prefixWord ++ tailWord_1076005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076005).length < 2 ^ (prefixWord ++ tailWord_1076005).sum := by decide
  have hdescent : baseEnd_1076005 < baseStart_1076005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076250 : List Nat := [3, 1, 1, 3, 1, 2, 4, 2, 4]
def baseStart_1076250 : Nat := 118140960795 + 1076250 * 2 ^ 59
def prefixEnd_1076250 : Nat := 4983230072969 + 3 ^ 40 * 1076250 * 2
def baseEnd_1076250 : Nat := 245614913067341955833521

theorem tailTrace_1076250 : CollatzResearch.WordTrace tailWord_1076250 prefixEnd_1076250 245614913067341955833521 := by
  unfold tailWord_1076250
  simp only [CollatzResearch.WordTrace]
  refine ⟨9813515587734383427834551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26169374900625022474225469 9813515587734383427834551)
  ·
    refine ⟨14720273381601575141751827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9813515587734383427834551 14720273381601575141751827)
    ·
      refine ⟨22080410072402362712627741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14720273381601575141751827 22080410072402362712627741)
      ·
        refine ⟨8280153777150886017235403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22080410072402362712627741 8280153777150886017235403)
        ·
          refine ⟨12420230665726329025853105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8280153777150886017235403 12420230665726329025853105)
          ·
            refine ⟨9315172999294746769389829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12420230665726329025853105 9315172999294746769389829)
            ·
              refine ⟨1746594937367765019260593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9315172999294746769389829 1746594937367765019260593)
              ·
                refine ⟨1309946203025823764445445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1746594937367765019260593 1309946203025823764445445)
                ·
                  refine ⟨245614913067341955833521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1309946203025823764445445 245614913067341955833521)
                  ·
                    rfl

theorem cell21_1076250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_1076250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076250 prefixEnd_1076250 := by exact prefixLift 1076250
  have htrace : WordTrace (prefixWord ++ tailWord_1076250) baseStart_1076250 baseEnd_1076250 := by
    simpa [prefixWord, tailWord_1076250, baseEnd_1076250] using wordTrace_append hprefix tailTrace_1076250
  have hstable : (prefixWord ++ tailWord_1076250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076250).length < 2 ^ (prefixWord ++ tailWord_1076250).sum := by decide
  have hdescent : baseEnd_1076250 < baseStart_1076250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076253 : List Nat := [1, 4, 2, 2, 3, 1, 1, 4, 3]
def baseStart_1076253 : Nat := 118140960795 + 1076253 * 2 ^ 59
def prefixEnd_1076253 : Nat := 4983230072969 + 3 ^ 40 * 1076253 * 2
def baseEnd_1076253 : Nat := 245615597708214617283515

theorem tailTrace_1076253 : CollatzResearch.WordTrace tailWord_1076253 prefixEnd_1076253 245615597708214617283515 := by
  unfold tailWord_1076253
  simp only [CollatzResearch.WordTrace]
  refine ⟨39254171769926665223697413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26169447846617776815798275 39254171769926665223697413)
  ·
    refine ⟨7360157206861249729443265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39254171769926665223697413 7360157206861249729443265)
    ·
      refine ⟨5520117905145937297082449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7360157206861249729443265 5520117905145937297082449)
      ·
        refine ⟨4140088428859452972811837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5520117905145937297082449 4140088428859452972811837)
        ·
          refine ⟨1552533160822294864804439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4140088428859452972811837 1552533160822294864804439)
          ·
            refine ⟨2328799741233442297206659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1552533160822294864804439 2328799741233442297206659)
            ·
              refine ⟨3493199611850163445809989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2328799741233442297206659 3493199611850163445809989)
              ·
                refine ⟨654974927221905646089373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3493199611850163445809989 654974927221905646089373)
                ·
                  refine ⟨245615597708214617283515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 654974927221905646089373 245615597708214617283515)
                  ·
                    rfl

theorem cell21_1076253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_1076253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076253 prefixEnd_1076253 := by exact prefixLift 1076253
  have htrace : WordTrace (prefixWord ++ tailWord_1076253) baseStart_1076253 baseEnd_1076253 := by
    simpa [prefixWord, tailWord_1076253, baseEnd_1076253] using wordTrace_append hprefix tailTrace_1076253
  have hstable : (prefixWord ++ tailWord_1076253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076253).length < 2 ^ (prefixWord ++ tailWord_1076253).sum := by decide
  have hdescent : baseEnd_1076253 < baseStart_1076253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076281 : List Nat := [1, 2, 1, 5, 2, 2, 3, 5]
def baseStart_1076281 : Nat := 118140960795 + 1076281 * 2 ^ 59
def prefixEnd_1076281 : Nat := 4983230072969 + 3 ^ 40 * 1076281 * 2
def baseEnd_1076281 : Nat := 81873995896564263605597

theorem tailTrace_1076281 : CollatzResearch.WordTrace tailWord_1076281 prefixEnd_1076281 81873995896564263605597 := by
  unfold tailWord_1076281
  simp only [CollatzResearch.WordTrace]
  refine ⟨39255193013825226005716697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26170128675883484003811131 39255193013825226005716697)
  ·
    refine ⟨29441394760368919504287523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39255193013825226005716697 29441394760368919504287523)
    ·
      refine ⟨44162092140553379256431285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29441394760368919504287523 44162092140553379256431285)
      ·
        refine ⟨4140196138176879305290433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44162092140553379256431285 4140196138176879305290433)
        ·
          refine ⟨3105147103632659478967825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4140196138176879305290433 3105147103632659478967825)
          ·
            refine ⟨2328860327724494609225869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3105147103632659478967825 2328860327724494609225869)
            ·
              refine ⟨873322622896685478459701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2328860327724494609225869 873322622896685478459701)
              ·
                refine ⟨81873995896564263605597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 873322622896685478459701 81873995896564263605597)
                ·
                  rfl

theorem cell21_1076281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 5].length) (baseStart_1076281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076281 prefixEnd_1076281 := by exact prefixLift 1076281
  have htrace : WordTrace (prefixWord ++ tailWord_1076281) baseStart_1076281 baseEnd_1076281 := by
    simpa [prefixWord, tailWord_1076281, baseEnd_1076281] using wordTrace_append hprefix tailTrace_1076281
  have hstable : (prefixWord ++ tailWord_1076281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076281).length < 2 ^ (prefixWord ++ tailWord_1076281).sum := by decide
  have hdescent : baseEnd_1076281 < baseStart_1076281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076309 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 6]
def baseStart_1076309 : Nat := 118140960795 + 1076309 * 2 ^ 59
def prefixEnd_1076309 : Nat := 4983230072969 + 3 ^ 40 * 1076309 * 2
def baseEnd_1076309 : Nat := 245628377671170964350067

theorem tailTrace_1076309 : CollatzResearch.WordTrace tailWord_1076309 prefixEnd_1076309 245628377671170964350067 := by
  unfold tailWord_1076309
  simp only [CollatzResearch.WordTrace]
  refine ⟨39256214257723786787735981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26170809505149191191823987 39256214257723786787735981)
  ·
    refine ⟨14721080346646420045400993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39256214257723786787735981 14721080346646420045400993)
    ·
      refine ⟨11040810259984815034050745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14721080346646420045400993 11040810259984815034050745)
      ·
        refine ⟨8280607694988611275538059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11040810259984815034050745 8280607694988611275538059)
        ·
          refine ⟨12420911542482916913307089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8280607694988611275538059 12420911542482916913307089)
          ·
            refine ⟨9315683656862187684980317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12420911542482916913307089 9315683656862187684980317)
            ·
              refine ⟨3493381371323320381867619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9315683656862187684980317 3493381371323320381867619)
              ·
                refine ⟨5240072056984980572801429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3493381371323320381867619 5240072056984980572801429)
                ·
                  refine ⟨245628377671170964350067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5240072056984980572801429 245628377671170964350067)
                  ·
                    rfl

theorem cell21_1076309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_1076309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076309 prefixEnd_1076309 := by exact prefixLift 1076309
  have htrace : WordTrace (prefixWord ++ tailWord_1076309) baseStart_1076309 baseEnd_1076309 := by
    simpa [prefixWord, tailWord_1076309, baseEnd_1076309] using wordTrace_append hprefix tailTrace_1076309
  have hstable : (prefixWord ++ tailWord_1076309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076309).length < 2 ^ (prefixWord ++ tailWord_1076309).sum := by decide
  have hdescent : baseEnd_1076309 < baseStart_1076309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076323 : List Nat := [1, 1, 1, 5, 1, 1, 1, 10]
def baseStart_1076323 : Nat := 118140960795 + 1076323 * 2 ^ 59
def prefixEnd_1076323 : Nat := 4983230072969 + 3 ^ 40 * 1076323 * 2
def baseEnd_1076323 : Nat := 81877190887303350372235

theorem tailTrace_1076323 : CollatzResearch.WordTrace tailWord_1076323 prefixEnd_1076323 81877190887303350372235 := by
  unfold tailWord_1076323
  simp only [CollatzResearch.WordTrace]
  refine ⟨39256724879673067178745623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26171149919782044785830415 39256724879673067178745623)
  ·
    refine ⟨58885087319509600768118435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39256724879673067178745623 58885087319509600768118435)
    ·
      refine ⟨88327630979264401152177653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58885087319509600768118435 88327630979264401152177653)
      ·
        refine ⟨8280715404306037608016655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88327630979264401152177653 8280715404306037608016655)
        ·
          refine ⟨12421073106459056412024983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8280715404306037608016655 12421073106459056412024983)
          ·
            refine ⟨18631609659688584618037475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12421073106459056412024983 18631609659688584618037475)
            ·
              refine ⟨27947414489532876927056213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18631609659688584618037475 27947414489532876927056213)
              ·
                refine ⟨81877190887303350372235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27947414489532876927056213 81877190887303350372235)
                ·
                  rfl

theorem cell21_1076323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 10].length) (baseStart_1076323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076323 prefixEnd_1076323 := by exact prefixLift 1076323
  have htrace : WordTrace (prefixWord ++ tailWord_1076323) baseStart_1076323 baseEnd_1076323 := by
    simpa [prefixWord, tailWord_1076323, baseEnd_1076323] using wordTrace_append hprefix tailTrace_1076323
  have hstable : (prefixWord ++ tailWord_1076323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076323).length < 2 ^ (prefixWord ++ tailWord_1076323).sum := by decide
  have hdescent : baseEnd_1076323 < baseStart_1076323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076357 : List Nat := [1, 3, 1, 1, 7, 1, 7]
def baseStart_1076357 : Nat := 118140960795 + 1076357 * 2 ^ 59
def prefixEnd_1076357 : Nat := 4983230072969 + 3 ^ 40 * 1076357 * 2
def baseEnd_1076357 : Nat := 27293259102792616394441

theorem tailTrace_1076357 : CollatzResearch.WordTrace tailWord_1076357 prefixEnd_1076357 27293259102792616394441 := by
  unfold tailWord_1076357
  simp only [CollatzResearch.WordTrace]
  refine ⟨39257964961549890985483325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26171976641033260656988883 39257964961549890985483325)
  ·
    refine ⟨14721736860581209119556247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39257964961549890985483325 14721736860581209119556247)
    ·
      refine ⟨22082605290871813679334371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14721736860581209119556247 22082605290871813679334371)
      ·
        refine ⟨33123907936307720519001557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22082605290871813679334371 33123907936307720519001557)
        ·
          refine ⟨776341592257212199664099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 33123907936307720519001557 776341592257212199664099)
          ·
            refine ⟨1164512388385818299496149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 776341592257212199664099 1164512388385818299496149)
            ·
              refine ⟨27293259102792616394441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1164512388385818299496149 27293259102792616394441)
              ·
                rfl

theorem cell21_1076357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 7].length) (baseStart_1076357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076357 prefixEnd_1076357 := by exact prefixLift 1076357
  have htrace : WordTrace (prefixWord ++ tailWord_1076357) baseStart_1076357 baseEnd_1076357 := by
    simpa [prefixWord, tailWord_1076357, baseEnd_1076357] using wordTrace_append hprefix tailTrace_1076357
  have hstable : (prefixWord ++ tailWord_1076357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076357).length < 2 ^ (prefixWord ++ tailWord_1076357).sum := by decide
  have hdescent : baseEnd_1076357 < baseStart_1076357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076371 : List Nat := [1, 1, 1, 2, 1, 2, 4, 6, 3]
def baseStart_1076371 : Nat := 118140960795 + 1076371 * 2 ^ 59
def prefixEnd_1076371 : Nat := 4983230072969 + 3 ^ 40 * 1076371 * 2
def baseEnd_1076371 : Nat := 245642526915872634316607

theorem tailTrace_1076371 : CollatzResearch.WordTrace tailWord_1076371 prefixEnd_1076371 245642526915872634316607 := by
  unfold tailWord_1076371
  simp only [CollatzResearch.WordTrace]
  refine ⟨39258475583499171376492967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26172317055666114250995311 39258475583499171376492967)
  ·
    refine ⟨58887713375248757064739451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39258475583499171376492967 58887713375248757064739451)
    ·
      refine ⟨88331570062873135597109177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58887713375248757064739451 88331570062873135597109177)
      ·
        refine ⟨66248677547154851697831883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88331570062873135597109177 66248677547154851697831883)
        ·
          refine ⟨99373016320732277546747825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66248677547154851697831883 99373016320732277546747825)
          ·
            refine ⟨74529762240549208160060869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99373016320732277546747825 74529762240549208160060869)
            ·
              refine ⟨13974330420102976530011413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74529762240549208160060869 13974330420102976530011413)
              ·
                refine ⟨655046738442327024844285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13974330420102976530011413 655046738442327024844285)
                ·
                  refine ⟨245642526915872634316607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 655046738442327024844285 245642526915872634316607)
                  ·
                    rfl

theorem cell21_1076371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 3].length) (baseStart_1076371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076371 prefixEnd_1076371 := by exact prefixLift 1076371
  have htrace : WordTrace (prefixWord ++ tailWord_1076371) baseStart_1076371 baseEnd_1076371 := by
    simpa [prefixWord, tailWord_1076371, baseEnd_1076371] using wordTrace_append hprefix tailTrace_1076371
  have hstable : (prefixWord ++ tailWord_1076371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076371).length < 2 ^ (prefixWord ++ tailWord_1076371).sum := by decide
  have hdescent : baseEnd_1076371 < baseStart_1076371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076399 : List Nat := [1, 1, 2, 1, 2, 3, 4, 7]
def baseStart_1076399 : Nat := 118140960795 + 1076399 * 2 ^ 59
def prefixEnd_1076399 : Nat := 4983230072969 + 3 ^ 40 * 1076399 * 2
def baseEnd_1076399 : Nat := 81882972299116935949961

theorem tailTrace_1076399 : CollatzResearch.WordTrace tailWord_1076399 prefixEnd_1076399 81882972299116935949961 := by
  unfold tailWord_1076399
  simp only [CollatzResearch.WordTrace]
  refine ⟨39259496827397732158512251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26172997884931821439008167 39259496827397732158512251)
  ·
    refine ⟨58889245241096598237768377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39259496827397732158512251 58889245241096598237768377)
    ·
      refine ⟨44166933930822448678326283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58889245241096598237768377 44166933930822448678326283)
      ·
        refine ⟨66250400896233673017489425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44166933930822448678326283 66250400896233673017489425)
        ·
          refine ⟨49687800672175254763117069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66250400896233673017489425 49687800672175254763117069)
          ·
            refine ⟨18632925252065720536168901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49687800672175254763117069 18632925252065720536168901)
            ·
              refine ⟨3493673484762322600531669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18632925252065720536168901 3493673484762322600531669)
              ·
                refine ⟨81882972299116935949961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3493673484762322600531669 81882972299116935949961)
                ·
                  rfl

theorem cell21_1076399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 7].length) (baseStart_1076399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076399 prefixEnd_1076399 := by exact prefixLift 1076399
  have htrace : WordTrace (prefixWord ++ tailWord_1076399) baseStart_1076399 baseEnd_1076399 := by
    simpa [prefixWord, tailWord_1076399, baseEnd_1076399] using wordTrace_append hprefix tailTrace_1076399
  have hstable : (prefixWord ++ tailWord_1076399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076399).length < 2 ^ (prefixWord ++ tailWord_1076399).sum := by decide
  have hdescent : baseEnd_1076399 < baseStart_1076399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076416 : List Nat := [2, 1, 1, 2, 7, 8]
def baseStart_1076416 : Nat := 118140960795 + 1076416 * 2 ^ 59
def prefixEnd_1076416 : Nat := 4983230072969 + 3 ^ 40 * 1076416 * 2
def baseEnd_1076416 : Nat := 9098251723294909483945

theorem tailTrace_1076416 : CollatzResearch.WordTrace tailWord_1076416 prefixEnd_1076416 9098251723294909483945 := by
  unfold tailWord_1076416
  simp only [CollatzResearch.WordTrace]
  refine ⟨19630058434168072030940551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26173411245557429374587401 19630058434168072030940551)
  ·
    refine ⟨29445087651252108046410827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19630058434168072030940551 29445087651252108046410827)
    ·
      refine ⟨44167631476878162069616241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29445087651252108046410827 44167631476878162069616241)
      ·
        refine ⟨33125723607658621552212181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44167631476878162069616241 33125723607658621552212181)
        ·
          refine ⟨776384147054498942629973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 33125723607658621552212181 776384147054498942629973)
          ·
            refine ⟨9098251723294909483945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 776384147054498942629973 9098251723294909483945)
            ·
              rfl

theorem cell21_1076416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 8].length) (baseStart_1076416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076416 prefixEnd_1076416 := by exact prefixLift 1076416
  have htrace : WordTrace (prefixWord ++ tailWord_1076416) baseStart_1076416 baseEnd_1076416 := by
    simpa [prefixWord, tailWord_1076416, baseEnd_1076416] using wordTrace_append hprefix tailTrace_1076416
  have hstable : (prefixWord ++ tailWord_1076416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076416).length < 2 ^ (prefixWord ++ tailWord_1076416).sum := by decide
  have hdescent : baseEnd_1076416 < baseStart_1076416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076478 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_1076478 : Nat := 118140960795 + 1076478 * 2 ^ 59
def prefixEnd_1076478 : Nat := 4983230072969 + 3 ^ 40 * 1076478 * 2
def baseEnd_1076478 : Nat := 245666945773664226033055

theorem tailTrace_1076478 : CollatzResearch.WordTrace tailWord_1076478 prefixEnd_1076478 245666945773664226033055 := by
  unfold tailWord_1076478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4907797274263941081329761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26174918796074352433758725 4907797274263941081329761)
  ·
    refine ⟨3680847955697955810997321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4907797274263941081329761 3680847955697955810997321)
    ·
      refine ⟨2760635966773466858247991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3680847955697955810997321 2760635966773466858247991)
      ·
        refine ⟨4140953950160200287371987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2760635966773466858247991 4140953950160200287371987)
        ·
          refine ⟨6211430925240300431057981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4140953950160200287371987 6211430925240300431057981)
          ·
            refine ⟨2329286596965112661646743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6211430925240300431057981 2329286596965112661646743)
            ·
              refine ⟨3493929895447668992470115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2329286596965112661646743 3493929895447668992470115)
              ·
                refine ⟨5240894843171503488705173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3493929895447668992470115 5240894843171503488705173)
                ·
                  refine ⟨245666945773664226033055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5240894843171503488705173 245666945773664226033055)
                  ·
                    rfl

theorem cell21_1076478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_1076478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076478 prefixEnd_1076478 := by exact prefixLift 1076478
  have htrace : WordTrace (prefixWord ++ tailWord_1076478) baseStart_1076478 baseEnd_1076478 := by
    simpa [prefixWord, tailWord_1076478, baseEnd_1076478] using wordTrace_append hprefix tailTrace_1076478
  have hstable : (prefixWord ++ tailWord_1076478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076478).length < 2 ^ (prefixWord ++ tailWord_1076478).sum := by decide
  have hdescent : baseEnd_1076478 < baseStart_1076478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076509 : List Nat := [1, 4, 2, 3, 1, 1, 4, 5]
def baseStart_1076509 : Nat := 118140960795 + 1076509 * 2 ^ 59
def prefixEnd_1076509 : Nat := 4983230072969 + 3 ^ 40 * 1076509 * 2
def baseEnd_1076509 : Nat := 81891340132005020338775

theorem tailTrace_1076509 : CollatzResearch.WordTrace tailWord_1076509 prefixEnd_1076509 81891340132005020338775 := by
  unfold tailWord_1076509
  simp only [CollatzResearch.WordTrace]
  refine ⟨39263508856999220945016581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26175672571332813963344387 39263508856999220945016581)
  ·
    refine ⟨7361907910687353927190609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39263508856999220945016581 7361907910687353927190609)
    ·
      refine ⟨5521430933015515445392957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7361907910687353927190609 5521430933015515445392957)
      ·
        refine ⟨2070536599880818292022359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5521430933015515445392957 2070536599880818292022359)
        ·
          refine ⟨3105804899821227438033539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2070536599880818292022359 3105804899821227438033539)
          ·
            refine ⟨4658707349731841157050309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3105804899821227438033539 4658707349731841157050309)
            ·
              refine ⟨873507628074720216946933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4658707349731841157050309 873507628074720216946933)
              ·
                refine ⟨81891340132005020338775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 873507628074720216946933 81891340132005020338775)
                ·
                  rfl

theorem cell21_1076509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 5].length) (baseStart_1076509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076509 prefixEnd_1076509 := by exact prefixLift 1076509
  have htrace : WordTrace (prefixWord ++ tailWord_1076509) baseStart_1076509 baseEnd_1076509 := by
    simpa [prefixWord, tailWord_1076509, baseEnd_1076509] using wordTrace_append hprefix tailTrace_1076509
  have hstable : (prefixWord ++ tailWord_1076509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076509).length < 2 ^ (prefixWord ++ tailWord_1076509).sum := by decide
  have hdescent : baseEnd_1076509 < baseStart_1076509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076551 : List Nat := [1, 1, 4, 1, 2, 3, 1, 8]
def baseStart_1076551 : Nat := 118140960795 + 1076551 * 2 ^ 59
def prefixEnd_1076551 : Nat := 4983230072969 + 3 ^ 40 * 1076551 * 2
def baseEnd_1076551 : Nat := 81894535122744107105413

theorem tailTrace_1076551 : CollatzResearch.WordTrace tailWord_1076551 prefixEnd_1076551 81894535122744107105413 := by
  unfold tailWord_1076551
  simp only [CollatzResearch.WordTrace]
  refine ⟨39265040722847062118045507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26176693815231374745363671 39265040722847062118045507)
  ·
    refine ⟨58897561084270593177068261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39265040722847062118045507 58897561084270593177068261)
    ·
      refine ⟨11043292703300736220700299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58897561084270593177068261 11043292703300736220700299)
      ·
        refine ⟨16564939054951104331050449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11043292703300736220700299 16564939054951104331050449)
        ·
          refine ⟨12423704291213328248287837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16564939054951104331050449 12423704291213328248287837)
          ·
            refine ⟨4658889109204998093107939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12423704291213328248287837 4658889109204998093107939)
            ·
              refine ⟨6988333663807497139661909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4658889109204998093107939 6988333663807497139661909)
              ·
                refine ⟨81894535122744107105413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6988333663807497139661909 81894535122744107105413)
                ·
                  rfl

theorem cell21_1076551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 8].length) (baseStart_1076551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076551 prefixEnd_1076551 := by exact prefixLift 1076551
  have htrace : WordTrace (prefixWord ++ tailWord_1076551) baseStart_1076551 baseEnd_1076551 := by
    simpa [prefixWord, tailWord_1076551, baseEnd_1076551] using wordTrace_append hprefix tailTrace_1076551
  have hstable : (prefixWord ++ tailWord_1076551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076551).length < 2 ^ (prefixWord ++ tailWord_1076551).sum := by decide
  have hdescent : baseEnd_1076551 < baseStart_1076551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076599 : List Nat := [1, 1, 3, 1, 1, 2, 5, 4, 3]
def baseStart_1076599 : Nat := 118140960795 + 1076599 * 2 ^ 59
def prefixEnd_1076599 : Nat := 4983230072969 + 3 ^ 40 * 1076599 * 2
def baseEnd_1076599 : Nat := 245694559622194904516141

theorem tailTrace_1076599 : CollatzResearch.WordTrace tailWord_1076599 prefixEnd_1076599 245694559622194904516141 := by
  unfold tailWord_1076599
  simp only [CollatzResearch.WordTrace]
  refine ⟨39266791426673166315792851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26177860951115444210528567 39266791426673166315792851)
  ·
    refine ⟨58900187140009749473689277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39266791426673166315792851 58900187140009749473689277)
    ·
      refine ⟨22087570177503656052633479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58900187140009749473689277 22087570177503656052633479)
      ·
        refine ⟨33131355266255484078950219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22087570177503656052633479 33131355266255484078950219)
        ·
          refine ⟨49697032899383226118425329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33131355266255484078950219 49697032899383226118425329)
          ·
            refine ⟨37272774674537419588818997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49697032899383226118425329 37272774674537419588818997)
            ·
              refine ⟨3494322625737883086451781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37272774674537419588818997 3494322625737883086451781)
              ·
                refine ⟨655185492325853078709709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3494322625737883086451781 655185492325853078709709)
                ·
                  refine ⟨245694559622194904516141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 655185492325853078709709 245694559622194904516141)
                  ·
                    rfl

theorem cell21_1076599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 3].length) (baseStart_1076599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076599 prefixEnd_1076599 := by exact prefixLift 1076599
  have htrace : WordTrace (prefixWord ++ tailWord_1076599) baseStart_1076599 baseEnd_1076599 := by
    simpa [prefixWord, tailWord_1076599, baseEnd_1076599] using wordTrace_append hprefix tailTrace_1076599
  have hstable : (prefixWord ++ tailWord_1076599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076599).length < 2 ^ (prefixWord ++ tailWord_1076599).sum := by decide
  have hdescent : baseEnd_1076599 < baseStart_1076599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076613 : List Nat := [1, 3, 1, 1, 3, 1, 4, 3, 4]
def baseStart_1076613 : Nat := 118140960795 + 1076613 * 2 ^ 59
def prefixEnd_1076613 : Nat := 4983230072969 + 3 ^ 40 * 1076613 * 2
def baseEnd_1076613 : Nat := 245697754612933991282779

theorem tailTrace_1076613 : CollatzResearch.WordTrace tailWord_1076613 prefixEnd_1076613 245697754612933991282779 := by
  unfold tailWord_1076613
  simp only [CollatzResearch.WordTrace]
  refine ⟨39267302048622446706802493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26178201365748297804534995 39267302048622446706802493)
  ·
    refine ⟨14725238268233417515050935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39267302048622446706802493 14725238268233417515050935)
    ·
      refine ⟨22087857402350126272576403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14725238268233417515050935 22087857402350126272576403)
      ·
        refine ⟨33131786103525189408864605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22087857402350126272576403 33131786103525189408864605)
        ·
          refine ⟨12424419788821946028324227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33131786103525189408864605 12424419788821946028324227)
          ·
            refine ⟨18636629683232919042486341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12424419788821946028324227 18636629683232919042486341)
            ·
              refine ⟨3494368065606172320466189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18636629683232919042486341 3494368065606172320466189)
              ·
                refine ⟨1310388024602314620174821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3494368065606172320466189 1310388024602314620174821)
                ·
                  refine ⟨245697754612933991282779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1310388024602314620174821 245697754612933991282779)
                  ·
                    rfl

theorem cell21_1076613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_1076613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076613 prefixEnd_1076613 := by exact prefixLift 1076613
  have htrace : WordTrace (prefixWord ++ tailWord_1076613) baseStart_1076613 baseEnd_1076613 := by
    simpa [prefixWord, tailWord_1076613, baseEnd_1076613] using wordTrace_append hprefix tailTrace_1076613
  have hstable : (prefixWord ++ tailWord_1076613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076613).length < 2 ^ (prefixWord ++ tailWord_1076613).sum := by decide
  have hdescent : baseEnd_1076613 < baseStart_1076613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076709 : List Nat := [1, 3, 1, 5, 1, 2, 3, 2, 3]
def baseStart_1076709 : Nat := 118140960795 + 1076709 * 2 ^ 59
def prefixEnd_1076709 : Nat := 4983230072969 + 3 ^ 40 * 1076709 * 2
def baseEnd_1076709 : Nat := 245719663120859157682583

theorem tailTrace_1076709 : CollatzResearch.WordTrace tailWord_1076709 prefixEnd_1076709 245719663120859157682583 := by
  unfold tailWord_1076709
  simp only [CollatzResearch.WordTrace]
  refine ⟨39270803456274655102297181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26180535637516436734864787 39270803456274655102297181)
  ·
    refine ⟨14726551296102995663361443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39270803456274655102297181 14726551296102995663361443)
    ·
      refine ⟨22089826944154493495042165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14726551296102995663361443 22089826944154493495042165)
      ·
        refine ⟨2070921276014483765160203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22089826944154493495042165 2070921276014483765160203)
        ·
          refine ⟨3106381914021725647740305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2070921276014483765160203 3106381914021725647740305)
          ·
            refine ⟨2329786435516294235805229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3106381914021725647740305 2329786435516294235805229)
            ·
              refine ⟨873669913318610338426961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2329786435516294235805229 873669913318610338426961)
              ·
                refine ⟨655252434988957753820221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 873669913318610338426961 655252434988957753820221)
                ·
                  refine ⟨245719663120859157682583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 655252434988957753820221 245719663120859157682583)
                  ·
                    rfl

theorem cell21_1076709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_1076709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076709 prefixEnd_1076709 := by exact prefixLift 1076709
  have htrace : WordTrace (prefixWord ++ tailWord_1076709) baseStart_1076709 baseEnd_1076709 := by
    simpa [prefixWord, tailWord_1076709, baseEnd_1076709] using wordTrace_append hprefix tailTrace_1076709
  have hstable : (prefixWord ++ tailWord_1076709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076709).length < 2 ^ (prefixWord ++ tailWord_1076709).sum := by decide
  have hdescent : baseEnd_1076709 < baseStart_1076709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076768 : List Nat := [2, 1, 1, 6, 1, 2, 1, 4, 3]
def baseStart_1076768 : Nat := 118140960795 + 1076768 * 2 ^ 59
def prefixEnd_1076768 : Nat := 4983230072969 + 3 ^ 40 * 1076768 * 2
def baseEnd_1076768 : Nat := 245733127724688166199129

theorem tailTrace_1076768 : CollatzResearch.WordTrace tailWord_1076768 prefixEnd_1076768 245733127724688166199129 := by
  unfold tailWord_1076768
  simp only [CollatzResearch.WordTrace]
  refine ⟨19636477681530454089347479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26181970242040605452463305 19636477681530454089347479)
  ·
    refine ⟨29454716522295681134021219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19636477681530454089347479 29454716522295681134021219)
    ·
      refine ⟨44182074783443521701031829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29454716522295681134021219 44182074783443521701031829)
      ·
        refine ⟨2071034755473915079735867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44182074783443521701031829 2071034755473915079735867)
        ·
          refine ⟨3106552133210872619603801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2071034755473915079735867 3106552133210872619603801)
          ·
            refine ⟨2329914099908154464702851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3106552133210872619603801 2329914099908154464702851)
            ·
              refine ⟨3494871149862231697054277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2329914099908154464702851 3494871149862231697054277)
              ·
                refine ⟨655288340599168443197677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3494871149862231697054277 655288340599168443197677)
                ·
                  refine ⟨245733127724688166199129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 655288340599168443197677 245733127724688166199129)
                  ·
                    rfl

theorem cell21_1076768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 3].length) (baseStart_1076768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076768 prefixEnd_1076768 := by exact prefixLift 1076768
  have htrace : WordTrace (prefixWord ++ tailWord_1076768) baseStart_1076768 baseEnd_1076768 := by
    simpa [prefixWord, tailWord_1076768, baseEnd_1076768] using wordTrace_append hprefix tailTrace_1076768
  have hstable : (prefixWord ++ tailWord_1076768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076768).length < 2 ^ (prefixWord ++ tailWord_1076768).sum := by decide
  have hdescent : baseEnd_1076768 < baseStart_1076768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076782 : List Nat := [4, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_1076782 : Nat := 118140960795 + 1076782 * 2 ^ 59
def prefixEnd_1076782 : Nat := 4983230072969 + 3 ^ 40 * 1076782 * 2
def baseEnd_1076782 : Nat := 245736322715427252965767

theorem tailTrace_1076782 : CollatzResearch.WordTrace tailWord_1076782 prefixEnd_1076782 245736322715427252965767 := by
  unfold tailWord_1076782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4909183248126273571213075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26182310656673459046469733 4909183248126273571213075)
  ·
    refine ⟨7363774872189410356819613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4909183248126273571213075 7363774872189410356819613)
    ·
      refine ⟨2761415577071028883807355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7363774872189410356819613 2761415577071028883807355)
      ·
        refine ⟨4142123365606543325711033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2761415577071028883807355 4142123365606543325711033)
        ·
          refine ⟨3106592524204907494283275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4142123365606543325711033 3106592524204907494283275)
          ·
            refine ⟨4659888786307361241424913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3106592524204907494283275 4659888786307361241424913)
            ·
              refine ⟨3494916589730520931068685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4659888786307361241424913 3494916589730520931068685)
              ·
                refine ⟨1310593721148945349150757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3494916589730520931068685 1310593721148945349150757)
                ·
                  refine ⟨245736322715427252965767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1310593721148945349150757 245736322715427252965767)
                  ·
                    rfl

theorem cell21_1076782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_1076782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076782 prefixEnd_1076782 := by exact prefixLift 1076782
  have htrace : WordTrace (prefixWord ++ tailWord_1076782) baseStart_1076782 baseEnd_1076782 := by
    simpa [prefixWord, tailWord_1076782, baseEnd_1076782] using wordTrace_append hprefix tailTrace_1076782
  have hstable : (prefixWord ++ tailWord_1076782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076782).length < 2 ^ (prefixWord ++ tailWord_1076782).sum := by decide
  have hdescent : baseEnd_1076782 < baseStart_1076782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076892 : List Nat := [2, 2, 3, 2, 4, 1, 2, 1, 4]
def baseStart_1076892 : Nat := 118140960795 + 1076892 * 2 ^ 59
def prefixEnd_1076892 : Nat := 4983230072969 + 3 ^ 40 * 1076892 * 2
def baseEnd_1076892 : Nat := 245761426214091506132209

theorem tailTrace_1076892 : CollatzResearch.WordTrace tailWord_1076892 prefixEnd_1076892 245761426214091506132209 := by
  unfold tailWord_1076892
  simp only [CollatzResearch.WordTrace]
  refine ⟨19638739007305838678104465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26184985343074451570805953 19638739007305838678104465)
  ·
    refine ⟨14729054255479379008578349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19638739007305838678104465 14729054255479379008578349)
    ·
      refine ⟨5523395345804767128216881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14729054255479379008578349 5523395345804767128216881)
      ·
        refine ⟨4142546509353575346162661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5523395345804767128216881 4142546509353575346162661)
        ·
          refine ⟨776727470503795377405499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4142546509353575346162661 776727470503795377405499)
          ·
            refine ⟨1165091205755693066108249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 776727470503795377405499 1165091205755693066108249)
            ·
              refine ⟨873818404316769799581187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1165091205755693066108249 873818404316769799581187)
              ·
                refine ⟨1310727606475154699371781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 873818404316769799581187 1310727606475154699371781)
                ·
                  refine ⟨245761426214091506132209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1310727606475154699371781 245761426214091506132209)
                  ·
                    rfl

theorem cell21_1076892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_1076892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076892 prefixEnd_1076892 := by exact prefixLift 1076892
  have htrace : WordTrace (prefixWord ++ tailWord_1076892) baseStart_1076892 baseEnd_1076892 := by
    simpa [prefixWord, tailWord_1076892, baseEnd_1076892] using wordTrace_append hprefix tailTrace_1076892
  have hstable : (prefixWord ++ tailWord_1076892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076892).length < 2 ^ (prefixWord ++ tailWord_1076892).sum := by decide
  have hdescent : baseEnd_1076892 < baseStart_1076892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076948 : List Nat := [2, 4, 1, 3, 1, 1, 3, 6]
def baseStart_1076948 : Nat := 118140960795 + 1076948 * 2 ^ 59
def prefixEnd_1076948 : Nat := 4983230072969 + 3 ^ 40 * 1076948 * 2
def baseEnd_1076948 : Nat := 81924735392349284399587

theorem tailTrace_1076948 : CollatzResearch.WordTrace tailWord_1076948 prefixEnd_1076948 81924735392349284399587 := by
  unfold tailWord_1076948
  simp only [CollatzResearch.WordTrace]
  refine ⟨19639760251204399460123749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26186347001605865946831665 19639760251204399460123749)
  ·
    refine ⟨3682455047100824898773203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19639760251204399460123749 3682455047100824898773203)
    ·
      refine ⟨5523682570651237348159805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3682455047100824898773203 5523682570651237348159805)
      ·
        refine ⟨2071380963994214005559927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5523682570651237348159805 2071380963994214005559927)
        ·
          refine ⟨3107071445991321008339891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2071380963994214005559927 3107071445991321008339891)
          ·
            refine ⟨4660607168986981512509837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3107071445991321008339891 4660607168986981512509837)
            ·
              refine ⟨1747727688370118067191189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4660607168986981512509837 1747727688370118067191189)
              ·
                refine ⟨81924735392349284399587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1747727688370118067191189 81924735392349284399587)
                ·
                  rfl

theorem cell21_1076948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 6].length) (baseStart_1076948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076948 prefixEnd_1076948 := by exact prefixLift 1076948
  have htrace : WordTrace (prefixWord ++ tailWord_1076948) baseStart_1076948 baseEnd_1076948 := by
    simpa [prefixWord, tailWord_1076948, baseEnd_1076948] using wordTrace_append hprefix tailTrace_1076948
  have hstable : (prefixWord ++ tailWord_1076948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076948).length < 2 ^ (prefixWord ++ tailWord_1076948).sum := by decide
  have hdescent : baseEnd_1076948 < baseStart_1076948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1076993 : List Nat := [1, 2, 4, 1, 1, 1, 5, 2, 4]
def baseStart_1076993 : Nat := 118140960795 + 1076993 * 2 ^ 59
def prefixEnd_1076993 : Nat := 4983230072969 + 3 ^ 40 * 1076993 * 2
def baseEnd_1076993 : Nat := 245784475790137774948669

theorem tailTrace_1076993 : CollatzResearch.WordTrace tailWord_1076993 prefixEnd_1076993 245784475790137774948669 := by
  unfold tailWord_1076993
  simp only [CollatzResearch.WordTrace]
  refine ⟨39281161787245771605635633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26187441191497181070423755 39281161787245771605635633)
  ·
    refine ⟨29460871340434328704226725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39281161787245771605635633 29460871340434328704226725)
    ·
      refine ⟨5523913376331436632042511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29460871340434328704226725 5523913376331436632042511)
      ·
        refine ⟨8285870064497154948063767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5523913376331436632042511 8285870064497154948063767)
        ·
          refine ⟨12428805096745732422095651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8285870064497154948063767 12428805096745732422095651)
          ·
            refine ⟨18643207645118598633143477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12428805096745732422095651 18643207645118598633143477)
            ·
              refine ⟨1747800716729868621857201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18643207645118598633143477 1747800716729868621857201)
              ·
                refine ⟨1310850537547401466392901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1747800716729868621857201 1310850537547401466392901)
                ·
                  refine ⟨245784475790137774948669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1310850537547401466392901 245784475790137774948669)
                  ·
                    rfl

theorem cell21_1076993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_1076993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1076993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1076993 prefixEnd_1076993 := by exact prefixLift 1076993
  have htrace : WordTrace (prefixWord ++ tailWord_1076993) baseStart_1076993 baseEnd_1076993 := by
    simpa [prefixWord, tailWord_1076993, baseEnd_1076993] using wordTrace_append hprefix tailTrace_1076993
  have hstable : (prefixWord ++ tailWord_1076993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1076993).length < 2 ^ (prefixWord ++ tailWord_1076993).sum := by decide
  have hdescent : baseEnd_1076993 < baseStart_1076993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1076993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077052 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 6]
def baseStart_1077052 : Nat := 118140960795 + 1077052 * 2 ^ 59
def prefixEnd_1077052 : Nat := 4983230072969 + 3 ^ 40 * 1077052 * 2
def baseEnd_1077052 : Nat := 245797940393966783465215

theorem tailTrace_1077052 : CollatzResearch.WordTrace tailWord_1077052 prefixEnd_1077052 245797940393966783465215 := by
  unfold tailWord_1077052
  simp only [CollatzResearch.WordTrace]
  refine ⟨19641656847016012341016705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26188875796021349788022273 19641656847016012341016705)
  ·
    refine ⟨14731242635262009255762529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19641656847016012341016705 14731242635262009255762529)
    ·
      refine ⟨11048431976446506941821897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14731242635262009255762529 11048431976446506941821897)
      ·
        refine ⟨8286323982334880206366423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11048431976446506941821897 8286323982334880206366423)
        ·
          refine ⟨12429485973502320309549635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8286323982334880206366423 12429485973502320309549635)
          ·
            refine ⟨18644228960253480464324453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12429485973502320309549635 18644228960253480464324453)
            ·
              refine ⟨3495792930047527587060835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18644228960253480464324453 3495792930047527587060835)
              ·
                refine ⟨5243689395071291380591253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3495792930047527587060835 5243689395071291380591253)
                ·
                  refine ⟨245797940393966783465215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5243689395071291380591253 245797940393966783465215)
                  ·
                    rfl

theorem cell21_1077052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_1077052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077052 prefixEnd_1077052 := by exact prefixLift 1077052
  have htrace : WordTrace (prefixWord ++ tailWord_1077052) baseStart_1077052 baseEnd_1077052 := by
    simpa [prefixWord, tailWord_1077052, baseEnd_1077052] using wordTrace_append hprefix tailTrace_1077052
  have hstable : (prefixWord ++ tailWord_1077052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077052).length < 2 ^ (prefixWord ++ tailWord_1077052).sum := by decide
  have hdescent : baseEnd_1077052 < baseStart_1077052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077055 : List Nat := [1, 1, 2, 2, 6, 2, 1, 1, 5]
def baseStart_1077055 : Nat := 118140960795 + 1077055 * 2 ^ 59
def prefixEnd_1077055 : Nat := 4983230072969 + 3 ^ 40 * 1077055 * 2
def baseEnd_1077055 : Nat := 245798625034839444915209

theorem tailTrace_1077055 : CollatzResearch.WordTrace tailWord_1077055 prefixEnd_1077055 245798625034839444915209 := by
  unfold tailWord_1077055
  simp only [CollatzResearch.WordTrace]
  refine ⟨39283423113021156194392619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26188948742014104129595079 39283423113021156194392619)
  ·
    refine ⟨58925134669531734291588929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39283423113021156194392619 58925134669531734291588929)
    ·
      refine ⟨44193851002148800718691697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58925134669531734291588929 44193851002148800718691697)
      ·
        refine ⟨33145388251611600539018773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44193851002148800718691697 33145388251611600539018773)
        ·
          refine ⟨1553690074294293775266505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33145388251611600539018773 1553690074294293775266505)
          ·
            refine ⟨1165267555720720331449879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1553690074294293775266505 1165267555720720331449879)
            ·
              refine ⟨1747901333581080497174819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1165267555720720331449879 1747901333581080497174819)
              ·
                refine ⟨2621852000371620745762229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1747901333581080497174819 2621852000371620745762229)
                ·
                  refine ⟨245798625034839444915209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2621852000371620745762229 245798625034839444915209)
                  ·
                    rfl

theorem cell21_1077055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 5].length) (baseStart_1077055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077055 prefixEnd_1077055 := by exact prefixLift 1077055
  have htrace : WordTrace (prefixWord ++ tailWord_1077055) baseStart_1077055 baseEnd_1077055 := by
    simpa [prefixWord, tailWord_1077055, baseEnd_1077055] using wordTrace_append hprefix tailTrace_1077055
  have hstable : (prefixWord ++ tailWord_1077055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077055).length < 2 ^ (prefixWord ++ tailWord_1077055).sum := by decide
  have hdescent : baseEnd_1077055 < baseStart_1077055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077148 : List Nat := [2, 2, 3, 3, 1, 2, 2, 3, 3]
def baseStart_1077148 : Nat := 118140960795 + 1077148 * 2 ^ 59
def prefixEnd_1077148 : Nat := 4983230072969 + 3 ^ 40 * 1077148 * 2
def baseEnd_1077148 : Nat := 245819848901891949865019

theorem tailTrace_1077148 : CollatzResearch.WordTrace tailWord_1077148 prefixEnd_1077148 245819848901891949865019 := by
  unfold tailWord_1077148
  simp only [CollatzResearch.WordTrace]
  refine ⟨19643407550842116538764049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26191210067789488718352065 19643407550842116538764049)
  ·
    refine ⟨14732555663131587404073037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19643407550842116538764049 14732555663131587404073037)
    ·
      refine ⟨5524708373674345276527389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14732555663131587404073037 5524708373674345276527389)
      ·
        refine ⟨2071765640127879478697771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5524708373674345276527389 2071765640127879478697771)
        ·
          refine ⟨3107648460191819218046657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2071765640127879478697771 3107648460191819218046657)
          ·
            refine ⟨2330736345143864413534993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3107648460191819218046657 2330736345143864413534993)
            ·
              refine ⟨1748052258857898310151245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2330736345143864413534993 1748052258857898310151245)
              ·
                refine ⟨655519597071711866306717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1748052258857898310151245 655519597071711866306717)
                ·
                  refine ⟨245819848901891949865019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 655519597071711866306717 245819848901891949865019)
                  ·
                    rfl

theorem cell21_1077148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_1077148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077148 prefixEnd_1077148 := by exact prefixLift 1077148
  have htrace : WordTrace (prefixWord ++ tailWord_1077148) baseStart_1077148 baseEnd_1077148 := by
    simpa [prefixWord, tailWord_1077148, baseEnd_1077148] using wordTrace_append hprefix tailTrace_1077148
  have hstable : (prefixWord ++ tailWord_1077148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077148).length < 2 ^ (prefixWord ++ tailWord_1077148).sum := by decide
  have hdescent : baseEnd_1077148 < baseStart_1077148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077159 : List Nat := [1, 1, 6, 1, 2, 2, 8]
def baseStart_1077159 : Nat := 118140960795 + 1077159 * 2 ^ 59
def prefixEnd_1077159 : Nat := 4983230072969 + 3 ^ 40 * 1077159 * 2
def baseEnd_1077159 : Nat := 27313595472417597242407

theorem tailTrace_1077159 : CollatzResearch.WordTrace tailWord_1077159 prefixEnd_1077159 27313595472417597242407 := by
  unfold tailWord_1077159
  simp only [CollatzResearch.WordTrace]
  refine ⟨39287216304644381956178531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26191477536429587970785687 39287216304644381956178531)
  ·
    refine ⟨58930824456966572934267797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39287216304644381956178531 58930824456966572934267797)
    ·
      refine ⟨2762382396420308106293803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58930824456966572934267797 2762382396420308106293803)
      ·
        refine ⟨4143573594630462159440705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2762382396420308106293803 4143573594630462159440705)
        ·
          refine ⟨3107680195972846619580529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4143573594630462159440705 3107680195972846619580529)
          ·
            refine ⟨2330760146979634964685397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3107680195972846619580529 2330760146979634964685397)
            ·
              refine ⟨27313595472417597242407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2330760146979634964685397 27313595472417597242407)
              ·
                rfl

theorem cell21_1077159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 8].length) (baseStart_1077159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077159 prefixEnd_1077159 := by exact prefixLift 1077159
  have htrace : WordTrace (prefixWord ++ tailWord_1077159) baseStart_1077159 baseEnd_1077159 := by
    simpa [prefixWord, tailWord_1077159, baseEnd_1077159] using wordTrace_append hprefix tailTrace_1077159
  have hstable : (prefixWord ++ tailWord_1077159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077159).length < 2 ^ (prefixWord ++ tailWord_1077159).sum := by decide
  have hdescent : baseEnd_1077159 < baseStart_1077159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077187 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 10]
def baseStart_1077187 : Nat := 118140960795 + 1077187 * 2 ^ 59
def prefixEnd_1077187 : Nat := 4983230072969 + 3 ^ 40 * 1077187 * 2
def baseEnd_1077187 : Nat := 245828749233236548714939

theorem tailTrace_1077187 : CollatzResearch.WordTrace tailWord_1077187 prefixEnd_1077187 245828749233236548714939 := by
  unfold tailWord_1077187
  simp only [CollatzResearch.WordTrace]
  refine ⟨39288237548542942738197815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26192158365695295158798543 39288237548542942738197815)
  ·
    refine ⟨58932356322814414107296723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39288237548542942738197815 58932356322814414107296723)
    ·
      refine ⟨88398534484221621160945085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58932356322814414107296723 88398534484221621160945085)
      ·
        refine ⟨33149450431583107935354407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88398534484221621160945085 33149450431583107935354407)
        ·
          refine ⟨49724175647374661903031611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33149450431583107935354407 49724175647374661903031611)
          ·
            refine ⟨74586263471061992854547417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49724175647374661903031611 74586263471061992854547417)
            ·
              refine ⟨55939697603296494640910563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74586263471061992854547417 55939697603296494640910563)
              ·
                refine ⟨83909546404944741961365845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55939697603296494640910563 83909546404944741961365845)
                ·
                  refine ⟨245828749233236548714939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 83909546404944741961365845 245828749233236548714939)
                  ·
                    rfl

theorem cell21_1077187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 10].length) (baseStart_1077187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077187 prefixEnd_1077187 := by exact prefixLift 1077187
  have htrace : WordTrace (prefixWord ++ tailWord_1077187) baseStart_1077187 baseEnd_1077187 := by
    simpa [prefixWord, tailWord_1077187, baseEnd_1077187] using wordTrace_append hprefix tailTrace_1077187
  have hstable : (prefixWord ++ tailWord_1077187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077187).length < 2 ^ (prefixWord ++ tailWord_1077187).sum := by decide
  have hdescent : baseEnd_1077187 < baseStart_1077187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077204 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 8]
def baseStart_1077204 : Nat := 118140960795 + 1077204 * 2 ^ 59
def prefixEnd_1077204 : Nat := 4983230072969 + 3 ^ 40 * 1077204 * 2
def baseEnd_1077204 : Nat := 245832628864848296931571

theorem tailTrace_1077204 : CollatzResearch.WordTrace tailWord_1077204 prefixEnd_1077204 245832628864848296931571 := by
  unfold tailWord_1077204
  simp only [CollatzResearch.WordTrace]
  refine ⟨19644428794740677320783333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26192571726320903094377777 19644428794740677320783333)
  ·
    refine ⟨3683330399013876997646875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19644428794740677320783333 3683330399013876997646875)
    ·
      refine ⟨5524995598520815496470313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3683330399013876997646875 5524995598520815496470313)
      ·
        refine ⟨4143746698890611622352735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5524995598520815496470313 4143746698890611622352735)
        ·
          refine ⟨6215620048335917433529103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4143746698890611622352735 6215620048335917433529103)
          ·
            refine ⟨9323430072503876150293655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6215620048335917433529103 9323430072503876150293655)
            ·
              refine ⟨13985145108755814225440483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9323430072503876150293655 13985145108755814225440483)
              ·
                refine ⟨20977717663133721338160725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13985145108755814225440483 20977717663133721338160725)
                ·
                  refine ⟨245832628864848296931571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20977717663133721338160725 245832628864848296931571)
                  ·
                    rfl

theorem cell21_1077204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_1077204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077204 prefixEnd_1077204 := by exact prefixLift 1077204
  have htrace : WordTrace (prefixWord ++ tailWord_1077204) baseStart_1077204 baseEnd_1077204 := by
    simpa [prefixWord, tailWord_1077204, baseEnd_1077204] using wordTrace_append hprefix tailTrace_1077204
  have hstable : (prefixWord ++ tailWord_1077204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077204).length < 2 ^ (prefixWord ++ tailWord_1077204).sum := by decide
  have hdescent : baseEnd_1077204 < baseStart_1077204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077238 : List Nat := [5, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_1077238 : Nat := 118140960795 + 1077238 * 2 ^ 59
def prefixEnd_1077238 : Nat := 4983230072969 + 3 ^ 40 * 1077238 * 2
def baseEnd_1077238 : Nat := 245840388128071793364835

theorem tailTrace_1077238 : CollatzResearch.WordTrace tailWord_1077238 prefixEnd_1077238 245840388128071793364835 := by
  unfold tailWord_1077238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2455631104459886153019023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26193398447572118965536245 2455631104459886153019023)
  ·
    refine ⟨3683446656689829229528535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2455631104459886153019023 3683446656689829229528535)
    ·
      refine ⟨5525169985034743844292803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3683446656689829229528535 5525169985034743844292803)
      ·
        refine ⟨8287754977552115766439205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5525169985034743844292803 8287754977552115766439205)
        ·
          refine ⟨1553954058291021706207351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8287754977552115766439205 1553954058291021706207351)
          ·
            refine ⟨2330931087436532559311027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1553954058291021706207351 2330931087436532559311027)
            ·
              refine ⟨3496396631154798838966541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2330931087436532559311027 3496396631154798838966541)
              ·
                refine ⟨1311148736683049564612453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3496396631154798838966541 1311148736683049564612453)
                ·
                  refine ⟨245840388128071793364835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1311148736683049564612453 245840388128071793364835)
                  ·
                    rfl

theorem cell21_1077238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_1077238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077238 prefixEnd_1077238 := by exact prefixLift 1077238
  have htrace : WordTrace (prefixWord ++ tailWord_1077238) baseStart_1077238 baseEnd_1077238 := by
    simpa [prefixWord, tailWord_1077238, baseEnd_1077238] using wordTrace_append hprefix tailTrace_1077238
  have hstable : (prefixWord ++ tailWord_1077238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077238).length < 2 ^ (prefixWord ++ tailWord_1077238).sum := by decide
  have hdescent : baseEnd_1077238 < baseStart_1077238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077249 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 7]
def baseStart_1077249 : Nat := 118140960795 + 1077249 * 2 ^ 59
def prefixEnd_1077249 : Nat := 4983230072969 + 3 ^ 40 * 1077249 * 2
def baseEnd_1077249 : Nat := 245842898477938218681479

theorem tailTrace_1077249 : CollatzResearch.WordTrace tailWord_1077249 prefixEnd_1077249 245842898477938218681479 := by
  unfold tailWord_1077249
  simp only [CollatzResearch.WordTrace]
  refine ⟨39290498874318327326954801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26193665916212218217969867 39290498874318327326954801)
  ·
    refine ⟨29467874155738745495216101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39290498874318327326954801 29467874155738745495216101)
    ·
      refine ⟨5525226404201014780353019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29467874155738745495216101 5525226404201014780353019)
      ·
        refine ⟨8287839606301522170529529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5525226404201014780353019 8287839606301522170529529)
        ·
          refine ⟨6215879704726141627897147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8287839606301522170529529 6215879704726141627897147)
          ·
            refine ⟨9323819557089212441845721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6215879704726141627897147 9323819557089212441845721)
            ·
              refine ⟨6992864667816909331384291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9323819557089212441845721 6992864667816909331384291)
              ·
                refine ⟨10489297001725363997076437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6992864667816909331384291 10489297001725363997076437)
                ·
                  refine ⟨245842898477938218681479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10489297001725363997076437 245842898477938218681479)
                  ·
                    rfl

theorem cell21_1077249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_1077249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077249 prefixEnd_1077249 := by exact prefixLift 1077249
  have htrace : WordTrace (prefixWord ++ tailWord_1077249) baseStart_1077249 baseEnd_1077249 := by
    simpa [prefixWord, tailWord_1077249, baseEnd_1077249] using wordTrace_append hprefix tailTrace_1077249
  have hstable : (prefixWord ++ tailWord_1077249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077249).length < 2 ^ (prefixWord ++ tailWord_1077249).sum := by decide
  have hdescent : baseEnd_1077249 < baseStart_1077249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077452 : List Nat := [2, 2, 1, 6, 1, 1, 1, 4, 3]
def baseStart_1077452 : Nat := 118140960795 + 1077452 * 2 ^ 59
def prefixEnd_1077452 : Nat := 4983230072969 + 3 ^ 40 * 1077452 * 2
def baseEnd_1077452 : Nat := 245889225843654976797731

theorem tailTrace_1077452 : CollatzResearch.WordTrace tailWord_1077452 prefixEnd_1077452 245889225843654976797731 := by
  unfold tailWord_1077452
  simp only [CollatzResearch.WordTrace]
  refine ⟨19648951446291446498297305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26198601928388595331063073 19648951446291446498297305)
  ·
    refine ⟨14736713584718584873722979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19648951446291446498297305 14736713584718584873722979)
    ·
      refine ⟨22105070377077877310584469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14736713584718584873722979 22105070377077877310584469)
      ·
        refine ⟨1036175173925525498933647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22105070377077877310584469 1036175173925525498933647)
        ·
          refine ⟨1554262760888288248400471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1036175173925525498933647 1554262760888288248400471)
          ·
            refine ⟨2331394141332432372600707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1554262760888288248400471 2331394141332432372600707)
            ·
              refine ⟨3497091211998648558901061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2331394141332432372600707 3497091211998648558901061)
              ·
                refine ⟨655704602249746604793949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3497091211998648558901061 655704602249746604793949)
                ·
                  refine ⟨245889225843654976797731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 655704602249746604793949 245889225843654976797731)
                  ·
                    rfl

theorem cell21_1077452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_1077452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077452 prefixEnd_1077452 := by exact prefixLift 1077452
  have htrace : WordTrace (prefixWord ++ tailWord_1077452) baseStart_1077452 baseEnd_1077452 := by
    simpa [prefixWord, tailWord_1077452, baseEnd_1077452] using wordTrace_append hprefix tailTrace_1077452
  have hstable : (prefixWord ++ tailWord_1077452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077452).length < 2 ^ (prefixWord ++ tailWord_1077452).sum := by decide
  have hdescent : baseEnd_1077452 < baseStart_1077452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077477 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 7]
def baseStart_1077477 : Nat := 118140960795 + 1077477 * 2 ^ 59
def prefixEnd_1077477 : Nat := 4983230072969 + 3 ^ 40 * 1077477 * 2
def baseEnd_1077477 : Nat := 245894931184260488881013

theorem tailTrace_1077477 : CollatzResearch.WordTrace tailWord_1077477 prefixEnd_1077477 245894931184260488881013 := by
  unfold tailWord_1077477
  simp only [CollatzResearch.WordTrace]
  refine ⟨39298814717492322266254685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26199209811661548177503123 39298814717492322266254685)
  ·
    refine ⟨14737055519059620849845507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39298814717492322266254685 14737055519059620849845507)
    ·
      refine ⟨22105583278589431274768261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14737055519059620849845507 22105583278589431274768261)
      ·
        refine ⟨4144796864735518364019049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22105583278589431274768261 4144796864735518364019049)
        ·
          refine ⟨3108597648551638773014287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4144796864735518364019049 3108597648551638773014287)
          ·
            refine ⟨4662896472827458159521431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3108597648551638773014287 4662896472827458159521431)
            ·
              refine ⟨6994344709241187239282147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4662896472827458159521431 6994344709241187239282147)
              ·
                refine ⟨10491517063861780858923221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6994344709241187239282147 10491517063861780858923221)
                ·
                  refine ⟨245894931184260488881013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10491517063861780858923221 245894931184260488881013)
                  ·
                    rfl

theorem cell21_1077477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_1077477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077477 prefixEnd_1077477 := by exact prefixLift 1077477
  have htrace : WordTrace (prefixWord ++ tailWord_1077477) baseStart_1077477 baseEnd_1077477 := by
    simpa [prefixWord, tailWord_1077477, baseEnd_1077477] using wordTrace_append hprefix tailTrace_1077477
  have hstable : (prefixWord ++ tailWord_1077477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077477).length < 2 ^ (prefixWord ++ tailWord_1077477).sum := by decide
  have hdescent : baseEnd_1077477 < baseStart_1077477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077491 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 6]
def baseStart_1077491 : Nat := 118140960795 + 1077491 * 2 ^ 59
def prefixEnd_1077491 : Nat := 4983230072969 + 3 ^ 40 * 1077491 * 2
def baseEnd_1077491 : Nat := 245898126174999575647651

theorem tailTrace_1077491 : CollatzResearch.WordTrace tailWord_1077491 prefixEnd_1077491 245898126174999575647651 := by
  unfold tailWord_1077491
  simp only [CollatzResearch.WordTrace]
  refine ⟨39299325339441602657264327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26199550226294401771509551 39299325339441602657264327)
  ·
    refine ⟨58948988009162403985896491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39299325339441602657264327 58948988009162403985896491)
    ·
      refine ⟨88423482013743605978844737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58948988009162403985896491 88423482013743605978844737)
      ·
        refine ⟨66317611510307704484133553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88423482013743605978844737 66317611510307704484133553)
        ·
          refine ⟨49738208632730778363100165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66317611510307704484133553 49738208632730778363100165)
          ·
            refine ⟨9325914118637020943081281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49738208632730778363100165 9325914118637020943081281)
            ·
              refine ⟨6994435588977765707310961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9325914118637020943081281 6994435588977765707310961)
              ·
                refine ⟨5245826691733324280483221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6994435588977765707310961 5245826691733324280483221)
                ·
                  refine ⟨245898126174999575647651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5245826691733324280483221 245898126174999575647651)
                  ·
                    rfl

theorem cell21_1077491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 6].length) (baseStart_1077491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077491 prefixEnd_1077491 := by exact prefixLift 1077491
  have htrace : WordTrace (prefixWord ++ tailWord_1077491) baseStart_1077491 baseEnd_1077491 := by
    simpa [prefixWord, tailWord_1077491, baseEnd_1077491] using wordTrace_append hprefix tailTrace_1077491
  have hstable : (prefixWord ++ tailWord_1077491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077491).length < 2 ^ (prefixWord ++ tailWord_1077491).sum := by decide
  have hdescent : baseEnd_1077491 < baseStart_1077491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077511 : List Nat := [1, 1, 4, 5, 1, 1, 2, 1, 5]
def baseStart_1077511 : Nat := 118140960795 + 1077511 * 2 ^ 59
def prefixEnd_1077511 : Nat := 4983230072969 + 3 ^ 40 * 1077511 * 2
def baseEnd_1077511 : Nat := 245902690447483985314277

theorem tailTrace_1077511 : CollatzResearch.WordTrace tailWord_1077511 prefixEnd_1077511 245902690447483985314277 := by
  unfold tailWord_1077511
  simp only [CollatzResearch.WordTrace]
  refine ⟨39300054799369146072992387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26200036532912764048661591 39300054799369146072992387)
  ·
    refine ⟨58950082199053719109488581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39300054799369146072992387 58950082199053719109488581)
    ·
      refine ⟨11053140412322572333029109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58950082199053719109488581 11053140412322572333029109)
      ·
        refine ⟨1036231913655241156221479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11053140412322572333029109 1036231913655241156221479)
        ·
          refine ⟨1554347870482861734332219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1036231913655241156221479 1554347870482861734332219)
          ·
            refine ⟨2331521805724292601498329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1554347870482861734332219 2331521805724292601498329)
            ·
              refine ⟨1748641354293219451123747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2331521805724292601498329 1748641354293219451123747)
              ·
                refine ⟨2622962031439829176685621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1748641354293219451123747 2622962031439829176685621)
                ·
                  refine ⟨245902690447483985314277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2622962031439829176685621 245902690447483985314277)
                  ·
                    rfl

theorem cell21_1077511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 5].length) (baseStart_1077511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077511 prefixEnd_1077511 := by exact prefixLift 1077511
  have htrace : WordTrace (prefixWord ++ tailWord_1077511) baseStart_1077511 baseEnd_1077511 := by
    simpa [prefixWord, tailWord_1077511, baseEnd_1077511] using wordTrace_append hprefix tailTrace_1077511
  have hstable : (prefixWord ++ tailWord_1077511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077511).length < 2 ^ (prefixWord ++ tailWord_1077511).sum := by decide
  have hdescent : baseEnd_1077511 < baseStart_1077511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077567 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 6]
def baseStart_1077567 : Nat := 118140960795 + 1077567 * 2 ^ 59
def prefixEnd_1077567 : Nat := 4983230072969 + 3 ^ 40 * 1077567 * 2
def baseEnd_1077567 : Nat := 245915470410440332380829

theorem tailTrace_1077567 : CollatzResearch.WordTrace tailWord_1077567 prefixEnd_1077567 245915470410440332380829 := by
  unfold tailWord_1077567
  simp only [CollatzResearch.WordTrace]
  refine ⟨39302097287166267637030955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26201398191444178424687303 39302097287166267637030955)
  ·
    refine ⟨58953145930749401455546433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39302097287166267637030955 58953145930749401455546433)
    ·
      refine ⟨44214859448062051091659825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58953145930749401455546433 44214859448062051091659825)
      ·
        refine ⟨33161144586046538318744869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44214859448062051091659825 33161144586046538318744869)
        ·
          refine ⟨6217714609883725934764663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33161144586046538318744869 6217714609883725934764663)
          ·
            refine ⟨9326571914825588902146995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6217714609883725934764663 9326571914825588902146995)
            ·
              refine ⟨13989857872238383353220493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9326571914825588902146995 13989857872238383353220493)
              ·
                refine ⟨5246196702089393757457685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13989857872238383353220493 5246196702089393757457685)
                ·
                  refine ⟨245915470410440332380829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5246196702089393757457685 245915470410440332380829)
                  ·
                    rfl

theorem cell21_1077567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 6].length) (baseStart_1077567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077567 prefixEnd_1077567 := by exact prefixLift 1077567
  have htrace : WordTrace (prefixWord ++ tailWord_1077567) baseStart_1077567 baseEnd_1077567 := by
    simpa [prefixWord, tailWord_1077567, baseEnd_1077567] using wordTrace_append hprefix tailTrace_1077567
  have hstable : (prefixWord ++ tailWord_1077567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077567).length < 2 ^ (prefixWord ++ tailWord_1077567).sum := by decide
  have hdescent : baseEnd_1077567 < baseStart_1077567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077584 : List Nat := [2, 1, 1, 1, 1, 7, 1, 3, 4]
def baseStart_1077584 : Nat := 118140960795 + 1077584 * 2 ^ 59
def prefixEnd_1077584 : Nat := 4983230072969 + 3 ^ 40 * 1077584 * 2
def baseEnd_1077584 : Nat := 245919350042052080597461

theorem tailTrace_1077584 : CollatzResearch.WordTrace tailWord_1077584 prefixEnd_1077584 245919350042052080597461 := by
  unfold tailWord_1077584
  simp only [CollatzResearch.WordTrace]
  refine ⟨19651358664052339770199903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26201811552069786360266537 19651358664052339770199903)
  ·
    refine ⟨29477037996078509655299855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19651358664052339770199903 29477037996078509655299855)
    ·
      refine ⟨44215556994117764482949783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29477037996078509655299855 44215556994117764482949783)
      ·
        refine ⟨66323335491176646724424675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44215556994117764482949783 66323335491176646724424675)
        ·
          refine ⟨99485003236764970086637013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66323335491176646724424675 99485003236764970086637013)
          ·
            refine ⟨2331679763361678986405555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 99485003236764970086637013 2331679763361678986405555)
            ·
              refine ⟨3497519645042518479608333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2331679763361678986405555 3497519645042518479608333)
              ·
                refine ⟨1311569866890944429853125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3497519645042518479608333 1311569866890944429853125)
                ·
                  refine ⟨245919350042052080597461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1311569866890944429853125 245919350042052080597461)
                  ·
                    rfl

theorem cell21_1077584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_1077584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077584 prefixEnd_1077584 := by exact prefixLift 1077584
  have htrace : WordTrace (prefixWord ++ tailWord_1077584) baseStart_1077584 baseEnd_1077584 := by
    simpa [prefixWord, tailWord_1077584, baseEnd_1077584] using wordTrace_append hprefix tailTrace_1077584
  have hstable : (prefixWord ++ tailWord_1077584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077584).length < 2 ^ (prefixWord ++ tailWord_1077584).sum := by decide
  have hdescent : baseEnd_1077584 < baseStart_1077584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077646 : List Nat := [4, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_1077646 : Nat := 118140960795 + 1077646 * 2 ^ 59
def prefixEnd_1077646 : Nat := 4983230072969 + 3 ^ 40 * 1077646 * 2
def baseEnd_1077646 : Nat := 245933499286753750564001

theorem tailTrace_1077646 : CollatzResearch.WordTrace tailWord_1077646 prefixEnd_1077646 245933499286753750564001 := by
  unfold tailWord_1077646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4913122331735008016144599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26203319102586709419437861 4913122331735008016144599)
  ·
    refine ⟨7369683497602512024216899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4913122331735008016144599 7369683497602512024216899)
    ·
      refine ⟨11054525246403768036325349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7369683497602512024216899 11054525246403768036325349)
      ·
        refine ⟨2072723483700706506811003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11054525246403768036325349 2072723483700706506811003)
        ·
          refine ⟨3109085225551059760216505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2072723483700706506811003 3109085225551059760216505)
          ·
            refine ⟨2331813919163294820162379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3109085225551059760216505 2331813919163294820162379)
            ·
              refine ⟨3497720878744942230243569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2331813919163294820162379 3497720878744942230243569)
              ·
                refine ⟨2623290659058706672682677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3497720878744942230243569 2623290659058706672682677)
                ·
                  refine ⟨245933499286753750564001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2623290659058706672682677 245933499286753750564001)
                  ·
                    rfl

theorem cell21_1077646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_1077646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077646 prefixEnd_1077646 := by exact prefixLift 1077646
  have htrace : WordTrace (prefixWord ++ tailWord_1077646) baseStart_1077646 baseEnd_1077646 := by
    simpa [prefixWord, tailWord_1077646, baseEnd_1077646] using wordTrace_append hprefix tailTrace_1077646
  have hstable : (prefixWord ++ tailWord_1077646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077646).length < 2 ^ (prefixWord ++ tailWord_1077646).sum := by decide
  have hdescent : baseEnd_1077646 < baseStart_1077646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077677 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 6]
def baseStart_1077677 : Nat := 118140960795 + 1077677 * 2 ^ 59
def prefixEnd_1077677 : Nat := 4983230072969 + 3 ^ 40 * 1077677 * 2
def baseEnd_1077677 : Nat := 245940573909104585547271

theorem tailTrace_1077677 : CollatzResearch.WordTrace tailWord_1077677 prefixEnd_1077677 245940573909104585547271 := by
  unfold tailWord_1077677
  simp only [CollatzResearch.WordTrace]
  refine ⟨39306109316767756423535285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26204072877845170949023523 39306109316767756423535285)
  ·
    refine ⟨3684947748446977164706433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39306109316767756423535285 3684947748446977164706433)
    ·
      refine ⟨2763710811335232873529825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3684947748446977164706433 2763710811335232873529825)
      ·
        refine ⟨2072783108501424655147369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2763710811335232873529825 2072783108501424655147369)
        ·
          refine ⟨1554587331376068491360527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2072783108501424655147369 1554587331376068491360527)
          ·
            refine ⟨2331880997064102737040791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1554587331376068491360527 2331880997064102737040791)
            ·
              refine ⟨3497821495596154105561187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2331880997064102737040791 3497821495596154105561187)
              ·
                refine ⟨5246732243394231158341781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3497821495596154105561187 5246732243394231158341781)
                ·
                  refine ⟨245940573909104585547271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5246732243394231158341781 245940573909104585547271)
                  ·
                    rfl

theorem cell21_1077677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_1077677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077677 prefixEnd_1077677 := by exact prefixLift 1077677
  have htrace : WordTrace (prefixWord ++ tailWord_1077677) baseStart_1077677 baseEnd_1077677 := by
    simpa [prefixWord, tailWord_1077677, baseEnd_1077677] using wordTrace_append hprefix tailTrace_1077677
  have hstable : (prefixWord ++ tailWord_1077677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077677).length < 2 ^ (prefixWord ++ tailWord_1077677).sum := by decide
  have hdescent : baseEnd_1077677 < baseStart_1077677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077708 : List Nat := [2, 2, 1, 4, 3, 2, 2, 5]
def baseStart_1077708 : Nat := 118140960795 + 1077708 * 2 ^ 59
def prefixEnd_1077708 : Nat := 4983230072969 + 3 ^ 40 * 1077708 * 2
def baseEnd_1077708 : Nat := 81982549510485140176847

theorem tailTrace_1077708 : CollatzResearch.WordTrace tailWord_1077708 prefixEnd_1077708 81982549510485140176847 := by
  unfold tailWord_1077708
  simp only [CollatzResearch.WordTrace]
  refine ⟨19653619989827724358956889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26204826653103632478609185 19653619989827724358956889)
  ·
    refine ⟨14740214992370793269217667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19653619989827724358956889 14740214992370793269217667)
    ·
      refine ⟨22110322488556189903826501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14740214992370793269217667 22110322488556189903826501)
      ·
        refine ⟨4145685466604285606967469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22110322488556189903826501 4145685466604285606967469)
        ·
          refine ⟨1554632049976607102612801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4145685466604285606967469 1554632049976607102612801)
          ·
            refine ⟨1165974037482455326959601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1554632049976607102612801 1165974037482455326959601)
            ·
              refine ⟨874480528111841495219701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1165974037482455326959601 874480528111841495219701)
              ·
                refine ⟨81982549510485140176847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 874480528111841495219701 81982549510485140176847)
                ·
                  rfl

theorem cell21_1077708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 5].length) (baseStart_1077708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077708 prefixEnd_1077708 := by exact prefixLift 1077708
  have htrace : WordTrace (prefixWord ++ tailWord_1077708) baseStart_1077708 baseEnd_1077708 := by
    simpa [prefixWord, tailWord_1077708, baseEnd_1077708] using wordTrace_append hprefix tailTrace_1077708
  have hstable : (prefixWord ++ tailWord_1077708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077708).length < 2 ^ (prefixWord ++ tailWord_1077708).sum := by decide
  have hdescent : baseEnd_1077708 < baseStart_1077708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077857 : List Nat := [1, 2, 3, 1, 1, 5, 2, 1, 5]
def baseStart_1077857 : Nat := 118140960795 + 1077857 * 2 ^ 59
def prefixEnd_1077857 : Nat := 4983230072969 + 3 ^ 40 * 1077857 * 2
def baseEnd_1077857 : Nat := 245981652361464272546903

theorem tailTrace_1077857 : CollatzResearch.WordTrace tailWord_1077857 prefixEnd_1077857 245981652361464272546903 := by
  unfold tailWord_1077857
  simp only [CollatzResearch.WordTrace]
  refine ⟨39312674456115647165087825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26208449637410431443391883 39312674456115647165087825)
  ·
    refine ⟨29484505842086735373815869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39312674456115647165087825 29484505842086735373815869)
    ·
      refine ⟨11056689690782525765180951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29484505842086735373815869 11056689690782525765180951)
      ·
        refine ⟨16585034536173788647771427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11056689690782525765180951 16585034536173788647771427)
        ·
          refine ⟨24877551804260682971657141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16585034536173788647771427 24877551804260682971657141)
          ·
            refine ⟨2332270481649439028592857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24877551804260682971657141 2332270481649439028592857)
            ·
              refine ⟨1749202861237079271444643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2332270481649439028592857 1749202861237079271444643)
              ·
                refine ⟨2623804291855618907166965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1749202861237079271444643 2623804291855618907166965)
                ·
                  refine ⟨245981652361464272546903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2623804291855618907166965 245981652361464272546903)
                  ·
                    rfl

theorem cell21_1077857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_1077857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077857 prefixEnd_1077857 := by exact prefixLift 1077857
  have htrace : WordTrace (prefixWord ++ tailWord_1077857) baseStart_1077857 baseEnd_1077857 := by
    simpa [prefixWord, tailWord_1077857, baseEnd_1077857] using wordTrace_append hprefix tailTrace_1077857
  have hstable : (prefixWord ++ tailWord_1077857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077857).length < 2 ^ (prefixWord ++ tailWord_1077857).sum := by decide
  have hdescent : baseEnd_1077857 < baseStart_1077857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077871 : List Nat := [1, 1, 2, 1, 3, 2, 2, 5, 4]
def baseStart_1077871 : Nat := 118140960795 + 1077871 * 2 ^ 59
def prefixEnd_1077871 : Nat := 4983230072969 + 3 ^ 40 * 1077871 * 2
def baseEnd_1077871 : Nat := 245984847352203359313541

theorem tailTrace_1077871 : CollatzResearch.WordTrace tailWord_1077871 prefixEnd_1077871 245984847352203359313541 := by
  unfold tailWord_1077871
  simp only [CollatzResearch.WordTrace]
  refine ⟨39313185078064927556097467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26208790052043285037398311 39313185078064927556097467)
  ·
    refine ⟨58969777617097391334146201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39313185078064927556097467 58969777617097391334146201)
    ·
      refine ⟨44227333212823043500609651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58969777617097391334146201 44227333212823043500609651)
      ·
        refine ⟨66340999819234565250914477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44227333212823043500609651 66340999819234565250914477)
        ·
          refine ⟨24877874932212961969092929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66340999819234565250914477 24877874932212961969092929)
          ·
            refine ⟨18658406199159721476819697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24877874932212961969092929 18658406199159721476819697)
            ·
              refine ⟨13993804649369791107614773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18658406199159721476819697 13993804649369791107614773)
              ·
                refine ⟨1311919185878417916338885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13993804649369791107614773 1311919185878417916338885)
                ·
                  refine ⟨245984847352203359313541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1311919185878417916338885 245984847352203359313541)
                  ·
                    rfl

theorem cell21_1077871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 4].length) (baseStart_1077871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077871 prefixEnd_1077871 := by exact prefixLift 1077871
  have htrace : WordTrace (prefixWord ++ tailWord_1077871) baseStart_1077871 baseEnd_1077871 := by
    simpa [prefixWord, tailWord_1077871, baseEnd_1077871] using wordTrace_append hprefix tailTrace_1077871
  have hstable : (prefixWord ++ tailWord_1077871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077871).length < 2 ^ (prefixWord ++ tailWord_1077871).sum := by decide
  have hdescent : baseEnd_1077871 < baseStart_1077871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077877 : List Nat := [1, 3, 4, 2, 3, 1, 2, 5]
def baseStart_1077877 : Nat := 118140960795 + 1077877 * 2 ^ 59
def prefixEnd_1077877 : Nat := 4983230072969 + 3 ^ 40 * 1077877 * 2
def baseEnd_1077877 : Nat := 81995405544649560737843

theorem tailTrace_1077877 : CollatzResearch.WordTrace tailWord_1077877 prefixEnd_1077877 81995405544649560737843 := by
  unfold tailWord_1077877
  simp only [CollatzResearch.WordTrace]
  refine ⟨39313403916043190580815885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26208935944028793720543923 39313403916043190580815885)
  ·
    refine ⟨14742526468516196467805957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39313403916043190580815885 14742526468516196467805957)
    ·
      refine ⟨2764223712846786837713617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14742526468516196467805957 2764223712846786837713617)
      ·
        refine ⟨2073167784635090128285213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2764223712846786837713617 2073167784635090128285213)
        ·
          refine ⟨777437919238158798106955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2073167784635090128285213 777437919238158798106955)
          ·
            refine ⟨1166156878857238197160433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777437919238158798106955 1166156878857238197160433)
            ·
              refine ⟨874617659142928647870325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1166156878857238197160433 874617659142928647870325)
              ·
                refine ⟨81995405544649560737843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 874617659142928647870325 81995405544649560737843)
                ·
                  rfl

theorem cell21_1077877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 5].length) (baseStart_1077877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077877 prefixEnd_1077877 := by exact prefixLift 1077877
  have htrace : WordTrace (prefixWord ++ tailWord_1077877) baseStart_1077877 baseEnd_1077877 := by
    simpa [prefixWord, tailWord_1077877, baseEnd_1077877] using wordTrace_append hprefix tailTrace_1077877
  have hstable : (prefixWord ++ tailWord_1077877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077877).length < 2 ^ (prefixWord ++ tailWord_1077877).sum := by decide
  have hdescent : baseEnd_1077877 < baseStart_1077877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077908 : List Nat := [2, 4, 2, 2, 1, 2, 3, 2, 3]
def baseStart_1077908 : Nat := 118140960795 + 1077908 * 2 ^ 59
def prefixEnd_1077908 : Nat := 4983230072969 + 3 ^ 40 * 1077908 * 2
def baseEnd_1077908 : Nat := 245993291256299517196799

theorem tailTrace_1077908 : CollatzResearch.WordTrace tailWord_1077908 prefixEnd_1077908 245993291256299517196799 := by
  unfold tailWord_1077908
  simp only [CollatzResearch.WordTrace]
  refine ⟨19657267289465441437597189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26209689719287255250129585 19657267289465441437597189)
  ·
    refine ⟨3685737616774770269549473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19657267289465441437597189 3685737616774770269549473)
    ·
      refine ⟨2764303212581077702162105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3685737616774770269549473 2764303212581077702162105)
      ·
        refine ⟨2073227409435808276621579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2764303212581077702162105 2073227409435808276621579)
        ·
          refine ⟨3109841114153712414932369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2073227409435808276621579 3109841114153712414932369)
          ·
            refine ⟨2332380835615284311199277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3109841114153712414932369 2332380835615284311199277)
            ·
              refine ⟨874642813355731616699729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2332380835615284311199277 874642813355731616699729)
              ·
                refine ⟨655982110016798712524797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 874642813355731616699729 655982110016798712524797)
                ·
                  refine ⟨245993291256299517196799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 655982110016798712524797 245993291256299517196799)
                  ·
                    rfl

theorem cell21_1077908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_1077908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077908 prefixEnd_1077908 := by exact prefixLift 1077908
  have htrace : WordTrace (prefixWord ++ tailWord_1077908) baseStart_1077908 baseEnd_1077908 := by
    simpa [prefixWord, tailWord_1077908, baseEnd_1077908] using wordTrace_append hprefix tailTrace_1077908
  have hstable : (prefixWord ++ tailWord_1077908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077908).length < 2 ^ (prefixWord ++ tailWord_1077908).sum := by decide
  have hdescent : baseEnd_1077908 < baseStart_1077908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077950 : List Nat := [4, 2, 1, 1, 2, 1, 2, 5, 3]
def baseStart_1077950 : Nat := 118140960795 + 1077950 * 2 ^ 59
def prefixEnd_1077950 : Nat := 4983230072969 + 3 ^ 40 * 1077950 * 2
def baseEnd_1077950 : Nat := 246002876228516777496713

theorem tailTrace_1077950 : CollatzResearch.WordTrace tailWord_1077950 prefixEnd_1077950 246002876228516777496713 := by
  unfold tailWord_1077950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4914508305597340506027913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26210710963185816032148869 4914508305597340506027913)
  ·
    refine ⟨3685881229198005379520935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4914508305597340506027913 3685881229198005379520935)
    ·
      refine ⟨5528821843797008069281403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3685881229198005379520935 5528821843797008069281403)
      ·
        refine ⟨8293232765695512103922105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5528821843797008069281403 8293232765695512103922105)
        ·
          refine ⟨6219924574271634077941579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8293232765695512103922105 6219924574271634077941579)
          ·
            refine ⟨9329886861407451116912369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6219924574271634077941579 9329886861407451116912369)
            ·
              refine ⟨6997415146055588337684277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9329886861407451116912369 6997415146055588337684277)
              ·
                refine ⟨656007669942711406657901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6997415146055588337684277 656007669942711406657901)
                ·
                  refine ⟨246002876228516777496713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 656007669942711406657901 246002876228516777496713)
                  ·
                    rfl

theorem cell21_1077950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_1077950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077950 prefixEnd_1077950 := by exact prefixLift 1077950
  have htrace : WordTrace (prefixWord ++ tailWord_1077950) baseStart_1077950 baseEnd_1077950 := by
    simpa [prefixWord, tailWord_1077950, baseEnd_1077950] using wordTrace_append hprefix tailTrace_1077950
  have hstable : (prefixWord ++ tailWord_1077950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077950).length < 2 ^ (prefixWord ++ tailWord_1077950).sum := by decide
  have hdescent : baseEnd_1077950 < baseStart_1077950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1077964 : List Nat := [2, 2, 1, 5, 1, 1, 1, 4, 4]
def baseStart_1077964 : Nat := 118140960795 + 1077964 * 2 ^ 59
def prefixEnd_1077964 : Nat := 4983230072969 + 3 ^ 40 * 1077964 * 2
def baseEnd_1077964 : Nat := 246006071219255864263351

theorem tailTrace_1077964 : CollatzResearch.WordTrace tailWord_1077964 prefixEnd_1077964 246006071219255864263351 := by
  unfold tailWord_1077964
  simp only [CollatzResearch.WordTrace]
  refine ⟨19658288533364002219616473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26211051377818669626155297 19658288533364002219616473)
  ·
    refine ⟨14743716400023001664712355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19658288533364002219616473 14743716400023001664712355)
    ·
      refine ⟨22115574600034502497068533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14743716400023001664712355 22115574600034502497068533)
      ·
        refine ⟨2073335118753234609100175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22115574600034502497068533 2073335118753234609100175)
        ·
          refine ⟨3110002678129851913650263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2073335118753234609100175 3110002678129851913650263)
          ·
            refine ⟨4665004017194777870475395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3110002678129851913650263 4665004017194777870475395)
            ·
              refine ⟨6997506025792166805713093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4665004017194777870475395 6997506025792166805713093)
              ·
                refine ⟨1312032379836031276071205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6997506025792166805713093 1312032379836031276071205)
                ·
                  refine ⟨246006071219255864263351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1312032379836031276071205 246006071219255864263351)
                  ·
                    rfl

theorem cell21_1077964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_1077964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1077964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1077964 prefixEnd_1077964 := by exact prefixLift 1077964
  have htrace : WordTrace (prefixWord ++ tailWord_1077964) baseStart_1077964 baseEnd_1077964 := by
    simpa [prefixWord, tailWord_1077964, baseEnd_1077964] using wordTrace_append hprefix tailTrace_1077964
  have hstable : (prefixWord ++ tailWord_1077964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1077964).length < 2 ^ (prefixWord ++ tailWord_1077964).sum := by decide
  have hdescent : baseEnd_1077964 < baseStart_1077964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1077964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078037 : List Nat := [1, 3, 2, 1, 2, 2, 2, 8]
def baseStart_1078037 : Nat := 118140960795 + 1078037 * 2 ^ 59
def prefixEnd_1078037 : Nat := 4983230072969 + 3 ^ 40 * 1078037 * 2
def baseEnd_1078037 : Nat := 82007576937941319848845

theorem tailTrace_1078037 : CollatzResearch.WordTrace tailWord_1078037 prefixEnd_1078037 82007576937941319848845 := by
  unfold tailWord_1078037
  simp only [CollatzResearch.WordTrace]
  refine ⟨39319239595463537906640365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26212826396975691937760243 39319239595463537906640365)
  ·
    refine ⟨14744714848298826714990137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39319239595463537906640365 14744714848298826714990137)
    ·
      refine ⟨11058536136224120036242603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14744714848298826714990137 11058536136224120036242603)
      ·
        refine ⟨16587804204336180054363905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11058536136224120036242603 16587804204336180054363905)
        ·
          refine ⟨12440853153252135040772929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16587804204336180054363905 12440853153252135040772929)
          ·
            refine ⟨9330639864939101280579697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12440853153252135040772929 9330639864939101280579697)
            ·
              refine ⟨6997979898704325960434773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9330639864939101280579697 6997979898704325960434773)
              ·
                refine ⟨82007576937941319848845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6997979898704325960434773 82007576937941319848845)
                ·
                  rfl

theorem cell21_1078037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 8].length) (baseStart_1078037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1078037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1078037 prefixEnd_1078037 := by exact prefixLift 1078037
  have htrace : WordTrace (prefixWord ++ tailWord_1078037) baseStart_1078037 baseEnd_1078037 := by
    simpa [prefixWord, tailWord_1078037, baseEnd_1078037] using wordTrace_append hprefix tailTrace_1078037
  have hstable : (prefixWord ++ tailWord_1078037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078037).length < 2 ^ (prefixWord ++ tailWord_1078037).sum := by decide
  have hdescent : baseEnd_1078037 < baseStart_1078037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078178 : List Nat := [3, 3, 1, 2, 2, 1, 1, 5, 3]
def baseStart_1078178 : Nat := 118140960795 + 1078178 * 2 ^ 59
def prefixEnd_1078178 : Nat := 4983230072969 + 3 ^ 40 * 1078178 * 2
def baseEnd_1078178 : Nat := 246054908934839047696247

theorem tailTrace_1078178 : CollatzResearch.WordTrace tailWord_1078178 prefixEnd_1078178 246054908934839047696247 := by
  unfold tailWord_1078178
  simp only [CollatzResearch.WordTrace]
  refine ⟨9831095571988179746880797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26216254858635145991682125 9831095571988179746880797)
  ·
    refine ⟨3686660839495567405080299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9831095571988179746880797 3686660839495567405080299)
    ·
      refine ⟨5529991259243351107620449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3686660839495567405080299 5529991259243351107620449)
      ·
        refine ⟨4147493444432513330715337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5529991259243351107620449 4147493444432513330715337)
        ·
          refine ⟨3110620083324384998036503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4147493444432513330715337 3110620083324384998036503)
          ·
            refine ⟨4665930124986577497054755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3110620083324384998036503 4665930124986577497054755)
            ·
              refine ⟨6998895187479866245582133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4665930124986577497054755 6998895187479866245582133)
              ·
                refine ⟨656146423826237460523325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6998895187479866245582133 656146423826237460523325)
                ·
                  refine ⟨246054908934839047696247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 656146423826237460523325 246054908934839047696247)
                  ·
                    rfl

theorem cell21_1078178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_1078178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1078178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1078178 prefixEnd_1078178 := by exact prefixLift 1078178
  have htrace : WordTrace (prefixWord ++ tailWord_1078178) baseStart_1078178 baseEnd_1078178 := by
    simpa [prefixWord, tailWord_1078178, baseEnd_1078178] using wordTrace_append hprefix tailTrace_1078178
  have hstable : (prefixWord ++ tailWord_1078178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078178).length < 2 ^ (prefixWord ++ tailWord_1078178).sum := by decide
  have hdescent : baseEnd_1078178 < baseStart_1078178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078220 : List Nat := [2, 2, 1, 4, 1, 1, 1, 4, 5]
def baseStart_1078220 : Nat := 118140960795 + 1078220 * 2 ^ 59
def prefixEnd_1078220 : Nat := 4983230072969 + 3 ^ 40 * 1078220 * 2
def baseEnd_1078220 : Nat := 246064493907056307996161

theorem tailTrace_1078220 : CollatzResearch.WordTrace tailWord_1078220 prefixEnd_1078220 246064493907056307996161 := by
  unfold tailWord_1078220
  simp only [CollatzResearch.WordTrace]
  refine ⟨19662957076900280080276057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26217276102533706773701409 19662957076900280080276057)
  ·
    refine ⟨14747217807675210060207043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19662957076900280080276057 14747217807675210060207043)
    ·
      refine ⟨22120826711512815090310565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14747217807675210060207043 22120826711512815090310565)
      ·
        refine ⟨4147655008408652829433231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22120826711512815090310565 4147655008408652829433231)
        ·
          refine ⟨6221482512612979244149847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4147655008408652829433231 6221482512612979244149847)
          ·
            refine ⟨9332223768919468866224771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6221482512612979244149847 9332223768919468866224771)
            ·
              refine ⟨13998335653379203299337157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9332223768919468866224771 13998335653379203299337157)
              ·
                refine ⟨2624687935008600618625717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13998335653379203299337157 2624687935008600618625717)
                ·
                  refine ⟨246064493907056307996161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2624687935008600618625717 246064493907056307996161)
                  ·
                    rfl

theorem cell21_1078220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_1078220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1078220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1078220 prefixEnd_1078220 := by exact prefixLift 1078220
  have htrace : WordTrace (prefixWord ++ tailWord_1078220) baseStart_1078220 baseEnd_1078220 := by
    simpa [prefixWord, tailWord_1078220, baseEnd_1078220] using wordTrace_append hprefix tailTrace_1078220
  have hstable : (prefixWord ++ tailWord_1078220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078220).length < 2 ^ (prefixWord ++ tailWord_1078220).sum := by decide
  have hdescent : baseEnd_1078220 < baseStart_1078220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078254 : List Nat := [4, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_1078254 : Nat := 118140960795 + 1078254 * 2 ^ 59
def prefixEnd_1078254 : Nat := 4983230072969 + 3 ^ 40 * 1078254 * 2
def baseEnd_1078254 : Nat := 246072253170279804429425

theorem tailTrace_1078254 : CollatzResearch.WordTrace tailWord_1078254 prefixEnd_1078254 246072253170279804429425 := by
  unfold tailWord_1078254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4915894279459672995911227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26218102823784922644859877 4915894279459672995911227)
  ·
    refine ⟨7373841419189509493866841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4915894279459672995911227 7373841419189509493866841)
    ·
      refine ⟨5530381064392132120400131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7373841419189509493866841 5530381064392132120400131)
      ·
        refine ⟨8295571596588198180600197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5530381064392132120400131 8295571596588198180600197)
        ·
          refine ⟨1555419674360287158862537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8295571596588198180600197 1555419674360287158862537)
          ·
            refine ⟨1166564755770215369146903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1555419674360287158862537 1166564755770215369146903)
            ·
              refine ⟨1749847133655323053720355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1166564755770215369146903 1749847133655323053720355)
              ·
                refine ⟨2624770700482984580580533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1749847133655323053720355 2624770700482984580580533)
                ·
                  refine ⟨246072253170279804429425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2624770700482984580580533 246072253170279804429425)
                  ·
                    rfl

theorem cell21_1078254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_1078254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1078254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1078254 prefixEnd_1078254 := by exact prefixLift 1078254
  have htrace : WordTrace (prefixWord ++ tailWord_1078254) baseStart_1078254 baseEnd_1078254 := by
    simpa [prefixWord, tailWord_1078254, baseEnd_1078254] using wordTrace_append hprefix tailTrace_1078254
  have hstable : (prefixWord ++ tailWord_1078254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078254).length < 2 ^ (prefixWord ++ tailWord_1078254).sum := by decide
  have hdescent : baseEnd_1078254 < baseStart_1078254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078265 : List Nat := [1, 2, 1, 3, 1, 3, 4, 6]
def baseStart_1078265 : Nat := 118140960795 + 1078265 * 2 ^ 59
def prefixEnd_1078265 : Nat := 4983230072969 + 3 ^ 40 * 1078265 * 2
def baseEnd_1078265 : Nat := 82024921173382076582023

theorem tailTrace_1078265 : CollatzResearch.WordTrace tailWord_1078265 prefixEnd_1078265 82024921173382076582023 := by
  unfold tailWord_1078265
  simp only [CollatzResearch.WordTrace]
  refine ⟨39327555438637532845940249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26218370292425021897293499 39327555438637532845940249)
  ·
    refine ⟨29495666578978149634455187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39327555438637532845940249 29495666578978149634455187)
    ·
      refine ⟨44243499868467224451682781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29495666578978149634455187 44243499868467224451682781)
      ·
        refine ⟨16591312450675209169381043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44243499868467224451682781 16591312450675209169381043)
        ·
          refine ⟨24886968676012813754071565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16591312450675209169381043 24886968676012813754071565)
          ·
            refine ⟨9332613253504805157776837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24886968676012813754071565 9332613253504805157776837)
            ·
              refine ⟨1749864985032150967083157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9332613253504805157776837 1749864985032150967083157)
              ·
                refine ⟨82024921173382076582023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1749864985032150967083157 82024921173382076582023)
                ·
                  rfl

theorem cell21_1078265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 6].length) (baseStart_1078265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1078265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1078265 prefixEnd_1078265 := by exact prefixLift 1078265
  have htrace : WordTrace (prefixWord ++ tailWord_1078265) baseStart_1078265 baseEnd_1078265 := by
    simpa [prefixWord, tailWord_1078265, baseEnd_1078265] using wordTrace_append hprefix tailTrace_1078265
  have hstable : (prefixWord ++ tailWord_1078265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078265).length < 2 ^ (prefixWord ++ tailWord_1078265).sum := by decide
  have hdescent : baseEnd_1078265 < baseStart_1078265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078268 : List Nat := [2, 2, 2, 1, 2, 3, 4, 1, 4]
def baseStart_1078268 : Nat := 118140960795 + 1078268 * 2 ^ 59
def prefixEnd_1078268 : Nat := 4983230072969 + 3 ^ 40 * 1078268 * 2
def baseEnd_1078268 : Nat := 246075448161018891196063

theorem tailTrace_1078268 : CollatzResearch.WordTrace tailWord_1078268 prefixEnd_1078268 246075448161018891196063 := by
  unfold tailWord_1078268
  simp only [CollatzResearch.WordTrace]
  refine ⟨19663832428813332179149729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26218443238417776238866305 19663832428813332179149729)
  ·
    refine ⟨14747874321609999134362297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19663832428813332179149729 14747874321609999134362297)
    ·
      refine ⟨11060905741207499350771723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14747874321609999134362297 11060905741207499350771723)
      ·
        refine ⟨16591358611811249026157585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11060905741207499350771723 16591358611811249026157585)
        ·
          refine ⟨12443518958858436769618189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16591358611811249026157585 12443518958858436769618189)
          ·
            refine ⟨4666319609571913788606821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12443518958858436769618189 4666319609571913788606821)
            ·
              refine ⟨874934926794733835363779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4666319609571913788606821 874934926794733835363779)
              ·
                refine ⟨1312402390192100753045669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 874934926794733835363779 1312402390192100753045669)
                ·
                  refine ⟨246075448161018891196063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1312402390192100753045669 246075448161018891196063)
                  ·
                    rfl

theorem cell21_1078268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_1078268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1078268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1078268 prefixEnd_1078268 := by exact prefixLift 1078268
  have htrace : WordTrace (prefixWord ++ tailWord_1078268) baseStart_1078268 baseEnd_1078268 := by
    simpa [prefixWord, tailWord_1078268, baseEnd_1078268] using wordTrace_append hprefix tailTrace_1078268
  have hstable : (prefixWord ++ tailWord_1078268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078268).length < 2 ^ (prefixWord ++ tailWord_1078268).sum := by decide
  have hdescent : baseEnd_1078268 < baseStart_1078268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078398 : List Nat := [4, 2, 4, 1, 2, 1, 1, 3, 3]
def baseStart_1078398 : Nat := 118140960795 + 1078398 * 2 ^ 59
def prefixEnd_1078398 : Nat := 4983230072969 + 3 ^ 40 * 1078398 * 2
def baseEnd_1078398 : Nat := 246105115932167554029131

theorem tailTrace_1078398 : CollatzResearch.WordTrace tailWord_1078398 prefixEnd_1078398 246105115932167554029131 := by
  unfold tailWord_1078398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4916550793394462070066481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26221604231437131040354565 4916550793394462070066481)
  ·
    refine ⟨3687413095045846552549861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4916550793394462070066481 3687413095045846552549861)
    ·
      refine ⟨691389955321096228603099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3687413095045846552549861 691389955321096228603099)
      ·
        refine ⟨1037084932981644342904649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 691389955321096228603099 1037084932981644342904649)
        ·
          refine ⟨777813699736233257178487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1037084932981644342904649 777813699736233257178487)
          ·
            refine ⟨1166720549604349885767731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777813699736233257178487 1166720549604349885767731)
            ·
              refine ⟨1750080824406524828651597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1166720549604349885767731 1750080824406524828651597)
              ·
                refine ⟨656280309152446810744349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1750080824406524828651597 656280309152446810744349)
                ·
                  refine ⟨246105115932167554029131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 656280309152446810744349 246105115932167554029131)
                  ·
                    rfl

theorem cell21_1078398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_1078398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1078398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1078398 prefixEnd_1078398 := by exact prefixLift 1078398
  have htrace : WordTrace (prefixWord ++ tailWord_1078398) baseStart_1078398 baseEnd_1078398 := by
    simpa [prefixWord, tailWord_1078398, baseEnd_1078398] using wordTrace_append hprefix tailTrace_1078398
  have hstable : (prefixWord ++ tailWord_1078398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078398).length < 2 ^ (prefixWord ++ tailWord_1078398).sum := by decide
  have hdescent : baseEnd_1078398 < baseStart_1078398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078476 : List Nat := [2, 2, 1, 16]
def baseStart_1078476 : Nat := 118140960795 + 1078476 * 2 ^ 59
def prefixEnd_1078476 : Nat := 4983230072969 + 3 ^ 40 * 1078476 * 2
def baseEnd_1078476 : Nat := 1012851508620809677897

theorem tailTrace_1078476 : CollatzResearch.WordTrace tailWord_1078476 prefixEnd_1078476 1012851508620809677897 := by
  unfold tailWord_1078476
  simp only [CollatzResearch.WordTrace]
  refine ⟨19667625620436557940935641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26223500827248743921247521 19667625620436557940935641)
  ·
    refine ⟨14750719215327418455701731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19667625620436557940935641 14750719215327418455701731)
    ·
      refine ⟨22126078822991127683552597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14750719215327418455701731 22126078822991127683552597)
      ·
        refine ⟨1012851508620809677897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 22126078822991127683552597 1012851508620809677897)
        ·
          rfl

theorem cell21_1078476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 16].length) (baseStart_1078476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1078476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1078476 prefixEnd_1078476 := by exact prefixLift 1078476
  have htrace : WordTrace (prefixWord ++ tailWord_1078476) baseStart_1078476 baseEnd_1078476 := by
    simpa [prefixWord, tailWord_1078476, baseEnd_1078476] using wordTrace_append hprefix tailTrace_1078476
  have hstable : (prefixWord ++ tailWord_1078476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078476).length < 2 ^ (prefixWord ++ tailWord_1078476).sum := by decide
  have hdescent : baseEnd_1078476 < baseStart_1078476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078507 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 7]
def baseStart_1078507 : Nat := 118140960795 + 1078507 * 2 ^ 59
def prefixEnd_1078507 : Nat := 4983230072969 + 3 ^ 40 * 1078507 * 2
def baseEnd_1078507 : Nat := 246129991217207586712241

theorem tailTrace_1078507 : CollatzResearch.WordTrace tailWord_1078507 prefixEnd_1078507 246129991217207586712241 := by
  unfold tailWord_1078507
  simp only [CollatzResearch.WordTrace]
  refine ⟨39336381903760808176249775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26224254602507205450833183 39336381903760808176249775)
  ·
    refine ⟨59004572855641212264374663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39336381903760808176249775 59004572855641212264374663)
    ·
      refine ⟨88506859283461818396561995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59004572855641212264374663 88506859283461818396561995)
      ·
        refine ⟨132760288925192727594842993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88506859283461818396561995 132760288925192727594842993)
        ·
          refine ⟨99570216693894545696132245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132760288925192727594842993 99570216693894545696132245)
          ·
            refine ⟨4667353907526306829506199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 99570216693894545696132245 4667353907526306829506199)
            ·
              refine ⟨7001030861289460244259299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4667353907526306829506199 7001030861289460244259299)
              ·
                refine ⟨10501546291934190366388949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7001030861289460244259299 10501546291934190366388949)
                ·
                  refine ⟨246129991217207586712241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10501546291934190366388949 246129991217207586712241)
                  ·
                    rfl

theorem cell21_1078507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 7].length) (baseStart_1078507 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1078507 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1078507 prefixEnd_1078507 := by exact prefixLift 1078507
  have htrace : WordTrace (prefixWord ++ tailWord_1078507) baseStart_1078507 baseEnd_1078507 := by
    simpa [prefixWord, tailWord_1078507, baseEnd_1078507] using wordTrace_append hprefix tailTrace_1078507
  have hstable : (prefixWord ++ tailWord_1078507).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078507).length < 2 ^ (prefixWord ++ tailWord_1078507).sum := by decide
  have hdescent : baseEnd_1078507 < baseStart_1078507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078530 : List Nat := [3, 4, 1, 1, 4, 1, 1, 2, 4]
def baseStart_1078530 : Nat := 118140960795 + 1078530 * 2 ^ 59
def prefixEnd_1078530 : Nat := 4983230072969 + 3 ^ 40 * 1078530 * 2
def baseEnd_1078530 : Nat := 246135240130564657828861

theorem tailTrace_1078530 : CollatzResearch.WordTrace tailWord_1078530 prefixEnd_1078530 246135240130564657828861 := by
  unfold tailWord_1078530
  simp only [CollatzResearch.WordTrace]
  refine ⟨9834305195669370776084261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26224813855118322069558029 9834305195669370776084261)
  ·
    refine ⟨1843932224188007020515799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9834305195669370776084261 1843932224188007020515799)
    ·
      refine ⟨2765898336282010530773699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1843932224188007020515799 2765898336282010530773699)
      ·
        refine ⟨4148847504423015796160549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2765898336282010530773699 4148847504423015796160549)
        ·
          refine ⟨777908907079315461780103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4148847504423015796160549 777908907079315461780103)
          ·
            refine ⟨1166863360618973192670155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777908907079315461780103 1166863360618973192670155)
            ·
              refine ⟨1750295040928459789005233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1166863360618973192670155 1750295040928459789005233)
              ·
                refine ⟨1312721280696344841753925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1750295040928459789005233 1312721280696344841753925)
                ·
                  refine ⟨246135240130564657828861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1312721280696344841753925 246135240130564657828861)
                  ·
                    rfl

theorem cell21_1078530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_1078530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1078530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1078530 prefixEnd_1078530 := by exact prefixLift 1078530
  have htrace : WordTrace (prefixWord ++ tailWord_1078530) baseStart_1078530 baseEnd_1078530 := by
    simpa [prefixWord, tailWord_1078530, baseEnd_1078530] using wordTrace_append hprefix tailTrace_1078530
  have hstable : (prefixWord ++ tailWord_1078530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078530).length < 2 ^ (prefixWord ++ tailWord_1078530).sum := by decide
  have hdescent : baseEnd_1078530 < baseStart_1078530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078645 : List Nat := [1, 3, 4, 1, 3, 9]
def baseStart_1078645 : Nat := 118140960795 + 1078645 * 2 ^ 59
def prefixEnd_1078645 : Nat := 4983230072969 + 3 ^ 40 * 1078645 * 2
def baseEnd_1078645 : Nat := 9117092025827778274517

theorem tailTrace_1078645 : CollatzResearch.WordTrace tailWord_1078645 prefixEnd_1078645 9117092025827778274517 := by
  unfold tailWord_1078645
  simp only [CollatzResearch.WordTrace]
  refine ⟨39341415177260857744773389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26227610118173905163182259 39341415177260857744773389)
  ·
    refine ⟨14753030691472821654290021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39341415177260857744773389 14753030691472821654290021)
    ·
      refine ⟨2766193254651154060179379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14753030691472821654290021 2766193254651154060179379)
      ·
        refine ⟨4149289881976731090269069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2766193254651154060179379 4149289881976731090269069)
        ·
          refine ⟨1555983705741274158850901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4149289881976731090269069 1555983705741274158850901)
          ·
            refine ⟨9117092025827778274517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1555983705741274158850901 9117092025827778274517)
            ·
              rfl

theorem cell21_1078645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 9].length) (baseStart_1078645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1078645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1078645 prefixEnd_1078645 := by exact prefixLift 1078645
  have htrace : WordTrace (prefixWord ++ tailWord_1078645) baseStart_1078645 baseEnd_1078645 := by
    simpa [prefixWord, tailWord_1078645, baseEnd_1078645] using wordTrace_append hprefix tailTrace_1078645
  have hstable : (prefixWord ++ tailWord_1078645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078645).length < 2 ^ (prefixWord ++ tailWord_1078645).sum := by decide
  have hdescent : baseEnd_1078645 < baseStart_1078645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078676 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 7]
def baseStart_1078676 : Nat := 118140960795 + 1078676 * 2 ^ 59
def prefixEnd_1078676 : Nat := 4983230072969 + 3 ^ 40 * 1078676 * 2
def baseEnd_1078676 : Nat := 246168559319700848395229

theorem tailTrace_1078676 : CollatzResearch.WordTrace tailWord_1078676 prefixEnd_1078676 246168559319700848395229 := by
  unfold tailWord_1078676
  simp only [CollatzResearch.WordTrace]
  refine ⟨19671272920074275019575941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26228363893432366692767921 19671272920074275019575941)
  ·
    refine ⟨3688363672513926566170489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19671272920074275019575941 3688363672513926566170489)
    ·
      refine ⟨2766272754385444924627867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3688363672513926566170489 2766272754385444924627867)
      ·
        refine ⟨4149409131578167386941801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2766272754385444924627867 4149409131578167386941801)
        ·
          refine ⟨3112056848683625540206351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4149409131578167386941801 3112056848683625540206351)
          ·
            refine ⟨4668085273025438310309527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3112056848683625540206351 4668085273025438310309527)
            ·
              refine ⟨7002127909538157465464291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4668085273025438310309527 7002127909538157465464291)
              ·
                refine ⟨10503191864307236198196437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7002127909538157465464291 10503191864307236198196437)
                ·
                  refine ⟨246168559319700848395229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10503191864307236198196437 246168559319700848395229)
                  ·
                    rfl

theorem cell21_1078676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_1078676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1078676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1078676 prefixEnd_1078676 := by exact prefixLift 1078676
  have htrace : WordTrace (prefixWord ++ tailWord_1078676) baseStart_1078676 baseEnd_1078676 := by
    simpa [prefixWord, tailWord_1078676, baseEnd_1078676] using wordTrace_append hprefix tailTrace_1078676
  have hstable : (prefixWord ++ tailWord_1078676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078676).length < 2 ^ (prefixWord ++ tailWord_1078676).sum := by decide
  have hdescent : baseEnd_1078676 < baseStart_1078676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078735 : List Nat := [1, 1, 2, 1, 1, 4, 4, 2, 5]
def baseStart_1078735 : Nat := 118140960795 + 1078735 * 2 ^ 59
def prefixEnd_1078735 : Nat := 4983230072969 + 3 ^ 40 * 1078735 * 2
def baseEnd_1078735 : Nat := 246182023923529856911775

theorem tailTrace_1078735 : CollatzResearch.WordTrace tailWord_1078735 prefixEnd_1078735 246182023923529856911775 := by
  unfold tailWord_1078735
  simp only [CollatzResearch.WordTrace]
  refine ⟨39344697746934803115549659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26229798497956535410366439 39344697746934803115549659)
  ·
    refine ⟨59017046620402204673324489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39344697746934803115549659 59017046620402204673324489)
    ·
      refine ⟨44262784965301653504993367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59017046620402204673324489 44262784965301653504993367)
      ·
        refine ⟨66394177447952480257490051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44262784965301653504993367 66394177447952480257490051)
        ·
          refine ⟨99591266171928720386235077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66394177447952480257490051 99591266171928720386235077)
          ·
            refine ⟨18673362407236635072419077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99591266171928720386235077 18673362407236635072419077)
            ·
              refine ⟨3501255451356869076078577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18673362407236635072419077 3501255451356869076078577)
              ·
                refine ⟨2625941588517651807058933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3501255451356869076078577 2625941588517651807058933)
                ·
                  refine ⟨246182023923529856911775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2625941588517651807058933 246182023923529856911775)
                  ·
                    rfl

theorem cell21_1078735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 5].length) (baseStart_1078735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1078735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1078735 prefixEnd_1078735 := by exact prefixLift 1078735
  have htrace : WordTrace (prefixWord ++ tailWord_1078735) baseStart_1078735 baseEnd_1078735 := by
    simpa [prefixWord, tailWord_1078735, baseEnd_1078735] using wordTrace_append hprefix tailTrace_1078735
  have hstable : (prefixWord ++ tailWord_1078735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078735).length < 2 ^ (prefixWord ++ tailWord_1078735).sum := by decide
  have hdescent : baseEnd_1078735 < baseStart_1078735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078752 : List Nat := [2, 1, 1, 3, 1, 1, 2, 7, 3]
def baseStart_1078752 : Nat := 118140960795 + 1078752 * 2 ^ 59
def prefixEnd_1078752 : Nat := 4983230072969 + 3 ^ 40 * 1078752 * 2
def baseEnd_1078752 : Nat := 246185903555141605128407

theorem tailTrace_1078752 : CollatzResearch.WordTrace tailWord_1078752 prefixEnd_1078752 246185903555141605128407 := by
  unfold tailWord_1078752
  simp only [CollatzResearch.WordTrace]
  refine ⟨19672658893936607509459255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26230211858582143345945673 19672658893936607509459255)
  ·
    refine ⟨29508988340904911264188883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19672658893936607509459255 29508988340904911264188883)
    ·
      refine ⟨44263482511357366896283325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29508988340904911264188883 44263482511357366896283325)
      ·
        refine ⟨16598805941759012586106247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44263482511357366896283325 16598805941759012586106247)
        ·
          refine ⟨24898208912638518879159371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16598805941759012586106247 24898208912638518879159371)
          ·
            refine ⟨37347313368957778318739057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24898208912638518879159371 37347313368957778318739057)
            ·
              refine ⟨28010485026718333739054293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37347313368957778318739057 28010485026718333739054293)
              ·
                refine ⟨656495742813710947009085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28010485026718333739054293 656495742813710947009085)
                ·
                  refine ⟨246185903555141605128407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 656495742813710947009085 246185903555141605128407)
                  ·
                    rfl

theorem cell21_1078752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 3].length) (baseStart_1078752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1078752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1078752 prefixEnd_1078752 := by exact prefixLift 1078752
  have htrace : WordTrace (prefixWord ++ tailWord_1078752) baseStart_1078752 baseEnd_1078752 := by
    simpa [prefixWord, tailWord_1078752, baseEnd_1078752] using wordTrace_append hprefix tailTrace_1078752
  have hstable : (prefixWord ++ tailWord_1078752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078752).length < 2 ^ (prefixWord ++ tailWord_1078752).sum := by decide
  have hdescent : baseEnd_1078752 < baseStart_1078752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078766 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_1078766 : Nat := 118140960795 + 1078766 * 2 ^ 59
def prefixEnd_1078766 : Nat := 4983230072969 + 3 ^ 40 * 1078766 * 2
def baseEnd_1078766 : Nat := 246189098545880691895045

theorem tailTrace_1078766 : CollatzResearch.WordTrace tailWord_1078766 prefixEnd_1078766 246189098545880691895045 := by
  unfold tailWord_1078766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4918228551227811926241019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26230552273214996939952101 4918228551227811926241019)
  ·
    refine ⟨7377342826841717889361529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4918228551227811926241019 7377342826841717889361529)
    ·
      refine ⟨5533007120131288417021147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7377342826841717889361529 5533007120131288417021147)
      ·
        refine ⟨8299510680196932625531721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5533007120131288417021147 8299510680196932625531721)
        ·
          refine ⟨6224633010147699469148791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8299510680196932625531721 6224633010147699469148791)
          ·
            refine ⟨9336949515221549203723187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6224633010147699469148791 9336949515221549203723187)
            ·
              refine ⟨14005424272832323805584781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9336949515221549203723187 14005424272832323805584781)
              ·
                refine ⟨5252034102312121427094293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14005424272832323805584781 5252034102312121427094293)
                ·
                  refine ⟨246189098545880691895045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5252034102312121427094293 246189098545880691895045)
                  ·
                    rfl

theorem cell21_1078766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_1078766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1078766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1078766 prefixEnd_1078766 := by exact prefixLift 1078766
  have htrace : WordTrace (prefixWord ++ tailWord_1078766) baseStart_1078766 baseEnd_1078766 := by
    simpa [prefixWord, tailWord_1078766, baseEnd_1078766] using wordTrace_append hprefix tailTrace_1078766
  have hstable : (prefixWord ++ tailWord_1078766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078766).length < 2 ^ (prefixWord ++ tailWord_1078766).sum := by decide
  have hdescent : baseEnd_1078766 < baseStart_1078766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078780 : List Nat := [2, 2, 2, 1, 2, 1, 3, 8]
def baseStart_1078780 : Nat := 118140960795 + 1078780 * 2 ^ 59
def prefixEnd_1078780 : Nat := 4983230072969 + 3 ^ 40 * 1078780 * 2
def baseEnd_1078780 : Nat := 82064097845539926220561

theorem tailTrace_1078780 : CollatzResearch.WordTrace tailWord_1078780 prefixEnd_1078780 82064097845539926220561 := by
  unfold tailWord_1078780
  simp only [CollatzResearch.WordTrace]
  refine ⟨19673169515885887900468897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26230892687847850533958529 19673169515885887900468897)
  ·
    refine ⟨14754877136914415925351673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19673169515885887900468897 14754877136914415925351673)
    ·
      refine ⟨11066157852685811944013755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14754877136914415925351673 11066157852685811944013755)
      ·
        refine ⟨16599236779028717916020633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11066157852685811944013755 16599236779028717916020633)
        ·
          refine ⟨12449427584271538437015475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16599236779028717916020633 12449427584271538437015475)
          ·
            refine ⟨18674141376407307655523213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12449427584271538437015475 18674141376407307655523213)
            ·
              refine ⟨7002803016152740370821205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18674141376407307655523213 7002803016152740370821205)
              ·
                refine ⟨82064097845539926220561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7002803016152740370821205 82064097845539926220561)
                ·
                  rfl

theorem cell21_1078780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 8].length) (baseStart_1078780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1078780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1078780 prefixEnd_1078780 := by exact prefixLift 1078780
  have htrace : WordTrace (prefixWord ++ tailWord_1078780) baseStart_1078780 baseEnd_1078780 := by
    simpa [prefixWord, tailWord_1078780, baseEnd_1078780] using wordTrace_append hprefix tailTrace_1078780
  have hstable : (prefixWord ++ tailWord_1078780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078780).length < 2 ^ (prefixWord ++ tailWord_1078780).sum := by decide
  have hdescent : baseEnd_1078780 < baseStart_1078780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078842 : List Nat := [3, 1, 1, 1, 3, 2, 1, 5, 4]
def baseStart_1078842 : Nat := 118140960795 + 1078842 * 2 ^ 59
def prefixEnd_1078842 : Nat := 4983230072969 + 3 ^ 40 * 1078842 * 2
def baseEnd_1078842 : Nat := 246206442781321448628223

theorem tailTrace_1078842 : CollatzResearch.WordTrace tailWord_1078842 prefixEnd_1078842 246206442781321448628223 := by
  unfold tailWord_1078842
  simp only [CollatzResearch.WordTrace]
  refine ⟨9837150089386790097423695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26232400238364773593129853 9837150089386790097423695)
  ·
    refine ⟨14755725134080185146135543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9837150089386790097423695 14755725134080185146135543)
    ·
      refine ⟨22133587701120277719203315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14755725134080185146135543 22133587701120277719203315)
      ·
        refine ⟨33200381551680416578804973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22133587701120277719203315 33200381551680416578804973)
        ·
          refine ⟨12450143081880156217051865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33200381551680416578804973 12450143081880156217051865)
          ·
            refine ⟨9337607311410117162788899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12450143081880156217051865 9337607311410117162788899)
            ·
              refine ⟨14006410967115175744183349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9337607311410117162788899 14006410967115175744183349)
              ·
                refine ⟨1313101028167047726017189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14006410967115175744183349 1313101028167047726017189)
                ·
                  refine ⟨246206442781321448628223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1313101028167047726017189 246206442781321448628223)
                  ·
                    rfl

theorem cell21_1078842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_1078842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1078842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1078842 prefixEnd_1078842 := by exact prefixLift 1078842
  have htrace : WordTrace (prefixWord ++ tailWord_1078842) baseStart_1078842 baseEnd_1078842 := by
    simpa [prefixWord, tailWord_1078842, baseEnd_1078842] using wordTrace_append hprefix tailTrace_1078842
  have hstable : (prefixWord ++ tailWord_1078842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078842).length < 2 ^ (prefixWord ++ tailWord_1078842).sum := by decide
  have hdescent : baseEnd_1078842 < baseStart_1078842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078876 : List Nat := [2, 2, 4, 1, 2, 3, 1, 2, 4]
def baseStart_1078876 : Nat := 118140960795 + 1078876 * 2 ^ 59
def prefixEnd_1078876 : Nat := 4983230072969 + 3 ^ 40 * 1078876 * 2
def baseEnd_1078876 : Nat := 246214202044544945061487

theorem tailTrace_1078876 : CollatzResearch.WordTrace tailWord_1078876 prefixEnd_1078876 246214202044544945061487 := by
  unfold tailWord_1078876
  simp only [CollatzResearch.WordTrace]
  refine ⟨19674920219711992098216241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26233226959615989464288321 19674920219711992098216241)
  ·
    refine ⟨14756190164783994073662181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19674920219711992098216241 14756190164783994073662181)
    ·
      refine ⟨2766785655896998888811659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14756190164783994073662181 2766785655896998888811659)
      ·
        refine ⟨4150178483845498333217489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2766785655896998888811659 4150178483845498333217489)
        ·
          refine ⟨3112633862884123749913117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4150178483845498333217489 3112633862884123749913117)
          ·
            refine ⟨1167237698581546406217419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3112633862884123749913117 1167237698581546406217419)
            ·
              refine ⟨1750856547872319609326129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1167237698581546406217419 1750856547872319609326129)
              ·
                refine ⟨1313142410904239706994597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1750856547872319609326129 1313142410904239706994597)
                ·
                  refine ⟨246214202044544945061487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1313142410904239706994597 246214202044544945061487)
                  ·
                    rfl

theorem cell21_1078876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_1078876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1078876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1078876 prefixEnd_1078876 := by exact prefixLift 1078876
  have htrace : WordTrace (prefixWord ++ tailWord_1078876) baseStart_1078876 baseEnd_1078876 := by
    simpa [prefixWord, tailWord_1078876, baseEnd_1078876] using wordTrace_append hprefix tailTrace_1078876
  have hstable : (prefixWord ++ tailWord_1078876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078876).length < 2 ^ (prefixWord ++ tailWord_1078876).sum := by decide
  have hdescent : baseEnd_1078876 < baseStart_1078876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078887 : List Nat := [1, 1, 5, 1, 1, 1, 3, 3, 5]
def baseStart_1078887 : Nat := 118140960795 + 1078887 * 2 ^ 59
def prefixEnd_1078887 : Nat := 4983230072969 + 3 ^ 40 * 1078887 * 2
def baseEnd_1078887 : Nat := 246216712394411370378131

theorem tailTrace_1078887 : CollatzResearch.WordTrace tailWord_1078887 prefixEnd_1078887 246216712394411370378131 := by
  unfold tailWord_1078887
  simp only [CollatzResearch.WordTrace]
  refine ⟨39350241642384133075082915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26233494428256088716721943 39350241642384133075082915)
  ·
    refine ⟨59025362463576199612624373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39350241642384133075082915 59025362463576199612624373)
    ·
      refine ⟨5533627730960268713683535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59025362463576199612624373 5533627730960268713683535)
      ·
        refine ⟨8300441596440403070525303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5533627730960268713683535 8300441596440403070525303)
        ·
          refine ⟨12450662394660604605787955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8300441596440403070525303 12450662394660604605787955)
          ·
            refine ⟨18675993591990906908681933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12450662394660604605787955 18675993591990906908681933)
            ·
              refine ⟨7003497596996590090755725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18675993591990906908681933 7003497596996590090755725)
              ·
                refine ⟨2626311598873721284033397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7003497596996590090755725 2626311598873721284033397)
                ·
                  refine ⟨246216712394411370378131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2626311598873721284033397 246216712394411370378131)
                  ·
                    rfl

theorem cell21_1078887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 5].length) (baseStart_1078887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1078887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1078887 prefixEnd_1078887 := by exact prefixLift 1078887
  have htrace : WordTrace (prefixWord ++ tailWord_1078887) baseStart_1078887 baseEnd_1078887 := by
    simpa [prefixWord, tailWord_1078887, baseEnd_1078887] using wordTrace_append hprefix tailTrace_1078887
  have hstable : (prefixWord ++ tailWord_1078887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078887).length < 2 ^ (prefixWord ++ tailWord_1078887).sum := by decide
  have hdescent : baseEnd_1078887 < baseStart_1078887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1078966 : List Nat := [5, 1, 3, 1, 1, 1, 2, 7]
def baseStart_1078966 : Nat := 118140960795 + 1078966 * 2 ^ 59
def prefixEnd_1078966 : Nat := 4983230072969 + 3 ^ 40 * 1078966 * 2
def baseEnd_1078966 : Nat := 82078247090241596187101

theorem tailTrace_1078966 : CollatzResearch.WordTrace tailWord_1078966 prefixEnd_1078966 82078247090241596187101 := by
  unfold tailWord_1078966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2459570188068620597950547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26235415339398619711472501 2459570188068620597950547)
  ·
    refine ⟨3689355282102930896925821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2459570188068620597950547 3689355282102930896925821)
    ·
      refine ⟨1383508230788599086347183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3689355282102930896925821 1383508230788599086347183)
      ·
        refine ⟨2075262346182898629520775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1383508230788599086347183 2075262346182898629520775)
        ·
          refine ⟨3112893519274347944281163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2075262346182898629520775 3112893519274347944281163)
          ·
            refine ⟨4669340278911521916421745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3112893519274347944281163 4669340278911521916421745)
            ·
              refine ⟨3502005209183641437316309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4669340278911521916421745 3502005209183641437316309)
              ·
                refine ⟨82078247090241596187101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3502005209183641437316309 82078247090241596187101)
                ·
                  rfl

theorem cell21_1078966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_1078966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1078966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1078966 prefixEnd_1078966 := by exact prefixLift 1078966
  have htrace : WordTrace (prefixWord ++ tailWord_1078966) baseStart_1078966 baseEnd_1078966 := by
    simpa [prefixWord, tailWord_1078966, baseEnd_1078966] using wordTrace_append hprefix tailTrace_1078966
  have hstable : (prefixWord ++ tailWord_1078966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1078966).length < 2 ^ (prefixWord ++ tailWord_1078966).sum := by decide
  have hdescent : baseEnd_1078966 < baseStart_1078966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1078966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079008 : List Nat := [2, 1, 1, 3, 1, 2, 5, 6]
def baseStart_1079008 : Nat := 118140960795 + 1079008 * 2 ^ 59
def prefixEnd_1079008 : Nat := 4983230072969 + 3 ^ 40 * 1079008 * 2
def baseEnd_1079008 : Nat := 82081442080980682953739

theorem tailTrace_1079008 : CollatzResearch.WordTrace tailWord_1079008 prefixEnd_1079008 82081442080980682953739 := by
  unfold tailWord_1079008
  simp only [CollatzResearch.WordTrace]
  refine ⟨19677327437472885370118839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26236436583297180493491785 19677327437472885370118839)
  ·
    refine ⟨29515991156209328055178259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19677327437472885370118839 29515991156209328055178259)
    ·
      refine ⟨44273986734313992082767389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29515991156209328055178259 44273986734313992082767389)
      ·
        refine ⟨16602745025367747031037771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44273986734313992082767389 16602745025367747031037771)
        ·
          refine ⟨24904117538051620546556657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16602745025367747031037771 24904117538051620546556657)
          ·
            refine ⟨18678088153538715409917493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24904117538051620546556657 18678088153538715409917493)
            ·
              refine ⟨1751070764394254569679765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18678088153538715409917493 1751070764394254569679765)
              ·
                refine ⟨82081442080980682953739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1751070764394254569679765 82081442080980682953739)
                ·
                  rfl

theorem cell21_1079008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 6].length) (baseStart_1079008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079008 prefixEnd_1079008 := by exact prefixLift 1079008
  have htrace : WordTrace (prefixWord ++ tailWord_1079008) baseStart_1079008 baseEnd_1079008 := by
    simpa [prefixWord, tailWord_1079008, baseEnd_1079008] using wordTrace_append hprefix tailTrace_1079008
  have hstable : (prefixWord ++ tailWord_1079008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079008).length < 2 ^ (prefixWord ++ tailWord_1079008).sum := by decide
  have hdescent : baseEnd_1079008 < baseStart_1079008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079025 : List Nat := [1, 2, 2, 2, 2, 4, 3, 5]
def baseStart_1079025 : Nat := 118140960795 + 1079025 * 2 ^ 59
def prefixEnd_1079025 : Nat := 4983230072969 + 3 ^ 40 * 1079025 * 2
def baseEnd_1079025 : Nat := 82082735291517932359283

theorem tailTrace_1079025 : CollatzResearch.WordTrace tailWord_1079025 prefixEnd_1079025 82082735291517932359283 := by
  unfold tailWord_1079025
  simp only [CollatzResearch.WordTrace]
  refine ⟨39355274915884182643606529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26236849943922788429071019 39355274915884182643606529)
  ·
    refine ⟨29516456186913136982704897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39355274915884182643606529 29516456186913136982704897)
    ·
      refine ⟨22137342140184852737028673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29516456186913136982704897 22137342140184852737028673)
      ·
        refine ⟨16603006605138639552771505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22137342140184852737028673 16603006605138639552771505)
        ·
          refine ⟨12452254953853979664578629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16603006605138639552771505 12452254953853979664578629)
          ·
            refine ⟨2334797803847621187108493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12452254953853979664578629 2334797803847621187108493)
            ·
              refine ⟨875549176442857945165685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2334797803847621187108493 875549176442857945165685)
              ·
                refine ⟨82082735291517932359283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 875549176442857945165685 82082735291517932359283)
                ·
                  rfl

theorem cell21_1079025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 5].length) (baseStart_1079025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079025 prefixEnd_1079025 := by exact prefixLift 1079025
  have htrace : WordTrace (prefixWord ++ tailWord_1079025) baseStart_1079025 baseEnd_1079025 := by
    simpa [prefixWord, tailWord_1079025, baseEnd_1079025] using wordTrace_append hprefix tailTrace_1079025
  have hstable : (prefixWord ++ tailWord_1079025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079025).length < 2 ^ (prefixWord ++ tailWord_1079025).sum := by decide
  have hdescent : baseEnd_1079025 < baseStart_1079025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079084 : List Nat := [2, 2, 1, 1, 1, 6, 1, 7]
def baseStart_1079084 : Nat := 118140960795 + 1079084 * 2 ^ 59
def prefixEnd_1079084 : Nat := 4983230072969 + 3 ^ 40 * 1079084 * 2
def baseEnd_1079084 : Nat := 82087223492794268531465

theorem tailTrace_1079084 : CollatzResearch.WordTrace tailWord_1079084 prefixEnd_1079084 82087223492794268531465 := by
  unfold tailWord_1079084
  simp only [CollatzResearch.WordTrace]
  refine ⟨19678713411335217860002153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26238284548446957146669537 19678713411335217860002153)
  ·
    refine ⟨14759035058501413395001615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19678713411335217860002153 14759035058501413395001615)
    ·
      refine ⟨22138552587752120092502423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14759035058501413395001615 22138552587752120092502423)
      ·
        refine ⟨33207828881628180138753635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22138552587752120092502423 33207828881628180138753635)
        ·
          refine ⟨49811743322442270208130453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33207828881628180138753635 49811743322442270208130453)
          ·
            refine ⟨2334925468239481416006115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49811743322442270208130453 2334925468239481416006115)
            ·
              refine ⟨3502388202359222124009173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2334925468239481416006115 3502388202359222124009173)
              ·
                refine ⟨82087223492794268531465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3502388202359222124009173 82087223492794268531465)
                ·
                  rfl

theorem cell21_1079084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 7].length) (baseStart_1079084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079084 prefixEnd_1079084 := by exact prefixLift 1079084
  have htrace : WordTrace (prefixWord ++ tailWord_1079084) baseStart_1079084 baseEnd_1079084 := by
    simpa [prefixWord, tailWord_1079084, baseEnd_1079084] using wordTrace_append hprefix tailTrace_1079084
  have hstable : (prefixWord ++ tailWord_1079084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079084).length < 2 ^ (prefixWord ++ tailWord_1079084).sum := by decide
  have hdescent : baseEnd_1079084 < baseStart_1079084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079101 : List Nat := [1, 4, 1, 4, 1, 3, 7]
def baseStart_1079101 : Nat := 118140960795 + 1079101 * 2 ^ 59
def prefixEnd_1079101 : Nat := 4983230072969 + 3 ^ 40 * 1079101 * 2
def baseEnd_1079101 : Nat := 27362838901110505979003

theorem tailTrace_1079101 : CollatzResearch.WordTrace tailWord_1079101 prefixEnd_1079101 27362838901110505979003 := by
  unfold tailWord_1079101
  simp only [CollatzResearch.WordTrace]
  refine ⟨39358046863608847623373157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26238697909072565082248771 39358046863608847623373157)
  ·
    refine ⟨7379633786926658929382467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39358046863608847623373157 7379633786926658929382467)
    ·
      refine ⟨11069450680389988394073701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7379633786926658929382467 11069450680389988394073701)
      ·
        refine ⟨2075522002573122823888819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11069450680389988394073701 2075522002573122823888819)
        ·
          refine ⟨3113283003859684235833229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2075522002573122823888819 3113283003859684235833229)
          ·
            refine ⟨1167481126447381588437461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3113283003859684235833229 1167481126447381588437461)
            ·
              refine ⟨27362838901110505979003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1167481126447381588437461 27362838901110505979003)
              ·
                rfl

theorem cell21_1079101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 7].length) (baseStart_1079101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079101 prefixEnd_1079101 := by exact prefixLift 1079101
  have htrace : WordTrace (prefixWord ++ tailWord_1079101) baseStart_1079101 baseEnd_1079101 := by
    simpa [prefixWord, tailWord_1079101, baseEnd_1079101] using wordTrace_append hprefix tailTrace_1079101
  have hstable : (prefixWord ++ tailWord_1079101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079101).length < 2 ^ (prefixWord ++ tailWord_1079101).sum := by decide
  have hdescent : baseEnd_1079101 < baseStart_1079101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079166 : List Nat := [4, 2, 3, 1, 1, 2, 1, 4, 3]
def baseStart_1079166 : Nat := 118140960795 + 1079166 * 2 ^ 59
def prefixEnd_1079166 : Nat := 4983230072969 + 3 ^ 40 * 1079166 * 2
def baseEnd_1079166 : Nat := 246280383995568885227561

theorem tailTrace_1079166 : CollatzResearch.WordTrace tailWord_1079166 prefixEnd_1079166 246280383995568885227561 := by
  unfold tailWord_1079166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4920052201046670465561169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26240278405582242482992901 4920052201046670465561169)
  ·
    refine ⟨3690039150785002849170877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4920052201046670465561169 3690039150785002849170877)
    ·
      refine ⟨1383764681544376068439079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3690039150785002849170877 1383764681544376068439079)
      ·
        refine ⟨2075647022316564102658619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1383764681544376068439079 2075647022316564102658619)
        ·
          refine ⟨3113470533474846153987929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2075647022316564102658619 3113470533474846153987929)
          ·
            refine ⟨2335102900106134615490947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3113470533474846153987929 2335102900106134615490947)
            ·
              refine ⟨3502654350159201923236421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2335102900106134615490947 3502654350159201923236421)
              ·
                refine ⟨656747690654850360606829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3502654350159201923236421 656747690654850360606829)
                ·
                  refine ⟨246280383995568885227561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 656747690654850360606829 246280383995568885227561)
                  ·
                    rfl

theorem cell21_1079166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_1079166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079166 prefixEnd_1079166 := by exact prefixLift 1079166
  have htrace : WordTrace (prefixWord ++ tailWord_1079166) baseStart_1079166 baseEnd_1079166 := by
    simpa [prefixWord, tailWord_1079166, baseEnd_1079166] using wordTrace_append hprefix tailTrace_1079166
  have hstable : (prefixWord ++ tailWord_1079166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079166).length < 2 ^ (prefixWord ++ tailWord_1079166).sum := by decide
  have hdescent : baseEnd_1079166 < baseStart_1079166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079191 : List Nat := [1, 1, 3, 3, 1, 4, 1, 2, 5]
def baseStart_1079191 : Nat := 118140960795 + 1079191 * 2 ^ 59
def prefixEnd_1079191 : Nat := 4983230072969 + 3 ^ 40 * 1079191 * 2
def baseEnd_1079191 : Nat := 246286089336174397310843

theorem tailTrace_1079191 : CollatzResearch.WordTrace tailWord_1079191 prefixEnd_1079191 246286089336174397310843 := by
  unfold tailWord_1079191
  simp only [CollatzResearch.WordTrace]
  refine ⟨39361329433282792994149427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26240886288855195329432951 39361329433282792994149427)
  ·
    refine ⟨59041994149924189491224141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39361329433282792994149427 59041994149924189491224141)
    ·
      refine ⟨22140747806221571059209053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59041994149924189491224141 22140747806221571059209053)
      ·
        refine ⟨8302780427333089147203395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22140747806221571059209053 8302780427333089147203395)
        ·
          refine ⟨12454170640999633720805093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8302780427333089147203395 12454170640999633720805093)
          ·
            refine ⟨2335156995187431322650955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12454170640999633720805093 2335156995187431322650955)
            ·
              refine ⟨3502735492781146983976433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2335156995187431322650955 3502735492781146983976433)
              ·
                refine ⟨2627051619585860237982325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3502735492781146983976433 2627051619585860237982325)
                ·
                  refine ⟨246286089336174397310843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2627051619585860237982325 246286089336174397310843)
                  ·
                    rfl

theorem cell21_1079191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 5].length) (baseStart_1079191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079191 prefixEnd_1079191 := by exact prefixLift 1079191
  have htrace : WordTrace (prefixWord ++ tailWord_1079191) baseStart_1079191 baseEnd_1079191 := by
    simpa [prefixWord, tailWord_1079191, baseEnd_1079191] using wordTrace_append hprefix tailTrace_1079191
  have hstable : (prefixWord ++ tailWord_1079191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079191).length < 2 ^ (prefixWord ++ tailWord_1079191).sum := by decide
  have hdescent : baseEnd_1079191 < baseStart_1079191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079214 : List Nat := [4, 1, 5, 1, 1, 2, 1, 2, 4]
def baseStart_1079214 : Nat := 118140960795 + 1079214 * 2 ^ 59
def prefixEnd_1079214 : Nat := 4983230072969 + 3 ^ 40 * 1079214 * 2
def baseEnd_1079214 : Nat := 246291338249531468427463

theorem tailTrace_1079214 : CollatzResearch.WordTrace tailWord_1079214 prefixEnd_1079214 246291338249531468427463 := by
  unfold tailWord_1079214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4920271039024933490279587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26241445541466311948157797 4920271039024933490279587)
  ·
    refine ⟨7380406558537400235419381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4920271039024933490279587 7380406558537400235419381)
    ·
      refine ⟨691913114862881272070567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7380406558537400235419381 691913114862881272070567)
      ·
        refine ⟨1037869672294321908105851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 691913114862881272070567 1037869672294321908105851)
        ·
          refine ⟨1556804508441482862158777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1037869672294321908105851 1556804508441482862158777)
          ·
            refine ⟨1167603381331112146619083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1556804508441482862158777 1167603381331112146619083)
            ·
              refine ⟨1751405071996668219928625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1167603381331112146619083 1751405071996668219928625)
              ·
                refine ⟨1313553803997501164946469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1751405071996668219928625 1313553803997501164946469)
                ·
                  refine ⟨246291338249531468427463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1313553803997501164946469 246291338249531468427463)
                  ·
                    rfl

theorem cell21_1079214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_1079214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079214 prefixEnd_1079214 := by exact prefixLift 1079214
  have htrace : WordTrace (prefixWord ++ tailWord_1079214) baseStart_1079214 baseEnd_1079214 := by
    simpa [prefixWord, tailWord_1079214, baseEnd_1079214] using wordTrace_append hprefix tailTrace_1079214
  have hstable : (prefixWord ++ tailWord_1079214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079214).length < 2 ^ (prefixWord ++ tailWord_1079214).sum := by decide
  have hdescent : baseEnd_1079214 < baseStart_1079214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079219 : List Nat := [1, 1, 1, 2, 3, 1, 12]
def baseStart_1079219 : Nat := 118140960795 + 1079219 * 2 ^ 59
def prefixEnd_1079219 : Nat := 4983230072969 + 3 ^ 40 * 1079219 * 2
def baseEnd_1079219 : Nat := 27365831035294730093791

theorem tailTrace_1079219 : CollatzResearch.WordTrace tailWord_1079219 prefixEnd_1079219 27365831035294730093791 := by
  unfold tailWord_1079219
  simp only [CollatzResearch.WordTrace]
  refine ⟨39362350677181353776168711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26241567118120902517445807 39362350677181353776168711)
  ·
    refine ⟨59043526015772030664253067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39362350677181353776168711 59043526015772030664253067)
    ·
      refine ⟨88565289023658045996379601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59043526015772030664253067 88565289023658045996379601)
      ·
        refine ⟨66423966767743534497284701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88565289023658045996379601 66423966767743534497284701)
        ·
          refine ⟨24908987537903825436481763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66423966767743534497284701 24908987537903825436481763)
          ·
            refine ⟨37363481306855738154722645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24908987537903825436481763 37363481306855738154722645)
            ·
              refine ⟨27365831035294730093791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 37363481306855738154722645 27365831035294730093791)
              ·
                rfl

theorem cell21_1079219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 12].length) (baseStart_1079219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079219 prefixEnd_1079219 := by exact prefixLift 1079219
  have htrace : WordTrace (prefixWord ++ tailWord_1079219) baseStart_1079219 baseEnd_1079219 := by
    simpa [prefixWord, tailWord_1079219, baseEnd_1079219] using wordTrace_append hprefix tailTrace_1079219
  have hstable : (prefixWord ++ tailWord_1079219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079219).length < 2 ^ (prefixWord ++ tailWord_1079219).sum := by decide
  have hdescent : baseEnd_1079219 < baseStart_1079219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079253 : List Nat := [1, 3, 2, 3, 2, 1, 4, 5]
def baseStart_1079253 : Nat := 118140960795 + 1079253 * 2 ^ 59
def prefixEnd_1079253 : Nat := 4983230072969 + 3 ^ 40 * 1079253 * 2
def baseEnd_1079253 : Nat := 82100079526958689092461

theorem tailTrace_1079253 : CollatzResearch.WordTrace tailWord_1079253 prefixEnd_1079253 82100079526958689092461 := by
  unfold tailWord_1079253
  simp only [CollatzResearch.WordTrace]
  refine ⟨39363590759058177582906413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26242393839372118388604275 39363590759058177582906413)
  ·
    refine ⟨14761346534646816593589905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39363590759058177582906413 14761346534646816593589905)
    ·
      refine ⟨11071009900985112445192429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14761346534646816593589905 11071009900985112445192429)
      ·
        refine ⟨4151628712869417166947161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11071009900985112445192429 4151628712869417166947161)
        ·
          refine ⟨3113721534652062875210371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4151628712869417166947161 3113721534652062875210371)
          ·
            refine ⟨4670582301978094312815557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3113721534652062875210371 4670582301978094312815557)
            ·
              refine ⟨875734181620892683652917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4670582301978094312815557 875734181620892683652917)
              ·
                refine ⟨82100079526958689092461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 875734181620892683652917 82100079526958689092461)
                ·
                  rfl

theorem cell21_1079253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 5].length) (baseStart_1079253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079253 prefixEnd_1079253 := by exact prefixLift 1079253
  have htrace : WordTrace (prefixWord ++ tailWord_1079253) baseStart_1079253 baseEnd_1079253 := by
    simpa [prefixWord, tailWord_1079253, baseEnd_1079253] using wordTrace_append hprefix tailTrace_1079253
  have hstable : (prefixWord ++ tailWord_1079253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079253).length < 2 ^ (prefixWord ++ tailWord_1079253).sum := by decide
  have hdescent : baseEnd_1079253 < baseStart_1079253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079335 : List Nat := [1, 1, 7, 1, 2, 2, 2, 2, 3]
def baseStart_1079335 : Nat := 118140960795 + 1079335 * 2 ^ 59
def prefixEnd_1079335 : Nat := 4983230072969 + 3 ^ 40 * 1079335 * 2
def baseEnd_1079335 : Nat := 246318952098062146910549

theorem tailTrace_1079335 : CollatzResearch.WordTrace tailWord_1079335 prefixEnd_1079335 246318952098062146910549 := by
  unfold tailWord_1079335
  simp only [CollatzResearch.WordTrace]
  refine ⟨39366581544761105587391459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26244387696507403724927639 39366581544761105587391459)
  ·
    refine ⟨59049872317141658381087189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39366581544761105587391459 59049872317141658381087189)
    ·
      refine ⟨1383981382433007618306731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 59049872317141658381087189 1383981382433007618306731)
      ·
        refine ⟨2075972073649511427460097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1383981382433007618306731 2075972073649511427460097)
        ·
          refine ⟨1556979055237133570595073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2075972073649511427460097 1556979055237133570595073)
          ·
            refine ⟨1167734291427850177946305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1556979055237133570595073 1167734291427850177946305)
            ·
              refine ⟨875800718570887633459729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1167734291427850177946305 875800718570887633459729)
              ·
                refine ⟨656850538928165725094797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 875800718570887633459729 656850538928165725094797)
                ·
                  refine ⟨246318952098062146910549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 656850538928165725094797 246318952098062146910549)
                  ·
                    rfl

theorem cell21_1079335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 3].length) (baseStart_1079335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079335 prefixEnd_1079335 := by exact prefixLift 1079335
  have htrace : WordTrace (prefixWord ++ tailWord_1079335) baseStart_1079335 baseEnd_1079335 := by
    simpa [prefixWord, tailWord_1079335, baseEnd_1079335] using wordTrace_append hprefix tailTrace_1079335
  have hstable : (prefixWord ++ tailWord_1079335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079335).length < 2 ^ (prefixWord ++ tailWord_1079335).sum := by decide
  have hdescent : baseEnd_1079335 < baseStart_1079335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079388 : List Nat := [2, 2, 4, 1, 1, 3, 8]
def baseStart_1079388 : Nat := 118140960795 + 1079388 * 2 ^ 59
def prefixEnd_1079388 : Nat := 4983230072969 + 3 ^ 40 * 1079388 * 2
def baseEnd_1079388 : Nat := 27370116380016203614123

theorem tailTrace_1079388 : CollatzResearch.WordTrace tailWord_1079388 prefixEnd_1079388 27370116380016203614123 := by
  unfold tailWord_1079388
  simp only [CollatzResearch.WordTrace]
  refine ⟨19684257306784547819535409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26245676409046063759380545 19684257306784547819535409)
  ·
    refine ⟨14763192980088410864651557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19684257306784547819535409 14763192980088410864651557)
    ·
      refine ⟨2768098683766577037122167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14763192980088410864651557 2768098683766577037122167)
      ·
        refine ⟨4152148025649865555683251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2768098683766577037122167 4152148025649865555683251)
        ·
          refine ⟨6228222038474798333524877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4152148025649865555683251 6228222038474798333524877)
          ·
            refine ⟨2335583264428049375071829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6228222038474798333524877 2335583264428049375071829)
            ·
              refine ⟨27370116380016203614123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2335583264428049375071829 27370116380016203614123)
              ·
                rfl

theorem cell21_1079388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 8].length) (baseStart_1079388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079388 prefixEnd_1079388 := by exact prefixLift 1079388
  have htrace : WordTrace (prefixWord ++ tailWord_1079388) baseStart_1079388 baseEnd_1079388 := by
    simpa [prefixWord, tailWord_1079388, baseEnd_1079388] using wordTrace_append hprefix tailTrace_1079388
  have hstable : (prefixWord ++ tailWord_1079388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079388).length < 2 ^ (prefixWord ++ tailWord_1079388).sum := by decide
  have hdescent : baseEnd_1079388 < baseStart_1079388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079453 : List Nat := [1, 4, 2, 1, 1, 4, 3, 2, 3]
def baseStart_1079453 : Nat := 118140960795 + 1079453 * 2 ^ 59
def prefixEnd_1079453 : Nat := 4983230072969 + 3 ^ 40 * 1079453 * 2
def baseEnd_1079453 : Nat := 246345881305720163943641

theorem tailTrace_1079453 : CollatzResearch.WordTrace tailWord_1079453 prefixEnd_1079453 246345881305720163943641 := by
  unfold tailWord_1079453
  simp only [CollatzResearch.WordTrace]
  refine ⟨39370885358333611740187013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26247256905555741160124675 39370885358333611740187013)
  ·
    refine ⟨7382041004687552201285065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39370885358333611740187013 7382041004687552201285065)
    ·
      refine ⟨5536530753515664150963799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7382041004687552201285065 5536530753515664150963799)
      ·
        refine ⟨8304796130273496226445699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5536530753515664150963799 8304796130273496226445699)
        ·
          refine ⟨12457194195410244339668549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8304796130273496226445699 12457194195410244339668549)
          ·
            refine ⟨2335723911639420813687853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12457194195410244339668549 2335723911639420813687853)
            ·
              refine ⟨875896466864782805132945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2335723911639420813687853 875896466864782805132945)
              ·
                refine ⟨656922350148587103849709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 875896466864782805132945 656922350148587103849709)
                ·
                  refine ⟨246345881305720163943641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 656922350148587103849709 246345881305720163943641)
                  ·
                    rfl

theorem cell21_1079453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_1079453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079453 prefixEnd_1079453 := by exact prefixLift 1079453
  have htrace : WordTrace (prefixWord ++ tailWord_1079453) baseStart_1079453 baseEnd_1079453 := by
    simpa [prefixWord, tailWord_1079453, baseEnd_1079453] using wordTrace_append hprefix tailTrace_1079453
  have hstable : (prefixWord ++ tailWord_1079453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079453).length < 2 ^ (prefixWord ++ tailWord_1079453).sum := by decide
  have hdescent : baseEnd_1079453 < baseStart_1079453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079512 : List Nat := [2, 1, 2, 2, 4, 2, 1, 4, 3]
def baseStart_1079512 : Nat := 118140960795 + 1079512 * 2 ^ 59
def prefixEnd_1079512 : Nat := 4983230072969 + 3 ^ 40 * 1079512 * 2
def baseEnd_1079512 : Nat := 246359345909549172460187

theorem tailTrace_1079512 : CollatzResearch.WordTrace tailWord_1079512 prefixEnd_1079512 246359345909549172460187 := by
  unfold tailWord_1079512
  simp only [CollatzResearch.WordTrace]
  refine ⟨19686518632559932408292395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26248691510079909877723193 19686518632559932408292395)
  ·
    refine ⟨29529777948839898612438593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19686518632559932408292395 29529777948839898612438593)
    ·
      refine ⟨22147333461629923959328945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29529777948839898612438593 22147333461629923959328945)
      ·
        refine ⟨16610500096222442969496709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22147333461629923959328945 16610500096222442969496709)
        ·
          refine ⟨3114468768041708056780633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16610500096222442969496709 3114468768041708056780633)
          ·
            refine ⟨2335851576031281042585475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3114468768041708056780633 2335851576031281042585475)
            ·
              refine ⟨3503777364046921563878213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2335851576031281042585475 3503777364046921563878213)
              ·
                refine ⟨656958255758797793227165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3503777364046921563878213 656958255758797793227165)
                ·
                  refine ⟨246359345909549172460187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 656958255758797793227165 246359345909549172460187)
                  ·
                    rfl

theorem cell21_1079512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 3].length) (baseStart_1079512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079512 prefixEnd_1079512 := by exact prefixLift 1079512
  have htrace : WordTrace (prefixWord ++ tailWord_1079512) baseStart_1079512 baseEnd_1079512 := by
    simpa [prefixWord, tailWord_1079512, baseEnd_1079512] using wordTrace_append hprefix tailTrace_1079512
  have hstable : (prefixWord ++ tailWord_1079512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079512).length < 2 ^ (prefixWord ++ tailWord_1079512).sum := by decide
  have hdescent : baseEnd_1079512 < baseStart_1079512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079585 : List Nat := [1, 2, 3, 2, 1, 1, 2, 5, 4]
def baseStart_1079585 : Nat := 118140960795 + 1079585 * 2 ^ 59
def prefixEnd_1079585 : Nat := 4983230072969 + 3 ^ 40 * 1079585 * 2
def baseEnd_1079585 : Nat := 246376005504117267743371

theorem tailTrace_1079585 : CollatzResearch.WordTrace tailWord_1079585 prefixEnd_1079585 246376005504117267743371 := by
  unfold tailWord_1079585
  simp only [CollatzResearch.WordTrace]
  refine ⟨39375699793855398283992209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26250466529236932189328139 39375699793855398283992209)
  ·
    refine ⟨29531774845391548712994157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39375699793855398283992209 29531774845391548712994157)
    ·
      refine ⟨11074415567021830767372809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29531774845391548712994157 11074415567021830767372809)
      ·
        refine ⟨8305811675266373075529607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11074415567021830767372809 8305811675266373075529607)
        ·
          refine ⟨12458717512899559613294411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8305811675266373075529607 12458717512899559613294411)
          ·
            refine ⟨18688076269349339419941617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12458717512899559613294411 18688076269349339419941617)
            ·
              refine ⟨14016057202012004564956213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18688076269349339419941617 14016057202012004564956213)
              ·
                refine ⟨1314005362688625427964645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14016057202012004564956213 1314005362688625427964645)
                ·
                  refine ⟨246376005504117267743371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1314005362688625427964645 246376005504117267743371)
                  ·
                    rfl

theorem cell21_1079585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_1079585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079585 prefixEnd_1079585 := by exact prefixLift 1079585
  have htrace : WordTrace (prefixWord ++ tailWord_1079585) baseStart_1079585 baseEnd_1079585 := by
    simpa [prefixWord, tailWord_1079585, baseEnd_1079585] using wordTrace_append hprefix tailTrace_1079585
  have hstable : (prefixWord ++ tailWord_1079585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079585).length < 2 ^ (prefixWord ++ tailWord_1079585).sum := by decide
  have hdescent : baseEnd_1079585 < baseStart_1079585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079630 : List Nat := [4, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_1079630 : Nat := 118140960795 + 1079630 * 2 ^ 59
def prefixEnd_1079630 : Nat := 4983230072969 + 3 ^ 40 * 1079630 * 2
def baseEnd_1079630 : Nat := 246386275117207189493279

theorem tailTrace_1079630 : CollatzResearch.WordTrace tailWord_1079630 prefixEnd_1079630 246386275117207189493279 := by
  unfold tailWord_1079630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4922167634836546371172543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26251560719128247312920229 4922167634836546371172543)
  ·
    refine ⟨7383251452254819556758815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4922167634836546371172543 7383251452254819556758815)
    ·
      refine ⟨11074877178382229335138223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7383251452254819556758815 11074877178382229335138223)
      ·
        refine ⟨16612315767573344002707335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11074877178382229335138223 16612315767573344002707335)
        ·
          refine ⟨24918473651360016004061003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16612315767573344002707335 24918473651360016004061003)
          ·
            refine ⟨37377710477040024006091505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24918473651360016004061003 37377710477040024006091505)
            ·
              refine ⟨28033282857780018004568629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37377710477040024006091505 28033282857780018004568629)
              ·
                refine ⟨2628120267916876687928309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28033282857780018004568629 2628120267916876687928309)
                ·
                  refine ⟨246386275117207189493279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2628120267916876687928309 246386275117207189493279)
                  ·
                    rfl

theorem cell21_1079630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_1079630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079630 prefixEnd_1079630 := by exact prefixLift 1079630
  have htrace : WordTrace (prefixWord ++ tailWord_1079630) baseStart_1079630 baseEnd_1079630 := by
    simpa [prefixWord, tailWord_1079630, baseEnd_1079630] using wordTrace_append hprefix tailTrace_1079630
  have hstable : (prefixWord ++ tailWord_1079630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079630).length < 2 ^ (prefixWord ++ tailWord_1079630).sum := by decide
  have hdescent : baseEnd_1079630 < baseStart_1079630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079681 : List Nat := [1, 2, 4, 3, 1, 1, 4, 2, 3]
def baseStart_1079681 : Nat := 118140960795 + 1079681 * 2 ^ 59
def prefixEnd_1079681 : Nat := 4983230072969 + 3 ^ 40 * 1079681 * 2
def baseEnd_1079681 : Nat := 246397914012042434143175

theorem tailTrace_1079681 : CollatzResearch.WordTrace tailWord_1079681 prefixEnd_1079681 246397914012042434143175 := by
  unfold tailWord_1079681
  simp only [CollatzResearch.WordTrace]
  refine ⟨39379201201507606679486897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26252800801005071119657931 39379201201507606679486897)
  ·
    refine ⟨29534400901130705009615173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39379201201507606679486897 29534400901130705009615173)
    ·
      refine ⟨5537700168962007189302845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29534400901130705009615173 5537700168962007189302845)
      ·
        refine ⟨2076637563360752695988567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5537700168962007189302845 2076637563360752695988567)
        ·
          refine ⟨3114956345041129043982851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2076637563360752695988567 3114956345041129043982851)
          ·
            refine ⟨4672434517561693565974277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3114956345041129043982851 4672434517561693565974277)
            ·
              refine ⟨876081472042817543620177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4672434517561693565974277 876081472042817543620177)
              ·
                refine ⟨657061104032113157715133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 876081472042817543620177 657061104032113157715133)
                ·
                  refine ⟨246397914012042434143175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 657061104032113157715133 246397914012042434143175)
                  ·
                    rfl

theorem cell21_1079681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 3].length) (baseStart_1079681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079681 prefixEnd_1079681 := by exact prefixLift 1079681
  have htrace : WordTrace (prefixWord ++ tailWord_1079681) baseStart_1079681 baseEnd_1079681 := by
    simpa [prefixWord, tailWord_1079681, baseEnd_1079681] using wordTrace_append hprefix tailTrace_1079681
  have hstable : (prefixWord ++ tailWord_1079681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079681).length < 2 ^ (prefixWord ++ tailWord_1079681).sum := by decide
  have hdescent : baseEnd_1079681 < baseStart_1079681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079692 : List Nat := [2, 2, 1, 2, 1, 6, 1, 6]
def baseStart_1079692 : Nat := 118140960795 + 1079692 * 2 ^ 59
def prefixEnd_1079692 : Nat := 4983230072969 + 3 ^ 40 * 1079692 * 2
def baseEnd_1079692 : Nat := 82133474787302953153273

theorem tailTrace_1079692 : CollatzResearch.WordTrace tailWord_1079692 prefixEnd_1079692 82133474787302953153273 := by
  unfold tailWord_1079692
  simp only [CollatzResearch.WordTrace]
  refine ⟨19689801202233877779068665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26253068269645170372091553 19689801202233877779068665)
  ·
    refine ⟨14767350901675408334301499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19689801202233877779068665 14767350901675408334301499)
    ·
      refine ⟨22151026352513112501452249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14767350901675408334301499 22151026352513112501452249)
      ·
        refine ⟨16613269764384834376089187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22151026352513112501452249 16613269764384834376089187)
        ·
          refine ⟨24919904646577251564133781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16613269764384834376089187 24919904646577251564133781)
          ·
            refine ⟨1168120530308308667068771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24919904646577251564133781 1168120530308308667068771)
            ·
              refine ⟨1752180795462463000603157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1168120530308308667068771 1752180795462463000603157)
              ·
                refine ⟨82133474787302953153273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1752180795462463000603157 82133474787302953153273)
                ·
                  rfl

theorem cell21_1079692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 6].length) (baseStart_1079692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079692 prefixEnd_1079692 := by exact prefixLift 1079692
  have htrace : WordTrace (prefixWord ++ tailWord_1079692) baseStart_1079692 baseEnd_1079692 := by
    simpa [prefixWord, tailWord_1079692, baseEnd_1079692] using wordTrace_append hprefix tailTrace_1079692
  have hstable : (prefixWord ++ tailWord_1079692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079692).length < 2 ^ (prefixWord ++ tailWord_1079692).sum := by decide
  have hdescent : baseEnd_1079692 < baseStart_1079692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079706 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 7]
def baseStart_1079706 : Nat := 118140960795 + 1079706 * 2 ^ 59
def prefixEnd_1079706 : Nat := 4983230072969 + 3 ^ 40 * 1079706 * 2
def baseEnd_1079706 : Nat := 246403619352647946226457

theorem tailTrace_1079706 : CollatzResearch.WordTrace tailWord_1079706 prefixEnd_1079706 246403619352647946226457 := by
  unfold tailWord_1079706
  simp only [CollatzResearch.WordTrace]
  refine ⟨9845028256604258987286743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26253408684278023966097981 9845028256604258987286743)
  ·
    refine ⟨14767542384906388480930115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9845028256604258987286743 14767542384906388480930115)
    ·
      refine ⟨22151313577359582721395173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14767542384906388480930115 22151313577359582721395173)
      ·
        refine ⟨4153371295754921760261595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22151313577359582721395173 4153371295754921760261595)
        ·
          refine ⟨6230056943632382640392393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4153371295754921760261595 6230056943632382640392393)
          ·
            refine ⟨4672542707724286980294295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6230056943632382640392393 4672542707724286980294295)
            ·
              refine ⟨7008814061586430470441443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4672542707724286980294295 7008814061586430470441443)
              ·
                refine ⟨10513221092379645705662165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7008814061586430470441443 10513221092379645705662165)
                ·
                  refine ⟨246403619352647946226457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10513221092379645705662165 246403619352647946226457)
                  ·
                    rfl

theorem cell21_1079706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_1079706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079706 prefixEnd_1079706 := by exact prefixLift 1079706
  have htrace : WordTrace (prefixWord ++ tailWord_1079706) baseStart_1079706 baseEnd_1079706 := by
    simpa [prefixWord, tailWord_1079706, baseEnd_1079706] using wordTrace_append hprefix tailTrace_1079706
  have hstable : (prefixWord ++ tailWord_1079706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079706).length < 2 ^ (prefixWord ++ tailWord_1079706).sum := by decide
  have hdescent : baseEnd_1079706 < baseStart_1079706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079709 : List Nat := [1, 4, 2, 1, 4, 1, 3, 5]
def baseStart_1079709 : Nat := 118140960795 + 1079709 * 2 ^ 59
def prefixEnd_1079709 : Nat := 4983230072969 + 3 ^ 40 * 1079709 * 2
def baseEnd_1079709 : Nat := 82134767997840202558817

theorem tailTrace_1079709 : CollatzResearch.WordTrace tailWord_1079709 prefixEnd_1079709 82134767997840202558817 := by
  unfold tailWord_1079709
  simp only [CollatzResearch.WordTrace]
  refine ⟨39380222445406167461506181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26253481630270778307670787 39380222445406167461506181)
  ·
    refine ⟨7383791708513656399032409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39380222445406167461506181 7383791708513656399032409)
    ·
      refine ⟨5537843781385242299274307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7383791708513656399032409 5537843781385242299274307)
      ·
        refine ⟨8306765672077863448911461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5537843781385242299274307 8306765672077863448911461)
        ·
          refine ⟨1557518563514599396670899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8306765672077863448911461 1557518563514599396670899)
          ·
            refine ⟨2336277845271899095006349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1557518563514599396670899 2336277845271899095006349)
            ·
              refine ⟨876104191976962160627381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2336277845271899095006349 876104191976962160627381)
              ·
                refine ⟨82134767997840202558817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 876104191976962160627381 82134767997840202558817)
                ·
                  rfl

theorem cell21_1079709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 5].length) (baseStart_1079709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079709 prefixEnd_1079709 := by exact prefixLift 1079709
  have htrace : WordTrace (prefixWord ++ tailWord_1079709) baseStart_1079709 baseEnd_1079709 := by
    simpa [prefixWord, tailWord_1079709, baseEnd_1079709] using wordTrace_append hprefix tailTrace_1079709
  have hstable : (prefixWord ++ tailWord_1079709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079709).length < 2 ^ (prefixWord ++ tailWord_1079709).sum := by decide
  have hdescent : baseEnd_1079709 < baseStart_1079709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079737 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 6]
def baseStart_1079737 : Nat := 118140960795 + 1079737 * 2 ^ 59
def prefixEnd_1079737 : Nat := 4983230072969 + 3 ^ 40 * 1079737 * 2
def baseEnd_1079737 : Nat := 246410693974998781209727

theorem tailTrace_1079737 : CollatzResearch.WordTrace tailWord_1079737 prefixEnd_1079737 246410693974998781209727 := by
  unfold tailWord_1079737
  simp only [CollatzResearch.WordTrace]
  refine ⟨39381243689304728243525465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26254162459536485495683643 39381243689304728243525465)
  ·
    refine ⟨29535932766978546182644099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39381243689304728243525465 29535932766978546182644099)
    ·
      refine ⟨44303899150467819273966149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29535932766978546182644099 44303899150467819273966149)
      ·
        refine ⟨8306981090712716113868653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44303899150467819273966149 8306981090712716113868653)
        ·
          refine ⟨3115117909017268542700745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8306981090712716113868653 3115117909017268542700745)
          ·
            refine ⟨2336338431762951407025559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3115117909017268542700745 2336338431762951407025559)
            ·
              refine ⟨3504507647644427110538339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2336338431762951407025559 3504507647644427110538339)
              ·
                refine ⟨5256761471466640665807509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3504507647644427110538339 5256761471466640665807509)
                ·
                  refine ⟨246410693974998781209727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5256761471466640665807509 246410693974998781209727)
                  ·
                    rfl

theorem cell21_1079737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_1079737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079737 prefixEnd_1079737 := by exact prefixLift 1079737
  have htrace : WordTrace (prefixWord ++ tailWord_1079737) baseStart_1079737 baseEnd_1079737 := by
    simpa [prefixWord, tailWord_1079737, baseEnd_1079737] using wordTrace_append hprefix tailTrace_1079737
  have hstable : (prefixWord ++ tailWord_1079737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079737).length < 2 ^ (prefixWord ++ tailWord_1079737).sum := by decide
  have hdescent : baseEnd_1079737 < baseStart_1079737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079740 : List Nat := [2, 2, 2, 4, 1, 1, 2, 4, 3]
def baseStart_1079740 : Nat := 118140960795 + 1079740 * 2 ^ 59
def prefixEnd_1079740 : Nat := 4983230072969 + 3 ^ 40 * 1079740 * 2
def baseEnd_1079740 : Nat := 246411378615871442659721

theorem tailTrace_1079740 : CollatzResearch.WordTrace tailWord_1079740 prefixEnd_1079740 246411378615871442659721 := by
  unfold tailWord_1079740
  simp only [CollatzResearch.WordTrace]
  refine ⟨19690676554146929877942337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26254235405529239837256449 19690676554146929877942337)
  ·
    refine ⟨14768007415610197408456753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19690676554146929877942337 14768007415610197408456753)
    ·
      refine ⟨11076005561707648056342565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14768007415610197408456753 11076005561707648056342565)
      ·
        refine ⟨2076751042820184010564231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11076005561707648056342565 2076751042820184010564231)
        ·
          refine ⟨3115126564230276015846347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2076751042820184010564231 3115126564230276015846347)
          ·
            refine ⟨4672689846345414023769521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3115126564230276015846347 4672689846345414023769521)
            ·
              refine ⟨3504517384759060517827141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4672689846345414023769521 3504517384759060517827141)
              ·
                refine ⟨657097009642323847092589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3504517384759060517827141 657097009642323847092589)
                ·
                  refine ⟨246411378615871442659721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 657097009642323847092589 246411378615871442659721)
                  ·
                    rfl

theorem cell21_1079740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_1079740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079740 prefixEnd_1079740 := by exact prefixLift 1079740
  have htrace : WordTrace (prefixWord ++ tailWord_1079740) baseStart_1079740 baseEnd_1079740 := by
    simpa [prefixWord, tailWord_1079740, baseEnd_1079740] using wordTrace_append hprefix tailTrace_1079740
  have hstable : (prefixWord ++ tailWord_1079740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079740).length < 2 ^ (prefixWord ++ tailWord_1079740).sum := by decide
  have hdescent : baseEnd_1079740 < baseStart_1079740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079754 : List Nat := [3, 1, 2, 1, 2, 2, 5, 1, 4]
def baseStart_1079754 : Nat := 118140960795 + 1079754 * 2 ^ 59
def prefixEnd_1079754 : Nat := 4983230072969 + 3 ^ 40 * 1079754 * 2
def baseEnd_1079754 : Nat := 246414573606610529426359

theorem tailTrace_1079754 : CollatzResearch.WordTrace tailWord_1079754 prefixEnd_1079754 246414573606610529426359 := by
  unfold tailWord_1079754
  simp only [CollatzResearch.WordTrace]
  refine ⟨9845465932560785036723579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26254575820162093431262877 9845465932560785036723579)
  ·
    refine ⟨14768198898841177555085369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9845465932560785036723579 14768198898841177555085369)
    ·
      refine ⟨11076149174130883166314027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14768198898841177555085369 11076149174130883166314027)
      ·
        refine ⟨16614223761196324749471041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11076149174130883166314027 16614223761196324749471041)
        ·
          refine ⟨12460667820897243562103281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16614223761196324749471041 12460667820897243562103281)
          ·
            refine ⟨9345500865672932671577461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12460667820897243562103281 9345500865672932671577461)
            ·
              refine ⟨876140706156837437960387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9345500865672932671577461 876140706156837437960387)
              ·
                refine ⟨1314211059235256156940581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 876140706156837437960387 1314211059235256156940581)
                ·
                  refine ⟨246414573606610529426359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1314211059235256156940581 246414573606610529426359)
                  ·
                    rfl

theorem cell21_1079754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_1079754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079754 prefixEnd_1079754 := by exact prefixLift 1079754
  have htrace : WordTrace (prefixWord ++ tailWord_1079754) baseStart_1079754 baseEnd_1079754 := by
    simpa [prefixWord, tailWord_1079754, baseEnd_1079754] using wordTrace_append hprefix tailTrace_1079754
  have hstable : (prefixWord ++ tailWord_1079754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079754).length < 2 ^ (prefixWord ++ tailWord_1079754).sum := by decide
  have hdescent : baseEnd_1079754 < baseStart_1079754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079844 : List Nat := [2, 3, 1, 5, 1, 9]
def baseStart_1079844 : Nat := 118140960795 + 1079844 * 2 ^ 59
def prefixEnd_1079844 : Nat := 4983230072969 + 3 ^ 40 * 1079844 * 2
def baseEnd_1079844 : Nat := 9127226401214458256525

theorem tailTrace_1079844 : CollatzResearch.WordTrace tailWord_1079844 prefixEnd_1079844 9127226401214458256525 := by
  unfold tailWord_1079844
  simp only [CollatzResearch.WordTrace]
  refine ⟨19692573149958542758835293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26256764199944723678447057 19692573149958542758835293)
  ·
    refine ⟨7384714931234453534563235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19692573149958542758835293 7384714931234453534563235)
    ·
      refine ⟨11077072396851680301844853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7384714931234453534563235 11077072396851680301844853)
      ·
        refine ⟨1038475537204845028297955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11077072396851680301844853 1038475537204845028297955)
        ·
          refine ⟨1557713305807267542446933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1038475537204845028297955 1557713305807267542446933)
          ·
            refine ⟨9127226401214458256525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1557713305807267542446933 9127226401214458256525)
            ·
              rfl

theorem cell21_1079844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 9].length) (baseStart_1079844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079844 prefixEnd_1079844 := by exact prefixLift 1079844
  have htrace : WordTrace (prefixWord ++ tailWord_1079844) baseStart_1079844 baseEnd_1079844 := by
    simpa [prefixWord, tailWord_1079844, baseEnd_1079844] using wordTrace_append hprefix tailTrace_1079844
  have hstable : (prefixWord ++ tailWord_1079844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079844).length < 2 ^ (prefixWord ++ tailWord_1079844).sum := by decide
  have hdescent : baseEnd_1079844 < baseStart_1079844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079878 : List Nat := [6, 1, 1, 1, 2, 2, 3, 5]
def baseStart_1079878 : Nat := 118140960795 + 1079878 * 2 ^ 59
def prefixEnd_1079878 : Nat := 4983230072969 + 3 ^ 40 * 1079878 * 2
def baseEnd_1079878 : Nat := 82147624032004623119813

theorem tailTrace_1079878 : CollatzResearch.WordTrace tailWord_1079878 prefixEnd_1079878 82147624032004623119813 := by
  unfold tailWord_1079878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1230824574431059666387759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26257590921195939549605525 1230824574431059666387759)
  ·
    refine ⟨1846236861646589499581639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1230824574431059666387759 1846236861646589499581639)
    ·
      refine ⟨2769355292469884249372459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1846236861646589499581639 2769355292469884249372459)
      ·
        refine ⟨4154032938704826374058689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2769355292469884249372459 4154032938704826374058689)
        ·
          refine ⟨3115524704028619780544017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4154032938704826374058689 3115524704028619780544017)
          ·
            refine ⟨2336643528021464835408013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3115524704028619780544017 2336643528021464835408013)
            ·
              refine ⟨876241323008049313278005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2336643528021464835408013 876241323008049313278005)
              ·
                refine ⟨82147624032004623119813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 876241323008049313278005 82147624032004623119813)
                ·
                  rfl

theorem cell21_1079878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_1079878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079878 prefixEnd_1079878 := by exact prefixLift 1079878
  have htrace : WordTrace (prefixWord ++ tailWord_1079878) baseStart_1079878 baseEnd_1079878 := by
    simpa [prefixWord, tailWord_1079878, baseEnd_1079878] using wordTrace_append hprefix tailTrace_1079878
  have hstable : (prefixWord ++ tailWord_1079878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079878).length < 2 ^ (prefixWord ++ tailWord_1079878).sum := by decide
  have hdescent : baseEnd_1079878 < baseStart_1079878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079892 : List Nat := [2, 4, 1, 1, 1, 4, 2, 3, 3]
def baseStart_1079892 : Nat := 118140960795 + 1079892 * 2 ^ 59
def prefixEnd_1079892 : Nat := 4983230072969 + 3 ^ 40 * 1079892 * 2
def baseEnd_1079892 : Nat := 246446067086752956126077

theorem tailTrace_1079892 : CollatzResearch.WordTrace tailWord_1079892 prefixEnd_1079892 246446067086752956126077 := by
  unfold tailWord_1079892
  simp only [CollatzResearch.WordTrace]
  refine ⟨19693448501871594857708965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26257931335828793143611953 19693448501871594857708965)
  ·
    refine ⟨3692521594100924035820431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19693448501871594857708965 3692521594100924035820431)
    ·
      refine ⟨5538782391151386053730647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3692521594100924035820431 5538782391151386053730647)
      ·
        refine ⟨8308173586727079080595971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5538782391151386053730647 8308173586727079080595971)
        ·
          refine ⟨12462260380090618620893957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8308173586727079080595971 12462260380090618620893957)
          ·
            refine ⟨2336673821266990991417617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12462260380090618620893957 2336673821266990991417617)
            ·
              refine ⟨1752505365950243243563213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2336673821266990991417617 1752505365950243243563213)
              ·
                refine ⟨657189512231341216336205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1752505365950243243563213 657189512231341216336205)
                ·
                  refine ⟨246446067086752956126077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 657189512231341216336205 246446067086752956126077)
                  ·
                    rfl

theorem cell21_1079892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_1079892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079892 prefixEnd_1079892 := by exact prefixLift 1079892
  have htrace : WordTrace (prefixWord ++ tailWord_1079892) baseStart_1079892 baseEnd_1079892 := by
    simpa [prefixWord, tailWord_1079892, baseEnd_1079892] using wordTrace_append hprefix tailTrace_1079892
  have hstable : (prefixWord ++ tailWord_1079892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079892).length < 2 ^ (prefixWord ++ tailWord_1079892).sum := by decide
  have hdescent : baseEnd_1079892 < baseStart_1079892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079968 : List Nat := [2, 1, 1, 4, 5, 1, 1, 1, 5]
def baseStart_1079968 : Nat := 118140960795 + 1079968 * 2 ^ 59
def prefixEnd_1079968 : Nat := 4983230072969 + 3 ^ 40 * 1079968 * 2
def baseEnd_1079968 : Nat := 246463411322193712859255

theorem tailTrace_1079968 : CollatzResearch.WordTrace tailWord_1079968 prefixEnd_1079968 246463411322193712859255 := by
  unfold tailWord_1079968
  simp only [CollatzResearch.WordTrace]
  refine ⟨19694834475733927347592279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26259779300978569796789705 19694834475733927347592279)
  ·
    refine ⟨29542251713600891021388419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19694834475733927347592279 29542251713600891021388419)
    ·
      refine ⟨44313377570401336532082629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29542251713600891021388419 44313377570401336532082629)
      ·
        refine ⟨8308758294450250599765493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44313377570401336532082629 8308758294450250599765493)
        ·
          refine ⟨778946090104710993728015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8308758294450250599765493 778946090104710993728015)
          ·
            refine ⟨1168419135157066490592023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778946090104710993728015 1168419135157066490592023)
            ·
              refine ⟨1752628702735599735888035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1168419135157066490592023 1752628702735599735888035)
              ·
                refine ⟨2628943054103399603832053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1752628702735599735888035 2628943054103399603832053)
                ·
                  refine ⟨246463411322193712859255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2628943054103399603832053 246463411322193712859255)
                  ·
                    rfl

theorem cell21_1079968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 5].length) (baseStart_1079968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079968 prefixEnd_1079968 := by exact prefixLift 1079968
  have htrace : WordTrace (prefixWord ++ tailWord_1079968) baseStart_1079968 baseEnd_1079968 := by
    simpa [prefixWord, tailWord_1079968, baseEnd_1079968] using wordTrace_append hprefix tailTrace_1079968
  have hstable : (prefixWord ++ tailWord_1079968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079968).length < 2 ^ (prefixWord ++ tailWord_1079968).sum := by decide
  have hdescent : baseEnd_1079968 < baseStart_1079968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1079993 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 7]
def baseStart_1079993 : Nat := 118140960795 + 1079993 * 2 ^ 59
def prefixEnd_1079993 : Nat := 4983230072969 + 3 ^ 40 * 1079993 * 2
def baseEnd_1079993 : Nat := 246469116662799224942537

theorem tailTrace_1079993 : CollatzResearch.WordTrace tailWord_1079993 prefixEnd_1079993 246469116662799224942537 := by
  unfold tailWord_1079993
  simp only [CollatzResearch.WordTrace]
  refine ⟨39390580776377283964844633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26260387184251522643229755 39390580776377283964844633)
  ·
    refine ⟨29542935582282962973633475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39390580776377283964844633 29542935582282962973633475)
    ·
      refine ⟨44314403373424444460450213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29542935582282962973633475 44314403373424444460450213)
      ·
        refine ⟨8308950632517083336334415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44314403373424444460450213 8308950632517083336334415)
        ·
          refine ⟨12463425948775625004501623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8308950632517083336334415 12463425948775625004501623)
          ·
            refine ⟨18695138923163437506752435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12463425948775625004501623 18695138923163437506752435)
            ·
              refine ⟨28042708384745156260128653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18695138923163437506752435 28042708384745156260128653)
              ·
                refine ⟨10516015644279433597548245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28042708384745156260128653 10516015644279433597548245)
                ·
                  refine ⟨246469116662799224942537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10516015644279433597548245 246469116662799224942537)
                  ·
                    rfl

theorem cell21_1079993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_1079993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1079993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1079993 prefixEnd_1079993 := by exact prefixLift 1079993
  have htrace : WordTrace (prefixWord ++ tailWord_1079993) baseStart_1079993 baseEnd_1079993 := by
    simpa [prefixWord, tailWord_1079993, baseEnd_1079993] using wordTrace_append hprefix tailTrace_1079993
  have hstable : (prefixWord ++ tailWord_1079993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1079993).length < 2 ^ (prefixWord ++ tailWord_1079993).sum := by decide
  have hdescent : baseEnd_1079993 < baseStart_1079993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1079993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080013 : List Nat := [1, 6, 2, 1, 3, 8]
def baseStart_1080013 : Nat := 118140960795 + 1080013 * 2 ^ 59
def prefixEnd_1080013 : Nat := 4983230072969 + 3 ^ 40 * 1080013 * 2
def baseEnd_1080013 : Nat := 9128654849454949429969

theorem tailTrace_1080013 : CollatzResearch.WordTrace tailWord_1080013 prefixEnd_1080013 9128654849454949429969 := by
  unfold tailWord_1080013
  simp only [CollatzResearch.WordTrace]
  refine ⟨39391310236304827380572693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26260873490869884920381795 39391310236304827380572693)
  ·
    refine ⟨1846467667326788783464345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39391310236304827380572693 1846467667326788783464345)
    ·
      refine ⟨1384850750495091587598259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1846467667326788783464345 1384850750495091587598259)
      ·
        refine ⟨2077276125742637381397389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1384850750495091587598259 2077276125742637381397389)
        ·
          refine ⟨778978547153489018024021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2077276125742637381397389 778978547153489018024021)
          ·
            refine ⟨9128654849454949429969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 778978547153489018024021 9128654849454949429969)
            ·
              rfl

theorem cell21_1080013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 8].length) (baseStart_1080013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080013 prefixEnd_1080013 := by exact prefixLift 1080013
  have htrace : WordTrace (prefixWord ++ tailWord_1080013) baseStart_1080013 baseEnd_1080013 := by
    simpa [prefixWord, tailWord_1080013, baseEnd_1080013] using wordTrace_append hprefix tailTrace_1080013
  have hstable : (prefixWord ++ tailWord_1080013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080013).length < 2 ^ (prefixWord ++ tailWord_1080013).sum := by decide
  have hdescent : baseEnd_1080013 < baseStart_1080013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080106 : List Nat := [3, 1, 4, 3, 1, 2, 2, 5]
def baseStart_1080106 : Nat := 118140960795 + 1080106 * 2 ^ 59
def prefixEnd_1080106 : Nat := 4983230072969 + 3 ^ 40 * 1080106 * 2
def baseEnd_1080106 : Nat := 82164968267445379852991

theorem tailTrace_1080106 : CollatzResearch.WordTrace tailWord_1080106 prefixEnd_1080106 82164968267445379852991 := by
  unfold tailWord_1080106
  simp only [CollatzResearch.WordTrace]
  refine ⟨9848675556241976065927043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26263134816645269509138781 9848675556241976065927043)
  ·
    refine ⟨14773013334362964098890565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9848675556241976065927043 14773013334362964098890565)
    ·
      refine ⟨2769940000193055768541981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14773013334362964098890565 2769940000193055768541981)
      ·
        refine ⟨1038727500072395913203243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2769940000193055768541981 1038727500072395913203243)
        ·
          refine ⟨1558091250108593869804865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1038727500072395913203243 1558091250108593869804865)
          ·
            refine ⟨1168568437581445402353649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1558091250108593869804865 1168568437581445402353649)
            ·
              refine ⟨876426328186084051765237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1168568437581445402353649 876426328186084051765237)
              ·
                refine ⟨82164968267445379852991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 876426328186084051765237 82164968267445379852991)
                ·
                  rfl

theorem cell21_1080106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_1080106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080106 prefixEnd_1080106 := by exact prefixLift 1080106
  have htrace : WordTrace (prefixWord ++ tailWord_1080106) baseStart_1080106 baseEnd_1080106 := by
    simpa [prefixWord, tailWord_1080106, baseEnd_1080106] using wordTrace_append hprefix tailTrace_1080106
  have hstable : (prefixWord ++ tailWord_1080106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080106).length < 2 ^ (prefixWord ++ tailWord_1080106).sum := by decide
  have hdescent : baseEnd_1080106 < baseStart_1080106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1080148 : List Nat := [2, 4, 1, 1, 4, 1, 2, 6]
def baseStart_1080148 : Nat := 118140960795 + 1080148 * 2 ^ 59
def prefixEnd_1080148 : Nat := 4983230072969 + 3 ^ 40 * 1080148 * 2
def baseEnd_1080148 : Nat := 82168163258184466619629

theorem tailTrace_1080148 : CollatzResearch.WordTrace tailWord_1080148 prefixEnd_1080148 82168163258184466619629 := by
  unfold tailWord_1080148
  simp only [CollatzResearch.WordTrace]
  refine ⟨19698117045407872718368549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26264156060543830291158065 19698117045407872718368549)
  ·
    refine ⟨3693396946013976134694103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19698117045407872718368549 3693396946013976134694103)
    ·
      refine ⟨5540095419020964202041155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3693396946013976134694103 5540095419020964202041155)
      ·
        refine ⟨8310143128531446303061733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5540095419020964202041155 8310143128531446303061733)
        ·
          refine ⟨1558151836599646181824075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8310143128531446303061733 1558151836599646181824075)
          ·
            refine ⟨2337227754899469272736113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1558151836599646181824075 2337227754899469272736113)
            ·
              refine ⟨1752920816174601954552085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2337227754899469272736113 1752920816174601954552085)
              ·
                refine ⟨82168163258184466619629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1752920816174601954552085 82168163258184466619629)
                ·
                  rfl

theorem cell21_1080148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 6].length) (baseStart_1080148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1080148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1080148 prefixEnd_1080148 := by exact prefixLift 1080148
  have htrace : WordTrace (prefixWord ++ tailWord_1080148) baseStart_1080148 baseEnd_1080148 := by
    simpa [prefixWord, tailWord_1080148, baseEnd_1080148] using wordTrace_append hprefix tailTrace_1080148
  have hstable : (prefixWord ++ tailWord_1080148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1080148).length < 2 ^ (prefixWord ++ tailWord_1080148).sum := by decide
  have hdescent : baseEnd_1080148 < baseStart_1080148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1080148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
