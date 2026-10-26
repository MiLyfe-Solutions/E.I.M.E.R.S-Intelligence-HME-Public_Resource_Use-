import V185TrunkScan23Chunk1100

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6520081 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 5]
def baseStart_6520081 : Nat := 118140960795 + 6520081 * 2 ^ 59
def prefixEnd_6520081 : Nat := 4983230072969 + 3 ^ 40 * 6520081 * 2
def baseEnd_6520081 : Nat := 3347935459247609886802199

theorem tailTrace_6520081 : CollatzResearch.WordTrace tailWord_6520081 prefixEnd_6520081 3347935459247609886802199 := by
  unfold tailWord_6520081
  simp only [CollatzResearch.WordTrace]
  refine ⟨237806890691867553026368097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158537927127911702017578731 237806890691867553026368097)
  ·
    refine ⟨178355168018900664769776073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237806890691867553026368097 178355168018900664769776073)
    ·
      refine ⟨133766376014175498577332055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178355168018900664769776073 133766376014175498577332055)
      ·
        refine ⟨200649564021263247865998083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133766376014175498577332055 200649564021263247865998083)
        ·
          refine ⟨300974346031894871798997125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200649564021263247865998083 300974346031894871798997125)
          ·
            refine ⟨56432689880980288462311961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300974346031894871798997125 56432689880980288462311961)
            ·
              refine ⟨42324517410735216346733971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56432689880980288462311961 42324517410735216346733971)
              ·
                refine ⟨63486776116102824520100957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42324517410735216346733971 63486776116102824520100957)
                ·
                  refine ⟨23807541043538559195037859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63486776116102824520100957 23807541043538559195037859)
                  ·
                    refine ⟨35711311565307838792556789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23807541043538559195037859 35711311565307838792556789)
                    ·
                      refine ⟨3347935459247609886802199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35711311565307838792556789 3347935459247609886802199)
                      ·
                        rfl

theorem cell23_6520081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_6520081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520081 prefixEnd_6520081 := by exact prefixLift 6520081
  have htrace : WordTrace (prefixWord ++ tailWord_6520081) baseStart_6520081 baseEnd_6520081 := by
    simpa [prefixWord, tailWord_6520081, baseEnd_6520081] using wordTrace_append hprefix tailTrace_6520081
  have hstable : (prefixWord ++ tailWord_6520081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520081).length < 2 ^ (prefixWord ++ tailWord_6520081).sum := by decide
  have hdescent : baseEnd_6520081 < baseStart_6520081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520088 : List Nat := [2, 1, 2, 3, 1, 4, 2, 1, 1, 6]
def baseStart_6520088 : Nat := 118140960795 + 6520088 * 2 ^ 59
def prefixEnd_6520088 : Nat := 4983230072969 + 3 ^ 40 * 6520088 * 2
def baseEnd_6520088 : Nat := 1115979684537397119804889

theorem tailTrace_6520088 : CollatzResearch.WordTrace tailWord_6520088 prefixEnd_6520088 1115979684537397119804889 := by
  unfold tailWord_6520088
  simp only [CollatzResearch.WordTrace]
  refine ⟨118903573001421096610936459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158538097335228128814581945 118903573001421096610936459)
  ·
    refine ⟨178355359502131644916404689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118903573001421096610936459 178355359502131644916404689)
    ·
      refine ⟨133766519626598733687303517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178355359502131644916404689 133766519626598733687303517)
      ·
        refine ⟨50162444859974525132738819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133766519626598733687303517 50162444859974525132738819)
        ·
          refine ⟨75243667289961787699108229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50162444859974525132738819 75243667289961787699108229)
          ·
            refine ⟨14108187616867835193582793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75243667289961787699108229 14108187616867835193582793)
            ·
              refine ⟨10581140712650876395187095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14108187616867835193582793 10581140712650876395187095)
              ·
                refine ⟨15871711068976314592780643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10581140712650876395187095 15871711068976314592780643)
                ·
                  refine ⟨23807566603464471889170965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15871711068976314592780643 23807566603464471889170965)
                  ·
                    refine ⟨1115979684537397119804889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23807566603464471889170965 1115979684537397119804889)
                    ·
                      rfl

theorem cell23_6520088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_6520088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520088 prefixEnd_6520088 := by exact prefixLift 6520088
  have htrace : WordTrace (prefixWord ++ tailWord_6520088) baseStart_6520088 baseEnd_6520088 := by
    simpa [prefixWord, tailWord_6520088, baseEnd_6520088] using wordTrace_append hprefix tailTrace_6520088
  have hstable : (prefixWord ++ tailWord_6520088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520088).length < 2 ^ (prefixWord ++ tailWord_6520088).sum := by decide
  have hdescent : baseEnd_6520088 < baseStart_6520088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520109 : List Nat := [1, 5, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_6520109 : Nat := 118140960795 + 6520109 * 2 ^ 59
def prefixEnd_6520109 : Nat := 4983230072969 + 3 ^ 40 * 6520109 * 2
def baseEnd_6520109 : Nat := 1115983278901978592417357

theorem tailTrace_6520109 : CollatzResearch.WordTrace tailWord_6520109 prefixEnd_6520109 1115983278901978592417357 := by
  unfold tailWord_6520109
  simp only [CollatzResearch.WordTrace]
  refine ⟨237807911935766113808387381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158538607957177409205591587 237807911935766113808387381)
  ·
    refine ⟨22294491743978073169536317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237807911935766113808387381 22294491743978073169536317)
    ·
      refine ⟨8360434403991777438576119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22294491743978073169536317 8360434403991777438576119)
      ·
        refine ⟨12540651605987666157864179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8360434403991777438576119 12540651605987666157864179)
        ·
          refine ⟨18810977408981499236796269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12540651605987666157864179 18810977408981499236796269)
          ·
            refine ⟨7054116528368062213798601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18810977408981499236796269 7054116528368062213798601)
            ·
              refine ⟨5290587396276046660348951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7054116528368062213798601 5290587396276046660348951)
              ·
                refine ⟨7935881094414069990523427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5290587396276046660348951 7935881094414069990523427)
                ·
                  refine ⟨11903821641621104985785141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7935881094414069990523427 11903821641621104985785141)
                  ·
                    refine ⟨1115983278901978592417357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11903821641621104985785141 1115983278901978592417357)
                    ·
                      rfl

theorem cell23_6520109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_6520109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520109 prefixEnd_6520109 := by exact prefixLift 6520109
  have htrace : WordTrace (prefixWord ++ tailWord_6520109) baseStart_6520109 baseEnd_6520109 := by
    simpa [prefixWord, tailWord_6520109, baseEnd_6520109] using wordTrace_append hprefix tailTrace_6520109
  have hstable : (prefixWord ++ tailWord_6520109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520109).length < 2 ^ (prefixWord ++ tailWord_6520109).sum := by decide
  have hdescent : baseEnd_6520109 < baseStart_6520109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520115 : List Nat := [1, 1, 1, 2, 5, 3, 1, 3, 1, 2, 3]
def baseStart_6520115 : Nat := 118140960795 + 6520115 * 2 ^ 59
def prefixEnd_6520115 : Nat := 4983230072969 + 3 ^ 40 * 6520115 * 2
def baseEnd_6520115 : Nat := 3347952917589862753777043

theorem tailTrace_6520115 : CollatzResearch.WordTrace tailWord_6520115 prefixEnd_6520115 3347952917589862753777043 := by
  unfold tailWord_6520115
  simp only [CollatzResearch.WordTrace]
  refine ⟨237808130773744376833105799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158538753849162917888737199 237808130773744376833105799)
  ·
    refine ⟨356712196160616565249658699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237808130773744376833105799 356712196160616565249658699)
    ·
      refine ⟨535068294240924847874488049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356712196160616565249658699 535068294240924847874488049)
      ·
        refine ⟨401301220680693635905866037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535068294240924847874488049 401301220680693635905866037)
        ·
          refine ⟨37621989438815028366174941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 401301220680693635905866037 37621989438815028366174941)
          ·
            refine ⟨14108246039555635637315603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37621989438815028366174941 14108246039555635637315603)
            ·
              refine ⟨21162369059333453455973405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14108246039555635637315603 21162369059333453455973405)
              ·
                refine ⟨7935888397250045045990027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21162369059333453455973405 7935888397250045045990027)
                ·
                  refine ⟨11903832595875067568985041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7935888397250045045990027 11903832595875067568985041)
                  ·
                    refine ⟨8927874446906300676738781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11903832595875067568985041 8927874446906300676738781)
                    ·
                      refine ⟨3347952917589862753777043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8927874446906300676738781 3347952917589862753777043)
                      ·
                        rfl

theorem cell23_6520115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 2, 3].length) (baseStart_6520115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520115 prefixEnd_6520115 := by exact prefixLift 6520115
  have htrace : WordTrace (prefixWord ++ tailWord_6520115) baseStart_6520115 baseEnd_6520115 := by
    simpa [prefixWord, tailWord_6520115, baseEnd_6520115] using wordTrace_append hprefix tailTrace_6520115
  have hstable : (prefixWord ++ tailWord_6520115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520115).length < 2 ^ (prefixWord ++ tailWord_6520115).sum := by decide
  have hdescent : baseEnd_6520115 < baseStart_6520115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520129 : List Nat := [1, 2, 5, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_6520129 : Nat := 118140960795 + 6520129 * 2 ^ 59
def prefixEnd_6520129 : Nat := 4983230072969 + 3 ^ 40 * 6520129 * 2
def baseEnd_6520129 : Nat := 3347960106319025699001979

theorem tailTrace_6520129 : CollatzResearch.WordTrace tailWord_6520129 prefixEnd_6520129 3347960106319025699001979 := by
  unfold tailWord_6520129
  simp only [CollatzResearch.WordTrace]
  refine ⟨237808641395693657224115441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158539094263795771482743627 237808641395693657224115441)
  ·
    refine ⟨178356481046770242918086581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237808641395693657224115441 178356481046770242918086581)
    ·
      refine ⟨16720920098134710273570617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178356481046770242918086581 16720920098134710273570617)
      ·
        refine ⟨12540690073601032705177963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16720920098134710273570617 12540690073601032705177963)
        ·
          refine ⟨18811035110401549057766945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12540690073601032705177963 18811035110401549057766945)
          ·
            refine ⟨14108276332801161793325209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18811035110401549057766945 14108276332801161793325209)
            ·
              refine ⟨10581207249600871344993907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14108276332801161793325209 10581207249600871344993907)
              ·
                refine ⟨15871810874401307017490861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10581207249600871344993907 15871810874401307017490861)
                ·
                  refine ⟨5951929077900490131559073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15871810874401307017490861 5951929077900490131559073)
                  ·
                    refine ⟨4463946808425367598669305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5951929077900490131559073 4463946808425367598669305)
                    ·
                      refine ⟨3347960106319025699001979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4463946808425367598669305 3347960106319025699001979)
                      ·
                        rfl

theorem cell23_6520129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_6520129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520129 prefixEnd_6520129 := by exact prefixLift 6520129
  have htrace : WordTrace (prefixWord ++ tailWord_6520129) baseStart_6520129 baseEnd_6520129 := by
    simpa [prefixWord, tailWord_6520129, baseEnd_6520129] using wordTrace_append hprefix tailTrace_6520129
  have hstable : (prefixWord ++ tailWord_6520129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520129).length < 2 ^ (prefixWord ++ tailWord_6520129).sum := by decide
  have hdescent : baseEnd_6520129 < baseStart_6520129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520161 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 1, 8]
def baseStart_6520161 : Nat := 118140960795 + 6520161 * 2 ^ 59
def prefixEnd_6520161 : Nat := 4983230072969 + 3 ^ 40 * 6520161 * 2
def baseEnd_6520161 : Nat := 1115992179233323191267277

theorem tailTrace_6520161 : CollatzResearch.WordTrace tailWord_6520161 prefixEnd_6520161 1115992179233323191267277 := by
  unfold tailWord_6520161
  simp only [CollatzResearch.WordTrace]
  refine ⟨237809808531577726689280337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158539872354385151126186891 237809808531577726689280337)
  ·
    refine ⟨178357356398683295016960253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237809808531577726689280337 178357356398683295016960253)
    ·
      refine ⟨66884008649506235631360095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178357356398683295016960253 66884008649506235631360095)
      ·
        refine ⟨100326012974259353447040143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66884008649506235631360095 100326012974259353447040143)
        ·
          refine ⟨150489019461389030170560215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100326012974259353447040143 150489019461389030170560215)
          ·
            refine ⟨225733529192083545255840323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150489019461389030170560215 225733529192083545255840323)
            ·
              refine ⟨338600293788125317883760485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225733529192083545255840323 338600293788125317883760485)
              ·
                refine ⟨63487555085273497103205091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 338600293788125317883760485 63487555085273497103205091)
                ·
                  refine ⟨95231332627910245654807637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63487555085273497103205091 95231332627910245654807637)
                  ·
                    refine ⟨1115992179233323191267277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95231332627910245654807637 1115992179233323191267277)
                    ·
                      rfl

theorem cell23_6520161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_6520161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520161 prefixEnd_6520161 := by exact prefixLift 6520161
  have htrace : WordTrace (prefixWord ++ tailWord_6520161) baseStart_6520161 baseEnd_6520161 := by
    simpa [prefixWord, tailWord_6520161, baseEnd_6520161] using wordTrace_append hprefix tailTrace_6520161
  have hstable : (prefixWord ++ tailWord_6520161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520161).length < 2 ^ (prefixWord ++ tailWord_6520161).sum := by decide
  have hdescent : baseEnd_6520161 < baseStart_6520161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520172 : List Nat := [2, 2, 1, 1, 5, 1, 2, 3, 1, 3, 2]
def baseStart_6520172 : Nat := 118140960795 + 6520172 * 2 ^ 59
def prefixEnd_6520172 : Nat := 4983230072969 + 3 ^ 40 * 6520172 * 2
def baseEnd_6520172 : Nat := 3347982185987169030764281

theorem tailTrace_6520172 : CollatzResearch.WordTrace tailWord_6520172 prefixEnd_6520172 3347982185987169030764281 := by
  unfold tailWord_6520172
  simp only [CollatzResearch.WordTrace]
  refine ⟨118905104867268937783965385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158540139823025250378620513 118905104867268937783965385)
  ·
    refine ⟨89178828650451703337974039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118905104867268937783965385 89178828650451703337974039)
    ·
      refine ⟨133768242975677555006961059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89178828650451703337974039 133768242975677555006961059)
      ·
        refine ⟨200652364463516332510441589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133768242975677555006961059 200652364463516332510441589)
        ·
          refine ⟨18811159168454656172853899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200652364463516332510441589 18811159168454656172853899)
          ·
            refine ⟨28216738752681984259280849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18811159168454656172853899 28216738752681984259280849)
            ·
              refine ⟨21162554064511488194460637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28216738752681984259280849 21162554064511488194460637)
              ·
                refine ⟨7935957774191808072922739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21162554064511488194460637 7935957774191808072922739)
                ·
                  refine ⟨11903936661287712109384109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7935957774191808072922739 11903936661287712109384109)
                  ·
                    refine ⟨4463976247982892041019041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11903936661287712109384109 4463976247982892041019041)
                    ·
                      refine ⟨3347982185987169030764281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4463976247982892041019041 3347982185987169030764281)
                      ·
                        rfl

theorem cell23_6520172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 3, 2].length) (baseStart_6520172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520172 prefixEnd_6520172 := by exact prefixLift 6520172
  have htrace : WordTrace (prefixWord ++ tailWord_6520172) baseStart_6520172 baseEnd_6520172 := by
    simpa [prefixWord, tailWord_6520172, baseEnd_6520172] using wordTrace_append hprefix tailTrace_6520172
  have hstable : (prefixWord ++ tailWord_6520172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520172).length < 2 ^ (prefixWord ++ tailWord_6520172).sum := by decide
  have hdescent : baseEnd_6520172 < baseStart_6520172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520188 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 2, 4, 3]
def baseStart_6520188 : Nat := 118140960795 + 6520188 * 2 ^ 59
def prefixEnd_6520188 : Nat := 4983230072969 + 3 ^ 40 * 6520188 * 2
def baseEnd_6520188 : Nat := 3347990401677640968164207

theorem tailTrace_6520188 : CollatzResearch.WordTrace tailWord_6520188 prefixEnd_6520188 3347990401677640968164207 := by
  unfold tailWord_6520188
  simp only [CollatzResearch.WordTrace]
  refine ⟨118905396651239955150256609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158540528868319940200342145 118905396651239955150256609)
  ·
    refine ⟨89179047488429966362692457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118905396651239955150256609 89179047488429966362692457)
    ·
      refine ⟨66884285616322474772019343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89179047488429966362692457 66884285616322474772019343)
      ·
        refine ⟨100326428424483712158029015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66884285616322474772019343 100326428424483712158029015)
        ·
          refine ⟨150489642636725568237043523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100326428424483712158029015 150489642636725568237043523)
          ·
            refine ⟨225734463955088352355565285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150489642636725568237043523 225734463955088352355565285)
            ·
              refine ⟨42325211991579066066668491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225734463955088352355565285 42325211991579066066668491)
              ·
                refine ⟨63487817987368599100002737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42325211991579066066668491 63487817987368599100002737)
                ·
                  refine ⟨47615863490526449325002053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63487817987368599100002737 47615863490526449325002053)
                  ·
                    refine ⟨8927974404473709248437885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47615863490526449325002053 8927974404473709248437885)
                    ·
                      refine ⟨3347990401677640968164207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8927974404473709248437885 3347990401677640968164207)
                      ·
                        rfl

theorem cell23_6520188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_6520188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520188 prefixEnd_6520188 := by exact prefixLift 6520188
  have htrace : WordTrace (prefixWord ++ tailWord_6520188) baseStart_6520188 baseEnd_6520188 := by
    simpa [prefixWord, tailWord_6520188, baseEnd_6520188] using wordTrace_append hprefix tailTrace_6520188
  have hstable : (prefixWord ++ tailWord_6520188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520188).length < 2 ^ (prefixWord ++ tailWord_6520188).sum := by decide
  have hdescent : baseEnd_6520188 < baseStart_6520188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520206 : List Nat := [4, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2]
def baseStart_6520206 : Nat := 118140960795 + 6520206 * 2 ^ 59
def prefixEnd_6520206 : Nat := 4983230072969 + 3 ^ 40 * 6520206 * 2
def baseEnd_6520206 : Nat := 3347999644329421897739125

theorem tailTrace_6520206 : CollatzResearch.WordTrace tailWord_6520206 prefixEnd_6520206 3347999644329421897739125 := by
  unfold tailWord_6520206
  simp only [CollatzResearch.WordTrace]
  refine ⟨29726431227051837421833559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158540966544276466249778981 29726431227051837421833559)
  ·
    refine ⟨44589646840577756132750339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29726431227051837421833559 44589646840577756132750339)
    ·
      refine ⟨66884470260866634199125509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44589646840577756132750339 66884470260866634199125509)
      ·
        refine ⟨12540838173912493912336033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66884470260866634199125509 12540838173912493912336033)
        ·
          refine ⟨9405628630434370434252025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12540838173912493912336033 9405628630434370434252025)
          ·
            refine ⟨7054221472825777825689019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9405628630434370434252025 7054221472825777825689019)
            ·
              refine ⟨10581332209238666738533529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7054221472825777825689019 10581332209238666738533529)
              ·
                refine ⟨7935999156929000053900147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10581332209238666738533529 7935999156929000053900147)
                ·
                  refine ⟨11903998735393500080850221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7935999156929000053900147 11903998735393500080850221)
                  ·
                    refine ⟨4463999525772562530318833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11903998735393500080850221 4463999525772562530318833)
                    ·
                      refine ⟨3347999644329421897739125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4463999525772562530318833 3347999644329421897739125)
                      ·
                        rfl

theorem cell23_6520206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_6520206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520206 prefixEnd_6520206 := by exact prefixLift 6520206
  have htrace : WordTrace (prefixWord ++ tailWord_6520206) baseStart_6520206 baseEnd_6520206 := by
    simpa [prefixWord, tailWord_6520206, baseEnd_6520206] using wordTrace_append hprefix tailTrace_6520206
  have hstable : (prefixWord ++ tailWord_6520206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520206).length < 2 ^ (prefixWord ++ tailWord_6520206).sum := by decide
  have hdescent : baseEnd_6520206 < baseStart_6520206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520211 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 8]
def baseStart_6520211 : Nat := 118140960795 + 6520211 * 2 ^ 59
def prefixEnd_6520211 : Nat := 4983230072969 + 3 ^ 40 * 6520211 * 2
def baseEnd_6520211 : Nat := 3348002211732694378176601

theorem tailTrace_6520211 : CollatzResearch.WordTrace tailWord_6520211 prefixEnd_6520211 3348002211732694378176601 := by
  unfold tailWord_6520211
  simp only [CollatzResearch.WordTrace]
  refine ⟨237811632181396585228600487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158541088120931056819066991 237811632181396585228600487)
  ·
    refine ⟨356717448272094877842900731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237811632181396585228600487 356717448272094877842900731)
    ·
      refine ⟨535076172408142316764351097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356717448272094877842900731 535076172408142316764351097)
      ·
        refine ⟨401307129306106737573263323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535076172408142316764351097 401307129306106737573263323)
        ·
          refine ⟨601960693959160106359894985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401307129306106737573263323 601960693959160106359894985)
          ·
            refine ⟨451470520469370079769921239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 601960693959160106359894985 451470520469370079769921239)
            ·
              refine ⟨677205780704055119654881859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451470520469370079769921239 677205780704055119654881859)
              ·
                refine ⟨1015808671056082679482322789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677205780704055119654881859 1015808671056082679482322789)
                ·
                  refine ⟨190464125823015502402935523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1015808671056082679482322789 190464125823015502402935523)
                  ·
                    refine ⟨285696188734523253604403285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 190464125823015502402935523 285696188734523253604403285)
                    ·
                      refine ⟨3348002211732694378176601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 285696188734523253604403285 3348002211732694378176601)
                      ·
                        rfl

theorem cell23_6520211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_6520211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520211 prefixEnd_6520211 := by exact prefixLift 6520211
  have htrace : WordTrace (prefixWord ++ tailWord_6520211) baseStart_6520211 baseEnd_6520211 := by
    simpa [prefixWord, tailWord_6520211, baseEnd_6520211] using wordTrace_append hprefix tailTrace_6520211
  have hstable : (prefixWord ++ tailWord_6520211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520211).length < 2 ^ (prefixWord ++ tailWord_6520211).sum := by decide
  have hdescent : baseEnd_6520211 < baseStart_6520211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520248 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 1, 2, 5]
def baseStart_6520248 : Nat := 118140960795 + 6520248 * 2 ^ 59
def prefixEnd_6520248 : Nat := 4983230072969 + 3 ^ 40 * 6520248 * 2
def baseEnd_6520248 : Nat := 3348021210516910733413931

theorem tailTrace_6520248 : CollatzResearch.WordTrace tailWord_6520248 prefixEnd_6520248 3348021210516910733413931 := by
  unfold tailWord_6520248
  simp only [CollatzResearch.WordTrace]
  refine ⟨118906490841131270273848699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158541987788175027031798265 118906490841131270273848699)
  ·
    refine ⟨178359736261696905410773049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118906490841131270273848699 178359736261696905410773049)
    ·
      refine ⟨133769802196272679058079787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178359736261696905410773049 133769802196272679058079787)
      ·
        refine ⟨200654703294409018587119681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133769802196272679058079787 200654703294409018587119681)
        ·
          refine ⟨150491027470806763940339761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200654703294409018587119681 150491027470806763940339761)
          ·
            refine ⟨112868270603105072955254821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150491027470806763940339761 112868270603105072955254821)
            ·
              refine ⟨21162800738082201179110279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112868270603105072955254821 21162800738082201179110279)
              ·
                refine ⟨31744201107123301768665419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21162800738082201179110279 31744201107123301768665419)
                ·
                  refine ⟨47616301660684952652998129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31744201107123301768665419 47616301660684952652998129)
                  ·
                    refine ⟨35712226245513714489748597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47616301660684952652998129 35712226245513714489748597)
                    ·
                      refine ⟨3348021210516910733413931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35712226245513714489748597 3348021210516910733413931)
                      ·
                        rfl

theorem cell23_6520248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_6520248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520248 prefixEnd_6520248 := by exact prefixLift 6520248
  have htrace : WordTrace (prefixWord ++ tailWord_6520248) baseStart_6520248 baseEnd_6520248 := by
    simpa [prefixWord, tailWord_6520248, baseEnd_6520248] using wordTrace_append hprefix tailTrace_6520248
  have hstable : (prefixWord ++ tailWord_6520248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520248).length < 2 ^ (prefixWord ++ tailWord_6520248).sum := by decide
  have hdescent : baseEnd_6520248 < baseStart_6520248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520252 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 2, 3, 3]
def baseStart_6520252 : Nat := 118140960795 + 6520252 * 2 ^ 59
def prefixEnd_6520252 : Nat := 4983230072969 + 3 ^ 40 * 6520252 * 2
def baseEnd_6520252 : Nat := 3348023264439528717763913

theorem tailTrace_6520252 : CollatzResearch.WordTrace tailWord_6520252 prefixEnd_6520252 3348023264439528717763913 := by
  unfold tailWord_6520252
  simp only [CollatzResearch.WordTrace]
  refine ⟨118906563787124024615421505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158542085049498699487228673 118906563787124024615421505)
  ·
    refine ⟨89179922840343018461566129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118906563787124024615421505 89179922840343018461566129)
    ·
      refine ⟨66884942130257263846174597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89179922840343018461566129 66884942130257263846174597)
      ·
        refine ⟨12540926649423236971157737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66884942130257263846174597 12540926649423236971157737)
        ·
          refine ⟨9405694987067427728368303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12540926649423236971157737 9405694987067427728368303)
          ·
            refine ⟨14108542480601141592552455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9405694987067427728368303 14108542480601141592552455)
            ·
              refine ⟨21162813720901712388828683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14108542480601141592552455 21162813720901712388828683)
              ·
                refine ⟨31744220581352568583243025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21162813720901712388828683 31744220581352568583243025)
                ·
                  refine ⟨23808165436014426437432269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31744220581352568583243025 23808165436014426437432269)
                  ·
                    refine ⟨8928062038505409914037101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23808165436014426437432269 8928062038505409914037101)
                    ·
                      refine ⟨3348023264439528717763913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8928062038505409914037101 3348023264439528717763913)
                      ·
                        rfl

theorem cell23_6520252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_6520252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520252 prefixEnd_6520252 := by exact prefixLift 6520252
  have htrace : WordTrace (prefixWord ++ tailWord_6520252) baseStart_6520252 baseEnd_6520252 := by
    simpa [prefixWord, tailWord_6520252, baseEnd_6520252] using wordTrace_append hprefix tailTrace_6520252
  have hstable : (prefixWord ++ tailWord_6520252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520252).length < 2 ^ (prefixWord ++ tailWord_6520252).sum := by decide
  have hdescent : baseEnd_6520252 < baseStart_6520252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520302 : List Nat := [4, 1, 2, 1, 2, 1, 4, 1, 3, 4]
def baseStart_6520302 : Nat := 118140960795 + 6520302 * 2 ^ 59
def prefixEnd_6520302 : Nat := 4983230072969 + 3 ^ 40 * 6520302 * 2
def baseEnd_6520302 : Nat := 1116016312824084507379561

theorem tailTrace_6520302 : CollatzResearch.WordTrace tailWord_6520302 prefixEnd_6520302 1116016312824084507379561 := by
  unfold tailWord_6520302
  simp only [CollatzResearch.WordTrace]
  refine ⟨29726868903008363471270395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158543300816044605180108773 29726868903008363471270395)
  ·
    refine ⟨44590303354512545206905593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29726868903008363471270395 44590303354512545206905593)
    ·
      refine ⟨33442727515884408905179195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44590303354512545206905593 33442727515884408905179195)
      ·
        refine ⟨50164091273826613357768793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33442727515884408905179195 50164091273826613357768793)
        ·
          refine ⟨37623068455369960018326595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50164091273826613357768793 37623068455369960018326595)
          ·
            refine ⟨56434602683054940027489893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37623068455369960018326595 56434602683054940027489893)
            ·
              refine ⟨10581488003072801255154355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56434602683054940027489893 10581488003072801255154355)
              ·
                refine ⟨15872232004609201882731533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10581488003072801255154355 15872232004609201882731533)
                ·
                  refine ⟨5952087001728450706024325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15872232004609201882731533 5952087001728450706024325)
                  ·
                    refine ⟨1116016312824084507379561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5952087001728450706024325 1116016312824084507379561)
                    ·
                      rfl

theorem cell23_6520302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_6520302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520302 prefixEnd_6520302 := by exact prefixLift 6520302
  have htrace : WordTrace (prefixWord ++ tailWord_6520302) baseStart_6520302 baseEnd_6520302 := by
    simpa [prefixWord, tailWord_6520302, baseEnd_6520302] using wordTrace_append hprefix tailTrace_6520302
  have hstable : (prefixWord ++ tailWord_6520302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520302).length < 2 ^ (prefixWord ++ tailWord_6520302).sum := by decide
  have hdescent : baseEnd_6520302 < baseStart_6520302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520309 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_6520309 : Nat := 118140960795 + 6520309 * 2 ^ 59
def prefixEnd_6520309 : Nat := 4983230072969 + 3 ^ 40 * 6520309 * 2
def baseEnd_6520309 : Nat := 3348052532836834994751151

theorem tailTrace_6520309 : CollatzResearch.WordTrace tailWord_6520309 prefixEnd_6520309 3348052532836834994751151 := by
  unfold tailWord_6520309
  simp only [CollatzResearch.WordTrace]
  refine ⟨237815206535041547965667981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158543471023361031977111987 237815206535041547965667981)
  ·
    refine ⟨89180702450640580487125493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237815206535041547965667981 89180702450640580487125493)
    ·
      refine ⟨8360690854747554420668015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89180702450640580487125493 8360690854747554420668015)
      ·
        refine ⟨12541036282121331631002023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8360690854747554420668015 12541036282121331631002023)
        ·
          refine ⟨18811554423181997446503035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12541036282121331631002023 18811554423181997446503035)
          ·
            refine ⟨28217331634772996169754553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18811554423181997446503035 28217331634772996169754553)
            ·
              refine ⟨21162998726079747127315915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28217331634772996169754553 21162998726079747127315915)
              ·
                refine ⟨31744498089119620690973873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21162998726079747127315915 31744498089119620690973873)
                ·
                  refine ⟨23808373566839715518230405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31744498089119620690973873 23808373566839715518230405)
                  ·
                    refine ⟨4464070043782446659668201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23808373566839715518230405 4464070043782446659668201)
                    ·
                      refine ⟨3348052532836834994751151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4464070043782446659668201 3348052532836834994751151)
                      ·
                        rfl

theorem cell23_6520309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_6520309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520309 prefixEnd_6520309 := by exact prefixLift 6520309
  have htrace : WordTrace (prefixWord ++ tailWord_6520309) baseStart_6520309 baseEnd_6520309 := by
    simpa [prefixWord, tailWord_6520309, baseEnd_6520309] using wordTrace_append hprefix tailTrace_6520309
  have hstable : (prefixWord ++ tailWord_6520309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520309).length < 2 ^ (prefixWord ++ tailWord_6520309).sum := by decide
  have hdescent : baseEnd_6520309 < baseStart_6520309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520335 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 5, 5, 2]
def baseStart_6520335 : Nat := 118140960795 + 6520335 * 2 ^ 59
def prefixEnd_6520335 : Nat := 4983230072969 + 3 ^ 40 * 6520335 * 2
def baseEnd_6520335 : Nat := 3348065883333851893026031

theorem tailTrace_6520335 : CollatzResearch.WordTrace tailWord_6520335 prefixEnd_6520335 3348065883333851893026031 := by
  unfold tailWord_6520335
  simp only [CollatzResearch.WordTrace]
  refine ⟨237816154832947354406114459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158544103221964902937409639 237816154832947354406114459)
  ·
    refine ⟨356724232249421031609171689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237816154832947354406114459 356724232249421031609171689)
    ·
      refine ⟨267543174187065773706878767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356724232249421031609171689 267543174187065773706878767)
      ·
        refine ⟨401314761280598660560318151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267543174187065773706878767 401314761280598660560318151)
        ·
          refine ⟨601972141920897990840477227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401314761280598660560318151 601972141920897990840477227)
          ·
            refine ⟨902958212881346986260715841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601972141920897990840477227 902958212881346986260715841)
            ·
              refine ⟨677218659661010239695536881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902958212881346986260715841 677218659661010239695536881)
              ·
                refine ⟨507913994745757679771652661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677218659661010239695536881 507913994745757679771652661)
                ·
                  refine ⟨47616937007414782478592437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 507913994745757679771652661 47616937007414782478592437)
                  ·
                    refine ⟨4464087844445135857368041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47616937007414782478592437 4464087844445135857368041)
                    ·
                      refine ⟨3348065883333851893026031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4464087844445135857368041 3348065883333851893026031)
                      ·
                        rfl

theorem cell23_6520335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 5, 2].length) (baseStart_6520335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520335 prefixEnd_6520335 := by exact prefixLift 6520335
  have htrace : WordTrace (prefixWord ++ tailWord_6520335) baseStart_6520335 baseEnd_6520335 := by
    simpa [prefixWord, tailWord_6520335, baseEnd_6520335] using wordTrace_append hprefix tailTrace_6520335
  have hstable : (prefixWord ++ tailWord_6520335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520335).length < 2 ^ (prefixWord ++ tailWord_6520335).sum := by decide
  have hdescent : baseEnd_6520335 < baseStart_6520335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520402 : List Nat := [3, 2, 2, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_6520402 : Nat := 118140960795 + 6520402 * 2 ^ 59
def prefixEnd_6520402 : Nat := 4983230072969 + 3 ^ 40 * 6520402 * 2
def baseEnd_6520402 : Nat := 3348100286537703130888223

theorem tailTrace_6520402 : CollatzResearch.WordTrace tailWord_6520402 prefixEnd_6520402 3348100286537703130888223 := by
  unfold tailWord_6520402
  simp only [CollatzResearch.WordTrace]
  refine ⟨59454649630926156212200865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158545732349136416565868973 59454649630926156212200865)
  ·
    refine ⟨44590987223194617159150649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59454649630926156212200865 44590987223194617159150649)
    ·
      refine ⟨33443240417395962869362987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44590987223194617159150649 33443240417395962869362987)
      ·
        refine ⟨50164860626093944304044481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33443240417395962869362987 50164860626093944304044481)
        ·
          refine ⟨37623645469570458228033361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50164860626093944304044481 37623645469570458228033361)
          ·
            refine ⟨28217734102177843671025021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37623645469570458228033361 28217734102177843671025021)
            ·
              refine ⟨10581650288316691376634383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28217734102177843671025021 10581650288316691376634383)
              ·
                refine ⟨15872475432475037064951575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10581650288316691376634383 15872475432475037064951575)
                ·
                  refine ⟨23808713148712555597427363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15872475432475037064951575 23808713148712555597427363)
                  ·
                    refine ⟨35713069723068833396141045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23808713148712555597427363 35713069723068833396141045)
                    ·
                      refine ⟨3348100286537703130888223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35713069723068833396141045 3348100286537703130888223)
                      ·
                        rfl

theorem cell23_6520402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_6520402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520402 prefixEnd_6520402 := by exact prefixLift 6520402
  have htrace : WordTrace (prefixWord ++ tailWord_6520402) baseStart_6520402 baseEnd_6520402 := by
    simpa [prefixWord, tailWord_6520402, baseEnd_6520402] using wordTrace_append hprefix tailTrace_6520402
  have hstable : (prefixWord ++ tailWord_6520402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520402).length < 2 ^ (prefixWord ++ tailWord_6520402).sum := by decide
  have hdescent : baseEnd_6520402 < baseStart_6520402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520429 : List Nat := [1, 5, 1, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_6520429 : Nat := 118140960795 + 6520429 * 2 ^ 59
def prefixEnd_6520429 : Nat := 4983230072969 + 3 ^ 40 * 6520429 * 2
def baseEnd_6520429 : Nat := 3348114150515374525250599

theorem tailTrace_6520429 : CollatzResearch.WordTrace tailWord_6520429 prefixEnd_6520429 3348114150515374525250599 := by
  unfold tailWord_6520429
  simp only [CollatzResearch.WordTrace]
  refine ⟨237819583294606808460036341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158546388863071205640024227 237819583294606808460036341)
  ·
    refine ⟨22295585933869388293128407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237819583294606808460036341 22295585933869388293128407)
    ·
      refine ⟨33443378900804082439692611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22295585933869388293128407 33443378900804082439692611)
      ·
        refine ⟨50165068351206123659538917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33443378900804082439692611 50165068351206123659538917)
        ·
          refine ⟨9405950315851148186163547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50165068351206123659538917 9405950315851148186163547)
          ·
            refine ⟨14108925473776722279245321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9405950315851148186163547 14108925473776722279245321)
            ·
              refine ⟨10581694105332541709433991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14108925473776722279245321 10581694105332541709433991)
              ·
                refine ⟨15872541157998812564150987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10581694105332541709433991 15872541157998812564150987)
                ·
                  refine ⟨23808811736998218846226481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15872541157998812564150987 23808811736998218846226481)
                  ·
                    refine ⟨17856608802748664134669861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23808811736998218846226481 17856608802748664134669861)
                    ·
                      refine ⟨3348114150515374525250599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17856608802748664134669861 3348114150515374525250599)
                      ·
                        rfl

theorem cell23_6520429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_6520429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520429 prefixEnd_6520429 := by exact prefixLift 6520429
  have htrace : WordTrace (prefixWord ++ tailWord_6520429) baseStart_6520429 baseEnd_6520429 := by
    simpa [prefixWord, tailWord_6520429, baseEnd_6520429] using wordTrace_append hprefix tailTrace_6520429
  have hstable : (prefixWord ++ tailWord_6520429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520429).length < 2 ^ (prefixWord ++ tailWord_6520429).sum := by decide
  have hdescent : baseEnd_6520429 < baseStart_6520429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520432 : List Nat := [2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 3]
def baseStart_6520432 : Nat := 118140960795 + 6520432 * 2 ^ 59
def prefixEnd_6520432 : Nat := 4983230072969 + 3 ^ 40 * 6520432 * 2
def baseEnd_6520432 : Nat := 3348115690957338013513085

theorem tailTrace_6520432 : CollatzResearch.WordTrace tailWord_6520432 prefixEnd_6520432 3348115690957338013513085 := by
  unfold tailWord_6520432
  simp only [CollatzResearch.WordTrace]
  refine ⟨118909846356797969986197775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158546461809063959981597033 118909846356797969986197775)
  ·
    refine ⟨178364769535196954979296663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118909846356797969986197775 178364769535196954979296663)
    ·
      refine ⟨267547154302795432468944995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178364769535196954979296663 267547154302795432468944995)
      ·
        refine ⟨401320731454193148703417493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267547154302795432468944995 401320731454193148703417493)
        ·
          refine ⟨18811909286915303845472695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 401320731454193148703417493 18811909286915303845472695)
          ·
            refine ⟨28217863930372955768209043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18811909286915303845472695 28217863930372955768209043)
            ·
              refine ⟨42326795895559433652313565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28217863930372955768209043 42326795895559433652313565)
              ·
                refine ⟨15872548460834787619617587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42326795895559433652313565 15872548460834787619617587)
                ·
                  refine ⟨23808822691252181429426381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15872548460834787619617587 23808822691252181429426381)
                  ·
                    refine ⟨8928308509219568036034893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23808822691252181429426381 8928308509219568036034893)
                    ·
                      refine ⟨3348115690957338013513085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8928308509219568036034893 3348115690957338013513085)
                      ·
                        rfl

theorem cell23_6520432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 3].length) (baseStart_6520432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520432 prefixEnd_6520432 := by exact prefixLift 6520432
  have htrace : WordTrace (prefixWord ++ tailWord_6520432) baseStart_6520432 baseEnd_6520432 := by
    simpa [prefixWord, tailWord_6520432, baseEnd_6520432] using wordTrace_append hprefix tailTrace_6520432
  have hstable : (prefixWord ++ tailWord_6520432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520432).length < 2 ^ (prefixWord ++ tailWord_6520432).sum := by decide
  have hdescent : baseEnd_6520432 < baseStart_6520432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520459 : List Nat := [1, 1, 1, 1, 4, 1, 5, 3, 1, 3, 2]
def baseStart_6520459 : Nat := 118140960795 + 6520459 * 2 ^ 59
def prefixEnd_6520459 : Nat := 4983230072969 + 3 ^ 40 * 6520459 * 2
def baseEnd_6520459 : Nat := 3348129554935009407875461

theorem tailTrace_6520459 : CollatzResearch.WordTrace tailWord_6520459 prefixEnd_6520459 3348129554935009407875461 := by
  unfold tailWord_6520459
  simp only [CollatzResearch.WordTrace]
  refine ⟨237820677484498123583628431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158547118322998749055752287 237820677484498123583628431)
  ·
    refine ⟨356731016226747185375442647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237820677484498123583628431 356731016226747185375442647)
    ·
      refine ⟨535096524340120778063163971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356731016226747185375442647 535096524340120778063163971)
      ·
        refine ⟨802644786510181167094745957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535096524340120778063163971 802644786510181167094745957)
        ·
          refine ⟨150495897470658968830264867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 802644786510181167094745957 150495897470658968830264867)
          ·
            refine ⟨225743846205988453245397301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150495897470658968830264867 225743846205988453245397301)
            ·
              refine ⟨21163485581811417491755997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 225743846205988453245397301 21163485581811417491755997)
              ·
                refine ⟨7936307093179281559408499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21163485581811417491755997 7936307093179281559408499)
                ·
                  refine ⟨11904460639768922339112749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7936307093179281559408499 11904460639768922339112749)
                  ·
                    refine ⟨4464172739913345877167281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11904460639768922339112749 4464172739913345877167281)
                    ·
                      refine ⟨3348129554935009407875461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4464172739913345877167281 3348129554935009407875461)
                      ·
                        rfl

theorem cell23_6520459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 3, 2].length) (baseStart_6520459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520459 prefixEnd_6520459 := by exact prefixLift 6520459
  have htrace : WordTrace (prefixWord ++ tailWord_6520459) baseStart_6520459 baseEnd_6520459 := by
    simpa [prefixWord, tailWord_6520459, baseEnd_6520459] using wordTrace_append hprefix tailTrace_6520459
  have hstable : (prefixWord ++ tailWord_6520459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520459).length < 2 ^ (prefixWord ++ tailWord_6520459).sum := by decide
  have hdescent : baseEnd_6520459 < baseStart_6520459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520466 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_6520466 : Nat := 118140960795 + 6520466 * 2 ^ 59
def prefixEnd_6520466 : Nat := 4983230072969 + 3 ^ 40 * 6520466 * 2
def baseEnd_6520466 : Nat := 3348133149299590880487929

theorem tailTrace_6520466 : CollatzResearch.WordTrace tailWord_6520466 prefixEnd_6520466 3348133149299590880487929 := by
  unfold tailWord_6520466
  simp only [CollatzResearch.WordTrace]
  refine ⟨59455233198868190944783313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158547288530315175852755501 59455233198868190944783313)
  ·
    refine ⟨44591424899151143208587485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59455233198868190944783313 44591424899151143208587485)
    ·
      refine ⟨16721784337181678703220307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44591424899151143208587485 16721784337181678703220307)
      ·
        refine ⟨25082676505772518054830461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16721784337181678703220307 25082676505772518054830461)
        ·
          refine ⟨9406003689664694270561423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25082676505772518054830461 9406003689664694270561423)
          ·
            refine ⟨14109005534497041405842135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9406003689664694270561423 14109005534497041405842135)
            ·
              refine ⟨21163508301745562108763203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14109005534497041405842135 21163508301745562108763203)
              ·
                refine ⟨31745262452618343163144805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21163508301745562108763203 31745262452618343163144805)
                ·
                  refine ⟨5952236709865939343089651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31745262452618343163144805 5952236709865939343089651)
                  ·
                    refine ⟨8928355064798909014634477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5952236709865939343089651 8928355064798909014634477)
                    ·
                      refine ⟨3348133149299590880487929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8928355064798909014634477 3348133149299590880487929)
                      ·
                        rfl

theorem cell23_6520466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_6520466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520466 prefixEnd_6520466 := by exact prefixLift 6520466
  have htrace : WordTrace (prefixWord ++ tailWord_6520466) baseStart_6520466 baseEnd_6520466 := by
    simpa [prefixWord, tailWord_6520466, baseEnd_6520466] using wordTrace_append hprefix tailTrace_6520466
  have hstable : (prefixWord ++ tailWord_6520466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520466).length < 2 ^ (prefixWord ++ tailWord_6520466).sum := by decide
  have hdescent : baseEnd_6520466 < baseStart_6520466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520495 : List Nat := [1, 1, 2, 1, 2, 4, 1, 4, 7]
def baseStart_6520495 : Nat := 118140960795 + 6520495 * 2 ^ 59
def prefixEnd_6520495 : Nat := 4983230072969 + 3 ^ 40 * 6520495 * 2
def baseEnd_6520495 : Nat := 372016448915396807447255

theorem tailTrace_6520495 : CollatzResearch.WordTrace tailWord_6520495 prefixEnd_6520495 372016448915396807447255 := by
  unfold tailWord_6520495
  simp only [CollatzResearch.WordTrace]
  refine ⟨237821990512367701731938939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158547993674911801154625959 237821990512367701731938939)
  ·
    refine ⟨356732985768551552597908409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237821990512367701731938939 356732985768551552597908409)
    ·
      refine ⟨267549739326413664448431307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356732985768551552597908409 267549739326413664448431307)
      ·
        refine ⟨401324608989620496672646961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267549739326413664448431307 401324608989620496672646961)
        ·
          refine ⟨300993456742215372504485221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401324608989620496672646961 300993456742215372504485221)
          ·
            refine ⟨56436273139165382344590979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300993456742215372504485221 56436273139165382344590979)
            ·
              refine ⟨84654409708748073516886469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56436273139165382344590979 84654409708748073516886469)
              ·
                refine ⟨15872701820390263784416213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84654409708748073516886469 15872701820390263784416213)
                ·
                  refine ⟨372016448915396807447255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15872701820390263784416213 372016448915396807447255)
                  ·
                    rfl

theorem cell23_6520495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 7].length) (baseStart_6520495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520495 prefixEnd_6520495 := by exact prefixLift 6520495
  have htrace : WordTrace (prefixWord ++ tailWord_6520495) baseStart_6520495 baseEnd_6520495 := by
    simpa [prefixWord, tailWord_6520495, baseEnd_6520495] using wordTrace_append hprefix tailTrace_6520495
  have hstable : (prefixWord ++ tailWord_6520495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520495).length < 2 ^ (prefixWord ++ tailWord_6520495).sum := by decide
  have hdescent : baseEnd_6520495 < baseStart_6520495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520534 : List Nat := [5, 2, 1, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_6520534 : Nat := 118140960795 + 6520534 * 2 ^ 59
def prefixEnd_6520534 : Nat := 4983230072969 + 3 ^ 40 * 6520534 * 2
def baseEnd_6520534 : Nat := 3348168065984096614437617

theorem tailTrace_6520534 : CollatzResearch.WordTrace tailWord_6520534 prefixEnd_6520534 3348168065984096614437617 := by
  unfold tailWord_6520534
  simp only [CollatzResearch.WordTrace]
  refine ⟨14863963309951650712038041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158548941972817607595072437 14863963309951650712038041)
  ·
    refine ⟨11147972482463738034028531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14863963309951650712038041 11147972482463738034028531)
    ·
      refine ⟨16721958723695607051042797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11147972482463738034028531 16721958723695607051042797)
      ·
        refine ⟨6270734521385852644141049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16721958723695607051042797 6270734521385852644141049)
        ·
          refine ⟨4703050891039389483105787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6270734521385852644141049 4703050891039389483105787)
          ·
            refine ⟨7054576336559084224658681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4703050891039389483105787 7054576336559084224658681)
            ·
              refine ⟨5290932252419313168494011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7054576336559084224658681 5290932252419313168494011)
              ·
                refine ⟨7936398378628969752741017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5290932252419313168494011 7936398378628969752741017)
                ·
                  refine ⟨5952298783971727314555763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7936398378628969752741017 5952298783971727314555763)
                  ·
                    refine ⟨8928448175957590971833645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5952298783971727314555763 8928448175957590971833645)
                    ·
                      refine ⟨3348168065984096614437617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8928448175957590971833645 3348168065984096614437617)
                      ·
                        rfl

theorem cell23_6520534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_6520534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520534 prefixEnd_6520534 := by exact prefixLift 6520534
  have htrace : WordTrace (prefixWord ++ tailWord_6520534) baseStart_6520534 baseEnd_6520534 := by
    simpa [prefixWord, tailWord_6520534, baseEnd_6520534] using wordTrace_append hprefix tailTrace_6520534
  have hstable : (prefixWord ++ tailWord_6520534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520534).length < 2 ^ (prefixWord ++ tailWord_6520534).sum := by decide
  have hdescent : baseEnd_6520534 < baseStart_6520534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520540 : List Nat := [2, 2, 5, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_6520540 : Nat := 118140960795 + 6520540 * 2 ^ 59
def prefixEnd_6520540 : Nat := 4983230072969 + 3 ^ 40 * 6520540 * 2
def baseEnd_6520540 : Nat := 3348171146868023590962589

theorem tailTrace_6520540 : CollatzResearch.WordTrace tailWord_6520540 prefixEnd_6520540 3348171146868023590962589 := by
  unfold tailWord_6520540
  simp only [CollatzResearch.WordTrace]
  refine ⟨118911815898602337208663537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158549087864803116278218049 118911815898602337208663537)
  ·
    refine ⟨89183861923951752906497653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118911815898602337208663537 89183861923951752906497653)
    ·
      refine ⟨8360987055370476834984155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89183861923951752906497653 8360987055370476834984155)
      ·
        refine ⟨12541480583055715252476233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8360987055370476834984155 12541480583055715252476233)
        ·
          refine ⟨9406110437291786439357175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12541480583055715252476233 9406110437291786439357175)
          ·
            refine ⟨14109165655937679659035763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9406110437291786439357175 14109165655937679659035763)
            ·
              refine ⟨21163748483906519488553645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14109165655937679659035763 21163748483906519488553645)
              ·
                refine ⟨7936405681464944808207617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21163748483906519488553645 7936405681464944808207617)
                ·
                  refine ⟨5952304261098708606155713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7936405681464944808207617 5952304261098708606155713)
                  ·
                    refine ⟨4464228195824031454616785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5952304261098708606155713 4464228195824031454616785)
                    ·
                      refine ⟨3348171146868023590962589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4464228195824031454616785 3348171146868023590962589)
                      ·
                        rfl

theorem cell23_6520540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_6520540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520540 prefixEnd_6520540 := by exact prefixLift 6520540
  have htrace : WordTrace (prefixWord ++ tailWord_6520540) baseStart_6520540 baseEnd_6520540 := by
    simpa [prefixWord, tailWord_6520540, baseEnd_6520540] using wordTrace_append hprefix tailTrace_6520540
  have hstable : (prefixWord ++ tailWord_6520540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520540).length < 2 ^ (prefixWord ++ tailWord_6520540).sum := by decide
  have hdescent : baseEnd_6520540 < baseStart_6520540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520555 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 2, 8]
def baseStart_6520555 : Nat := 118140960795 + 6520555 * 2 ^ 59
def prefixEnd_6520555 : Nat := 4983230072969 + 3 ^ 40 * 6520555 * 2
def baseEnd_6520555 : Nat := 1116059616359280344091673

theorem tailTrace_6520555 : CollatzResearch.WordTrace tailWord_6520555 prefixEnd_6520555 1116059616359280344091673 := by
  unfold tailWord_6520555
  simp only [CollatzResearch.WordTrace]
  refine ⟨237824178892150331979123119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158549452594766887986082079 237824178892150331979123119)
  ·
    refine ⟨356736268338225497968684679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237824178892150331979123119 356736268338225497968684679)
    ·
      refine ⟨535104402507338246953027019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356736268338225497968684679 535104402507338246953027019)
      ·
        refine ⟨802656603761007370429540529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535104402507338246953027019 802656603761007370429540529)
        ·
          refine ⟨601992452820755527822155397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 802656603761007370429540529 601992452820755527822155397)
          ·
            refine ⟨112873584903891661466654137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 601992452820755527822155397 112873584903891661466654137)
            ·
              refine ⟨84655188677918746099990603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112873584903891661466654137 84655188677918746099990603)
              ·
                refine ⟨126982783016878119149985905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84655188677918746099990603 126982783016878119149985905)
                ·
                  refine ⟨95237087262658589362489429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126982783016878119149985905 95237087262658589362489429)
                  ·
                    refine ⟨1116059616359280344091673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95237087262658589362489429 1116059616359280344091673)
                    ·
                      rfl

theorem cell23_6520555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 8].length) (baseStart_6520555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520555 prefixEnd_6520555 := by exact prefixLift 6520555
  have htrace : WordTrace (prefixWord ++ tailWord_6520555) baseStart_6520555 baseEnd_6520555 := by
    simpa [prefixWord, tailWord_6520555, baseEnd_6520555] using wordTrace_append hprefix tailTrace_6520555
  have hstable : (prefixWord ++ tailWord_6520555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520555).length < 2 ^ (prefixWord ++ tailWord_6520555).sum := by decide
  have hdescent : baseEnd_6520555 < baseStart_6520555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520616 : List Nat := [2, 1, 5, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_6520616 : Nat := 118140960795 + 6520616 * 2 ^ 59
def prefixEnd_6520616 : Nat := 4983230072969 + 3 ^ 40 * 6520616 * 2
def baseEnd_6520616 : Nat := 3348210171397765293612239

theorem tailTrace_6520616 : CollatzResearch.WordTrace tailWord_6520616 prefixEnd_6520616 3348210171397765293612239 := by
  unfold tailWord_6520616
  simp only [CollatzResearch.WordTrace]
  refine ⟨118913201872464669698546851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158550935829952892931395801 118913201872464669698546851)
  ·
    refine ⟨178369802808697004547820277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118913201872464669698546851 178369802808697004547820277)
    ·
      refine ⟨16722169013315344176358151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178369802808697004547820277 16722169013315344176358151)
      ·
        refine ⟨25083253519973016264537227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16722169013315344176358151 25083253519973016264537227)
        ·
          refine ⟨37624880279959524396805841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25083253519973016264537227 37624880279959524396805841)
          ·
            refine ⟨28218660209969643297604381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37624880279959524396805841 28218660209969643297604381)
            ·
              refine ⟨10581997578738616236601643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28218660209969643297604381 10581997578738616236601643)
              ·
                refine ⟨15872996368107924354902465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10581997578738616236601643 15872996368107924354902465)
                ·
                  refine ⟨11904747276080943266176849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15872996368107924354902465 11904747276080943266176849)
                  ·
                    refine ⟨8928560457060707449632637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11904747276080943266176849 8928560457060707449632637)
                    ·
                      refine ⟨3348210171397765293612239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8928560457060707449632637 3348210171397765293612239)
                      ·
                        rfl

theorem cell23_6520616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_6520616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520616 prefixEnd_6520616 := by exact prefixLift 6520616
  have htrace : WordTrace (prefixWord ++ tailWord_6520616) baseStart_6520616 baseEnd_6520616 := by
    simpa [prefixWord, tailWord_6520616, baseEnd_6520616] using wordTrace_append hprefix tailTrace_6520616
  have hstable : (prefixWord ++ tailWord_6520616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520616).length < 2 ^ (prefixWord ++ tailWord_6520616).sum := by decide
  have hdescent : baseEnd_6520616 < baseStart_6520616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520653 : List Nat := [1, 6, 1, 2, 1, 2, 3, 1, 6]
def baseStart_6520653 : Nat := 118140960795 + 6520653 * 2 ^ 59
def prefixEnd_6520653 : Nat := 4983230072969 + 3 ^ 40 * 6520653 * 2
def baseEnd_6520653 : Nat := 372025463353553516538841

theorem tailTrace_6520653 : CollatzResearch.WordTrace tailWord_6520653 prefixEnd_6520653 372025463353553516538841 := by
  unfold tailWord_6520653
  simp only [CollatzResearch.WordTrace]
  refine ⟨237827753245795294716190613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158551835497196863144127075 237827753245795294716190613)
  ·
    refine ⟨11148175933396654439821435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 237827753245795294716190613 11148175933396654439821435)
    ·
      refine ⟨16722263900094981659732153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11148175933396654439821435 16722263900094981659732153)
      ·
        refine ⟨12541697925071236244799115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16722263900094981659732153 12541697925071236244799115)
        ·
          refine ⟨18812546887606854367198673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12541697925071236244799115 18812546887606854367198673)
          ·
            refine ⟨14109410165705140775399005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18812546887606854367198673 14109410165705140775399005)
            ·
              refine ⟨5291028812139427790774627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14109410165705140775399005 5291028812139427790774627)
              ·
                refine ⟨7936543218209141686161941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5291028812139427790774627 7936543218209141686161941)
                ·
                  refine ⟨372025463353553516538841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7936543218209141686161941 372025463353553516538841)
                  ·
                    rfl

theorem cell23_6520653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_6520653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520653 prefixEnd_6520653 := by exact prefixLift 6520653
  have htrace : WordTrace (prefixWord ++ tailWord_6520653) baseStart_6520653 baseEnd_6520653 := by
    simpa [prefixWord, tailWord_6520653, baseEnd_6520653] using wordTrace_append hprefix tailTrace_6520653
  have hstable : (prefixWord ++ tailWord_6520653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520653).length < 2 ^ (prefixWord ++ tailWord_6520653).sum := by decide
  have hdescent : baseEnd_6520653 < baseStart_6520653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520679 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 6, 4]
def baseStart_6520679 : Nat := 118140960795 + 6520679 * 2 ^ 59
def prefixEnd_6520679 : Nat := 4983230072969 + 3 ^ 40 * 6520679 * 2
def baseEnd_6520679 : Nat := 1116080840226332849041483

theorem tailTrace_6520679 : CollatzResearch.WordTrace tailWord_6520679 prefixEnd_6520679 1116080840226332849041483 := by
  unfold tailWord_6520679
  simp only [CollatzResearch.WordTrace]
  refine ⟨237828701543701101156637091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158552467695800734104424727 237828701543701101156637091)
  ·
    refine ⟨356743052315551651734955637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237828701543701101156637091 356743052315551651734955637)
    ·
      refine ⟨33444661154582967350152091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 356743052315551651734955637 33444661154582967350152091)
      ·
        refine ⟨50166991731874451025228137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33444661154582967350152091 50166991731874451025228137)
        ·
          refine ⟨37625243798905838268921103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50166991731874451025228137 37625243798905838268921103)
          ·
            refine ⟨56437865698358757403381655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37625243798905838268921103 56437865698358757403381655)
            ·
              refine ⟨84656798547538136105072483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56437865698358757403381655 84656798547538136105072483)
              ·
                refine ⟨126985197821307204157608725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84656798547538136105072483 126985197821307204157608725)
                ·
                  refine ⟨5952431147873775194887909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126985197821307204157608725 5952431147873775194887909)
                  ·
                    refine ⟨1116080840226332849041483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5952431147873775194887909 1116080840226332849041483)
                    ·
                      rfl

theorem cell23_6520679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_6520679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520679 prefixEnd_6520679 := by exact prefixLift 6520679
  have htrace : WordTrace (prefixWord ++ tailWord_6520679) baseStart_6520679 baseEnd_6520679 := by
    simpa [prefixWord, tailWord_6520679, baseEnd_6520679] using wordTrace_append hprefix tailTrace_6520679
  have hstable : (prefixWord ++ tailWord_6520679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520679).length < 2 ^ (prefixWord ++ tailWord_6520679).sum := by decide
  have hdescent : baseEnd_6520679 < baseStart_6520679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520689 : List Nat := [1, 2, 2, 2, 1, 3, 4, 1, 1, 1, 5]
def baseStart_6520689 : Nat := 118140960795 + 6520689 * 2 ^ 59
def prefixEnd_6520689 : Nat := 4983230072969 + 3 ^ 40 * 6520689 * 2
def baseEnd_6520689 : Nat := 3348247655485543507999403

theorem tailTrace_6520689 : CollatzResearch.WordTrace tailWord_6520689 prefixEnd_6520689 3348247655485543507999403 := by
  unfold tailWord_6520689
  simp only [CollatzResearch.WordTrace]
  refine ⟨237829066273664872864501121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158552710849109915243000747 237829066273664872864501121)
  ·
    refine ⟨178371799705248654648375841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237829066273664872864501121 178371799705248654648375841)
    ·
      refine ⟨133778849778936490986281881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178371799705248654648375841 133778849778936490986281881)
      ·
        refine ⟨100334137334202368239711411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133778849778936490986281881 100334137334202368239711411)
        ·
          refine ⟨150501206001303552359567117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100334137334202368239711411 150501206001303552359567117)
          ·
            refine ⟨56437952250488832134837669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150501206001303552359567117 56437952250488832134837669)
            ·
              refine ⟨10582116046966656025282063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56437952250488832134837669 10582116046966656025282063)
              ·
                refine ⟨15873174070449984037923095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10582116046966656025282063 15873174070449984037923095)
                ·
                  refine ⟨23809761105674976056884643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15873174070449984037923095 23809761105674976056884643)
                  ·
                    refine ⟨35714641658512464085326965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23809761105674976056884643 35714641658512464085326965)
                    ·
                      refine ⟨3348247655485543507999403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35714641658512464085326965 3348247655485543507999403)
                      ·
                        rfl

theorem cell23_6520689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_6520689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520689 prefixEnd_6520689 := by exact prefixLift 6520689
  have htrace : WordTrace (prefixWord ++ tailWord_6520689) baseStart_6520689 baseEnd_6520689 := by
    simpa [prefixWord, tailWord_6520689, baseEnd_6520689] using wordTrace_append hprefix tailTrace_6520689
  have hstable : (prefixWord ++ tailWord_6520689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520689).length < 2 ^ (prefixWord ++ tailWord_6520689).sum := by decide
  have hdescent : baseEnd_6520689 < baseStart_6520689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520752 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 5, 8]
def baseStart_6520752 : Nat := 118140960795 + 6520752 * 2 ^ 59
def prefixEnd_6520752 : Nat := 4983230072969 + 3 ^ 40 * 6520752 * 2
def baseEnd_6520752 : Nat := 1116093334922258920503871

theorem tailTrace_6520752 : CollatzResearch.WordTrace tailWord_6520752 prefixEnd_6520752 1116093334922258920503871 := by
  unfold tailWord_6520752
  simp only [CollatzResearch.WordTrace]
  refine ⟨118915682036218317312022255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158554242714957756416029673 118915682036218317312022255)
  ·
    refine ⟨178373523054327475968033383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118915682036218317312022255 178373523054327475968033383)
    ·
      refine ⟨267560284581491213952050075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178373523054327475968033383 267560284581491213952050075)
      ·
        refine ⟨401340426872236820928075113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267560284581491213952050075 401340426872236820928075113)
        ·
          refine ⟨301005320154177615696056335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401340426872236820928075113 301005320154177615696056335)
          ·
            refine ⟨451507980231266423544084503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301005320154177615696056335 451507980231266423544084503)
            ·
              refine ⟨677261970346899635316126755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451507980231266423544084503 677261970346899635316126755)
              ·
                refine ⟨1015892955520349452974190133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677261970346899635316126755 1015892955520349452974190133)
                ·
                  refine ⟨95239964580032761216330325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1015892955520349452974190133 95239964580032761216330325)
                  ·
                    refine ⟨1116093334922258920503871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95239964580032761216330325 1116093334922258920503871)
                    ·
                      rfl

theorem cell23_6520752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 8].length) (baseStart_6520752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520752 prefixEnd_6520752 := by exact prefixLift 6520752
  have htrace : WordTrace (prefixWord ++ tailWord_6520752) baseStart_6520752 baseEnd_6520752 := by
    simpa [prefixWord, tailWord_6520752, baseEnd_6520752] using wordTrace_append hprefix tailTrace_6520752
  have hstable : (prefixWord ++ tailWord_6520752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520752).length < 2 ^ (prefixWord ++ tailWord_6520752).sum := by decide
  have hdescent : baseEnd_6520752 < baseStart_6520752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520753 : List Nat := [1, 2, 2, 4, 2, 1, 1, 4, 2, 1, 3]
def baseStart_6520753 : Nat := 118140960795 + 6520753 * 2 ^ 59
def prefixEnd_6520753 : Nat := 4983230072969 + 3 ^ 40 * 6520753 * 2
def baseEnd_6520753 : Nat := 3348280518247431257599109

theorem tailTrace_6520753 : CollatzResearch.WordTrace tailWord_6520753 prefixEnd_6520753 3348280518247431257599109 := by
  unfold tailWord_6520753
  simp only [CollatzResearch.WordTrace]
  refine ⟨237831400545433011794830913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158554267030288674529887275 237831400545433011794830913)
  ·
    refine ⟨178373550409074758846123185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237831400545433011794830913 178373550409074758846123185)
    ·
      refine ⟨133780162806806069134592389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178373550409074758846123185 133780162806806069134592389)
      ·
        refine ⟨25083780526276137962736073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133780162806806069134592389 25083780526276137962736073)
        ·
          refine ⟨18812835394707103472052055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25083780526276137962736073 18812835394707103472052055)
          ·
            refine ⟨28219253092060655208078083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18812835394707103472052055 28219253092060655208078083)
            ·
              refine ⟨42328879638090982812117125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28219253092060655208078083 42328879638090982812117125)
              ·
                refine ⟨7936664932142059277271961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42328879638090982812117125 7936664932142059277271961)
                ·
                  refine ⟨5952498699106544457953971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7936664932142059277271961 5952498699106544457953971)
                  ·
                    refine ⟨8928748048659816686930957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5952498699106544457953971 8928748048659816686930957)
                    ·
                      refine ⟨3348280518247431257599109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8928748048659816686930957 3348280518247431257599109)
                      ·
                        rfl

theorem cell23_6520753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_6520753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520753 prefixEnd_6520753 := by exact prefixLift 6520753
  have htrace : WordTrace (prefixWord ++ tailWord_6520753) baseStart_6520753 baseEnd_6520753 := by
    simpa [prefixWord, tailWord_6520753, baseEnd_6520753] using wordTrace_append hprefix tailTrace_6520753
  have hstable : (prefixWord ++ tailWord_6520753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520753).length < 2 ^ (prefixWord ++ tailWord_6520753).sum := by decide
  have hdescent : baseEnd_6520753 < baseStart_6520753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520779 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 3]
def baseStart_6520779 : Nat := 118140960795 + 6520779 * 2 ^ 59
def prefixEnd_6520779 : Nat := 4983230072969 + 3 ^ 40 * 6520779 * 2
def baseEnd_6520779 : Nat := 3348293868744448155873989

theorem tailTrace_6520779 : CollatzResearch.WordTrace tailWord_6520779 prefixEnd_6520779 3348293868744448155873989 := by
  unfold tailWord_6520779
  simp only [CollatzResearch.WordTrace]
  refine ⟨237832348843338818235277391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158554899228892545490184927 237832348843338818235277391)
  ·
    refine ⟨356748523265008227352916087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237832348843338818235277391 356748523265008227352916087)
    ·
      refine ⟨535122784897512341029374131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356748523265008227352916087 535122784897512341029374131)
      ·
        refine ⟨802684177346268511544061197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535122784897512341029374131 802684177346268511544061197)
        ·
          refine ⟨301006566504850691829022949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 802684177346268511544061197 301006566504850691829022949)
          ·
            refine ⟨56438731219659504717941803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 301006566504850691829022949 56438731219659504717941803)
            ·
              refine ⟨84658096829489257076912705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56438731219659504717941803 84658096829489257076912705)
              ·
                refine ⟨63493572622116942807684529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84658096829489257076912705 63493572622116942807684529)
                ·
                  refine ⟨47620179466587707105763397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63493572622116942807684529 47620179466587707105763397)
                  ·
                    refine ⟨8928783649985195082330637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47620179466587707105763397 8928783649985195082330637)
                    ·
                      refine ⟨3348293868744448155873989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8928783649985195082330637 3348293868744448155873989)
                      ·
                        rfl

theorem cell23_6520779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 3].length) (baseStart_6520779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520779 prefixEnd_6520779 := by exact prefixLift 6520779
  have htrace : WordTrace (prefixWord ++ tailWord_6520779) baseStart_6520779 baseEnd_6520779 := by
    simpa [prefixWord, tailWord_6520779, baseEnd_6520779] using wordTrace_append hprefix tailTrace_6520779
  have hstable : (prefixWord ++ tailWord_6520779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520779).length < 2 ^ (prefixWord ++ tailWord_6520779).sum := by decide
  have hdescent : baseEnd_6520779 < baseStart_6520779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520816 : List Nat := [2, 1, 1, 1, 3, 2, 4, 4, 5]
def baseStart_6520816 : Nat := 118140960795 + 6520816 * 2 ^ 59
def prefixEnd_6520816 : Nat := 4983230072969 + 3 ^ 40 * 6520816 * 2
def baseEnd_6520816 : Nat := 372034763058740501234591

theorem tailTrace_6520816 : CollatzResearch.WordTrace tailWord_6520816 prefixEnd_6520816 372034763058740501234591 := by
  unfold tailWord_6520816
  simp only [CollatzResearch.WordTrace]
  refine ⟨118916849172102386777187151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158555798896136515702916201 118916849172102386777187151)
  ·
    refine ⟨178375273758153580165780727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118916849172102386777187151 178375273758153580165780727)
    ·
      refine ⟨267562910637230370248671091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178375273758153580165780727 267562910637230370248671091)
      ·
        refine ⟨401344365955845555373006637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267562910637230370248671091 401344365955845555373006637)
        ·
          refine ⟨150504137233442083264877489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401344365955845555373006637 150504137233442083264877489)
          ·
            refine ⟨112878102925081562448658117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150504137233442083264877489 112878102925081562448658117)
            ·
              refine ⟨21164644298452792959123397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112878102925081562448658117 21164644298452792959123397)
              ·
                refine ⟨3968370805959898679835637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21164644298452792959123397 3968370805959898679835637)
                ·
                  refine ⟨372034763058740501234591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3968370805959898679835637 372034763058740501234591)
                  ·
                    rfl

theorem cell23_6520816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 5].length) (baseStart_6520816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520816 prefixEnd_6520816 := by exact prefixLift 6520816
  have htrace : WordTrace (prefixWord ++ tailWord_6520816) baseStart_6520816 baseEnd_6520816 := by
    simpa [prefixWord, tailWord_6520816, baseEnd_6520816] using wordTrace_append hprefix tailTrace_6520816
  have hstable : (prefixWord ++ tailWord_6520816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520816).length < 2 ^ (prefixWord ++ tailWord_6520816).sum := by decide
  have hdescent : baseEnd_6520816 < baseStart_6520816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520829 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 1, 7]
def baseStart_6520829 : Nat := 118140960795 + 6520829 * 2 ^ 59
def prefixEnd_6520829 : Nat := 4983230072969 + 3 ^ 40 * 6520829 * 2
def baseEnd_6520829 : Nat := 1116106514259057653416253

theorem tailTrace_6520829 : CollatzResearch.WordTrace tailWord_6520829 prefixEnd_6520829 1116106514259057653416253 := by
  unfold tailWord_6520829
  simp only [CollatzResearch.WordTrace]
  refine ⟨237834172493157676774597541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158556114995438451183065027 237834172493157676774597541)
  ·
    refine ⟨44593907342467064395237039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237834172493157676774597541 44593907342467064395237039)
    ·
      refine ⟨66890861013700596592855559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44593907342467064395237039 66890861013700596592855559)
      ·
        refine ⟨100336291520550894889283339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66890861013700596592855559 100336291520550894889283339)
        ·
          refine ⟨150504437280826342333925009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100336291520550894889283339 150504437280826342333925009)
          ·
            refine ⟨112878327960619756750443757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150504437280826342333925009 112878327960619756750443757)
            ·
              refine ⟨42329372985232408781416409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112878327960619756750443757 42329372985232408781416409)
              ·
                refine ⟨31747029738924306586062307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42329372985232408781416409 31747029738924306586062307)
                ·
                  refine ⟨47620544608386459879093461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31747029738924306586062307 47620544608386459879093461)
                  ·
                    refine ⟨1116106514259057653416253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47620544608386459879093461 1116106514259057653416253)
                    ·
                      rfl

theorem cell23_6520829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_6520829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520829 prefixEnd_6520829 := by exact prefixLift 6520829
  have htrace : WordTrace (prefixWord ++ tailWord_6520829) baseStart_6520829 baseEnd_6520829 := by
    simpa [prefixWord, tailWord_6520829, baseEnd_6520829] using wordTrace_append hprefix tailTrace_6520829
  have hstable : (prefixWord ++ tailWord_6520829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520829).length < 2 ^ (prefixWord ++ tailWord_6520829).sum := by decide
  have hdescent : baseEnd_6520829 < baseStart_6520829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520846 : List Nat := [4, 1, 1, 2, 2, 1, 2, 3, 2, 5]
def baseStart_6520846 : Nat := 118140960795 + 6520846 * 2 ^ 59
def prefixEnd_6520846 : Nat := 4983230072969 + 3 ^ 40 * 6520846 * 2
def baseEnd_6520846 : Nat := 1116109423982766464578727

theorem tailTrace_6520846 : CollatzResearch.WordTrace tailWord_6520846 prefixEnd_6520846 1116109423982766464578727 := by
  unfold tailWord_6520846
  simp only [CollatzResearch.WordTrace]
  refine ⟨29729349066762011084745799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158556528356064059118644261 29729349066762011084745799)
  ·
    refine ⟨44594023600143016627118699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29729349066762011084745799 44594023600143016627118699)
    ·
      refine ⟨66891035400214524940678049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44594023600143016627118699 66891035400214524940678049)
      ·
        refine ⟨50168276550160893705508537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66891035400214524940678049 50168276550160893705508537)
        ·
          refine ⟨37626207412620670279131403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50168276550160893705508537 37626207412620670279131403)
          ·
            refine ⟨56439311118931005418697105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37626207412620670279131403 56439311118931005418697105)
            ·
              refine ⟨42329483339198254064022829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56439311118931005418697105 42329483339198254064022829)
              ·
                refine ⟨15873556252199345274008561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42329483339198254064022829 15873556252199345274008561)
                ·
                  refine ⟨11905167189149508955506421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15873556252199345274008561 11905167189149508955506421)
                  ·
                    refine ⟨1116109423982766464578727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11905167189149508955506421 1116109423982766464578727)
                    ·
                      rfl

theorem cell23_6520846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_6520846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520846 prefixEnd_6520846 := by exact prefixLift 6520846
  have htrace : WordTrace (prefixWord ++ tailWord_6520846) baseStart_6520846 baseEnd_6520846 := by
    simpa [prefixWord, tailWord_6520846, baseEnd_6520846] using wordTrace_append hprefix tailTrace_6520846
  have hstable : (prefixWord ++ tailWord_6520846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520846).length < 2 ^ (prefixWord ++ tailWord_6520846).sum := by decide
  have hdescent : baseEnd_6520846 < baseStart_6520846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520876 : List Nat := [2, 2, 1, 1, 1, 2, 2, 5, 3, 4]
def baseStart_6520876 : Nat := 118140960795 + 6520876 * 2 ^ 59
def prefixEnd_6520876 : Nat := 4983230072969 + 3 ^ 40 * 6520876 * 2
def baseEnd_6520876 : Nat := 1116114558789311425453681

theorem tailTrace_6520876 : CollatzResearch.WordTrace tailWord_6520876 prefixEnd_6520876 1116114558789311425453681 := by
  unfold tailWord_6520876
  simp only [CollatzResearch.WordTrace]
  refine ⟨118917943361993701900779241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158557257815991602534372321 118917943361993701900779241)
  ·
    refine ⟨89188457521495276425584431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118917943361993701900779241 89188457521495276425584431)
    ·
      refine ⟨133782686282242914638376647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89188457521495276425584431 133782686282242914638376647)
      ·
        refine ⟨200674029423364371957564971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133782686282242914638376647 200674029423364371957564971)
        ·
          refine ⟨301011044135046557936347457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200674029423364371957564971 301011044135046557936347457)
          ·
            refine ⟨225758283101284918452260593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301011044135046557936347457 225758283101284918452260593)
            ·
              refine ⟨169318712325963688839195445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225758283101284918452260593 169318712325963688839195445)
              ·
                refine ⟨15873629280559095828674573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169318712325963688839195445 15873629280559095828674573)
                ·
                  refine ⟨5952610980209660935752965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15873629280559095828674573 5952610980209660935752965)
                  ·
                    refine ⟨1116114558789311425453681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5952610980209660935752965 1116114558789311425453681)
                    ·
                      rfl

theorem cell23_6520876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_6520876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520876 prefixEnd_6520876 := by exact prefixLift 6520876
  have htrace : WordTrace (prefixWord ++ tailWord_6520876) baseStart_6520876 baseEnd_6520876 := by
    simpa [prefixWord, tailWord_6520876, baseEnd_6520876] using wordTrace_append hprefix tailTrace_6520876
  have hstable : (prefixWord ++ tailWord_6520876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520876).length < 2 ^ (prefixWord ++ tailWord_6520876).sum := by decide
  have hdescent : baseEnd_6520876 < baseStart_6520876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520879 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 4]
def baseStart_6520879 : Nat := 118140960795 + 6520879 * 2 ^ 59
def prefixEnd_6520879 : Nat := 4983230072969 + 3 ^ 40 * 6520879 * 2
def baseEnd_6520879 : Nat := 3348345216809897764623529

theorem tailTrace_6520879 : CollatzResearch.WordTrace tailWord_6520879 prefixEnd_6520879 3348345216809897764623529 := by
  unfold tailWord_6520879
  simp only [CollatzResearch.WordTrace]
  refine ⟨237835996142976535313917691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158557330761984356875945127 237835996142976535313917691)
  ·
    refine ⟨356753994214464802970876537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237835996142976535313917691 356753994214464802970876537)
    ·
      refine ⟨267565495660848602228157403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356753994214464802970876537 267565495660848602228157403)
      ·
        refine ⟨401348243491272903342236105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267565495660848602228157403 401348243491272903342236105)
        ·
          refine ⟨301011182618454677506677079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401348243491272903342236105 301011182618454677506677079)
          ·
            refine ⟨451516773927682016260015619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301011182618454677506677079 451516773927682016260015619)
            ·
              refine ⟨677275160891523024390023429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451516773927682016260015619 677275160891523024390023429)
              ·
                refine ⟨126989092667160567073129393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 677275160891523024390023429 126989092667160567073129393)
                ·
                  refine ⟨95241819500370425304847045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126989092667160567073129393 95241819500370425304847045)
                  ·
                    refine ⟨17857841156319454744658821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95241819500370425304847045 17857841156319454744658821)
                    ·
                      refine ⟨3348345216809897764623529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17857841156319454744658821 3348345216809897764623529)
                      ·
                        rfl

theorem cell23_6520879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_6520879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520879 prefixEnd_6520879 := by exact prefixLift 6520879
  have htrace : WordTrace (prefixWord ++ tailWord_6520879) baseStart_6520879 baseEnd_6520879 := by
    simpa [prefixWord, tailWord_6520879, baseEnd_6520879] using wordTrace_append hprefix tailTrace_6520879
  have hstable : (prefixWord ++ tailWord_6520879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520879).length < 2 ^ (prefixWord ++ tailWord_6520879).sum := by decide
  have hdescent : baseEnd_6520879 < baseStart_6520879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520903 : List Nat := [1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 3]
def baseStart_6520903 : Nat := 118140960795 + 6520903 * 2 ^ 59
def prefixEnd_6520903 : Nat := 4983230072969 + 3 ^ 40 * 6520903 * 2
def baseEnd_6520903 : Nat := 3348357540345605670723419

theorem tailTrace_6520903 : CollatzResearch.WordTrace tailWord_6520903 prefixEnd_6520903 3348357540345605670723419 := by
  unfold tailWord_6520903
  simp only [CollatzResearch.WordTrace]
  refine ⟨237836871494889587412791363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158557914329926391608527575 237836871494889587412791363)
  ·
    refine ⟨356755307242334381119187045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237836871494889587412791363 356755307242334381119187045)
    ·
      refine ⟨66891620107937696459847571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 356755307242334381119187045 66891620107937696459847571)
      ·
        refine ⟨100337430161906544689771357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66891620107937696459847571 100337430161906544689771357)
        ·
          refine ⟨37626536310714954258664259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100337430161906544689771357 37626536310714954258664259)
          ·
            refine ⟨56439804466072431387996389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37626536310714954258664259 56439804466072431387996389)
            ·
              refine ⟨10582463337388580885249323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56439804466072431387996389 10582463337388580885249323)
              ·
                refine ⟨15873695006082871327873985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10582463337388580885249323 15873695006082871327873985)
                ·
                  refine ⟨11905271254562153495905489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15873695006082871327873985 11905271254562153495905489)
                  ·
                    refine ⟨8928953440921615121929117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11905271254562153495905489 8928953440921615121929117)
                    ·
                      refine ⟨3348357540345605670723419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8928953440921615121929117 3348357540345605670723419)
                      ·
                        rfl

theorem cell23_6520903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_6520903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520903 prefixEnd_6520903 := by exact prefixLift 6520903
  have htrace : WordTrace (prefixWord ++ tailWord_6520903) baseStart_6520903 baseEnd_6520903 := by
    simpa [prefixWord, tailWord_6520903, baseEnd_6520903] using wordTrace_append hprefix tailTrace_6520903
  have hstable : (prefixWord ++ tailWord_6520903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520903).length < 2 ^ (prefixWord ++ tailWord_6520903).sum := by decide
  have hdescent : baseEnd_6520903 < baseStart_6520903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520950 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_6520950 : Nat := 118140960795 + 6520950 * 2 ^ 59
def prefixEnd_6520950 : Nat := 4983230072969 + 3 ^ 40 * 6520950 * 2
def baseEnd_6520950 : Nat := 3348381673936366986835703

theorem tailTrace_6520950 : CollatzResearch.WordTrace tailWord_6520950 prefixEnd_6520950 3348381673936366986835703 := by
  unfold tailWord_6520950
  simp only [CollatzResearch.WordTrace]
  refine ⟨14864911607857457152484519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158559057150479542959834869 14864911607857457152484519)
  ·
    refine ⟨22297367411786185728726779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14864911607857457152484519 22297367411786185728726779)
    ·
      refine ⟨33446051117679278593090169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22297367411786185728726779 33446051117679278593090169)
      ·
        refine ⟨25084538338259458944817627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33446051117679278593090169 25084538338259458944817627)
        ·
          refine ⟨37626807507389188417226441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25084538338259458944817627 37626807507389188417226441)
          ·
            refine ⟨28220105630541891312919831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37626807507389188417226441 28220105630541891312919831)
            ·
              refine ⟨42330158445812836969379747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28220105630541891312919831 42330158445812836969379747)
              ·
                refine ⟨63495237668719255454069621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42330158445812836969379747 63495237668719255454069621)
                ·
                  refine ⟨5952678531442430198819027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63495237668719255454069621 5952678531442430198819027)
                  ·
                    refine ⟨8929017797163645298228541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5952678531442430198819027 8929017797163645298228541)
                    ·
                      refine ⟨3348381673936366986835703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8929017797163645298228541 3348381673936366986835703)
                      ·
                        rfl

theorem cell23_6520950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_6520950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520950 prefixEnd_6520950 := by exact prefixLift 6520950
  have htrace : WordTrace (prefixWord ++ tailWord_6520950) baseStart_6520950 baseEnd_6520950 := by
    simpa [prefixWord, tailWord_6520950, baseEnd_6520950] using wordTrace_append hprefix tailTrace_6520950
  have hstable : (prefixWord ++ tailWord_6520950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520950).length < 2 ^ (prefixWord ++ tailWord_6520950).sum := by decide
  have hdescent : baseEnd_6520950 < baseStart_6520950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520970 : List Nat := [3, 1, 2, 3, 1, 2, 4, 1, 1, 5]
def baseStart_6520970 : Nat := 118140960795 + 6520970 * 2 ^ 59
def prefixEnd_6520970 : Nat := 4983230072969 + 3 ^ 40 * 6520970 * 2
def baseEnd_6520970 : Nat := 1116130647849818969528537

theorem tailTrace_6520970 : CollatzResearch.WordTrace tailWord_6520970 prefixEnd_6520970 1116130647849818969528537 := by
  unfold tailWord_6520970
  simp only [CollatzResearch.WordTrace]
  refine ⟨59459828796411714463870091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158559543457097905236986909 59459828796411714463870091)
  ·
    refine ⟨89189743194617571695805137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59459828796411714463870091 89189743194617571695805137)
    ·
      refine ⟨66892307395963178771853853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89189743194617571695805137 66892307395963178771853853)
      ·
        refine ⟨25084615273486192039445195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66892307395963178771853853 25084615273486192039445195)
        ·
          refine ⟨37626922910229288059167793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25084615273486192039445195 37626922910229288059167793)
          ·
            refine ⟨28220192182671966044375845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37626922910229288059167793 28220192182671966044375845)
            ·
              refine ⟨5291286034250993633320471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28220192182671966044375845 5291286034250993633320471)
              ·
                refine ⟨7936929051376490449980707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5291286034250993633320471 7936929051376490449980707)
                ·
                  refine ⟨11905393577064735674971061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7936929051376490449980707 11905393577064735674971061)
                  ·
                    refine ⟨1116130647849818969528537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11905393577064735674971061 1116130647849818969528537)
                    ·
                      rfl

theorem cell23_6520970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_6520970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520970 prefixEnd_6520970 := by exact prefixLift 6520970
  have htrace : WordTrace (prefixWord ++ tailWord_6520970) baseStart_6520970 baseEnd_6520970 := by
    simpa [prefixWord, tailWord_6520970, baseEnd_6520970] using wordTrace_append hprefix tailTrace_6520970
  have hstable : (prefixWord ++ tailWord_6520970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520970).length < 2 ^ (prefixWord ++ tailWord_6520970).sum := by decide
  have hdescent : baseEnd_6520970 < baseStart_6520970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520976 : List Nat := [2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 5]
def baseStart_6520976 : Nat := 118140960795 + 6520976 * 2 ^ 59
def prefixEnd_6520976 : Nat := 4983230072969 + 3 ^ 40 * 6520976 * 2
def baseEnd_6520976 : Nat := 3348395024433383885110583

theorem tailTrace_6520976 : CollatzResearch.WordTrace tailWord_6520976 prefixEnd_6520976 3348395024433383885110583 := by
  unfold tailWord_6520976
  simp only [CollatzResearch.WordTrace]
  refine ⟨118919767011812560440099391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158559689349083413920132521 118919767011812560440099391)
  ·
    refine ⟨178379650517718840660149087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118919767011812560440099391 178379650517718840660149087)
    ·
      refine ⟨267569475776578260990223631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178379650517718840660149087 267569475776578260990223631)
      ·
        refine ⟨401354213664867391485335447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267569475776578260990223631 401354213664867391485335447)
        ·
          refine ⟨602031320497301087228003171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401354213664867391485335447 602031320497301087228003171)
          ·
            refine ⟨903046980745951630842004757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602031320497301087228003171 903046980745951630842004757)
            ·
              refine ⟨42330327222466482695718973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 903046980745951630842004757 42330327222466482695718973)
              ·
                refine ⟨15873872708424931010894615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42330327222466482695718973 15873872708424931010894615)
                ·
                  refine ⟨23810809062637396516341923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15873872708424931010894615 23810809062637396516341923)
                  ·
                    refine ⟨35716213593956094774512885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23810809062637396516341923 35716213593956094774512885)
                    ·
                      refine ⟨3348395024433383885110583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35716213593956094774512885 3348395024433383885110583)
                      ·
                        rfl

theorem cell23_6520976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 5].length) (baseStart_6520976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520976 prefixEnd_6520976 := by exact prefixLift 6520976
  have htrace : WordTrace (prefixWord ++ tailWord_6520976) baseStart_6520976 baseEnd_6520976 := by
    simpa [prefixWord, tailWord_6520976, baseEnd_6520976] using wordTrace_append hprefix tailTrace_6520976
  have hstable : (prefixWord ++ tailWord_6520976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520976).length < 2 ^ (prefixWord ++ tailWord_6520976).sum := by decide
  have hdescent : baseEnd_6520976 < baseStart_6520976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520993 : List Nat := [1, 2, 3, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_6520993 : Nat := 118140960795 + 6520993 * 2 ^ 59
def prefixEnd_6520993 : Nat := 4983230072969 + 3 ^ 40 * 6520993 * 2
def baseEnd_6520993 : Nat := 3348403753604510318598005

theorem tailTrace_6520993 : CollatzResearch.WordTrace tailWord_6520993 prefixEnd_6520993 3348403753604510318598005 := by
  unfold tailWord_6520993
  simp only [CollatzResearch.WordTrace]
  refine ⟨237840154064563532783567633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158560102709709021855711755 237840154064563532783567633)
  ·
    refine ⟨178380115548422649587675725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237840154064563532783567633 178380115548422649587675725)
    ·
      refine ⟨66892543330658493595378397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178380115548422649587675725 66892543330658493595378397)
      ·
        refine ⟨25084703748996935098266899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66892543330658493595378397 25084703748996935098266899)
        ·
          refine ⟨37627055623495402647400349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25084703748996935098266899 37627055623495402647400349)
          ·
            refine ⟨14110145858810775992775131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37627055623495402647400349 14110145858810775992775131)
            ·
              refine ⟨21165218788216163989162697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14110145858810775992775131 21165218788216163989162697)
              ·
                refine ⟨15873914091162122991872023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21165218788216163989162697 15873914091162122991872023)
                ·
                  refine ⟨23810871136743184487808035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15873914091162122991872023 23810871136743184487808035)
                  ·
                    refine ⟨35716306705114776731712053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23810871136743184487808035 35716306705114776731712053)
                    ·
                      refine ⟨3348403753604510318598005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35716306705114776731712053 3348403753604510318598005)
                      ·
                        rfl

theorem cell23_6520993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_6520993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520993 prefixEnd_6520993 := by exact prefixLift 6520993
  have htrace : WordTrace (prefixWord ++ tailWord_6520993) baseStart_6520993 baseEnd_6520993 := by
    simpa [prefixWord, tailWord_6520993, baseEnd_6520993] using wordTrace_append hprefix tailTrace_6520993
  have hstable : (prefixWord ++ tailWord_6520993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520993).length < 2 ^ (prefixWord ++ tailWord_6520993).sum := by decide
  have hdescent : baseEnd_6520993 < baseStart_6520993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521010 : List Nat := [3, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3]
def baseStart_6521010 : Nat := 118140960795 + 6521010 * 2 ^ 59
def prefixEnd_6521010 : Nat := 4983230072969 + 3 ^ 40 * 6521010 * 2
def baseEnd_6521010 : Nat := 3348412482775636752085427

theorem tailTrace_6521010 : CollatzResearch.WordTrace tailWord_6521010 prefixEnd_6521010 3348412482775636752085427 := by
  unfold tailWord_6521010
  simp only [CollatzResearch.WordTrace]
  refine ⟨59460193526375486171734121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158560516070334629791290989 59460193526375486171734121)
  ·
    refine ⟨44595145144781614628800591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59460193526375486171734121 44595145144781614628800591)
    ·
      refine ⟨66892717717172421943200887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44595145144781614628800591 66892717717172421943200887)
      ·
        refine ⟨100339076575758632914801331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66892717717172421943200887 100339076575758632914801331)
        ·
          refine ⟨150508614863637949372201997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100339076575758632914801331 150508614863637949372201997)
          ·
            refine ⟨56440730573864231014575749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150508614863637949372201997 56440730573864231014575749)
            ·
              refine ⟨10582636982599543315232953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56440730573864231014575749 10582636982599543315232953)
              ·
                refine ⟨7936977736949657486424715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10582636982599543315232953 7936977736949657486424715)
                ·
                  refine ⟨11905466605424486229637073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7936977736949657486424715 11905466605424486229637073)
                  ·
                    refine ⟨8929099954068364672227805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11905466605424486229637073 8929099954068364672227805)
                    ·
                      refine ⟨3348412482775636752085427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8929099954068364672227805 3348412482775636752085427)
                      ·
                        rfl

theorem cell23_6521010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_6521010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521010 prefixEnd_6521010 := by exact prefixLift 6521010
  have htrace : WordTrace (prefixWord ++ tailWord_6521010) baseStart_6521010 baseEnd_6521010 := by
    simpa [prefixWord, tailWord_6521010, baseEnd_6521010] using wordTrace_append hprefix tailTrace_6521010
  have hstable : (prefixWord ++ tailWord_6521010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521010).length < 2 ^ (prefixWord ++ tailWord_6521010).sum := by decide
  have hdescent : baseEnd_6521010 < baseStart_6521010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521024 : List Nat := [2, 1, 1, 2, 5, 1, 3, 3, 1, 2, 2]
def baseStart_6521024 : Nat := 118140960795 + 6521024 * 2 ^ 59
def prefixEnd_6521024 : Nat := 4983230072969 + 3 ^ 40 * 6521024 * 2
def baseEnd_6521024 : Nat := 3348419671504799697310363

theorem tailTrace_6521024 : CollatzResearch.WordTrace tailWord_6521024 prefixEnd_6521024 3348419671504799697310363 := by
  unfold tailWord_6521024
  simp only [CollatzResearch.WordTrace]
  refine ⟨118920642363725612538973063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158560856484967483385297417 118920642363725612538973063)
  ·
    refine ⟨178380963545588418808459595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118920642363725612538973063 178380963545588418808459595)
    ·
      refine ⟨267571445318382628212689393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178380963545588418808459595 267571445318382628212689393)
      ·
        refine ⟨200678583988786971159517045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267571445318382628212689393 200678583988786971159517045)
        ·
          refine ⟨18813617248948778546204723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200678583988786971159517045 18813617248948778546204723)
          ·
            refine ⟨28220425873423167819307085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18813617248948778546204723 28220425873423167819307085)
            ·
              refine ⟨10582659702533687932240157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28220425873423167819307085 10582659702533687932240157)
              ·
                refine ⟨3968497388450132974590059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10582659702533687932240157 3968497388450132974590059)
                ·
                  refine ⟨5952746082675199461885089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3968497388450132974590059 5952746082675199461885089)
                  ·
                    refine ⟨4464559562006399596413817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5952746082675199461885089 4464559562006399596413817)
                    ·
                      refine ⟨3348419671504799697310363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4464559562006399596413817 3348419671504799697310363)
                      ·
                        rfl

theorem cell23_6521024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 1, 2, 2].length) (baseStart_6521024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521024 prefixEnd_6521024 := by exact prefixLift 6521024
  have htrace : WordTrace (prefixWord ++ tailWord_6521024) baseStart_6521024 baseEnd_6521024 := by
    simpa [prefixWord, tailWord_6521024, baseEnd_6521024] using wordTrace_append hprefix tailTrace_6521024
  have hstable : (prefixWord ++ tailWord_6521024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521024).length < 2 ^ (prefixWord ++ tailWord_6521024).sum := by decide
  have hdescent : baseEnd_6521024 < baseStart_6521024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521056 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 1, 8]
def baseStart_6521056 : Nat := 118140960795 + 6521056 * 2 ^ 59
def prefixEnd_6521056 : Nat := 4983230072969 + 3 ^ 40 * 6521056 * 2
def baseEnd_6521056 : Nat := 1116145367628581190703405

theorem tailTrace_6521056 : CollatzResearch.WordTrace tailWord_6521056 prefixEnd_6521056 1116145367628581190703405 := by
  unfold tailWord_6521056
  simp only [CollatzResearch.WordTrace]
  refine ⟨118921225931667647271555511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158561634575556863028740681 118921225931667647271555511)
  ·
    refine ⟨178381838897501470907333267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118921225931667647271555511 178381838897501470907333267)
    ·
      refine ⟨267572758346252206360999901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178381838897501470907333267 267572758346252206360999901)
      ·
        refine ⟨100339784379844577385374963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267572758346252206360999901 100339784379844577385374963)
        ·
          refine ⟨150509676569766866078062445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100339784379844577385374963 150509676569766866078062445)
          ·
            refine ⟨56441128713662574779273417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150509676569766866078062445 56441128713662574779273417)
            ·
              refine ⟨42330846535246931084455063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56441128713662574779273417 42330846535246931084455063)
              ·
                refine ⟨63496269802870396626682595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42330846535246931084455063 63496269802870396626682595)
                ·
                  refine ⟨95244404704305594940023893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63496269802870396626682595 95244404704305594940023893)
                  ·
                    refine ⟨1116145367628581190703405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95244404704305594940023893 1116145367628581190703405)
                    ·
                      rfl

theorem cell23_6521056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 8].length) (baseStart_6521056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521056 prefixEnd_6521056 := by exact prefixLift 6521056
  have htrace : WordTrace (prefixWord ++ tailWord_6521056) baseStart_6521056 baseEnd_6521056 := by
    simpa [prefixWord, tailWord_6521056, baseEnd_6521056] using wordTrace_append hprefix tailTrace_6521056
  have hstable : (prefixWord ++ tailWord_6521056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521056).length < 2 ^ (prefixWord ++ tailWord_6521056).sum := by decide
  have hdescent : baseEnd_6521056 < baseStart_6521056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521058 : List Nat := [3, 3, 4, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_6521058 : Nat := 118140960795 + 6521058 * 2 ^ 59
def prefixEnd_6521058 : Nat := 4983230072969 + 3 ^ 40 * 6521058 * 2
def baseEnd_6521058 : Nat := 3348437129847052564285207

theorem tailTrace_6521058 : CollatzResearch.WordTrace tailWord_6521058 prefixEnd_6521058 3348437129847052564285207 := by
  unfold tailWord_6521058
  simp only [CollatzResearch.WordTrace]
  refine ⟨59460631202332012221170957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158561683206218699256455885 59460631202332012221170957)
  ·
    refine ⟨22297736700874504582939109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59460631202332012221170957 22297736700874504582939109)
    ·
      refine ⟨4180825631413969609301083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22297736700874504582939109 4180825631413969609301083)
      ·
        refine ⟨6271238447120954413951625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4180825631413969609301083 6271238447120954413951625)
        ·
          refine ⟨4703428835340715810463719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6271238447120954413951625 4703428835340715810463719)
          ·
            refine ⟨7055143253011073715695579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4703428835340715810463719 7055143253011073715695579)
            ·
              refine ⟨10582714879516610573543369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7055143253011073715695579 10582714879516610573543369)
              ·
                refine ⟨7937036159637457930157527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10582714879516610573543369 7937036159637457930157527)
                ·
                  refine ⟨11905554239456186895236291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7937036159637457930157527 11905554239456186895236291)
                  ·
                    refine ⟨17858331359184280342854437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11905554239456186895236291 17858331359184280342854437)
                    ·
                      refine ⟨3348437129847052564285207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17858331359184280342854437 3348437129847052564285207)
                      ·
                        rfl

theorem cell23_6521058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_6521058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521058 prefixEnd_6521058 := by exact prefixLift 6521058
  have htrace : WordTrace (prefixWord ++ tailWord_6521058) baseStart_6521058 baseEnd_6521058 := by
    simpa [prefixWord, tailWord_6521058, baseEnd_6521058] using wordTrace_append hprefix tailTrace_6521058
  have hstable : (prefixWord ++ tailWord_6521058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521058).length < 2 ^ (prefixWord ++ tailWord_6521058).sum := by decide
  have hdescent : baseEnd_6521058 < baseStart_6521058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521080 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 6, 2, 2]
def baseStart_6521080 : Nat := 118140960795 + 6521080 * 2 ^ 59
def prefixEnd_6521080 : Nat := 4983230072969 + 3 ^ 40 * 6521080 * 2
def baseEnd_6521080 : Nat := 3348448426421451478210105

theorem tailTrace_6521080 : CollatzResearch.WordTrace tailWord_6521080 prefixEnd_6521080 3348448426421451478210105 := by
  unfold tailWord_6521080
  simp only [CollatzResearch.WordTrace]
  refine ⟨118921663607624173320992347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158562218143498897761323129 118921663607624173320992347)
  ·
    refine ⟨178382495411436259981488521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118921663607624173320992347 178382495411436259981488521)
    ·
      refine ⟨133786871558577194986116391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178382495411436259981488521 133786871558577194986116391)
      ·
        refine ⟨200680307337865792479174587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133786871558577194986116391 200680307337865792479174587)
        ·
          refine ⟨301020461006798688718761881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200680307337865792479174587 301020461006798688718761881)
          ·
            refine ⟨225765345755099016539071411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301020461006798688718761881 225765345755099016539071411)
            ·
              refine ⟨338648018632648524808607117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225765345755099016539071411 338648018632648524808607117)
              ·
                refine ⟨126993006987243196803227669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 338648018632648524808607117 126993006987243196803227669)
                ·
                  refine ⟨5952797202527024850151297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126993006987243196803227669 5952797202527024850151297)
                  ·
                    refine ⟨4464597901895268637613473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5952797202527024850151297 4464597901895268637613473)
                    ·
                      refine ⟨3348448426421451478210105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4464597901895268637613473 3348448426421451478210105)
                      ·
                        rfl

theorem cell23_6521080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 6, 2, 2].length) (baseStart_6521080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521080 prefixEnd_6521080 := by exact prefixLift 6521080
  have htrace : WordTrace (prefixWord ++ tailWord_6521080) baseStart_6521080 baseEnd_6521080 := by
    simpa [prefixWord, tailWord_6521080, baseEnd_6521080] using wordTrace_append hprefix tailTrace_6521080
  have hstable : (prefixWord ++ tailWord_6521080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521080).length < 2 ^ (prefixWord ++ tailWord_6521080).sum := by decide
  have hdescent : baseEnd_6521080 < baseStart_6521080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521084 : List Nat := [2, 2, 2, 1, 4, 2, 3, 1, 1, 3, 2]
def baseStart_6521084 : Nat := 118140960795 + 6521084 * 2 ^ 59
def prefixEnd_6521084 : Nat := 4983230072969 + 3 ^ 40 * 6521084 * 2
def baseEnd_6521084 : Nat := 3348450480344069462560087

theorem tailTrace_6521084 : CollatzResearch.WordTrace tailWord_6521084 prefixEnd_6521084 3348450480344069462560087 := by
  unfold tailWord_6521084
  simp only [CollatzResearch.WordTrace]
  refine ⟨118921736553616927662565153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158562315404822570216753537 118921736553616927662565153)
  ·
    refine ⟨89191302415212695746923865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118921736553616927662565153 89191302415212695746923865)
    ·
      refine ⟨66893476811409521810192899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89191302415212695746923865 66893476811409521810192899)
      ·
        refine ⟨100340215217114282715289349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66893476811409521810192899 100340215217114282715289349)
        ·
          refine ⟨18813790353208928009116753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100340215217114282715289349 18813790353208928009116753)
          ·
            refine ⟨14110342764906696006837565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18813790353208928009116753 14110342764906696006837565)
            ·
              refine ⟨5291378536840011002564087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14110342764906696006837565 5291378536840011002564087)
              ·
                refine ⟨7937067805260016503846131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5291378536840011002564087 7937067805260016503846131)
                ·
                  refine ⟨11905601707890024755769197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7937067805260016503846131 11905601707890024755769197)
                  ·
                    refine ⟨4464600640458759283413449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11905601707890024755769197 4464600640458759283413449)
                    ·
                      refine ⟨3348450480344069462560087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4464600640458759283413449 3348450480344069462560087)
                      ·
                        rfl

theorem cell23_6521084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_6521084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521084 prefixEnd_6521084 := by exact prefixLift 6521084
  have htrace : WordTrace (prefixWord ++ tailWord_6521084) baseStart_6521084 baseEnd_6521084 := by
    simpa [prefixWord, tailWord_6521084, baseEnd_6521084] using wordTrace_append hprefix tailTrace_6521084
  have hstable : (prefixWord ++ tailWord_6521084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521084).length < 2 ^ (prefixWord ++ tailWord_6521084).sum := by decide
  have hdescent : baseEnd_6521084 < baseStart_6521084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521097 : List Nat := [1, 2, 1, 1, 3, 4, 1, 4, 2, 2, 2]
def baseStart_6521097 : Nat := 118140960795 + 6521097 * 2 ^ 59
def prefixEnd_6521097 : Nat := 4983230072969 + 3 ^ 40 * 6521097 * 2
def baseEnd_6521097 : Nat := 3348457155592577911697527

theorem tailTrace_6521097 : CollatzResearch.WordTrace tailWord_6521097 prefixEnd_6521097 3348457155592577911697527 := by
  unfold tailWord_6521097
  simp only [CollatzResearch.WordTrace]
  refine ⟨237843947256186758545353545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158562631504124505696902363 237843947256186758545353545)
  ·
    refine ⟨178382960442140068909015159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237843947256186758545353545 178382960442140068909015159)
    ·
      refine ⟨267574440663210103363522739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178382960442140068909015159 267574440663210103363522739)
      ·
        refine ⟨401361660994815155045284109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267574440663210103363522739 401361660994815155045284109)
        ·
          refine ⟨150510622873055683141981541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401361660994815155045284109 150510622873055683141981541)
          ·
            refine ⟨28220741788697940589121539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150510622873055683141981541 28220741788697940589121539)
            ·
              refine ⟨42331112683046910883682309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28220741788697940589121539 42331112683046910883682309)
              ·
                refine ⟨7937083628071295790690433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42331112683046910883682309 7937083628071295790690433)
                ·
                  refine ⟨5952812721053471843017825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7937083628071295790690433 5952812721053471843017825)
                  ·
                    refine ⟨4464609540790103882263369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5952812721053471843017825 4464609540790103882263369)
                    ·
                      refine ⟨3348457155592577911697527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4464609540790103882263369 3348457155592577911697527)
                      ·
                        rfl

theorem cell23_6521097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 2, 2].length) (baseStart_6521097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521097 prefixEnd_6521097 := by exact prefixLift 6521097
  have htrace : WordTrace (prefixWord ++ tailWord_6521097) baseStart_6521097 baseEnd_6521097 := by
    simpa [prefixWord, tailWord_6521097, baseEnd_6521097] using wordTrace_append hprefix tailTrace_6521097
  have hstable : (prefixWord ++ tailWord_6521097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521097).length < 2 ^ (prefixWord ++ tailWord_6521097).sum := by decide
  have hdescent : baseEnd_6521097 < baseStart_6521097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521137 : List Nat := [1, 2, 2, 3, 4, 1, 2, 3, 5]
def baseStart_6521137 : Nat := 118140960795 + 6521137 * 2 ^ 59
def prefixEnd_6521137 : Nat := 4983230072969 + 3 ^ 40 * 6521137 * 2
def baseEnd_6521137 : Nat := 372053077202084195021927

theorem tailTrace_6521137 : CollatzResearch.WordTrace tailWord_6521137 prefixEnd_6521137 372053077202084195021927 := by
  unfold tailWord_6521137
  simp only [CollatzResearch.WordTrace]
  refine ⟨237845406176041845376809665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158563604117361230251206443 237845406176041845376809665)
  ·
    refine ⟨178384054632031384032607249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237845406176041845376809665 178384054632031384032607249)
    ·
      refine ⟨133788040974023538024455437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178384054632031384032607249 133788040974023538024455437)
      ·
        refine ⟨50170515365258826759170789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133788040974023538024455437 50170515365258826759170789)
        ·
          refine ⟨9406971630986030017344523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50170515365258826759170789 9406971630986030017344523)
          ·
            refine ⟨14110457446479045026016785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9406971630986030017344523 14110457446479045026016785)
            ·
              refine ⟨10582843084859283769512589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14110457446479045026016785 10582843084859283769512589)
              ·
                refine ⟨3968566156822231413567221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10582843084859283769512589 3968566156822231413567221)
                ·
                  refine ⟨372053077202084195021927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3968566156822231413567221 372053077202084195021927)
                  ·
                    rfl

theorem cell23_6521137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 5].length) (baseStart_6521137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521137 prefixEnd_6521137 := by exact prefixLift 6521137
  have htrace : WordTrace (prefixWord ++ tailWord_6521137) baseStart_6521137 baseEnd_6521137 := by
    simpa [prefixWord, tailWord_6521137, baseEnd_6521137] using wordTrace_append hprefix tailTrace_6521137
  have hstable : (prefixWord ++ tailWord_6521137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521137).length < 2 ^ (prefixWord ++ tailWord_6521137).sum := by decide
  have hdescent : baseEnd_6521137 < baseStart_6521137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521203 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 3]
def baseStart_6521203 : Nat := 118140960795 + 6521203 * 2 ^ 59
def prefixEnd_6521203 : Nat := 4983230072969 + 3 ^ 40 * 6521203 * 2
def baseEnd_6521203 : Nat := 3348511584541954496972039

theorem tailTrace_6521203 : CollatzResearch.WordTrace tailWord_6521203 prefixEnd_6521203 3348511584541954496972039 := by
  unfold tailWord_6521203
  simp only [CollatzResearch.WordTrace]
  refine ⟨237847813393802738648712263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158565208929201825765808175 237847813393802738648712263)
  ·
    refine ⟨356771720090704107973068395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237847813393802738648712263 356771720090704107973068395)
    ·
      refine ⟨535157580136056161959602593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356771720090704107973068395 535157580136056161959602593)
      ·
        refine ⟨401368185102042121469701945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535157580136056161959602593 401368185102042121469701945)
        ·
          refine ⟨301026138826531591102276459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401368185102042121469701945 301026138826531591102276459)
          ·
            refine ⟨451539208239797386653414689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301026138826531591102276459 451539208239797386653414689)
            ·
              refine ⟨338654406179848039990061017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451539208239797386653414689 338654406179848039990061017)
              ·
                refine ⟨253990804634886029992545763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338654406179848039990061017 253990804634886029992545763)
                ·
                  refine ⟨380986206952329044988818645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253990804634886029992545763 380986206952329044988818645)
                  ·
                    refine ⟨8929364225445211991925437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 380986206952329044988818645 8929364225445211991925437)
                    ·
                      refine ⟨3348511584541954496972039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8929364225445211991925437 3348511584541954496972039)
                      ·
                        rfl

theorem cell23_6521203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 3].length) (baseStart_6521203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521203 prefixEnd_6521203 := by exact prefixLift 6521203
  have htrace : WordTrace (prefixWord ++ tailWord_6521203) baseStart_6521203 baseEnd_6521203 := by
    simpa [prefixWord, tailWord_6521203, baseEnd_6521203] using wordTrace_append hprefix tailTrace_6521203
  have hstable : (prefixWord ++ tailWord_6521203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521203).length < 2 ^ (prefixWord ++ tailWord_6521203).sum := by decide
  have hdescent : baseEnd_6521203 < baseStart_6521203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521227 : List Nat := [1, 1, 1, 1, 4, 6, 2, 1, 6]
def baseStart_6521227 : Nat := 118140960795 + 6521227 * 2 ^ 59
def prefixEnd_6521227 : Nat := 4983230072969 + 3 ^ 40 * 6521227 * 2
def baseEnd_6521227 : Nat := 372058212008629155896881

theorem tailTrace_6521227 : CollatzResearch.WordTrace tailWord_6521227 prefixEnd_6521227 372058212008629155896881 := by
  unfold tailWord_6521227
  simp only [CollatzResearch.WordTrace]
  refine ⟨237848688745715790747585935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158565792497143860498390623 237848688745715790747585935)
  ·
    refine ⟨356773033118573686121378903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237848688745715790747585935 356773033118573686121378903)
    ·
      refine ⟨535159549677860529182068355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356773033118573686121378903 535159549677860529182068355)
      ·
        refine ⟨802739324516790793773102533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535159549677860529182068355 802739324516790793773102533)
        ·
          refine ⟨150513623346898273832456725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 802739324516790793773102533 150513623346898273832456725)
          ·
            refine ⟨7055326094385856585896409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 150513623346898273832456725 7055326094385856585896409)
            ·
              refine ⟨5291494570789392439422307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7055326094385856585896409 5291494570789392439422307)
              ·
                refine ⟨7937241856184088659133461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5291494570789392439422307 7937241856184088659133461)
                ·
                  refine ⟨372058212008629155896881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7937241856184088659133461 372058212008629155896881)
                  ·
                    rfl

theorem cell23_6521227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 6].length) (baseStart_6521227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521227 prefixEnd_6521227 := by exact prefixLift 6521227
  have htrace : WordTrace (prefixWord ++ tailWord_6521227) baseStart_6521227 baseEnd_6521227 := by
    simpa [prefixWord, tailWord_6521227, baseEnd_6521227] using wordTrace_append hprefix tailTrace_6521227
  have hstable : (prefixWord ++ tailWord_6521227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521227).length < 2 ^ (prefixWord ++ tailWord_6521227).sum := by decide
  have hdescent : baseEnd_6521227 < baseStart_6521227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521238 : List Nat := [5, 3, 1, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_6521238 : Nat := 118140960795 + 6521238 * 2 ^ 59
def prefixEnd_6521238 : Nat := 4983230072969 + 3 ^ 40 * 6521238 * 2
def baseEnd_6521238 : Nat := 3348529556364861860034379

theorem tailTrace_6521238 : CollatzResearch.WordTrace tailWord_6521238 prefixEnd_6521238 3348529556364861860034379 := by
  unfold tailWord_6521238
  simp only [CollatzResearch.WordTrace]
  refine ⟨14865568121792246226639773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158566059965783959750824245 14865568121792246226639773)
  ·
    refine ⟨5574588045672092334989915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14865568121792246226639773 5574588045672092334989915)
    ·
      refine ⟨8361882068508138502484873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5574588045672092334989915 8361882068508138502484873)
      ·
        refine ⟨6271411551381103876863655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8361882068508138502484873 6271411551381103876863655)
        ·
          refine ⟨9407117327071655815295483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6271411551381103876863655 9407117327071655815295483)
          ·
            refine ⟨14110675990607483722943225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9407117327071655815295483 14110675990607483722943225)
            ·
              refine ⟨10583006992955612792207419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14110675990607483722943225 10583006992955612792207419)
              ·
                refine ⟨15874510489433419188311129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10583006992955612792207419 15874510489433419188311129)
                ·
                  refine ⟨11905882867075064391233347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15874510489433419188311129 11905882867075064391233347)
                  ·
                    refine ⟨17858824300612596586850021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11905882867075064391233347 17858824300612596586850021)
                    ·
                      refine ⟨3348529556364861860034379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17858824300612596586850021 3348529556364861860034379)
                      ·
                        rfl

theorem cell23_6521238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_6521238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521238 prefixEnd_6521238 := by exact prefixLift 6521238
  have htrace : WordTrace (prefixWord ++ tailWord_6521238) baseStart_6521238 baseEnd_6521238 := by
    simpa [prefixWord, tailWord_6521238, baseEnd_6521238] using wordTrace_append hprefix tailTrace_6521238
  have hstable : (prefixWord ++ tailWord_6521238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521238).length < 2 ^ (prefixWord ++ tailWord_6521238).sum := by decide
  have hdescent : baseEnd_6521238 < baseStart_6521238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521271 : List Nat := [1, 1, 3, 1, 3, 3, 4, 2, 1, 1, 3]
def baseStart_6521271 : Nat := 118140960795 + 6521271 * 2 ^ 59
def prefixEnd_6521271 : Nat := 4983230072969 + 3 ^ 40 * 6521271 * 2
def baseEnd_6521271 : Nat := 3348546501226460230921727

theorem tailTrace_6521271 : CollatzResearch.WordTrace tailWord_6521271 prefixEnd_6521271 3348546501226460230921727 := by
  unfold tailWord_6521271
  simp only [CollatzResearch.WordTrace]
  refine ⟨237850293557556386262187667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158566862371704257508125111 237850293557556386262187667)
  ·
    refine ⟨356775440336334579393281501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237850293557556386262187667 356775440336334579393281501)
    ·
      refine ⟨133790790126125467272480563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356775440336334579393281501 133790790126125467272480563)
      ·
        refine ⟨200686185189188200908720845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133790790126125467272480563 200686185189188200908720845)
        ·
          refine ⟨75257319445945575340770317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200686185189188200908720845 75257319445945575340770317)
          ·
            refine ⟨28221494792229590752788869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75257319445945575340770317 28221494792229590752788869)
            ·
              refine ⟨5291530273543048266147913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28221494792229590752788869 5291530273543048266147913)
              ·
                refine ⟨3968647705157286199610935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5291530273543048266147913 3968647705157286199610935)
                ·
                  refine ⟨5952971557735929299416403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3968647705157286199610935 5952971557735929299416403)
                  ·
                    refine ⟨8929457336603893949124605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5952971557735929299416403 8929457336603893949124605)
                    ·
                      refine ⟨3348546501226460230921727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8929457336603893949124605 3348546501226460230921727)
                      ·
                        rfl

theorem cell23_6521271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 1, 1, 3].length) (baseStart_6521271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521271 prefixEnd_6521271 := by exact prefixLift 6521271
  have htrace : WordTrace (prefixWord ++ tailWord_6521271) baseStart_6521271 baseEnd_6521271 := by
    simpa [prefixWord, tailWord_6521271, baseEnd_6521271] using wordTrace_append hprefix tailTrace_6521271
  have hstable : (prefixWord ++ tailWord_6521271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521271).length < 2 ^ (prefixWord ++ tailWord_6521271).sum := by decide
  have hdescent : baseEnd_6521271 < baseStart_6521271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521287 : List Nat := [1, 1, 4, 1, 1, 4, 2, 3, 2, 4]
def baseStart_6521287 : Nat := 118140960795 + 6521287 * 2 ^ 59
def prefixEnd_6521287 : Nat := 4983230072969 + 3 ^ 40 * 6521287 * 2
def baseEnd_6521287 : Nat := 1116184905638977389440551

theorem tailTrace_6521287 : CollatzResearch.WordTrace tailWord_6521287 prefixEnd_6521287 1116184905638977389440551 := by
  unfold tailWord_6521287
  simp only [CollatzResearch.WordTrace]
  refine ⟨237850877125498420994770115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158567251416998947329846743 237850877125498420994770115)
  ·
    refine ⟨356776315688247631492155173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237850877125498420994770115 356776315688247631492155173)
    ·
      refine ⟨66895559191546430904779095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 356776315688247631492155173 66895559191546430904779095)
      ·
        refine ⟨100343338787319646357168643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66895559191546430904779095 100343338787319646357168643)
        ·
          refine ⟨150515008180979469535752965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100343338787319646357168643 150515008180979469535752965)
          ·
            refine ⟨28221564033933650537953681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150515008180979469535752965 28221564033933650537953681)
            ·
              refine ⟨21166173025450237903465261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28221564033933650537953681 21166173025450237903465261)
              ·
                refine ⟨7937314884543839213799473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21166173025450237903465261 7937314884543839213799473)
                ·
                  refine ⟨5952986163407879410349605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7937314884543839213799473 5952986163407879410349605)
                  ·
                    refine ⟨1116184905638977389440551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5952986163407879410349605 1116184905638977389440551)
                    ·
                      rfl

theorem cell23_6521287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_6521287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521287 prefixEnd_6521287 := by exact prefixLift 6521287
  have htrace : WordTrace (prefixWord ++ tailWord_6521287) baseStart_6521287 baseEnd_6521287 := by
    simpa [prefixWord, tailWord_6521287, baseEnd_6521287] using wordTrace_append hprefix tailTrace_6521287
  have hstable : (prefixWord ++ tailWord_6521287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521287).length < 2 ^ (prefixWord ++ tailWord_6521287).sum := by decide
  have hdescent : baseEnd_6521287 < baseStart_6521287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521298 : List Nat := [3, 2, 2, 4, 1, 2, 1, 1, 2, 3, 2]
def baseStart_6521298 : Nat := 118140960795 + 6521298 * 2 ^ 59
def prefixEnd_6521298 : Nat := 4983230072969 + 3 ^ 40 * 6521298 * 2
def baseEnd_6521298 : Nat := 3348560365204131625284103

theorem tailTrace_6521298 : CollatzResearch.WordTrace tailWord_6521298 prefixEnd_6521298 3348560365204131625284103 := by
  unfold tailWord_6521298
  simp only [CollatzResearch.WordTrace]
  refine ⟨59462819582114642468355137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158567518885639046582280365 59462819582114642468355137)
  ·
    refine ⟨44597114686585981851266353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59462819582114642468355137 44597114686585981851266353)
    ·
      refine ⟨33447836014939486388449765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44597114686585981851266353 33447836014939486388449765)
      ·
        refine ⟨6271469252801153697834331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33447836014939486388449765 6271469252801153697834331)
        ·
          refine ⟨9407203879201730546751497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6271469252801153697834331 9407203879201730546751497)
          ·
            refine ⟨7055402909401297910063623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9407203879201730546751497 7055402909401297910063623)
            ·
              refine ⟨10583104364101946865095435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7055402909401297910063623 10583104364101946865095435)
              ·
                refine ⟨15874656546152920297643153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10583104364101946865095435 15874656546152920297643153)
                ·
                  refine ⟨11905992409614690223232365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15874656546152920297643153 11905992409614690223232365)
                  ·
                    refine ⟨4464747153605508833712137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11905992409614690223232365 4464747153605508833712137)
                    ·
                      refine ⟨3348560365204131625284103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4464747153605508833712137 3348560365204131625284103)
                      ·
                        rfl

theorem cell23_6521298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_6521298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521298 prefixEnd_6521298 := by exact prefixLift 6521298
  have htrace : WordTrace (prefixWord ++ tailWord_6521298) baseStart_6521298 baseEnd_6521298 := by
    simpa [prefixWord, tailWord_6521298, baseEnd_6521298] using wordTrace_append hprefix tailTrace_6521298
  have hstable : (prefixWord ++ tailWord_6521298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521298).length < 2 ^ (prefixWord ++ tailWord_6521298).sum := by decide
  have hdescent : baseEnd_6521298 < baseStart_6521298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521311 : List Nat := [1, 1, 2, 3, 3, 2, 1, 5, 1, 2, 2]
def baseStart_6521311 : Nat := 118140960795 + 6521311 * 2 ^ 59
def prefixEnd_6521311 : Nat := 4983230072969 + 3 ^ 40 * 6521311 * 2
def baseEnd_6521311 : Nat := 3348567040452640074421543

theorem tailTrace_6521311 : CollatzResearch.WordTrace tailWord_6521311 prefixEnd_6521311 3348567040452640074421543 := by
  unfold tailWord_6521311
  simp only [CollatzResearch.WordTrace]
  refine ⟨237851752477411473093643787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158567834984940982062429191 237851752477411473093643787)
  ·
    refine ⟨356777628716117209640465681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237851752477411473093643787 356777628716117209640465681)
    ·
      refine ⟨267583221537087907230349261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356777628716117209640465681 267583221537087907230349261)
      ·
        refine ⟨100343708076407965211380973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267583221537087907230349261 100343708076407965211380973)
        ·
          refine ⟨37628890528652986954267865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100343708076407965211380973 37628890528652986954267865)
          ·
            refine ⟨28221667896489740215700899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37628890528652986954267865 28221667896489740215700899)
            ·
              refine ⟨42332501844734610323551349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28221667896489740215700899 42332501844734610323551349)
              ·
                refine ⟨3968672047943869717832939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42332501844734610323551349 3968672047943869717832939)
                ·
                  refine ⟨5953008071915804576749409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3968672047943869717832939 5953008071915804576749409)
                  ·
                    refine ⟨4464756053936853432562057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5953008071915804576749409 4464756053936853432562057)
                    ·
                      refine ⟨3348567040452640074421543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4464756053936853432562057 3348567040452640074421543)
                      ·
                        rfl

theorem cell23_6521311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 1, 2, 2].length) (baseStart_6521311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521311 prefixEnd_6521311 := by exact prefixLift 6521311
  have htrace : WordTrace (prefixWord ++ tailWord_6521311) baseStart_6521311 baseEnd_6521311 := by
    simpa [prefixWord, tailWord_6521311, baseEnd_6521311] using wordTrace_append hprefix tailTrace_6521311
  have hstable : (prefixWord ++ tailWord_6521311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521311).length < 2 ^ (prefixWord ++ tailWord_6521311).sum := by decide
  have hdescent : baseEnd_6521311 < baseStart_6521311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521337 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 5, 3, 2]
def baseStart_6521337 : Nat := 118140960795 + 6521337 * 2 ^ 59
def prefixEnd_6521337 : Nat := 4983230072969 + 3 ^ 40 * 6521337 * 2
def baseEnd_6521337 : Nat := 3348580390949656972696423

theorem tailTrace_6521337 : CollatzResearch.WordTrace tailWord_6521337 prefixEnd_6521337 3348580390949656972696423 := by
  unfold tailWord_6521337
  simp only [CollatzResearch.WordTrace]
  refine ⟨237852700775317279534090265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158568467183544853022726843 237852700775317279534090265)
  ·
    refine ⟨178389525581487959650567699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237852700775317279534090265 178389525581487959650567699)
    ·
      refine ⟨267584288372231939475851549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178389525581487959650567699 267584288372231939475851549)
      ·
        refine ⟨100344108139586977303444331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267584288372231939475851549 100344108139586977303444331)
        ·
          refine ⟨150516162209380465955166497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100344108139586977303444331 150516162209380465955166497)
          ·
            refine ⟨112887121657035349466374873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150516162209380465955166497 112887121657035349466374873)
            ·
              refine ⟨84665341242776512099781155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112887121657035349466374873 84665341242776512099781155)
              ·
                refine ⟨126998011864164768149671733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84665341242776512099781155 126998011864164768149671733)
                ·
                  refine ⟨11906063612265447014031725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126998011864164768149671733 11906063612265447014031725)
                  ·
                    refine ⟨4464773854599542630261897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11906063612265447014031725 4464773854599542630261897)
                    ·
                      refine ⟨3348580390949656972696423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4464773854599542630261897 3348580390949656972696423)
                      ·
                        rfl

theorem cell23_6521337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_6521337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521337 prefixEnd_6521337 := by exact prefixLift 6521337
  have htrace : WordTrace (prefixWord ++ tailWord_6521337) baseStart_6521337 baseEnd_6521337 := by
    simpa [prefixWord, tailWord_6521337, baseEnd_6521337] using wordTrace_append hprefix tailTrace_6521337
  have hstable : (prefixWord ++ tailWord_6521337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521337).length < 2 ^ (prefixWord ++ tailWord_6521337).sum := by decide
  have hdescent : baseEnd_6521337 < baseStart_6521337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521370 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5]
def baseStart_6521370 : Nat := 118140960795 + 6521370 * 2 ^ 59
def prefixEnd_6521370 : Nat := 4983230072969 + 3 ^ 40 * 6521370 * 2
def baseEnd_6521370 : Nat := 3348597335811255343583771

theorem tailTrace_6521370 : CollatzResearch.WordTrace tailWord_6521370 prefixEnd_6521370 3348597335811255343583771 := by
  unfold tailWord_6521370
  simp only [CollatzResearch.WordTrace]
  refine ⟨59463476096049431542510391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158569269589465150780027709 59463476096049431542510391)
  ·
    refine ⟨89195214144074147313765587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59463476096049431542510391 89195214144074147313765587)
    ·
      refine ⟨133792821216111220970648381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89195214144074147313765587 133792821216111220970648381)
      ·
        refine ⟨50172307956041707863993143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133792821216111220970648381 50172307956041707863993143)
        ·
          refine ⟨75258461934062561795989715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50172307956041707863993143 75258461934062561795989715)
          ·
            refine ⟨112887692901093842693984573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75258461934062561795989715 112887692901093842693984573)
            ·
              refine ⟨42332884837910191010244215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112887692901093842693984573 42332884837910191010244215)
              ·
                refine ⟨63499327256865286515366323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42332884837910191010244215 63499327256865286515366323)
                ·
                  refine ⟨95248990885297929773049485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63499327256865286515366323 95248990885297929773049485)
                  ·
                    refine ⟨35718371581986723664893557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95248990885297929773049485 35718371581986723664893557)
                    ·
                      refine ⟨3348597335811255343583771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35718371581986723664893557 3348597335811255343583771)
                      ·
                        rfl

theorem cell23_6521370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_6521370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521370 prefixEnd_6521370 := by exact prefixLift 6521370
  have htrace : WordTrace (prefixWord ++ tailWord_6521370) baseStart_6521370 baseEnd_6521370 := by
    simpa [prefixWord, tailWord_6521370, baseEnd_6521370] using wordTrace_append hprefix tailTrace_6521370
  have hstable : (prefixWord ++ tailWord_6521370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521370).length < 2 ^ (prefixWord ++ tailWord_6521370).sum := by decide
  have hdescent : baseEnd_6521370 < baseStart_6521370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521401 : List Nat := [1, 2, 1, 5, 1, 1, 3, 3, 2, 2, 2]
def baseStart_6521401 : Nat := 118140960795 + 6521401 * 2 ^ 59
def prefixEnd_6521401 : Nat := 4983230072969 + 3 ^ 40 * 6521401 * 2
def baseEnd_6521401 : Nat := 3348613253711544722296129

theorem tailTrace_6521401 : CollatzResearch.WordTrace tailWord_6521401 prefixEnd_6521401 3348613253711544722296129 := by
  unfold tailWord_6521401
  simp only [CollatzResearch.WordTrace]
  refine ⟨237855035047085418464420057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158570023364723612309613371 237855035047085418464420057)
  ·
    refine ⟨178391276285314063848315043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237855035047085418464420057 178391276285314063848315043)
    ·
      refine ⟨267586914427971095772472565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178391276285314063848315043 267586914427971095772472565)
      ·
        refine ⟨25086273227622290228669303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 267586914427971095772472565 25086273227622290228669303)
        ·
          refine ⟨37629409841433435343003955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25086273227622290228669303 37629409841433435343003955)
          ·
            refine ⟨56444114762150153014505933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37629409841433435343003955 56444114762150153014505933)
            ·
              refine ⟨21166543035806307380439725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56444114762150153014505933 21166543035806307380439725)
              ·
                refine ⟨7937453638427365267664897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21166543035806307380439725 7937453638427365267664897)
                ·
                  refine ⟨5953090228820523950748673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7937453638427365267664897 5953090228820523950748673)
                  ·
                    refine ⟨4464817671615392963061505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5953090228820523950748673 4464817671615392963061505)
                    ·
                      refine ⟨3348613253711544722296129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4464817671615392963061505 3348613253711544722296129)
                      ·
                        rfl

theorem cell23_6521401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_6521401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521401 prefixEnd_6521401 := by exact prefixLift 6521401
  have htrace : WordTrace (prefixWord ++ tailWord_6521401) baseStart_6521401 baseEnd_6521401 := by
    simpa [prefixWord, tailWord_6521401, baseEnd_6521401] using wordTrace_append hprefix tailTrace_6521401
  have hstable : (prefixWord ++ tailWord_6521401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521401).length < 2 ^ (prefixWord ++ tailWord_6521401).sum := by decide
  have hdescent : baseEnd_6521401 < baseStart_6521401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521441 : List Nat := [1, 2, 3, 1, 1, 6, 2, 2, 5]
def baseStart_6521441 : Nat := 118140960795 + 6521441 * 2 ^ 59
def prefixEnd_6521441 : Nat := 4983230072969 + 3 ^ 40 * 6521441 * 2
def baseEnd_6521441 : Nat := 372070421437524951755105

theorem tailTrace_6521441 : CollatzResearch.WordTrace tailWord_6521441 prefixEnd_6521441 372070421437524951755105 := by
  unfold tailWord_6521441
  simp only [CollatzResearch.WordTrace]
  refine ⟨237856493966940505295876177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158570995977960336863917451 237856493966940505295876177)
  ·
    refine ⟨178392370475205378971907133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237856493966940505295876177 178392370475205378971907133)
    ·
      refine ⟨66897138928202017114465175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178392370475205378971907133 66897138928202017114465175)
      ·
        refine ⟨100345708392303025671697763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66897138928202017114465175 100345708392303025671697763)
        ·
          refine ⟨150518562588454538507546645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100345708392303025671697763 150518562588454538507546645)
          ·
            refine ⟨7055557621333806492541249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 150518562588454538507546645 7055557621333806492541249)
            ·
              refine ⟨5291668216000354869405937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7055557621333806492541249 5291668216000354869405937)
              ·
                refine ⟨3968751162000266152054453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5291668216000354869405937 3968751162000266152054453)
                ·
                  refine ⟨372070421437524951755105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3968751162000266152054453 372070421437524951755105)
                  ·
                    rfl

theorem cell23_6521441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 5].length) (baseStart_6521441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521441 prefixEnd_6521441 := by exact prefixLift 6521441
  have htrace : WordTrace (prefixWord ++ tailWord_6521441) baseStart_6521441 baseEnd_6521441 := by
    simpa [prefixWord, tailWord_6521441, baseEnd_6521441] using wordTrace_append hprefix tailTrace_6521441
  have hstable : (prefixWord ++ tailWord_6521441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521441).length < 2 ^ (prefixWord ++ tailWord_6521441).sum := by decide
  have hdescent : baseEnd_6521441 < baseStart_6521441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521501 : List Nat := [1, 4, 2, 1, 1, 1, 4, 4, 1, 4]
def baseStart_6521501 : Nat := 118140960795 + 6521501 * 2 ^ 59
def prefixEnd_6521501 : Nat := 4983230072969 + 3 ^ 40 * 6521501 * 2
def baseEnd_6521501 : Nat := 1116221533925664777015223

theorem tailTrace_6521501 : CollatzResearch.WordTrace tailWord_6521501 prefixEnd_6521501 1116221533925664777015223 := by
  unfold tailWord_6521501
  simp only [CollatzResearch.WordTrace]
  refine ⟨237858682346723135543060357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158572454897815423695373571 237858682346723135543060357)
  ·
    refine ⟨44598502940010587914323817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237858682346723135543060357 44598502940010587914323817)
    ·
      refine ⟨33448877205007940935742863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44598502940010587914323817 33448877205007940935742863)
      ·
        refine ⟨50173315807511911403614295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33448877205007940935742863 50173315807511911403614295)
        ·
          refine ⟨75259973711267867105421443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50173315807511911403614295 75259973711267867105421443)
          ·
            refine ⟨112889960566901800658132165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75259973711267867105421443 112889960566901800658132165)
            ·
              refine ⟨21166867606294087623399781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112889960566901800658132165 21166867606294087623399781)
              ·
                refine ⟨3968787676180141429387459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21166867606294087623399781 3968787676180141429387459)
                ·
                  refine ⟨5953181514270212144081189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3968787676180141429387459 5953181514270212144081189)
                  ·
                    refine ⟨1116221533925664777015223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5953181514270212144081189 1116221533925664777015223)
                    ·
                      rfl

theorem cell23_6521501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_6521501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521501 prefixEnd_6521501 := by exact prefixLift 6521501
  have htrace : WordTrace (prefixWord ++ tailWord_6521501) baseStart_6521501 baseEnd_6521501 := by
    simpa [prefixWord, tailWord_6521501, baseEnd_6521501] using wordTrace_append hprefix tailTrace_6521501
  have hstable : (prefixWord ++ tailWord_6521501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521501).length < 2 ^ (prefixWord ++ tailWord_6521501).sum := by decide
  have hdescent : baseEnd_6521501 < baseStart_6521501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521544 : List Nat := [2, 1, 3, 1, 2, 3, 2, 3, 1, 5]
def baseStart_6521544 : Nat := 118140960795 + 6521544 * 2 ^ 59
def prefixEnd_6521544 : Nat := 4983230072969 + 3 ^ 40 * 6521544 * 2
def baseEnd_6521544 : Nat := 1116228893815045887602657

theorem tailTrace_6521544 : CollatzResearch.WordTrace tailWord_6521544 prefixEnd_6521544 1116228893815045887602657 := by
  unfold tailWord_6521544
  simp only [CollatzResearch.WordTrace]
  refine ⟨118930125342783676943437843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158573500457044902591250457 118930125342783676943437843)
  ·
    refine ⟨178395188014175515415156765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118930125342783676943437843 178395188014175515415156765)
    ·
      refine ⟨66898195505315818280683787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178395188014175515415156765 66898195505315818280683787)
      ·
        refine ⟨100347293257973727421025681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66898195505315818280683787 100347293257973727421025681)
        ·
          refine ⟨75260469943480295565769261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100347293257973727421025681 75260469943480295565769261)
          ·
            refine ⟨28222676228805110837163473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75260469943480295565769261 28222676228805110837163473)
            ·
              refine ⟨21167007171603833127872605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28222676228805110837163473 21167007171603833127872605)
              ·
                refine ⟨7937627689351437422952227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21167007171603833127872605 7937627689351437422952227)
                ·
                  refine ⟨11906441534027156134428341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7937627689351437422952227 11906441534027156134428341)
                  ·
                    refine ⟨1116228893815045887602657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11906441534027156134428341 1116228893815045887602657)
                    ·
                      rfl

theorem cell23_6521544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_6521544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521544 prefixEnd_6521544 := by exact prefixLift 6521544
  have htrace : WordTrace (prefixWord ++ tailWord_6521544) baseStart_6521544 baseEnd_6521544 := by
    simpa [prefixWord, tailWord_6521544, baseEnd_6521544] using wordTrace_append hprefix tailTrace_6521544
  have hstable : (prefixWord ++ tailWord_6521544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521544).length < 2 ^ (prefixWord ++ tailWord_6521544).sum := by decide
  have hdescent : baseEnd_6521544 < baseStart_6521544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521547 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 4]
def baseStart_6521547 : Nat := 118140960795 + 6521547 * 2 ^ 59
def prefixEnd_6521547 : Nat := 4983230072969 + 3 ^ 40 * 6521547 * 2
def baseEnd_6521547 : Nat := 3348688221887101151070457

theorem tailTrace_6521547 : CollatzResearch.WordTrace tailWord_6521547 prefixEnd_6521547 3348688221887101151070457 := by
  unfold tailWord_6521547
  simp only [CollatzResearch.WordTrace]
  refine ⟨237860360104556485399234895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158573573403037656932823263 237860360104556485399234895)
  ·
    refine ⟨356790540156834728098852343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237860360104556485399234895 356790540156834728098852343)
    ·
      refine ⟨535185810235252092148278515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356790540156834728098852343 535185810235252092148278515)
      ·
        refine ⟨802778715352878138222417773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535185810235252092148278515 802778715352878138222417773)
        ·
          refine ⟨301042018257329301833406665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 802778715352878138222417773 301042018257329301833406665)
          ·
            refine ⟨225781513692996976375054999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301042018257329301833406665 225781513692996976375054999)
            ·
              refine ⟨338672270539495464562582499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225781513692996976375054999 338672270539495464562582499)
              ·
                refine ⟨508008405809243196843873749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338672270539495464562582499 508008405809243196843873749)
                ·
                  refine ⟨11906447011154137426028291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 508008405809243196843873749 11906447011154137426028291)
                  ·
                    refine ⟨17859670516731206139042437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11906447011154137426028291 17859670516731206139042437)
                    ·
                      refine ⟨3348688221887101151070457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17859670516731206139042437 3348688221887101151070457)
                      ·
                        rfl

theorem cell23_6521547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 4].length) (baseStart_6521547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521547 prefixEnd_6521547 := by exact prefixLift 6521547
  have htrace : WordTrace (prefixWord ++ tailWord_6521547) baseStart_6521547 baseEnd_6521547 := by
    simpa [prefixWord, tailWord_6521547, baseEnd_6521547] using wordTrace_append hprefix tailTrace_6521547
  have hstable : (prefixWord ++ tailWord_6521547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521547).length < 2 ^ (prefixWord ++ tailWord_6521547).sum := by decide
  have hdescent : baseEnd_6521547 < baseStart_6521547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521577 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 1, 1, 6]
def baseStart_6521577 : Nat := 118140960795 + 6521577 * 2 ^ 59
def prefixEnd_6521577 : Nat := 4983230072969 + 3 ^ 40 * 6521577 * 2
def baseEnd_6521577 : Nat := 3348703626306736033695319

theorem tailTrace_6521577 : CollatzResearch.WordTrace tailWord_6521577 prefixEnd_6521577 3348703626306736033695319 := by
  unfold tailWord_6521577
  simp only [CollatzResearch.WordTrace]
  refine ⟨237861454294447800522826985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158574302862965200348551323 237861454294447800522826985)
  ·
    refine ⟨178396090720835850392120239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237861454294447800522826985 178396090720835850392120239)
    ·
      refine ⟨267594136081253775588180359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178396090720835850392120239 267594136081253775588180359)
      ·
        refine ⟨401391204121880663382270539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267594136081253775588180359 401391204121880663382270539)
        ·
          refine ⟨602086806182820995073405809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401391204121880663382270539 602086806182820995073405809)
          ·
            refine ⟨451565104637115746305054357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602086806182820995073405809 451565104637115746305054357)
            ·
              refine ⟨21167114279864800608049423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 451565104637115746305054357 21167114279864800608049423)
              ·
                refine ⟨31750671419797200912074135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21167114279864800608049423 31750671419797200912074135)
                ·
                  refine ⟨47626007129695801368111203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31750671419797200912074135 47626007129695801368111203)
                  ·
                    refine ⟨71439010694543702052166805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47626007129695801368111203 71439010694543702052166805)
                    ·
                      refine ⟨3348703626306736033695319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71439010694543702052166805 3348703626306736033695319)
                      ·
                        rfl

theorem cell23_6521577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_6521577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521577 prefixEnd_6521577 := by exact prefixLift 6521577
  have htrace : WordTrace (prefixWord ++ tailWord_6521577) baseStart_6521577 baseEnd_6521577 := by
    simpa [prefixWord, tailWord_6521577, baseEnd_6521577] using wordTrace_append hprefix tailTrace_6521577
  have hstable : (prefixWord ++ tailWord_6521577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521577).length < 2 ^ (prefixWord ++ tailWord_6521577).sum := by decide
  have hdescent : baseEnd_6521577 < baseStart_6521577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521584 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 3]
def baseStart_6521584 : Nat := 118140960795 + 6521584 * 2 ^ 59
def prefixEnd_6521584 : Nat := 4983230072969 + 3 ^ 40 * 6521584 * 2
def baseEnd_6521584 : Nat := 3348707220671317506307787

theorem tailTrace_6521584 : CollatzResearch.WordTrace tailWord_6521584 prefixEnd_6521584 3348707220671317506307787 := by
  unfold tailWord_6521584
  simp only [CollatzResearch.WordTrace]
  refine ⟨118930854802711220359165903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158574473070281627145554537 118930854802711220359165903)
  ·
    refine ⟨178396282204066830538748855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118930854802711220359165903 178396282204066830538748855)
    ·
      refine ⟨267594423306100245808123283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178396282204066830538748855 267594423306100245808123283)
      ·
        refine ⟨401391634959150368712184925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267594423306100245808123283 401391634959150368712184925)
        ·
          refine ⟨150521863109681388267069347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401391634959150368712184925 150521863109681388267069347)
          ·
            refine ⟨225782794664522082400604021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150521863109681388267069347 225782794664522082400604021)
            ·
              refine ⟨21167136999798945225056627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 225782794664522082400604021 21167136999798945225056627)
              ·
                refine ⟨31750705499698417837584941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21167136999798945225056627 31750705499698417837584941)
                ·
                  refine ⟨11906514562386906689094353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31750705499698417837584941 11906514562386906689094353)
                  ·
                    refine ⟨8929885921790180016820765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11906514562386906689094353 8929885921790180016820765)
                    ·
                      refine ⟨3348707220671317506307787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8929885921790180016820765 3348707220671317506307787)
                      ·
                        rfl

theorem cell23_6521584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 3].length) (baseStart_6521584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521584 prefixEnd_6521584 := by exact prefixLift 6521584
  have htrace : WordTrace (prefixWord ++ tailWord_6521584) baseStart_6521584 baseEnd_6521584 := by
    simpa [prefixWord, tailWord_6521584, baseEnd_6521584] using wordTrace_append hprefix tailTrace_6521584
  have hstable : (prefixWord ++ tailWord_6521584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521584).length < 2 ^ (prefixWord ++ tailWord_6521584).sum := by decide
  have hdescent : baseEnd_6521584 < baseStart_6521584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521614 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3]
def baseStart_6521614 : Nat := 118140960795 + 6521614 * 2 ^ 59
def prefixEnd_6521614 : Nat := 4983230072969 + 3 ^ 40 * 6521614 * 2
def baseEnd_6521614 : Nat := 3348722625090952388932649

theorem tailTrace_6521614 : CollatzResearch.WordTrace tailWord_6521614 prefixEnd_6521614 3348722625090952388932649 := by
  unfold tailWord_6521614
  simp only [CollatzResearch.WordTrace]
  refine ⟨29732850474414219480240487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158575202530209170561282597 29732850474414219480240487)
  ·
    refine ⟨44599275711621329220360731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29732850474414219480240487 44599275711621329220360731)
    ·
      refine ⟨66898913567431993830541097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44599275711621329220360731 66898913567431993830541097)
      ·
        refine ⟨50174185175573995372905823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66898913567431993830541097 50174185175573995372905823)
        ·
          refine ⟨75261277763360993059358735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50174185175573995372905823 75261277763360993059358735)
          ·
            refine ⟨112891916645041489589038103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75261277763360993059358735 112891916645041489589038103)
            ·
              refine ⟨169337874967562234383557155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112891916645041489589038103 169337874967562234383557155)
              ·
                refine ⟨254006812451343351575335733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169337874967562234383557155 254006812451343351575335733)
                ·
                  refine ⟨23813138667313439210187725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 254006812451343351575335733 23813138667313439210187725)
                  ·
                    refine ⟨8929927000242539703820397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23813138667313439210187725 8929927000242539703820397)
                    ·
                      refine ⟨3348722625090952388932649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8929927000242539703820397 3348722625090952388932649)
                      ·
                        rfl

theorem cell23_6521614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_6521614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521614 prefixEnd_6521614 := by exact prefixLift 6521614
  have htrace : WordTrace (prefixWord ++ tailWord_6521614) baseStart_6521614 baseEnd_6521614 := by
    simpa [prefixWord, tailWord_6521614, baseEnd_6521614] using wordTrace_append hprefix tailTrace_6521614
  have hstable : (prefixWord ++ tailWord_6521614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521614).length < 2 ^ (prefixWord ++ tailWord_6521614).sum := by decide
  have hdescent : baseEnd_6521614 < baseStart_6521614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521617 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 2, 7]
def baseStart_6521617 : Nat := 118140960795 + 6521617 * 2 ^ 59
def prefixEnd_6521617 : Nat := 4983230072969 + 3 ^ 40 * 6521617 * 2
def baseEnd_6521617 : Nat := 1116241388510971959065045

theorem tailTrace_6521617 : CollatzResearch.WordTrace tailWord_6521617 prefixEnd_6521617 1116241388510971959065045 := by
  unfold tailWord_6521617
  simp only [CollatzResearch.WordTrace]
  refine ⟨237862913214302887354283105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158575275476201924902855403 237862913214302887354283105)
  ·
    refine ⟨178397184910727165515712329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237862913214302887354283105 178397184910727165515712329)
    ·
      refine ⟨133797888683045374136784247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178397184910727165515712329 133797888683045374136784247)
      ·
        refine ⟨200696833024568061205176371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133797888683045374136784247 200696833024568061205176371)
        ·
          refine ⟨301045249536852091807764557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200696833024568061205176371 301045249536852091807764557)
          ·
            refine ⟨112891968576319534427911709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301045249536852091807764557 112891968576319534427911709)
            ·
              refine ⟨42334488216119825410466891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112891968576319534427911709 42334488216119825410466891)
              ·
                refine ⟨63501732324179738115700337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42334488216119825410466891 63501732324179738115700337)
                ·
                  refine ⟨47626299243134803586775253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63501732324179738115700337 47626299243134803586775253)
                  ·
                    refine ⟨1116241388510971959065045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47626299243134803586775253 1116241388510971959065045)
                    ·
                      rfl

theorem cell23_6521617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_6521617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521617 prefixEnd_6521617 := by exact prefixLift 6521617
  have htrace : WordTrace (prefixWord ++ tailWord_6521617) baseStart_6521617 baseEnd_6521617 := by
    simpa [prefixWord, tailWord_6521617, baseEnd_6521617] using wordTrace_append hprefix tailTrace_6521617
  have hstable : (prefixWord ++ tailWord_6521617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521617).length < 2 ^ (prefixWord ++ tailWord_6521617).sum := by decide
  have hdescent : baseEnd_6521617 < baseStart_6521617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521631 : List Nat := [1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 3]
def baseStart_6521631 : Nat := 118140960795 + 6521631 * 2 ^ 59
def prefixEnd_6521631 : Nat := 4983230072969 + 3 ^ 40 * 6521631 * 2
def baseEnd_6521631 : Nat := 3348731354262078822420071

theorem tailTrace_6521631 : CollatzResearch.WordTrace tailWord_6521631 prefixEnd_6521631 3348731354262078822420071 := by
  unfold tailWord_6521631
  simp only [CollatzResearch.WordTrace]
  refine ⟨237863423836252167745292747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158575615890834778496861831 237863423836252167745292747)
  ·
    refine ⟨356795135754378251617939121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237863423836252167745292747 356795135754378251617939121)
    ·
      refine ⟨267596351815783688713454341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356795135754378251617939121 267596351815783688713454341)
      ·
        refine ⟨50174315965459441633772689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267596351815783688713454341 50174315965459441633772689)
        ·
          refine ⟨37630736974094581225329517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50174315965459441633772689 37630736974094581225329517)
          ·
            refine ⟨14111526365285467959498569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37630736974094581225329517 14111526365285467959498569)
            ·
              refine ⟨10583644773964100969623927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14111526365285467959498569 10583644773964100969623927)
              ·
                refine ⟨15875467160946151454435891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10583644773964100969623927 15875467160946151454435891)
                ·
                  refine ⟨23813200741419227181653837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15875467160946151454435891 23813200741419227181653837)
                  ·
                    refine ⟨8929950278032210193120189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23813200741419227181653837 8929950278032210193120189)
                    ·
                      refine ⟨3348731354262078822420071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8929950278032210193120189 3348731354262078822420071)
                      ·
                        rfl

theorem cell23_6521631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_6521631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521631 prefixEnd_6521631 := by exact prefixLift 6521631
  have htrace : WordTrace (prefixWord ++ tailWord_6521631) baseStart_6521631 baseEnd_6521631 := by
    simpa [prefixWord, tailWord_6521631, baseEnd_6521631] using wordTrace_append hprefix tailTrace_6521631
  have hstable : (prefixWord ++ tailWord_6521631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521631).length < 2 ^ (prefixWord ++ tailWord_6521631).sum := by decide
  have hdescent : baseEnd_6521631 < baseStart_6521631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521647 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 6, 6]
def baseStart_6521647 : Nat := 118140960795 + 6521647 * 2 ^ 59
def prefixEnd_6521647 : Nat := 4983230072969 + 3 ^ 40 * 6521647 * 2
def baseEnd_6521647 : Nat := 1116246523317516919939999

theorem tailTrace_6521647 : CollatzResearch.WordTrace tailWord_6521647 prefixEnd_6521647 1116246523317516919939999 := by
  unfold tailWord_6521647
  simp only [CollatzResearch.WordTrace]
  refine ⟨237864007404194202477875195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158576004936129468318583463 237864007404194202477875195)
  ·
    refine ⟨356796011106291303716812793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237864007404194202477875195 356796011106291303716812793)
    ·
      refine ⟨267597008329718477787609595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356796011106291303716812793 267597008329718477787609595)
      ·
        refine ⟨401395512494577716681414393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267597008329718477787609595 401395512494577716681414393)
        ·
          refine ⟨301046634370933287511060795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401395512494577716681414393 301046634370933287511060795)
          ·
            refine ⟨451569951556399931266591193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301046634370933287511060795 451569951556399931266591193)
            ·
              refine ⟨338677463667299948449943395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451569951556399931266591193 338677463667299948449943395)
              ·
                refine ⟨508016195500949922674915093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338677463667299948449943395 508016195500949922674915093)
                ·
                  refine ⟨23813259164107027625386645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 508016195500949922674915093 23813259164107027625386645)
                  ·
                    refine ⟨1116246523317516919939999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23813259164107027625386645 1116246523317516919939999)
                    ·
                      rfl

theorem cell23_6521647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 6].length) (baseStart_6521647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521647 prefixEnd_6521647 := by exact prefixLift 6521647
  have htrace : WordTrace (prefixWord ++ tailWord_6521647) baseStart_6521647 baseEnd_6521647 := by
    simpa [prefixWord, tailWord_6521647, baseEnd_6521647] using wordTrace_append hprefix tailTrace_6521647
  have hstable : (prefixWord ++ tailWord_6521647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521647).length < 2 ^ (prefixWord ++ tailWord_6521647).sum := by decide
  have hdescent : baseEnd_6521647 < baseStart_6521647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521652 : List Nat := [2, 5, 1, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_6521652 : Nat := 118140960795 + 6521652 * 2 ^ 59
def prefixEnd_6521652 : Nat := 4983230072969 + 3 ^ 40 * 6521652 * 2
def baseEnd_6521652 : Nat := 3348742137355823240257475

theorem tailTrace_6521652 : CollatzResearch.WordTrace tailWord_6521652 prefixEnd_6521652 3348742137355823240257475 := by
  unfold tailWord_6521652
  simp only [CollatzResearch.WordTrace]
  refine ⟨118932094884588044165903605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158576126512784058887871473 118932094884588044165903605)
  ·
    refine ⟨11149883895430129140553463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118932094884588044165903605 11149883895430129140553463)
    ·
      refine ⟨16724825843145193710830195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11149883895430129140553463 16724825843145193710830195)
      ·
        refine ⟨25087238764717790566245293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16724825843145193710830195 25087238764717790566245293)
        ·
          refine ⟨9407714536769171462341985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25087238764717790566245293 9407714536769171462341985)
          ·
            refine ⟨7055785902576878596756489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9407714536769171462341985 7055785902576878596756489)
            ·
              refine ⟨5291839426932658947567367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7055785902576878596756489 5291839426932658947567367)
              ·
                refine ⟨7937759140398988421351051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5291839426932658947567367 7937759140398988421351051)
                ·
                  refine ⟨11906638710598482632026577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7937759140398988421351051 11906638710598482632026577)
                  ·
                    refine ⟨8929979032948861974019933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11906638710598482632026577 8929979032948861974019933)
                    ·
                      refine ⟨3348742137355823240257475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8929979032948861974019933 3348742137355823240257475)
                      ·
                        rfl

theorem cell23_6521652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_6521652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521652 prefixEnd_6521652 := by exact prefixLift 6521652
  have htrace : WordTrace (prefixWord ++ tailWord_6521652) baseStart_6521652 baseEnd_6521652 := by
    simpa [prefixWord, tailWord_6521652, baseEnd_6521652] using wordTrace_append hprefix tailTrace_6521652
  have hstable : (prefixWord ++ tailWord_6521652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521652).length < 2 ^ (prefixWord ++ tailWord_6521652).sum := by decide
  have hdescent : baseEnd_6521652 < baseStart_6521652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521665 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_6521665 : Nat := 118140960795 + 6521665 * 2 ^ 59
def prefixEnd_6521665 : Nat := 4983230072969 + 3 ^ 40 * 6521665 * 2
def baseEnd_6521665 : Nat := 3348748812604331689394915

theorem tailTrace_6521665 : CollatzResearch.WordTrace tailWord_6521665 prefixEnd_6521665 3348748812604331689394915 := by
  unfold tailWord_6521665
  simp only [CollatzResearch.WordTrace]
  refine ⟨237864663918128991552030449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158576442612085994368020299 237864663918128991552030449)
  ·
    refine ⟨178398497938596743664022837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237864663918128991552030449 178398497938596743664022837)
    ·
      refine ⟨16724859181743444718502141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178398497938596743664022837 16724859181743444718502141)
      ·
        refine ⟨6271822193153791769438303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16724859181743444718502141 6271822193153791769438303)
        ·
          refine ⟨9407733289730687654157455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6271822193153791769438303 9407733289730687654157455)
          ·
            refine ⟨14111599934596031481236183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9407733289730687654157455 14111599934596031481236183)
            ·
              refine ⟨21167399901894047221854275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14111599934596031481236183 21167399901894047221854275)
              ·
                refine ⟨31751099852841070832781413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21167399901894047221854275 31751099852841070832781413)
                ·
                  refine ⟨5953331222407700781146515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31751099852841070832781413 5953331222407700781146515)
                  ·
                    refine ⟨8929996833611551171719773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5953331222407700781146515 8929996833611551171719773)
                    ·
                      refine ⟨3348748812604331689394915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8929996833611551171719773 3348748812604331689394915)
                      ·
                        rfl

theorem cell23_6521665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_6521665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521665 prefixEnd_6521665 := by exact prefixLift 6521665
  have htrace : WordTrace (prefixWord ++ tailWord_6521665) baseStart_6521665 baseEnd_6521665 := by
    simpa [prefixWord, tailWord_6521665, baseEnd_6521665] using wordTrace_append hprefix tailTrace_6521665
  have hstable : (prefixWord ++ tailWord_6521665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521665).length < 2 ^ (prefixWord ++ tailWord_6521665).sum := by decide
  have hdescent : baseEnd_6521665 < baseStart_6521665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521674 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 2, 4, 3]
def baseStart_6521674 : Nat := 118140960795 + 6521674 * 2 ^ 59
def prefixEnd_6521674 : Nat := 4983230072969 + 3 ^ 40 * 6521674 * 2
def baseEnd_6521674 : Nat := 3348753433930222154182373

theorem tailTrace_6521674 : CollatzResearch.WordTrace tailWord_6521674 prefixEnd_6521674 3348753433930222154182373 := by
  unfold tailWord_6521674
  simp only [CollatzResearch.WordTrace]
  refine ⟨59466248043774096522277019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158576661450064257392738717 59466248043774096522277019)
  ·
    refine ⟨89199372065661144783415529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59466248043774096522277019 89199372065661144783415529)
    ·
      refine ⟨66899529049245858587561647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89199372065661144783415529 66899529049245858587561647)
      ·
        refine ⟨100349293573868787881342471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66899529049245858587561647 100349293573868787881342471)
        ·
          refine ⟨150523940360803181822013707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100349293573868787881342471 150523940360803181822013707)
          ·
            refine ⟨225785910541204772733020561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150523940360803181822013707 225785910541204772733020561)
            ·
              refine ⟨169339432905903579549765421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225785910541204772733020561 169339432905903579549765421)
              ·
                refine ⟨63502287339713842331162033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169339432905903579549765421 63502287339713842331162033)
                ·
                  refine ⟨47626715504785381748371525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63502287339713842331162033 47626715504785381748371525)
                  ·
                    refine ⟨8930009157147259077819661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47626715504785381748371525 8930009157147259077819661)
                    ·
                      refine ⟨3348753433930222154182373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8930009157147259077819661 3348753433930222154182373)
                      ·
                        rfl

theorem cell23_6521674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_6521674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521674 prefixEnd_6521674 := by exact prefixLift 6521674
  have htrace : WordTrace (prefixWord ++ tailWord_6521674) baseStart_6521674 baseEnd_6521674 := by
    simpa [prefixWord, tailWord_6521674, baseEnd_6521674] using wordTrace_append hprefix tailTrace_6521674
  have hstable : (prefixWord ++ tailWord_6521674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521674).length < 2 ^ (prefixWord ++ tailWord_6521674).sum := by decide
  have hdescent : baseEnd_6521674 < baseStart_6521674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521688 : List Nat := [2, 1, 2, 2, 1, 1, 1, 7, 2, 2, 2]
def baseStart_6521688 : Nat := 118140960795 + 6521688 * 2 ^ 59
def prefixEnd_6521688 : Nat := 4983230072969 + 3 ^ 40 * 6521688 * 2
def baseEnd_6521688 : Nat := 3348760622659385099407309

theorem tailTrace_6521688 : CollatzResearch.WordTrace tailWord_6521688 prefixEnd_6521688 3348760622659385099407309 := by
  unfold tailWord_6521688
  simp only [CollatzResearch.WordTrace]
  refine ⟨118932751398522833240058859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158577001864697110986745145 118932751398522833240058859)
  ·
    refine ⟨178399127097784249860088289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118932751398522833240058859 178399127097784249860088289)
    ·
      refine ⟨133799345323338187395066217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178399127097784249860088289 133799345323338187395066217)
      ·
        refine ⟨100349508992503640546299663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133799345323338187395066217 100349508992503640546299663)
        ·
          refine ⟨150524263488755460819449495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100349508992503640546299663 150524263488755460819449495)
          ·
            refine ⟨225786395233133191229174243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150524263488755460819449495 225786395233133191229174243)
            ·
              refine ⟨338679592849699786843761365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225786395233133191229174243 338679592849699786843761365)
              ·
                refine ⟨7937802957414838754150657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 338679592849699786843761365 7937802957414838754150657)
                ·
                  refine ⟨5953352218061129065612993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7937802957414838754150657 5953352218061129065612993)
                  ·
                    refine ⟨4465014163545846799209745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5953352218061129065612993 4465014163545846799209745)
                    ·
                      refine ⟨3348760622659385099407309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4465014163545846799209745 3348760622659385099407309)
                      ·
                        rfl

theorem cell23_6521688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_6521688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521688 prefixEnd_6521688 := by exact prefixLift 6521688
  have htrace : WordTrace (prefixWord ++ tailWord_6521688) baseStart_6521688 baseEnd_6521688 := by
    simpa [prefixWord, tailWord_6521688, baseEnd_6521688] using wordTrace_append hprefix tailTrace_6521688
  have hstable : (prefixWord ++ tailWord_6521688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521688).length < 2 ^ (prefixWord ++ tailWord_6521688).sum := by decide
  have hdescent : baseEnd_6521688 < baseStart_6521688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521731 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 2, 5, 2]
def baseStart_6521731 : Nat := 118140960795 + 6521731 * 2 ^ 59
def prefixEnd_6521731 : Nat := 4983230072969 + 3 ^ 40 * 6521731 * 2
def baseEnd_6521731 : Nat := 3348782702327528431169611

theorem tailTrace_6521731 : CollatzResearch.WordTrace tailWord_6521731 prefixEnd_6521731 3348782702327528431169611 := by
  unfold tailWord_6521731
  simp only [CollatzResearch.WordTrace]
  refine ⟨237867071135889884823933047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158578047423926589882622031 237867071135889884823933047)
  ·
    refine ⟨356800606703834827235899571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237867071135889884823933047 356800606703834827235899571)
    ·
      refine ⟨535200910055752240853849357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356800606703834827235899571 535200910055752240853849357)
      ·
        refine ⟨200700341270907090320193509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 535200910055752240853849357 200700341270907090320193509)
        ·
          refine ⟨37631313988295079435036283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200700341270907090320193509 37631313988295079435036283)
          ·
            refine ⟨56446970982442619152554425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37631313988295079435036283 56446970982442619152554425)
            ·
              refine ⟨42335228236831964364415819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56446970982442619152554425 42335228236831964364415819)
              ·
                refine ⟨63502842355247946546623729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42335228236831964364415819 63502842355247946546623729)
                ·
                  refine ⟨47627131766435959909967797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63502842355247946546623729 47627131766435959909967797)
                  ·
                    refine ⟨4465043603103371241559481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47627131766435959909967797 4465043603103371241559481)
                    ·
                      refine ⟨3348782702327528431169611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4465043603103371241559481 3348782702327528431169611)
                      ·
                        rfl

theorem cell23_6521731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 5, 2].length) (baseStart_6521731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521731 prefixEnd_6521731 := by exact prefixLift 6521731
  have htrace : WordTrace (prefixWord ++ tailWord_6521731) baseStart_6521731 baseEnd_6521731 := by
    simpa [prefixWord, tailWord_6521731, baseEnd_6521731] using wordTrace_append hprefix tailTrace_6521731
  have hstable : (prefixWord ++ tailWord_6521731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521731).length < 2 ^ (prefixWord ++ tailWord_6521731).sum := by decide
  have hdescent : baseEnd_6521731 < baseStart_6521731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521824 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 5]
def baseStart_6521824 : Nat := 118140960795 + 6521824 * 2 ^ 59
def prefixEnd_6521824 : Nat := 4983230072969 + 3 ^ 40 * 6521824 * 2
def baseEnd_6521824 : Nat := 3348830456028396567306683

theorem tailTrace_6521824 : CollatzResearch.WordTrace tailWord_6521824 prefixEnd_6521824 3348830456028396567306683 := by
  unfold tailWord_6521824
  simp only [CollatzResearch.WordTrace]
  refine ⟨118935231562276480853534263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158580308749701974471379017 118935231562276480853534263)
  ·
    refine ⟨178402847343414721280301395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118935231562276480853534263 178402847343414721280301395)
    ·
      refine ⟨267604271015122081920452093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178402847343414721280301395 267604271015122081920452093)
      ·
        refine ⟨100351601630670780720169535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267604271015122081920452093 100351601630670780720169535)
        ·
          refine ⟨150527402446006171080254303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100351601630670780720169535 150527402446006171080254303)
          ·
            refine ⟨225791103669009256620381455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150527402446006171080254303 225791103669009256620381455)
            ·
              refine ⟨338686655503513884930572183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225791103669009256620381455 338686655503513884930572183)
              ·
                refine ⟨508029983255270827395858275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338686655503513884930572183 508029983255270827395858275)
                ·
                  refine ⟨762044974882906241093787413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508029983255270827395858275 762044974882906241093787413)
                  ·
                    refine ⟨35720858197636230051271285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 762044974882906241093787413 35720858197636230051271285)
                    ·
                      refine ⟨3348830456028396567306683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35720858197636230051271285 3348830456028396567306683)
                      ·
                        rfl

theorem cell23_6521824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_6521824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521824 prefixEnd_6521824 := by exact prefixLift 6521824
  have htrace : WordTrace (prefixWord ++ tailWord_6521824) baseStart_6521824 baseEnd_6521824 := by
    simpa [prefixWord, tailWord_6521824, baseEnd_6521824] using wordTrace_append hprefix tailTrace_6521824
  have hstable : (prefixWord ++ tailWord_6521824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521824).length < 2 ^ (prefixWord ++ tailWord_6521824).sum := by decide
  have hdescent : baseEnd_6521824 < baseStart_6521824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521868 : List Nat := [2, 2, 1, 2, 3, 2, 1, 4, 1, 1, 4]
def baseStart_6521868 : Nat := 118140960795 + 6521868 * 2 ^ 59
def prefixEnd_6521868 : Nat := 4983230072969 + 3 ^ 40 * 6521868 * 2
def baseEnd_6521868 : Nat := 3348853049177194395156481

theorem tailTrace_6521868 : CollatzResearch.WordTrace tailWord_6521868 prefixEnd_6521868 3348853049177194395156481 := by
  unfold tailWord_6521868
  simp only [CollatzResearch.WordTrace]
  refine ⟨118936033968196778610835129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158581378624262371481113505 118936033968196778610835129)
  ·
    refine ⟨89202025476147583958126347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118936033968196778610835129 89202025476147583958126347)
    ·
      refine ⟨133803038214221375937189521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89202025476147583958126347 133803038214221375937189521)
      ·
        refine ⟨100352278660666031952892141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133803038214221375937189521 100352278660666031952892141)
        ·
          refine ⟨37632104497749761982334553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100352278660666031952892141 37632104497749761982334553)
          ·
            refine ⟨28224078373312321486750915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37632104497749761982334553 28224078373312321486750915)
            ·
              refine ⟨42336117559968482230126373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28224078373312321486750915 42336117559968482230126373)
              ·
                refine ⟨7938022042494090418148695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42336117559968482230126373 7938022042494090418148695)
                ·
                  refine ⟨11907033063741135627223043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7938022042494090418148695 11907033063741135627223043)
                  ·
                    refine ⟨17860549595611703440834565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11907033063741135627223043 17860549595611703440834565)
                    ·
                      refine ⟨3348853049177194395156481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17860549595611703440834565 3348853049177194395156481)
                      ·
                        rfl

theorem cell23_6521868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_6521868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521868 prefixEnd_6521868 := by exact prefixLift 6521868
  have htrace : WordTrace (prefixWord ++ tailWord_6521868) baseStart_6521868 baseEnd_6521868 := by
    simpa [prefixWord, tailWord_6521868, baseEnd_6521868] using wordTrace_append hprefix tailTrace_6521868
  have hstable : (prefixWord ++ tailWord_6521868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521868).length < 2 ^ (prefixWord ++ tailWord_6521868).sum := by decide
  have hdescent : baseEnd_6521868 < baseStart_6521868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521879 : List Nat := [1, 1, 3, 5, 1, 3, 1, 3, 1, 1, 3]
def baseStart_6521879 : Nat := 118140960795 + 6521879 * 2 ^ 59
def prefixEnd_6521879 : Nat := 4983230072969 + 3 ^ 40 * 6521879 * 2
def baseEnd_6521879 : Nat := 3348858697464393852118931

theorem tailTrace_6521879 : CollatzResearch.WordTrace tailWord_6521879 prefixEnd_6521879 3348858697464393852118931 := by
  unfold tailWord_6521879
  simp only [CollatzResearch.WordTrace]
  refine ⟨237872469139353706100320691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158581646092902470733547127 237872469139353706100320691)
  ·
    refine ⟨356808703709030559150481037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237872469139353706100320691 356808703709030559150481037)
    ·
      refine ⟨133803263890886459681430389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356808703709030559150481037 133803263890886459681430389)
      ·
        refine ⟨12544055989770605595134099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133803263890886459681430389 12544055989770605595134099)
        ·
          refine ⟨18816083984655908392701149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12544055989770605595134099 18816083984655908392701149)
          ·
            refine ⟨7056031494245965647262931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18816083984655908392701149 7056031494245965647262931)
            ·
              refine ⟨10584047241368948470894397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7056031494245965647262931 10584047241368948470894397)
              ·
                refine ⟨3969017715513355676585399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10584047241368948470894397 3969017715513355676585399)
                ·
                  refine ⟨5953526573270033514878099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3969017715513355676585399 5953526573270033514878099)
                  ·
                    refine ⟨8930289859905050272317149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5953526573270033514878099 8930289859905050272317149)
                    ·
                      refine ⟨3348858697464393852118931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8930289859905050272317149 3348858697464393852118931)
                      ·
                        rfl

theorem cell23_6521879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_6521879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521879 prefixEnd_6521879 := by exact prefixLift 6521879
  have htrace : WordTrace (prefixWord ++ tailWord_6521879) baseStart_6521879 baseEnd_6521879 := by
    simpa [prefixWord, tailWord_6521879, baseEnd_6521879] using wordTrace_append hprefix tailTrace_6521879
  have hstable : (prefixWord ++ tailWord_6521879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521879).length < 2 ^ (prefixWord ++ tailWord_6521879).sum := by decide
  have hdescent : baseEnd_6521879 < baseStart_6521879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521881 : List Nat := [1, 2, 1, 2, 1, 1, 4, 4, 1, 2, 4]
def baseStart_6521881 : Nat := 118140960795 + 6521881 * 2 ^ 59
def prefixEnd_6521881 : Nat := 4983230072969 + 3 ^ 40 * 6521881 * 2
def baseEnd_6521881 : Nat := 3348859724425702844293921

theorem tailTrace_6521881 : CollatzResearch.WordTrace tailWord_6521881 prefixEnd_6521881 3348859724425702844293921 := by
  unfold tailWord_6521881
  simp only [CollatzResearch.WordTrace]
  refine ⟨237872542085346460441893497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158581694723564306961262331 237872542085346460441893497)
  ·
    refine ⟨178404406564009845331420123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237872542085346460441893497 178404406564009845331420123)
    ·
      refine ⟨267606609846014767997130185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178404406564009845331420123 267606609846014767997130185)
      ·
        refine ⟨200704957384511075997847639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267606609846014767997130185 200704957384511075997847639)
        ·
          refine ⟨301057436076766613996771459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200704957384511075997847639 301057436076766613996771459)
          ·
            refine ⟨451586154115149920995157189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301057436076766613996771459 451586154115149920995157189)
            ·
              refine ⟨84672403896590610186591973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 451586154115149920995157189 84672403896590610186591973)
              ·
                refine ⟨15876075730610739409985995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84672403896590610186591973 15876075730610739409985995)
                ·
                  refine ⟨23814113595916109114978993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15876075730610739409985995 23814113595916109114978993)
                  ·
                    refine ⟨17860585196937081836234245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23814113595916109114978993 17860585196937081836234245)
                    ·
                      refine ⟨3348859724425702844293921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17860585196937081836234245 3348859724425702844293921)
                      ·
                        rfl

theorem cell23_6521881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_6521881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521881 prefixEnd_6521881 := by exact prefixLift 6521881
  have htrace : WordTrace (prefixWord ++ tailWord_6521881) baseStart_6521881 baseEnd_6521881 := by
    simpa [prefixWord, tailWord_6521881, baseEnd_6521881] using wordTrace_append hprefix tailTrace_6521881
  have hstable : (prefixWord ++ tailWord_6521881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521881).length < 2 ^ (prefixWord ++ tailWord_6521881).sum := by decide
  have hdescent : baseEnd_6521881 < baseStart_6521881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521891 : List Nat := [1, 1, 1, 4, 3, 4, 9]
def baseStart_6521891 : Nat := 118140960795 + 6521891 * 2 ^ 59
def prefixEnd_6521891 : Nat := 4983230072969 + 3 ^ 40 * 6521891 * 2
def baseEnd_6521891 : Nat := 41344010607805528458875

theorem tailTrace_6521891 : CollatzResearch.WordTrace tailWord_6521891 prefixEnd_6521891 41344010607805528458875 := by
  unfold tailWord_6521891
  simp only [CollatzResearch.WordTrace]
  refine ⟨237872906815310232149757527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158581937876873488099838351 237872906815310232149757527)
  ·
    refine ⟨356809360222965348224636291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237872906815310232149757527 356809360222965348224636291)
    ·
      refine ⟨535214040334448022336954437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356809360222965348224636291 535214040334448022336954437)
      ·
        refine ⟨100352632562709004188178957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 535214040334448022336954437 100352632562709004188178957)
        ·
          refine ⟨37632237211015876570567109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100352632562709004188178957 37632237211015876570567109)
          ·
            refine ⟨7056044477065476856981333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37632237211015876570567109 7056044477065476856981333)
            ·
              refine ⟨41344010607805528458875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7056044477065476856981333 41344010607805528458875)
              ·
                rfl

theorem cell23_6521891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 9].length) (baseStart_6521891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521891 prefixEnd_6521891 := by exact prefixLift 6521891
  have htrace : WordTrace (prefixWord ++ tailWord_6521891) baseStart_6521891 baseEnd_6521891 := by
    simpa [prefixWord, tailWord_6521891, baseEnd_6521891] using wordTrace_append hprefix tailTrace_6521891
  have hstable : (prefixWord ++ tailWord_6521891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521891).length < 2 ^ (prefixWord ++ tailWord_6521891).sum := by decide
  have hdescent : baseEnd_6521891 < baseStart_6521891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521895 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 4, 4]
def baseStart_6521895 : Nat := 118140960795 + 6521895 * 2 ^ 59
def prefixEnd_6521895 : Nat := 4983230072969 + 3 ^ 40 * 6521895 * 2
def baseEnd_6521895 : Nat := 1116288971051621929839619

theorem tailTrace_6521895 : CollatzResearch.WordTrace tailWord_6521895 prefixEnd_6521895 1116288971051621929839619 := by
  unfold tailWord_6521895
  simp only [CollatzResearch.WordTrace]
  refine ⟨237873052707295740832903139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158582035138197160555268759 237873052707295740832903139)
  ·
    refine ⟨356809579060943611249354709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237873052707295740832903139 356809579060943611249354709)
    ·
      refine ⟨8362724509240865888656751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 356809579060943611249354709 8362724509240865888656751)
      ·
        refine ⟨12544086763861298832985127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8362724509240865888656751 12544086763861298832985127)
        ·
          refine ⟨18816130145791948249477691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12544086763861298832985127 18816130145791948249477691)
          ·
            refine ⟨28224195218687922374216537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18816130145791948249477691 28224195218687922374216537)
            ·
              refine ⟨21168146414015941780662403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28224195218687922374216537 21168146414015941780662403)
              ·
                refine ⟨31752219621023912670993605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21168146414015941780662403 31752219621023912670993605)
                ·
                  refine ⟨5953541178941983625811301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31752219621023912670993605 5953541178941983625811301)
                  ·
                    refine ⟨1116288971051621929839619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5953541178941983625811301 1116288971051621929839619)
                    ·
                      rfl

theorem cell23_6521895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_6521895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521895 prefixEnd_6521895 := by exact prefixLift 6521895
  have htrace : WordTrace (prefixWord ++ tailWord_6521895) baseStart_6521895 baseEnd_6521895 := by
    simpa [prefixWord, tailWord_6521895, baseEnd_6521895] using wordTrace_append hprefix tailTrace_6521895
  have hstable : (prefixWord ++ tailWord_6521895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521895).length < 2 ^ (prefixWord ++ tailWord_6521895).sum := by decide
  have hdescent : baseEnd_6521895 < baseStart_6521895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521908 : List Nat := [2, 5, 1, 2, 1, 1, 1, 10]
def baseStart_6521908 : Nat := 118140960795 + 6521908 * 2 ^ 59
def prefixEnd_6521908 : Nat := 4983230072969 + 3 ^ 40 * 6521908 * 2
def baseEnd_6521908 : Nat := 124032355126050897728011

theorem tailTrace_6521908 : CollatzResearch.WordTrace tailWord_6521908 prefixEnd_6521908 124032355126050897728011 := by
  unfold tailWord_6521908
  simp only [CollatzResearch.WordTrace]
  refine ⟨118936763428124322026563189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158582351237499096035417585 118936763428124322026563189)
  ·
    refine ⟨11150321571386655189990299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118936763428124322026563189 11150321571386655189990299)
    ·
      refine ⟨16725482357079982784985449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11150321571386655189990299 16725482357079982784985449)
      ·
        refine ⟨12544111767809987088739087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16725482357079982784985449 12544111767809987088739087)
        ·
          refine ⟨18816167651714980633108631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12544111767809987088739087 18816167651714980633108631)
          ·
            refine ⟨28224251477572470949662947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18816167651714980633108631 28224251477572470949662947)
            ·
              refine ⟨42336377216358706424494421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28224251477572470949662947 42336377216358706424494421)
              ·
                refine ⟨124032355126050897728011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42336377216358706424494421 124032355126050897728011)
                ·
                  rfl

theorem cell23_6521908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 10].length) (baseStart_6521908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521908 prefixEnd_6521908 := by exact prefixLift 6521908
  have htrace : WordTrace (prefixWord ++ tailWord_6521908) baseStart_6521908 baseEnd_6521908 := by
    simpa [prefixWord, tailWord_6521908, baseEnd_6521908] using wordTrace_append hprefix tailTrace_6521908
  have hstable : (prefixWord ++ tailWord_6521908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521908).length < 2 ^ (prefixWord ++ tailWord_6521908).sum := by decide
  have hdescent : baseEnd_6521908 < baseStart_6521908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521912 : List Nat := [2, 1, 2, 1, 5, 3, 2, 1, 2, 4]
def baseStart_6521912 : Nat := 118140960795 + 6521912 * 2 ^ 59
def prefixEnd_6521912 : Nat := 4983230072969 + 3 ^ 40 * 6521912 * 2
def baseEnd_6521912 : Nat := 1116291880775330741002093

theorem tailTrace_6521912 : CollatzResearch.WordTrace tailWord_6521912 prefixEnd_6521912 1116291880775330741002093 := by
  unfold tailWord_6521912
  simp only [CollatzResearch.WordTrace]
  refine ⟨118936836374117076368135995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158582448498822768490847993 118936836374117076368135995)
  ·
    refine ⟨178405254561175614552203993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118936836374117076368135995 178405254561175614552203993)
    ·
      refine ⟨133803940920881710914152995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178405254561175614552203993 133803940920881710914152995)
      ·
        refine ⟨200705911381322566371229493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133803940920881710914152995 200705911381322566371229493)
        ·
          refine ⟨18816179191998990597302765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200705911381322566371229493 18816179191998990597302765)
          ·
            refine ⟨7056067196999621473988537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18816179191998990597302765 7056067196999621473988537)
            ·
              refine ⟨5292050397749716105491403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7056067196999621473988537 5292050397749716105491403)
              ·
                refine ⟨7938075596624574158237105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5292050397749716105491403 7938075596624574158237105)
                ·
                  refine ⟨5953556697468430618677829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7938075596624574158237105 5953556697468430618677829)
                  ·
                    refine ⟨1116291880775330741002093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5953556697468430618677829 1116291880775330741002093)
                    ·
                      rfl

theorem cell23_6521912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 2, 4].length) (baseStart_6521912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521912 prefixEnd_6521912 := by exact prefixLift 6521912
  have htrace : WordTrace (prefixWord ++ tailWord_6521912) baseStart_6521912 baseEnd_6521912 := by
    simpa [prefixWord, tailWord_6521912, baseEnd_6521912] using wordTrace_append hprefix tailTrace_6521912
  have hstable : (prefixWord ++ tailWord_6521912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521912).length < 2 ^ (prefixWord ++ tailWord_6521912).sum := by decide
  have hdescent : baseEnd_6521912 < baseStart_6521912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521951 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 2, 6]
def baseStart_6521951 : Nat := 118140960795 + 6521951 * 2 ^ 59
def prefixEnd_6521951 : Nat := 4983230072969 + 3 ^ 40 * 6521951 * 2
def baseEnd_6521951 : Nat := 1116298556023839190139533

theorem tailTrace_6521951 : CollatzResearch.WordTrace tailWord_6521951 prefixEnd_6521951 1116298556023839190139533 := by
  unfold tailWord_6521951
  simp only [CollatzResearch.WordTrace]
  refine ⟨237875095195092862396941707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158583396796728574931294471 237875095195092862396941707)
  ·
    refine ⟨356812642792639293595412561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237875095195092862396941707 356812642792639293595412561)
    ·
      refine ⟨267609482094479470196559421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356812642792639293595412561 267609482094479470196559421)
      ·
        refine ⟨100353555785429801323709783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267609482094479470196559421 100353555785429801323709783)
        ·
          refine ⟨150530333678144701985564675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100353555785429801323709783 150530333678144701985564675)
          ·
            refine ⟨225795500517217052978347013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150530333678144701985564675 225795500517217052978347013)
            ·
              refine ⟨42336656346978197433440065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225795500517217052978347013 42336656346978197433440065)
              ·
                refine ⟨31752492260233648075080049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42336656346978197433440065 31752492260233648075080049)
                ·
                  refine ⟨23814369195175236056310037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31752492260233648075080049 23814369195175236056310037)
                  ·
                    refine ⟨1116298556023839190139533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23814369195175236056310037 1116298556023839190139533)
                    ·
                      rfl

theorem cell23_6521951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 6].length) (baseStart_6521951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521951 prefixEnd_6521951 := by exact prefixLift 6521951
  have htrace : WordTrace (prefixWord ++ tailWord_6521951) baseStart_6521951 baseEnd_6521951 := by
    simpa [prefixWord, tailWord_6521951, baseEnd_6521951] using wordTrace_append hprefix tailTrace_6521951
  have hstable : (prefixWord ++ tailWord_6521951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521951).length < 2 ^ (prefixWord ++ tailWord_6521951).sum := by decide
  have hdescent : baseEnd_6521951 < baseStart_6521951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521975 : List Nat := [1, 1, 3, 1, 1, 4, 4, 1, 1, 4, 2]
def baseStart_6521975 : Nat := 118140960795 + 6521975 * 2 ^ 59
def prefixEnd_6521975 : Nat := 4983230072969 + 3 ^ 40 * 6521975 * 2
def baseEnd_6521975 : Nat := 3348907991607225476518489

theorem tailTrace_6521975 : CollatzResearch.WordTrace tailWord_6521975 prefixEnd_6521975 3348907991607225476518489 := by
  unfold tailWord_6521975
  simp only [CollatzResearch.WordTrace]
  refine ⟨237875970547005914495815379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158583980364670609663876919 237875970547005914495815379)
  ·
    refine ⟨356813955820508871743723069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237875970547005914495815379 356813955820508871743723069)
    ·
      refine ⟨133805233432690826903896151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356813955820508871743723069 133805233432690826903896151)
      ·
        refine ⟨200707850149036240355844227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133805233432690826903896151 200707850149036240355844227)
        ·
          refine ⟨301061775223554360533766341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200707850149036240355844227 301061775223554360533766341)
          ·
            refine ⟨56449082854416442600081189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 301061775223554360533766341 56449082854416442600081189)
            ·
              refine ⟨10584203035203082987515223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56449082854416442600081189 10584203035203082987515223)
              ·
                refine ⟨15876304552804624481272835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10584203035203082987515223 15876304552804624481272835)
                ·
                  refine ⟨23814456829206936721909253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15876304552804624481272835 23814456829206936721909253)
                  ·
                    refine ⟨4465210655476300635357985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23814456829206936721909253 4465210655476300635357985)
                    ·
                      refine ⟨3348907991607225476518489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4465210655476300635357985 3348907991607225476518489)
                      ·
                        rfl

theorem cell23_6521975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 4, 2].length) (baseStart_6521975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521975 prefixEnd_6521975 := by exact prefixLift 6521975
  have htrace : WordTrace (prefixWord ++ tailWord_6521975) baseStart_6521975 baseEnd_6521975 := by
    simpa [prefixWord, tailWord_6521975, baseEnd_6521975] using wordTrace_append hprefix tailTrace_6521975
  have hstable : (prefixWord ++ tailWord_6521975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521975).length < 2 ^ (prefixWord ++ tailWord_6521975).sum := by decide
  have hdescent : baseEnd_6521975 < baseStart_6521975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6521991 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_6521991 : Nat := 118140960795 + 6521991 * 2 ^ 59
def prefixEnd_6521991 : Nat := 4983230072969 + 3 ^ 40 * 6521991 * 2
def baseEnd_6521991 : Nat := 3348916207297697413918415

theorem tailTrace_6521991 : CollatzResearch.WordTrace tailWord_6521991 prefixEnd_6521991 3348916207297697413918415 := by
  unfold tailWord_6521991
  simp only [CollatzResearch.WordTrace]
  refine ⟨237876554114947949228397827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158584369409965299485598551 237876554114947949228397827)
  ·
    refine ⟨356814831172421923842596741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237876554114947949228397827 356814831172421923842596741)
    ·
      refine ⟨66902780844829110720486889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 356814831172421923842596741 66902780844829110720486889)
      ·
        refine ⟨50177085633621833040365167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66902780844829110720486889 50177085633621833040365167)
        ·
          refine ⟨75265628450432749560547751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50177085633621833040365167 75265628450432749560547751)
          ·
            refine ⟨112898442675649124340821627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75265628450432749560547751 112898442675649124340821627)
            ·
              refine ⟨169347664013473686511232441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112898442675649124340821627 169347664013473686511232441)
              ·
                refine ⟨127010748010105264883424331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169347664013473686511232441 127010748010105264883424331)
                ·
                  refine ⟨190516122015157897325136497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127010748010105264883424331 190516122015157897325136497)
                  ·
                    refine ⟨142887091511368422993852373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 190516122015157897325136497 142887091511368422993852373)
                    ·
                      refine ⟨3348916207297697413918415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142887091511368422993852373 3348916207297697413918415)
                      ·
                        rfl

theorem cell23_6521991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_6521991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6521991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6521991 prefixEnd_6521991 := by exact prefixLift 6521991
  have htrace : WordTrace (prefixWord ++ tailWord_6521991) baseStart_6521991 baseEnd_6521991 := by
    simpa [prefixWord, tailWord_6521991, baseEnd_6521991] using wordTrace_append hprefix tailTrace_6521991
  have hstable : (prefixWord ++ tailWord_6521991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6521991).length < 2 ^ (prefixWord ++ tailWord_6521991).sum := by decide
  have hdescent : baseEnd_6521991 < baseStart_6521991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6521991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522015 : List Nat := [1, 1, 2, 6, 2, 1, 2, 1, 7]
def baseStart_6522015 : Nat := 118140960795 + 6522015 * 2 ^ 59
def prefixEnd_6522015 : Nat := 4983230072969 + 3 ^ 40 * 6522015 * 2
def baseEnd_6522015 : Nat := 372103170092600591113145

theorem tailTrace_6522015 : CollatzResearch.WordTrace tailWord_6522015 prefixEnd_6522015 372103170092600591113145 := by
  unfold tailWord_6522015
  simp only [CollatzResearch.WordTrace]
  refine ⟨237877429466861001327271499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158584952977907334218180999 237877429466861001327271499)
  ·
    refine ⟨356816144200291501990907249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237877429466861001327271499 356816144200291501990907249)
    ·
      refine ⟨267612108150218626493180437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356816144200291501990907249 267612108150218626493180437)
      ·
        refine ⟨12544317569541498116867833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 267612108150218626493180437 12544317569541498116867833)
        ·
          refine ⟨9408238177156123587650875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12544317569541498116867833 9408238177156123587650875)
          ·
            refine ⟨14112357265734185381476313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9408238177156123587650875 14112357265734185381476313)
            ·
              refine ⟨10584267949300639036107235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14112357265734185381476313 10584267949300639036107235)
              ·
                refine ⟨15876401923950958554160853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10584267949300639036107235 15876401923950958554160853)
                ·
                  refine ⟨372103170092600591113145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15876401923950958554160853 372103170092600591113145)
                  ·
                    rfl

theorem cell23_6522015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 7].length) (baseStart_6522015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522015 prefixEnd_6522015 := by exact prefixLift 6522015
  have htrace : WordTrace (prefixWord ++ tailWord_6522015) baseStart_6522015 baseEnd_6522015 := by
    simpa [prefixWord, tailWord_6522015, baseEnd_6522015] using wordTrace_append hprefix tailTrace_6522015
  have hstable : (prefixWord ++ tailWord_6522015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522015).length < 2 ^ (prefixWord ++ tailWord_6522015).sum := by decide
  have hdescent : baseEnd_6522015 < baseStart_6522015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522049 : List Nat := [1, 2, 6, 1, 1, 3, 1, 3, 5]
def baseStart_6522049 : Nat := 118140960795 + 6522049 * 2 ^ 59
def prefixEnd_6522049 : Nat := 4983230072969 + 3 ^ 40 * 6522049 * 2
def baseEnd_6522049 : Nat := 372105109908406465221461

theorem tailTrace_6522049 : CollatzResearch.WordTrace tailWord_6522049 prefixEnd_6522049 372105109908406465221461 := by
  unfold tailWord_6522049
  simp only [CollatzResearch.WordTrace]
  refine ⟨237878669548737825134009201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158585779699158550089339467 237878669548737825134009201)
  ·
    refine ⟨178409002161553368850506901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237878669548737825134009201 178409002161553368850506901)
    ·
      refine ⟨8362921976322814164867511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 178409002161553368850506901 8362921976322814164867511)
      ·
        refine ⟨12544382964484221247301267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8362921976322814164867511 12544382964484221247301267)
        ·
          refine ⟨18816574446726331870951901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12544382964484221247301267 18816574446726331870951901)
          ·
            refine ⟨7056215417522374451606963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18816574446726331870951901 7056215417522374451606963)
            ·
              refine ⟨10584323126283561677410445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7056215417522374451606963 10584323126283561677410445)
              ·
                refine ⟨3969121172356335629028917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10584323126283561677410445 3969121172356335629028917)
                ·
                  refine ⟨372105109908406465221461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3969121172356335629028917 372105109908406465221461)
                  ·
                    rfl

theorem cell23_6522049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 5].length) (baseStart_6522049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522049 prefixEnd_6522049 := by exact prefixLift 6522049
  have htrace : WordTrace (prefixWord ++ tailWord_6522049) baseStart_6522049 baseEnd_6522049 := by
    simpa [prefixWord, tailWord_6522049, baseEnd_6522049] using wordTrace_append hprefix tailTrace_6522049
  have hstable : (prefixWord ++ tailWord_6522049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522049).length < 2 ^ (prefixWord ++ tailWord_6522049).sum := by decide
  have hdescent : baseEnd_6522049 < baseStart_6522049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522126 : List Nat := [4, 1, 1, 2, 1, 5, 2, 2, 1, 4]
def baseStart_6522126 : Nat := 118140960795 + 6522126 * 2 ^ 59
def prefixEnd_6522126 : Nat := 4983230072969 + 3 ^ 40 * 6522126 * 2
def baseEnd_6522126 : Nat := 1116328509062018128576765

theorem tailTrace_6522126 : CollatzResearch.WordTrace tailWord_6522126 prefixEnd_6522126 1116328509062018128576765 := by
  unfold tailWord_6522126
  simp only [CollatzResearch.WordTrace]
  refine ⟨29735184746182358410570279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158587651979639244856374821 29735184746182358410570279)
  ·
    refine ⟨44602777119273537615855419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29735184746182358410570279 44602777119273537615855419)
    ·
      refine ⟨66904165678910306423783129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44602777119273537615855419 66904165678910306423783129)
      ·
        refine ⟨50178124259182729817837347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66904165678910306423783129 50178124259182729817837347)
        ·
          refine ⟨75267186388774094726756021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50178124259182729817837347 75267186388774094726756021)
          ·
            refine ⟨7056298723947571380633377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75267186388774094726756021 7056298723947571380633377)
            ·
              refine ⟨5292224042960678535475033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7056298723947571380633377 5292224042960678535475033)
              ·
                refine ⟨3969168032220508901606275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5292224042960678535475033 3969168032220508901606275)
                ·
                  refine ⟨5953752048330763352409413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3969168032220508901606275 5953752048330763352409413)
                  ·
                    refine ⟨1116328509062018128576765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5953752048330763352409413 1116328509062018128576765)
                    ·
                      rfl

theorem cell23_6522126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_6522126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522126 prefixEnd_6522126 := by exact prefixLift 6522126
  have htrace : WordTrace (prefixWord ++ tailWord_6522126) baseStart_6522126 baseEnd_6522126 := by
    simpa [prefixWord, tailWord_6522126, baseEnd_6522126] using wordTrace_append hprefix tailTrace_6522126
  have hstable : (prefixWord ++ tailWord_6522126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522126).length < 2 ^ (prefixWord ++ tailWord_6522126).sum := by decide
  have hdescent : baseEnd_6522126 < baseStart_6522126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522165 : List Nat := [1, 3, 3, 1, 2, 2, 2, 2, 1, 6]
def baseStart_6522165 : Nat := 118140960795 + 6522165 * 2 ^ 59
def prefixEnd_6522165 : Nat := 4983230072969 + 3 ^ 40 * 6522165 * 2
def baseEnd_6522165 : Nat := 1116335184310526577714205

theorem tailTrace_6522165 : CollatzResearch.WordTrace tailWord_6522165 prefixEnd_6522165 1116335184310526577714205 := by
  unfold tailWord_6522165
  simp only [CollatzResearch.WordTrace]
  refine ⟨237882900416317576945231949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158588600277545051296821299 237882900416317576945231949)
  ·
    refine ⟨89206087656119091354461981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237882900416317576945231949 89206087656119091354461981)
    ·
      refine ⟨33452282871044659257923243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89206087656119091354461981 33452282871044659257923243)
      ·
        refine ⟨50178424306566988886884865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33452282871044659257923243 50178424306566988886884865)
        ·
          refine ⟨37633818229925241665163649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50178424306566988886884865 37633818229925241665163649)
          ·
            refine ⟨28225363672443931248872737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37633818229925241665163649 28225363672443931248872737)
            ·
              refine ⟨21169022754332948436654553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28225363672443931248872737 21169022754332948436654553)
              ·
                refine ⟨15876767065749711327490915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21169022754332948436654553 15876767065749711327490915)
                ·
                  refine ⟨23815150598624566991236373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15876767065749711327490915 23815150598624566991236373)
                  ·
                    refine ⟨1116335184310526577714205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23815150598624566991236373 1116335184310526577714205)
                    ·
                      rfl

theorem cell23_6522165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_6522165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522165 prefixEnd_6522165 := by exact prefixLift 6522165
  have htrace : WordTrace (prefixWord ++ tailWord_6522165) baseStart_6522165 baseEnd_6522165 := by
    simpa [prefixWord, tailWord_6522165, baseEnd_6522165] using wordTrace_append hprefix tailTrace_6522165
  have hstable : (prefixWord ++ tailWord_6522165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522165).length < 2 ^ (prefixWord ++ tailWord_6522165).sum := by decide
  have hdescent : baseEnd_6522165 < baseStart_6522165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522168 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 3, 1, 6]
def baseStart_6522168 : Nat := 118140960795 + 6522168 * 2 ^ 59
def prefixEnd_6522168 : Nat := 4983230072969 + 3 ^ 40 * 6522168 * 2
def baseEnd_6522168 : Nat := 3349007093373543221405101

theorem tailTrace_6522168 : CollatzResearch.WordTrace tailWord_6522168 prefixEnd_6522168 3349007093373543221405101 := by
  unfold tailWord_6522168
  simp only [CollatzResearch.WordTrace]
  refine ⟨118941504917653354228795579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158588673223537805638394105 118941504917653354228795579)
  ·
    refine ⟨178412257376480031343193369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118941504917653354228795579 178412257376480031343193369)
    ·
      refine ⟨133809193032360023507395027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178412257376480031343193369 133809193032360023507395027)
      ·
        refine ⟨200713789548540035261092541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133809193032360023507395027 200713789548540035261092541)
        ·
          refine ⟨75267671080702513222909703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200713789548540035261092541 75267671080702513222909703)
          ·
            refine ⟨112901506621053769834364555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75267671080702513222909703 112901506621053769834364555)
            ·
              refine ⟨169352259931580654751546833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112901506621053769834364555 169352259931580654751546833)
              ·
                refine ⟨127014194948685491063660125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169352259931580654751546833 127014194948685491063660125)
                ·
                  refine ⟨47630323105757059148872547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127014194948685491063660125 47630323105757059148872547)
                  ·
                    refine ⟨71445484658635588723308821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47630323105757059148872547 71445484658635588723308821)
                    ·
                      refine ⟨3349007093373543221405101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71445484658635588723308821 3349007093373543221405101)
                      ·
                        rfl

theorem cell23_6522168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_6522168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522168 prefixEnd_6522168 := by exact prefixLift 6522168
  have htrace : WordTrace (prefixWord ++ tailWord_6522168) baseStart_6522168 baseEnd_6522168 := by
    simpa [prefixWord, tailWord_6522168, baseEnd_6522168] using wordTrace_append hprefix tailTrace_6522168
  have hstable : (prefixWord ++ tailWord_6522168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522168).length < 2 ^ (prefixWord ++ tailWord_6522168).sum := by decide
  have hdescent : baseEnd_6522168 < baseStart_6522168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522172 : List Nat := [2, 2, 2, 2, 1, 4, 1, 3, 1, 1, 4]
def baseStart_6522172 : Nat := 118140960795 + 6522172 * 2 ^ 59
def prefixEnd_6522172 : Nat := 4983230072969 + 3 ^ 40 * 6522172 * 2
def baseEnd_6522172 : Nat := 3349009147296161205755083

theorem tailTrace_6522172 : CollatzResearch.WordTrace tailWord_6522172 prefixEnd_6522172 3349009147296161205755083 := by
  unfold tailWord_6522172
  simp only [CollatzResearch.WordTrace]
  refine ⟨118941577863646108570368385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158588770484861478093824513 118941577863646108570368385)
  ·
    refine ⟨89206183397734581427776289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118941577863646108570368385 89206183397734581427776289)
    ·
      refine ⟨66904637548300936070832217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89206183397734581427776289 66904637548300936070832217)
      ·
        refine ⟨50178478161225702053124163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66904637548300936070832217 50178478161225702053124163)
        ·
          refine ⟨75267717241838553079686245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50178478161225702053124163 75267717241838553079686245)
          ·
            refine ⟨14112696982844728702441171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75267717241838553079686245 14112696982844728702441171)
            ·
              refine ⟨21169045474267093053661757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14112696982844728702441171 21169045474267093053661757)
              ·
                refine ⟨7938392052850159895123159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21169045474267093053661757 7938392052850159895123159)
                ·
                  refine ⟨11907588079275239842684739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7938392052850159895123159 11907588079275239842684739)
                  ·
                    refine ⟨17861382118912859764027109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11907588079275239842684739 17861382118912859764027109)
                    ·
                      refine ⟨3349009147296161205755083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17861382118912859764027109 3349009147296161205755083)
                      ·
                        rfl

theorem cell23_6522172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_6522172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522172 prefixEnd_6522172 := by exact prefixLift 6522172
  have htrace : WordTrace (prefixWord ++ tailWord_6522172) baseStart_6522172 baseEnd_6522172 := by
    simpa [prefixWord, tailWord_6522172, baseEnd_6522172] using wordTrace_append hprefix tailTrace_6522172
  have hstable : (prefixWord ++ tailWord_6522172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522172).length < 2 ^ (prefixWord ++ tailWord_6522172).sum := by decide
  have hdescent : baseEnd_6522172 < baseStart_6522172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522199 : List Nat := [1, 1, 3, 2, 3, 3, 3, 1, 2, 4]
def baseStart_6522199 : Nat := 118140960795 + 6522199 * 2 ^ 59
def prefixEnd_6522199 : Nat := 4983230072969 + 3 ^ 40 * 6522199 * 2
def baseEnd_6522199 : Nat := 1116341003757944200039153

theorem tailTrace_6522199 : CollatzResearch.WordTrace tailWord_6522199 prefixEnd_6522199 1116341003757944200039153 := by
  unfold tailWord_6522199
  simp only [CollatzResearch.WordTrace]
  refine ⟨237884140498194400751969651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158589426998796267167979767 237884140498194400751969651)
  ·
    refine ⟨356826210747291601127954477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237884140498194400751969651 356826210747291601127954477)
    ·
      refine ⟨133809829030234350422982929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356826210747291601127954477 133809829030234350422982929)
      ·
        refine ⟨100357371772675762817237197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133809829030234350422982929 100357371772675762817237197)
        ·
          refine ⟨37634014414753411056463949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100357371772675762817237197 37634014414753411056463949)
          ·
            refine ⟨14112755405532529146173981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37634014414753411056463949 14112755405532529146173981)
            ·
              refine ⟨5292283277074698429815243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14112755405532529146173981 5292283277074698429815243)
              ·
                refine ⟨7938424915612047644722865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5292283277074698429815243 7938424915612047644722865)
                ·
                  refine ⟨5953818686709035733542149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7938424915612047644722865 5953818686709035733542149)
                  ·
                    refine ⟨1116341003757944200039153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5953818686709035733542149 1116341003757944200039153)
                    ·
                      rfl

theorem cell23_6522199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 2, 4].length) (baseStart_6522199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522199 prefixEnd_6522199 := by exact prefixLift 6522199
  have htrace : WordTrace (prefixWord ++ tailWord_6522199) baseStart_6522199 baseEnd_6522199 := by
    simpa [prefixWord, tailWord_6522199, baseEnd_6522199] using wordTrace_append hprefix tailTrace_6522199
  have hstable : (prefixWord ++ tailWord_6522199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522199).length < 2 ^ (prefixWord ++ tailWord_6522199).sum := by decide
  have hdescent : baseEnd_6522199 < baseStart_6522199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522212 : List Nat := [2, 3, 1, 1, 3, 4, 2, 7]
def baseStart_6522212 : Nat := 118140960795 + 6522212 * 2 ^ 59
def prefixEnd_6522212 : Nat := 4983230072969 + 3 ^ 40 * 6522212 * 2
def baseEnd_6522212 : Nat := 124038136537864483305737

theorem tailTrace_6522212 : CollatzResearch.WordTrace tailWord_6522212 prefixEnd_6522212 124038136537864483305737 := by
  unfold tailWord_6522212
  simp only [CollatzResearch.WordTrace]
  refine ⟨118942307323573651986096445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158589743098098202648128593 118942307323573651986096445)
  ·
    refine ⟨44603365246340119494786167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118942307323573651986096445 44603365246340119494786167)
    ·
      refine ⟨66905047869510179242179251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44603365246340119494786167 66905047869510179242179251)
      ·
        refine ⟨100357571804265268863268877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66905047869510179242179251 100357571804265268863268877)
        ·
          refine ⟨37634089426599475823725829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100357571804265268863268877 37634089426599475823725829)
          ·
            refine ⟨7056391767487401716948593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37634089426599475823725829 7056391767487401716948593)
            ·
              refine ⟨5292293825615551287711445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7056391767487401716948593 5292293825615551287711445)
              ·
                refine ⟨124038136537864483305737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5292293825615551287711445 124038136537864483305737)
                ·
                  rfl

theorem cell23_6522212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 7].length) (baseStart_6522212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522212 prefixEnd_6522212 := by exact prefixLift 6522212
  have htrace : WordTrace (prefixWord ++ tailWord_6522212) baseStart_6522212 baseEnd_6522212 := by
    simpa [prefixWord, tailWord_6522212, baseEnd_6522212] using wordTrace_append hprefix tailTrace_6522212
  have hstable : (prefixWord ++ tailWord_6522212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522212).length < 2 ^ (prefixWord ++ tailWord_6522212).sum := by decide
  have hdescent : baseEnd_6522212 < baseStart_6522212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522265 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 2, 1, 5]
def baseStart_6522265 : Nat := 118140960795 + 6522265 * 2 ^ 59
def prefixEnd_6522265 : Nat := 4983230072969 + 3 ^ 40 * 6522265 * 2
def baseEnd_6522265 : Nat := 3349056900997029341892155

theorem tailTrace_6522265 : CollatzResearch.WordTrace tailWord_6522265 prefixEnd_6522265 3349056900997029341892155 := by
  unfold tailWord_6522265
  simp only [CollatzResearch.WordTrace]
  refine ⟨237886547715955294023872249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158591031810636862682581499 237886547715955294023872249)
  ·
    refine ⟨178414910786966470517904187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237886547715955294023872249 178414910786966470517904187)
    ·
      refine ⟨267622366180449705776856281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178414910786966470517904187 267622366180449705776856281)
      ·
        refine ⟨200716774635337279332642211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267622366180449705776856281 200716774635337279332642211)
        ·
          refine ⟨301075161953005918998963317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200716774635337279332642211 301075161953005918998963317)
          ·
            refine ⟨28225796433094304906152811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 301075161953005918998963317 28225796433094304906152811)
            ·
              refine ⟨42338694649641457359229217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28225796433094304906152811 42338694649641457359229217)
              ·
                refine ⟨31754020987231093019421913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42338694649641457359229217 31754020987231093019421913)
                ·
                  refine ⟨23815515740423319764566435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31754020987231093019421913 23815515740423319764566435)
                  ·
                    refine ⟨35723273610634979646849653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23815515740423319764566435 35723273610634979646849653)
                    ·
                      refine ⟨3349056900997029341892155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35723273610634979646849653 3349056900997029341892155)
                      ·
                        rfl

theorem cell23_6522265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_6522265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522265 prefixEnd_6522265 := by exact prefixLift 6522265
  have htrace : WordTrace (prefixWord ++ tailWord_6522265) baseStart_6522265 baseEnd_6522265 := by
    simpa [prefixWord, tailWord_6522265, baseEnd_6522265] using wordTrace_append hprefix tailTrace_6522265
  have hstable : (prefixWord ++ tailWord_6522265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522265).length < 2 ^ (prefixWord ++ tailWord_6522265).sum := by decide
  have hdescent : baseEnd_6522265 < baseStart_6522265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522279 : List Nat := [1, 1, 6, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_6522279 : Nat := 118140960795 + 6522279 * 2 ^ 59
def prefixEnd_6522279 : Nat := 4983230072969 + 3 ^ 40 * 6522279 * 2
def baseEnd_6522279 : Nat := 3349064089726192287117091

theorem tailTrace_6522279 : CollatzResearch.WordTrace tailWord_6522279 prefixEnd_6522279 3349064089726192287117091 := by
  unfold tailWord_6522279
  simp only [CollatzResearch.WordTrace]
  refine ⟨237887058337904574414881891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158591372225269716276587927 237887058337904574414881891)
  ·
    refine ⟨356830587506856861622322837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237887058337904574414881891 356830587506856861622322837)
    ·
      refine ⟨16726433789383915388546383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 356830587506856861622322837 16726433789383915388546383)
      ·
        refine ⟨25089650684075873082819575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16726433789383915388546383 25089650684075873082819575)
        ·
          refine ⟨37634476026113809624229363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25089650684075873082819575 37634476026113809624229363)
          ·
            refine ⟨56451714039170714436344045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37634476026113809624229363 56451714039170714436344045)
            ·
              refine ⟨21169392764689017913629017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56451714039170714436344045 21169392764689017913629017)
              ·
                refine ⟨15877044573516763435221763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21169392764689017913629017 15877044573516763435221763)
                ·
                  refine ⟨23815566860275145152832645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15877044573516763435221763 23815566860275145152832645)
                  ·
                    refine ⟨4465418786301589716156121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23815566860275145152832645 4465418786301589716156121)
                    ·
                      refine ⟨3349064089726192287117091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4465418786301589716156121 3349064089726192287117091)
                      ·
                        rfl

theorem cell23_6522279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_6522279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522279 prefixEnd_6522279 := by exact prefixLift 6522279
  have htrace : WordTrace (prefixWord ++ tailWord_6522279) baseStart_6522279 baseEnd_6522279 := by
    simpa [prefixWord, tailWord_6522279, baseEnd_6522279] using wordTrace_append hprefix tailTrace_6522279
  have hstable : (prefixWord ++ tailWord_6522279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522279).length < 2 ^ (prefixWord ++ tailWord_6522279).sum := by decide
  have hdescent : baseEnd_6522279 < baseStart_6522279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522312 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 2, 3, 3]
def baseStart_6522312 : Nat := 118140960795 + 6522312 * 2 ^ 59
def prefixEnd_6522312 : Nat := 4983230072969 + 3 ^ 40 * 6522312 * 2
def baseEnd_6522312 : Nat := 3349081034587790658004439

theorem tailTrace_6522312 : CollatzResearch.WordTrace tailWord_6522312 prefixEnd_6522312 3349081034587790658004439 := by
  unfold tailWord_6522312
  simp only [CollatzResearch.WordTrace]
  refine ⟨118944130973392510525416595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158592174631190014033888793 118944130973392510525416595)
  ·
    refine ⟨178416196460088765788124893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118944130973392510525416595 178416196460088765788124893)
    ·
      refine ⟨66906073672533287170546835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178416196460088765788124893 66906073672533287170546835)
      ·
        refine ⟨100359110508799930755820253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66906073672533287170546835 100359110508799930755820253)
        ·
          refine ⟨37634666440799974033432595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100359110508799930755820253 37634666440799974033432595)
          ·
            refine ⟨56451999661199961050148893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37634666440799974033432595 56451999661199961050148893)
            ·
              refine ⟨21169499872949985393805835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56451999661199961050148893 21169499872949985393805835)
              ·
                refine ⟨31754249809424978090708753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21169499872949985393805835 31754249809424978090708753)
                ·
                  refine ⟨23815687357068733568031565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31754249809424978090708753 23815687357068733568031565)
                  ·
                    refine ⟨8930882758900775088011837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23815687357068733568031565 8930882758900775088011837)
                    ·
                      refine ⟨3349081034587790658004439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8930882758900775088011837 3349081034587790658004439)
                      ·
                        rfl

theorem cell23_6522312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_6522312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522312 prefixEnd_6522312 := by exact prefixLift 6522312
  have htrace : WordTrace (prefixWord ++ tailWord_6522312) baseStart_6522312 baseEnd_6522312 := by
    simpa [prefixWord, tailWord_6522312, baseEnd_6522312] using wordTrace_append hprefix tailTrace_6522312
  have hstable : (prefixWord ++ tailWord_6522312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522312).length < 2 ^ (prefixWord ++ tailWord_6522312).sum := by decide
  have hdescent : baseEnd_6522312 < baseStart_6522312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522315 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 4, 5]
def baseStart_6522315 : Nat := 118140960795 + 6522315 * 2 ^ 59
def prefixEnd_6522315 : Nat := 4983230072969 + 3 ^ 40 * 6522315 * 2
def baseEnd_6522315 : Nat := 1116360858343251382088975

theorem tailTrace_6522315 : CollatzResearch.WordTrace tailWord_6522315 prefixEnd_6522315 1116360858343251382088975 := by
  unfold tailWord_6522315
  simp only [CollatzResearch.WordTrace]
  refine ⟨237888371365774152563192399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158592247577182768375461599 237888371365774152563192399)
  ·
    refine ⟨356832557048661228844788599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237888371365774152563192399 356832557048661228844788599)
    ·
      refine ⟨535248835572991843267182899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356832557048661228844788599 535248835572991843267182899)
      ·
        refine ⟨802873253359487764900774349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535248835572991843267182899 802873253359487764900774349)
        ·
          refine ⟨301077470009807911837790381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 802873253359487764900774349 301077470009807911837790381)
          ·
            refine ⟨112904051253677966939171393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301077470009807911837790381 112904051253677966939171393)
            ·
              refine ⟨84678038440258475204378545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112904051253677966939171393 84678038440258475204378545)
              ·
                refine ⟨63508528830193856403283909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84678038440258475204378545 63508528830193856403283909)
                ·
                  refine ⟨11907849155661348075615733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63508528830193856403283909 11907849155661348075615733)
                  ·
                    refine ⟨1116360858343251382088975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11907849155661348075615733 1116360858343251382088975)
                    ·
                      rfl

theorem cell23_6522315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 5].length) (baseStart_6522315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522315 prefixEnd_6522315 := by exact prefixLift 6522315
  have htrace : WordTrace (prefixWord ++ tailWord_6522315) baseStart_6522315 baseEnd_6522315 := by
    simpa [prefixWord, tailWord_6522315, baseEnd_6522315] using wordTrace_append hprefix tailTrace_6522315
  have hstable : (prefixWord ++ tailWord_6522315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522315).length < 2 ^ (prefixWord ++ tailWord_6522315).sum := by decide
  have hdescent : baseEnd_6522315 < baseStart_6522315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522439 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 3, 5]
def baseStart_6522439 : Nat := 118140960795 + 6522439 * 2 ^ 59
def prefixEnd_6522439 : Nat := 4983230072969 + 3 ^ 40 * 6522439 * 2
def baseEnd_6522439 : Nat := 1116382082210303887038785

theorem tailTrace_6522439 : CollatzResearch.WordTrace tailWord_6522439 prefixEnd_6522439 1116382082210303887038785 := by
  unfold tailWord_6522439
  simp only [CollatzResearch.WordTrace]
  refine ⟨237892894017324921740706371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158595262678216614493804247 237892894017324921740706371)
  ·
    refine ⟨356839341025987382611059557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237892894017324921740706371 356839341025987382611059557)
    ·
      refine ⟨66907376442372634239573667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 356839341025987382611059557 66907376442372634239573667)
      ·
        refine ⟨100361064663558951359360501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66907376442372634239573667 100361064663558951359360501)
        ·
          refine ⟨9408849812208651689940047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100361064663558951359360501 9408849812208651689940047)
          ·
            refine ⟨14113274718312977534910071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9408849812208651689940047 14113274718312977534910071)
            ·
              refine ⟨21169912077469466302365107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14113274718312977534910071 21169912077469466302365107)
              ·
                refine ⟨31754868116204199453547661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21169912077469466302365107 31754868116204199453547661)
                ·
                  refine ⟨11908075543576574795080373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31754868116204199453547661 11908075543576574795080373)
                  ·
                    refine ⟨1116382082210303887038785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11908075543576574795080373 1116382082210303887038785)
                    ·
                      rfl

theorem cell23_6522439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_6522439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522439 prefixEnd_6522439 := by exact prefixLift 6522439
  have htrace : WordTrace (prefixWord ++ tailWord_6522439) baseStart_6522439 baseEnd_6522439 := by
    simpa [prefixWord, tailWord_6522439, baseEnd_6522439] using wordTrace_append hprefix tailTrace_6522439
  have hstable : (prefixWord ++ tailWord_6522439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522439).length < 2 ^ (prefixWord ++ tailWord_6522439).sum := by decide
  have hdescent : baseEnd_6522439 < baseStart_6522439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522476 : List Nat := [2, 2, 1, 1, 3, 1, 1, 5, 3, 2, 2]
def baseStart_6522476 : Nat := 118140960795 + 6522476 * 2 ^ 59
def prefixEnd_6522476 : Nat := 4983230072969 + 3 ^ 40 * 6522476 * 2
def baseEnd_6522476 : Nat := 3349165245415128016353685

theorem tailTrace_6522476 : CollatzResearch.WordTrace tailWord_6522476 prefixEnd_6522476 3349165245415128016353685 := by
  unfold tailWord_6522476
  simp only [CollatzResearch.WordTrace]
  refine ⟨118947121759095438529901641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158596162345460584706535521 118947121759095438529901641)
  ·
    refine ⟨89210341319321578897426231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118947121759095438529901641 89210341319321578897426231)
    ·
      refine ⟨133815511978982368346139347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89210341319321578897426231 133815511978982368346139347)
      ·
        refine ⟨200723267968473552519209021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133815511978982368346139347 200723267968473552519209021)
        ·
          refine ⟨75271225488177582194703383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200723267968473552519209021 75271225488177582194703383)
          ·
            refine ⟨112906838232266373292055075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75271225488177582194703383 112906838232266373292055075)
            ·
              refine ⟨169360257348399559938082613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112906838232266373292055075 169360257348399559938082613)
              ·
                refine ⟨15877524126412458744195245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169360257348399559938082613 15877524126412458744195245)
                ·
                  refine ⟨5954071547404672029073217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15877524126412458744195245 5954071547404672029073217)
                  ·
                    refine ⟨4465553660553504021804913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5954071547404672029073217 4465553660553504021804913)
                    ·
                      refine ⟨3349165245415128016353685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4465553660553504021804913 3349165245415128016353685)
                      ·
                        rfl

theorem cell23_6522476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 2, 2].length) (baseStart_6522476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522476 prefixEnd_6522476 := by exact prefixLift 6522476
  have htrace : WordTrace (prefixWord ++ tailWord_6522476) baseStart_6522476 baseEnd_6522476 := by
    simpa [prefixWord, tailWord_6522476, baseEnd_6522476] using wordTrace_append hprefix tailTrace_6522476
  have hstable : (prefixWord ++ tailWord_6522476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522476).length < 2 ^ (prefixWord ++ tailWord_6522476).sum := by decide
  have hdescent : baseEnd_6522476 < baseStart_6522476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522486 : List Nat := [5, 1, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_6522486 : Nat := 118140960795 + 6522486 * 2 ^ 59
def prefixEnd_6522486 : Nat := 4983230072969 + 3 ^ 40 * 6522486 * 2
def baseEnd_6522486 : Nat := 1116390126740557659076213

theorem tailTrace_6522486 : CollatzResearch.WordTrace tailWord_6522486 prefixEnd_6522486 1116390126740557659076213 := by
  unfold tailWord_6522486
  simp only [CollatzResearch.WordTrace]
  refine ⟨14868413015509665547979207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158596405498769765845111541 14868413015509665547979207)
  ·
    refine ⟨22302619523264498321968811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14868413015509665547979207 22302619523264498321968811)
    ·
      refine ⟨33453929284896747482953217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22302619523264498321968811 33453929284896747482953217)
      ·
        refine ⟨25090446963672560612214913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33453929284896747482953217 25090446963672560612214913)
        ·
          refine ⟨18817835222754420459161185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25090446963672560612214913 18817835222754420459161185)
          ·
            refine ⟨14113376417065815344370889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18817835222754420459161185 14113376417065815344370889)
            ·
              refine ⟨10585032312799361508278167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14113376417065815344370889 10585032312799361508278167)
              ·
                refine ⟨15877548469199042262417251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10585032312799361508278167 15877548469199042262417251)
                ·
                  refine ⟨23816322703798563393625877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15877548469199042262417251 23816322703798563393625877)
                  ·
                    refine ⟨1116390126740557659076213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23816322703798563393625877 1116390126740557659076213)
                    ·
                      rfl

theorem cell23_6522486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_6522486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522486 prefixEnd_6522486 := by exact prefixLift 6522486
  have htrace : WordTrace (prefixWord ++ tailWord_6522486) baseStart_6522486 baseEnd_6522486 := by
    simpa [prefixWord, tailWord_6522486, baseEnd_6522486] using wordTrace_append hprefix tailTrace_6522486
  have hstable : (prefixWord ++ tailWord_6522486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522486).length < 2 ^ (prefixWord ++ tailWord_6522486).sum := by decide
  have hdescent : baseEnd_6522486 < baseStart_6522486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522489 : List Nat := [1, 2, 1, 3, 3, 1, 4, 1, 1, 2, 4]
def baseStart_6522489 : Nat := 118140960795 + 6522489 * 2 ^ 59
def prefixEnd_6522489 : Nat := 4983230072969 + 3 ^ 40 * 6522489 * 2
def baseEnd_6522489 : Nat := 3349171920663636465491125

theorem tailTrace_6522489 : CollatzResearch.WordTrace tailWord_6522489 prefixEnd_6522489 3349171920663636465491125 := by
  unfold tailWord_6522489
  simp only [CollatzResearch.WordTrace]
  refine ⟨237894717667143780280026521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158596478444762520186684347 237894717667143780280026521)
  ·
    refine ⟨178421038250357835210019891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237894717667143780280026521 178421038250357835210019891)
    ·
      refine ⟨267631557375536752815029837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178421038250357835210019891 267631557375536752815029837)
      ·
        refine ⟨100361834015826282305636189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267631557375536752815029837 100361834015826282305636189)
        ·
          refine ⟨37635687755934855864613571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100361834015826282305636189 37635687755934855864613571)
          ·
            refine ⟨56453531633902283796920357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37635687755934855864613571 56453531633902283796920357)
            ·
              refine ⟨10585037181356678211922567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56453531633902283796920357 10585037181356678211922567)
              ·
                refine ⟨15877555772035017317883851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10585037181356678211922567 15877555772035017317883851)
                ·
                  refine ⟨23816333658052525976825777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15877555772035017317883851 23816333658052525976825777)
                  ·
                    refine ⟨17862250243539394482619333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23816333658052525976825777 17862250243539394482619333)
                    ·
                      refine ⟨3349171920663636465491125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17862250243539394482619333 3349171920663636465491125)
                      ·
                        rfl

theorem cell23_6522489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_6522489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522489 prefixEnd_6522489 := by exact prefixLift 6522489
  have htrace : WordTrace (prefixWord ++ tailWord_6522489) baseStart_6522489 baseEnd_6522489 := by
    simpa [prefixWord, tailWord_6522489, baseEnd_6522489] using wordTrace_append hprefix tailTrace_6522489
  have hstable : (prefixWord ++ tailWord_6522489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522489).length < 2 ^ (prefixWord ++ tailWord_6522489).sum := by decide
  have hdescent : baseEnd_6522489 < baseStart_6522489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522493 : List Nat := [1, 4, 1, 1, 4, 2, 1, 2, 3, 2, 2]
def baseStart_6522493 : Nat := 118140960795 + 6522493 * 2 ^ 59
def prefixEnd_6522493 : Nat := 4983230072969 + 3 ^ 40 * 6522493 * 2
def baseEnd_6522493 : Nat := 3349173974586254449841107

theorem tailTrace_6522493 : CollatzResearch.WordTrace tailWord_6522493 prefixEnd_6522493 3349173974586254449841107 := by
  unfold tailWord_6522493
  simp only [CollatzResearch.WordTrace]
  refine ⟨237894863559129288963172133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158596575706086192642114755 237894863559129288963172133)
  ·
    refine ⟨44605286917336741680594775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237894863559129288963172133 44605286917336741680594775)
    ·
      refine ⟨66907930376005112520892163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44605286917336741680594775 66907930376005112520892163)
      ·
        refine ⟨100361895564007668781338245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66907930376005112520892163 100361895564007668781338245)
        ·
          refine ⟨18817855418251437896500921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100361895564007668781338245 18817855418251437896500921)
          ·
            refine ⟨14113391563688578422375691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18817855418251437896500921 14113391563688578422375691)
            ·
              refine ⟨21170087345532867633563537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14113391563688578422375691 21170087345532867633563537)
              ·
                refine ⟨15877565509149650725172653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21170087345532867633563537 15877565509149650725172653)
                ·
                  refine ⟨5954087065931119021939745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15877565509149650725172653 5954087065931119021939745)
                  ·
                    refine ⟨4465565299448339266454809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5954087065931119021939745 4465565299448339266454809)
                    ·
                      refine ⟨3349173974586254449841107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4465565299448339266454809 3349173974586254449841107)
                      ·
                        rfl

theorem cell23_6522493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_6522493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522493 prefixEnd_6522493 := by exact prefixLift 6522493
  have htrace : WordTrace (prefixWord ++ tailWord_6522493) baseStart_6522493 baseEnd_6522493 := by
    simpa [prefixWord, tailWord_6522493, baseEnd_6522493] using wordTrace_append hprefix tailTrace_6522493
  have hstable : (prefixWord ++ tailWord_6522493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522493).length < 2 ^ (prefixWord ++ tailWord_6522493).sum := by decide
  have hdescent : baseEnd_6522493 < baseStart_6522493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522510 : List Nat := [4, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2]
def baseStart_6522510 : Nat := 118140960795 + 6522510 * 2 ^ 59
def prefixEnd_6522510 : Nat := 4983230072969 + 3 ^ 40 * 6522510 * 2
def baseEnd_6522510 : Nat := 3349182703757380883328529

theorem tailTrace_6522510 : CollatzResearch.WordTrace tailWord_6522510 prefixEnd_6522510 3349182703757380883328529 := by
  unfold tailWord_6522510
  simp only [CollatzResearch.WordTrace]
  refine ⟨29736935450008462608317623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158596989066711800577693989 29736935450008462608317623)
  ·
    refine ⟨44605403175012693912476435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29736935450008462608317623 44605403175012693912476435)
    ·
      refine ⟨66908104762519040868714653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44605403175012693912476435 66908104762519040868714653)
      ·
        refine ⟨25090539285944640325767995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66908104762519040868714653 25090539285944640325767995)
        ·
          refine ⟨37635808928916960488651993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25090539285944640325767995 37635808928916960488651993)
          ·
            refine ⟨28226856696687720366488995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37635808928916960488651993 28226856696687720366488995)
            ·
              refine ⟨42340285045031580549733493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28226856696687720366488995 42340285045031580549733493)
              ·
                refine ⟨3969401722971710676537515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42340285045031580549733493 3969401722971710676537515)
                ·
                  refine ⟨5954102584457566014806273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3969401722971710676537515 5954102584457566014806273)
                  ·
                    refine ⟨4465576938343174511104705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5954102584457566014806273 4465576938343174511104705)
                    ·
                      refine ⟨3349182703757380883328529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4465576938343174511104705 3349182703757380883328529)
                      ·
                        rfl

theorem cell23_6522510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_6522510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522510 prefixEnd_6522510 := by exact prefixLift 6522510
  have htrace : WordTrace (prefixWord ++ tailWord_6522510) baseStart_6522510 baseEnd_6522510 := by
    simpa [prefixWord, tailWord_6522510, baseEnd_6522510] using wordTrace_append hprefix tailTrace_6522510
  have hstable : (prefixWord ++ tailWord_6522510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522510).length < 2 ^ (prefixWord ++ tailWord_6522510).sum := by decide
  have hdescent : baseEnd_6522510 < baseStart_6522510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522543 : List Nat := [1, 1, 2, 1, 2, 4, 5, 1, 2, 1, 3]
def baseStart_6522543 : Nat := 118140960795 + 6522543 * 2 ^ 59
def prefixEnd_6522543 : Nat := 4983230072969 + 3 ^ 40 * 6522543 * 2
def baseEnd_6522543 : Nat := 3349199648618979254215877

theorem tailTrace_6522543 : CollatzResearch.WordTrace tailWord_6522543 prefixEnd_6522543 3349199648618979254215877 := by
  unfold tailWord_6522543
  simp only [CollatzResearch.WordTrace]
  refine ⟨237896687208948147502492283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158597791472632098334994855 237896687208948147502492283)
  ·
    refine ⟨356845030813422221253738425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237896687208948147502492283 356845030813422221253738425)
    ·
      refine ⟨267633773110066665940303819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356845030813422221253738425 267633773110066665940303819)
      ·
        refine ⟨401450659665099998910455729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267633773110066665940303819 401450659665099998910455729)
        ·
          refine ⟨301087994748824999182841797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401450659665099998910455729 301087994748824999182841797)
          ·
            refine ⟨56453999015404687346782837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 301087994748824999182841797 56453999015404687346782837)
            ·
              refine ⟨5292562407694189438760891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56453999015404687346782837 5292562407694189438760891)
              ·
                refine ⟨7938843611541284158141337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5292562407694189438760891 7938843611541284158141337)
                ·
                  refine ⟨5954132708655963118606003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7938843611541284158141337 5954132708655963118606003)
                  ·
                    refine ⟨8931199062983944677909005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5954132708655963118606003 8931199062983944677909005)
                    ·
                      refine ⟨3349199648618979254215877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8931199062983944677909005 3349199648618979254215877)
                      ·
                        rfl

theorem cell23_6522543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 2, 1, 3].length) (baseStart_6522543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522543 prefixEnd_6522543 := by exact prefixLift 6522543
  have htrace : WordTrace (prefixWord ++ tailWord_6522543) baseStart_6522543 baseEnd_6522543 := by
    simpa [prefixWord, tailWord_6522543, baseEnd_6522543] using wordTrace_append hprefix tailTrace_6522543
  have hstable : (prefixWord ++ tailWord_6522543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522543).length < 2 ^ (prefixWord ++ tailWord_6522543).sum := by decide
  have hdescent : baseEnd_6522543 < baseStart_6522543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522552 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 3, 3, 5]
def baseStart_6522552 : Nat := 118140960795 + 6522552 * 2 ^ 59
def prefixEnd_6522552 : Nat := 4983230072969 + 3 ^ 40 * 6522552 * 2
def baseEnd_6522552 : Nat := 3349204269944869719003335

theorem tailTrace_6522552 : CollatzResearch.WordTrace tailWord_6522552 prefixEnd_6522552 3349204269944869719003335 := by
  unfold tailWord_6522552
  simp only [CollatzResearch.WordTrace]
  refine ⟨118948507732957771019784955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158598010310610361359713273 118948507732957771019784955)
  ·
    refine ⟨178422761599436656529677433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118948507732957771019784955 178422761599436656529677433)
    ·
      refine ⟨133817071199577492397258075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178422761599436656529677433 133817071199577492397258075)
      ·
        refine ⟨200725606799366238595887113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133817071199577492397258075 200725606799366238595887113)
        ·
          refine ⟨150544205099524678946915335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200725606799366238595887113 150544205099524678946915335)
          ·
            refine ⟨225816307649287018420373003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150544205099524678946915335 225816307649287018420373003)
            ·
              refine ⟨338724461473930527630559505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225816307649287018420373003 338724461473930527630559505)
              ·
                refine ⟨254043346105447895722919629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338724461473930527630559505 254043346105447895722919629)
                ·
                  refine ⟨95266254789542960896094861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254043346105447895722919629 95266254789542960896094861)
                  ·
                    refine ⟨35724845546078610336035573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95266254789542960896094861 35724845546078610336035573)
                    ·
                      refine ⟨3349204269944869719003335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35724845546078610336035573 3349204269944869719003335)
                      ·
                        rfl

theorem cell23_6522552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_6522552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522552 prefixEnd_6522552 := by exact prefixLift 6522552
  have htrace : WordTrace (prefixWord ++ tailWord_6522552) baseStart_6522552 baseEnd_6522552 := by
    simpa [prefixWord, tailWord_6522552, baseEnd_6522552] using wordTrace_append hprefix tailTrace_6522552
  have hstable : (prefixWord ++ tailWord_6522552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522552).length < 2 ^ (prefixWord ++ tailWord_6522552).sum := by decide
  have hdescent : baseEnd_6522552 < baseStart_6522552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522583 : List Nat := [1, 1, 3, 2, 1, 3, 2, 4, 2, 2, 2]
def baseStart_6522583 : Nat := 118140960795 + 6522583 * 2 ^ 59
def prefixEnd_6522583 : Nat := 4983230072969 + 3 ^ 40 * 6522583 * 2
def baseEnd_6522583 : Nat := 3349220187845159097715693

theorem tailTrace_6522583 : CollatzResearch.WordTrace tailWord_6522583 prefixEnd_6522583 3349220187845159097715693 := by
  unfold tailWord_6522583
  simp only [CollatzResearch.WordTrace]
  refine ⟨237898146128803234333948403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158598764085868822889298935 237898146128803234333948403)
  ·
    refine ⟨356847219193204851500922605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237898146128803234333948403 356847219193204851500922605)
    ·
      refine ⟨133817707197451819312845977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356847219193204851500922605 133817707197451819312845977)
      ·
        refine ⟨100363280398088864484634483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133817707197451819312845977 100363280398088864484634483)
        ·
          refine ⟨150544920597133296726951725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100363280398088864484634483 150544920597133296726951725)
          ·
            refine ⟨56454345223924986272606897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150544920597133296726951725 56454345223924986272606897)
            ·
              refine ⟨42340758917943739704455173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56454345223924986272606897 42340758917943739704455173)
              ·
                refine ⟨7938892297114451194585345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42340758917943739704455173 7938892297114451194585345)
                ·
                  refine ⟨5954169222835838395939009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7938892297114451194585345 5954169222835838395939009)
                  ·
                    refine ⟨4465626917126878796954257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5954169222835838395939009 4465626917126878796954257)
                    ·
                      refine ⟨3349220187845159097715693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4465626917126878796954257 3349220187845159097715693)
                      ·
                        rfl

theorem cell23_6522583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_6522583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522583 prefixEnd_6522583 := by exact prefixLift 6522583
  have htrace : WordTrace (prefixWord ++ tailWord_6522583) baseStart_6522583 baseEnd_6522583 := by
    simpa [prefixWord, tailWord_6522583, baseEnd_6522583] using wordTrace_append hprefix tailTrace_6522583
  have hstable : (prefixWord ++ tailWord_6522583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522583).length < 2 ^ (prefixWord ++ tailWord_6522583).sum := by decide
  have hdescent : baseEnd_6522583 < baseStart_6522583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522600 : List Nat := [2, 1, 4, 1, 3, 2, 1, 3, 2, 2, 2]
def baseStart_6522600 : Nat := 118140960795 + 6522600 * 2 ^ 59
def prefixEnd_6522600 : Nat := 4983230072969 + 3 ^ 40 * 6522600 * 2
def baseEnd_6522600 : Nat := 3349228917016285531203115

theorem tailTrace_6522600 : CollatzResearch.WordTrace tailWord_6522600 prefixEnd_6522600 3349228917016285531203115 := by
  unfold tailWord_6522600
  simp only [CollatzResearch.WordTrace]
  refine ⟨118949383084870823118658627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158599177446494430824878169 118949383084870823118658627)
  ·
    refine ⟨178424074627306234677987941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118949383084870823118658627 178424074627306234677987941)
    ·
      refine ⟨33454513992619919002122739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178424074627306234677987941 33454513992619919002122739)
      ·
        refine ⟨50181770988929878503184109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33454513992619919002122739 50181770988929878503184109)
        ·
          refine ⟨18818164120848704438694041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50181770988929878503184109 18818164120848704438694041)
          ·
            refine ⟨14113623090636528329020531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18818164120848704438694041 14113623090636528329020531)
            ·
              refine ⟨21170434635954792493530797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14113623090636528329020531 21170434635954792493530797)
              ·
                refine ⟨7938912988483047185074049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21170434635954792493530797 7938912988483047185074049)
                ·
                  refine ⟨5954184741362285388805537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7938912988483047185074049 5954184741362285388805537)
                  ·
                    refine ⟨4465638556021714041604153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5954184741362285388805537 4465638556021714041604153)
                    ·
                      refine ⟨3349228917016285531203115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4465638556021714041604153 3349228917016285531203115)
                      ·
                        rfl

theorem cell23_6522600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_6522600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522600 prefixEnd_6522600 := by exact prefixLift 6522600
  have htrace : WordTrace (prefixWord ++ tailWord_6522600) baseStart_6522600 baseEnd_6522600 := by
    simpa [prefixWord, tailWord_6522600, baseEnd_6522600] using wordTrace_append hprefix tailTrace_6522600
  have hstable : (prefixWord ++ tailWord_6522600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522600).length < 2 ^ (prefixWord ++ tailWord_6522600).sum := by decide
  have hdescent : baseEnd_6522600 < baseStart_6522600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522639 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 4]
def baseStart_6522639 : Nat := 118140960795 + 6522639 * 2 ^ 59
def prefixEnd_6522639 : Nat := 4983230072969 + 3 ^ 40 * 6522639 * 2
def baseEnd_6522639 : Nat := 3349248942761810878615435

theorem tailTrace_6522639 : CollatzResearch.WordTrace tailWord_6522639 prefixEnd_6522639 3349248942761810878615435 := by
  unfold tailWord_6522639
  simp only [CollatzResearch.WordTrace]
  refine ⟨237900188616600355897986971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158600125744400237265324647 237900188616600355897986971)
  ·
    refine ⟨356850282924900533846980457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237900188616600355897986971 356850282924900533846980457)
    ·
      refine ⟨267637712193675400385235343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356850282924900533846980457 267637712193675400385235343)
      ·
        refine ⟨401456568290513100577853015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267637712193675400385235343 401456568290513100577853015)
        ·
          refine ⟨602184852435769650866779523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401456568290513100577853015 602184852435769650866779523)
          ·
            refine ⟨903277278653654476300169285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602184852435769650866779523 903277278653654476300169285)
            ·
              refine ⟨169364489747560214306281741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 903277278653654476300169285 169364489747560214306281741)
              ·
                refine ⟨63511683655335080364855653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169364489747560214306281741 63511683655335080364855653)
                ·
                  refine ⟨11908440685375327568410435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63511683655335080364855653 11908440685375327568410435)
                  ·
                    refine ⟨17862661028062991352615653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11908440685375327568410435 17862661028062991352615653)
                    ·
                      refine ⟨3349248942761810878615435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17862661028062991352615653 3349248942761810878615435)
                      ·
                        rfl

theorem cell23_6522639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 4].length) (baseStart_6522639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522639 prefixEnd_6522639 := by exact prefixLift 6522639
  have htrace : WordTrace (prefixWord ++ tailWord_6522639) baseStart_6522639 baseEnd_6522639 := by
    simpa [prefixWord, tailWord_6522639, baseEnd_6522639] using wordTrace_append hprefix tailTrace_6522639
  have hstable : (prefixWord ++ tailWord_6522639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522639).length < 2 ^ (prefixWord ++ tailWord_6522639).sum := by decide
  have hdescent : baseEnd_6522639 < baseStart_6522639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522670 : List Nat := [4, 1, 3, 2, 2, 2, 1, 1, 2, 5]
def baseStart_6522670 : Nat := 118140960795 + 6522670 * 2 ^ 59
def prefixEnd_6522670 : Nat := 4983230072969 + 3 ^ 40 * 6522670 * 2
def baseEnd_6522670 : Nat := 1116421620220700085775931

theorem tailTrace_6522670 : CollatzResearch.WordTrace tailWord_6522670 prefixEnd_6522670 1116421620220700085775931 := by
  unfold tailWord_6522670
  simp only [CollatzResearch.WordTrace]
  refine ⟨29737664909936006024045683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158600879519658698794910309 29737664909936006024045683)
  ·
    refine ⟨44606497364904009036068525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29737664909936006024045683 44606497364904009036068525)
    ·
      refine ⟨16727436511839003388525697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44606497364904009036068525 16727436511839003388525697)
      ·
        refine ⟨12545577383879252541394273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16727436511839003388525697 12545577383879252541394273)
        ·
          refine ⟨9409183037909439406045705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12545577383879252541394273 9409183037909439406045705)
          ·
            refine ⟨7056887278432079554534279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9409183037909439406045705 7056887278432079554534279)
            ·
              refine ⟨10585330917648119331801419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7056887278432079554534279 10585330917648119331801419)
              ·
                refine ⟨15877996376472178997702129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10585330917648119331801419 15877996376472178997702129)
                ·
                  refine ⟨11908497282354134248276597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15877996376472178997702129 11908497282354134248276597)
                  ·
                    refine ⟨1116421620220700085775931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11908497282354134248276597 1116421620220700085775931)
                    ·
                      rfl

theorem cell23_6522670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_6522670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522670 prefixEnd_6522670 := by exact prefixLift 6522670
  have htrace : WordTrace (prefixWord ++ tailWord_6522670) baseStart_6522670 baseEnd_6522670 := by
    simpa [prefixWord, tailWord_6522670, baseEnd_6522670] using wordTrace_append hprefix tailTrace_6522670
  have hstable : (prefixWord ++ tailWord_6522670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522670).length < 2 ^ (prefixWord ++ tailWord_6522670).sum := by decide
  have hdescent : baseEnd_6522670 < baseStart_6522670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522673 : List Nat := [1, 2, 2, 3, 2, 4, 1, 1, 2, 1, 4]
def baseStart_6522673 : Nat := 118140960795 + 6522673 * 2 ^ 59
def prefixEnd_6522673 : Nat := 4983230072969 + 3 ^ 40 * 6522673 * 2
def baseEnd_6522673 : Nat := 3349266401104063745590279

theorem tailTrace_6522673 : CollatzResearch.WordTrace tailWord_6522673 prefixEnd_6522673 3349266401104063745590279 := by
  unfold tailWord_6522673
  simp only [CollatzResearch.WordTrace]
  refine ⟨237901428698477179704724673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158600952465651453136483115 237901428698477179704724673)
  ·
    refine ⟨178426071523857884778543505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237901428698477179704724673 178426071523857884778543505)
    ·
      refine ⟨133819553642893413583907629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178426071523857884778543505 133819553642893413583907629)
      ·
        refine ⟨50182332616085030093965361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133819553642893413583907629 50182332616085030093965361)
        ·
          refine ⟨37636749462063772570474021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50182332616085030093965361 37636749462063772570474021)
          ·
            refine ⟨7056890524136957356963879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37636749462063772570474021 7056890524136957356963879)
            ·
              refine ⟨10585335786205436035445819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7056890524136957356963879 10585335786205436035445819)
              ·
                refine ⟨15878003679308154053168729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10585335786205436035445819 15878003679308154053168729)
                ·
                  refine ⟨11908502759481115539876547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15878003679308154053168729 11908502759481115539876547)
                  ·
                    refine ⟨17862754139221673309814821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11908502759481115539876547 17862754139221673309814821)
                    ·
                      refine ⟨3349266401104063745590279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17862754139221673309814821 3349266401104063745590279)
                      ·
                        rfl

theorem cell23_6522673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_6522673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522673 prefixEnd_6522673 := by exact prefixLift 6522673
  have htrace : WordTrace (prefixWord ++ tailWord_6522673) baseStart_6522673 baseEnd_6522673 := by
    simpa [prefixWord, tailWord_6522673, baseEnd_6522673] using wordTrace_append hprefix tailTrace_6522673
  have hstable : (prefixWord ++ tailWord_6522673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522673).length < 2 ^ (prefixWord ++ tailWord_6522673).sum := by decide
  have hdescent : baseEnd_6522673 < baseStart_6522673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522686 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_6522686 : Nat := 118140960795 + 6522686 * 2 ^ 59
def prefixEnd_6522686 : Nat := 4983230072969 + 3 ^ 40 * 6522686 * 2
def baseEnd_6522686 : Nat := 3349273076352572194727719

theorem tailTrace_6522686 : CollatzResearch.WordTrace tailWord_6522686 prefixEnd_6522686 3349273076352572194727719 := by
  unfold tailWord_6522686
  simp only [CollatzResearch.WordTrace]
  refine ⟨29737737855928760365618489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158601268564953388616631941 29737737855928760365618489)
  ·
    refine ⟨22303303391946570274213867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29737737855928760365618489 22303303391946570274213867)
    ·
      refine ⟨33454955087919855411320801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22303303391946570274213867 33454955087919855411320801)
      ·
        refine ⟨25091216315939891558490601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33454955087919855411320801 25091216315939891558490601)
        ·
          refine ⟨18818412236954918668867951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25091216315939891558490601 18818412236954918668867951)
          ·
            refine ⟨28227618355432378003301927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18818412236954918668867951 28227618355432378003301927)
            ·
              refine ⟨42341427533148567004952891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28227618355432378003301927 42341427533148567004952891)
              ·
                refine ⟨63512141299722850507429337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42341427533148567004952891 63512141299722850507429337)
                ·
                  refine ⟨47634105974792137880572003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63512141299722850507429337 47634105974792137880572003)
                  ·
                    refine ⟨71451158962188206820858005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47634105974792137880572003 71451158962188206820858005)
                    ·
                      refine ⟨3349273076352572194727719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71451158962188206820858005 3349273076352572194727719)
                      ·
                        rfl

theorem cell23_6522686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_6522686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522686 prefixEnd_6522686 := by exact prefixLift 6522686
  have htrace : WordTrace (prefixWord ++ tailWord_6522686) baseStart_6522686 baseEnd_6522686 := by
    simpa [prefixWord, tailWord_6522686, baseEnd_6522686] using wordTrace_append hprefix tailTrace_6522686
  have hstable : (prefixWord ++ tailWord_6522686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522686).length < 2 ^ (prefixWord ++ tailWord_6522686).sum := by decide
  have hdescent : baseEnd_6522686 < baseStart_6522686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522696 : List Nat := [2, 1, 3, 1, 1, 4, 3, 2, 6]
def baseStart_6522696 : Nat := 118140960795 + 6522696 * 2 ^ 59
def prefixEnd_6522696 : Nat := 4983230072969 + 3 ^ 40 * 6522696 * 2
def baseEnd_6522696 : Nat := 372142023462124128400297

theorem tailTrace_6522696 : CollatzResearch.WordTrace tailWord_6522696 prefixEnd_6522696 372142023462124128400297 := by
  unfold tailWord_6522696
  simp only [CollatzResearch.WordTrace]
  refine ⟨118951133788696927316405971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158601511718262569755207961 118951133788696927316405971)
  ·
    refine ⟨178426700683045390974608957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118951133788696927316405971 178426700683045390974608957)
    ·
      refine ⟨66910012756142021615478359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178426700683045390974608957 66910012756142021615478359)
      ·
        refine ⟨100365019134213032423217539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66910012756142021615478359 100365019134213032423217539)
        ·
          refine ⟨150547528701319548634826309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100365019134213032423217539 150547528701319548634826309)
          ·
            refine ⟨28227661631497415369029933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150547528701319548634826309 28227661631497415369029933)
            ·
              refine ⟨10585373111811530763386225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28227661631497415369029933 10585373111811530763386225)
              ·
                refine ⟨7939029833858648072539669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10585373111811530763386225 7939029833858648072539669)
                ·
                  refine ⟨372142023462124128400297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7939029833858648072539669 372142023462124128400297)
                  ·
                    rfl

theorem cell23_6522696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 6].length) (baseStart_6522696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522696 prefixEnd_6522696 := by exact prefixLift 6522696
  have htrace : WordTrace (prefixWord ++ tailWord_6522696) baseStart_6522696 baseEnd_6522696 := by
    simpa [prefixWord, tailWord_6522696, baseEnd_6522696] using wordTrace_append hprefix tailTrace_6522696
  have hstable : (prefixWord ++ tailWord_6522696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522696).length < 2 ^ (prefixWord ++ tailWord_6522696).sum := by decide
  have hdescent : baseEnd_6522696 < baseStart_6522696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522729 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 2, 5, 4]
def baseStart_6522729 : Nat := 118140960795 + 6522729 * 2 ^ 59
def prefixEnd_6522729 : Nat := 4983230072969 + 3 ^ 40 * 6522729 * 2
def baseEnd_6522729 : Nat := 3349295156020715526490021

theorem tailTrace_6522729 : CollatzResearch.WordTrace tailWord_6522729 prefixEnd_6522729 3349295156020715526490021 := by
  unfold tailWord_6522729
  simp only [CollatzResearch.WordTrace]
  refine ⟨237903471186274301268763241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158602314124182867512508827 237903471186274301268763241)
  ·
    refine ⟨178427603389705725951572431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237903471186274301268763241 178427603389705725951572431)
    ·
      refine ⟨267641405084558588927358647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178427603389705725951572431 267641405084558588927358647)
      ·
        refine ⟨401462107626837883391037971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267641405084558588927358647 401462107626837883391037971)
        ·
          refine ⟨602193161440256825086556957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401462107626837883391037971 602193161440256825086556957)
          ·
            refine ⟨225822435540096309407458859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 602193161440256825086556957 225822435540096309407458859)
            ·
              refine ⟨338733653310144464111188289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225822435540096309407458859 338733653310144464111188289)
              ·
                refine ⟨254050239982608348083391217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338733653310144464111188289 254050239982608348083391217)
                ·
                  refine ⟨190537679986956261062543413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254050239982608348083391217 190537679986956261062543413)
                  ·
                    refine ⟨17862907498777149474613445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 190537679986956261062543413 17862907498777149474613445)
                    ·
                      refine ⟨3349295156020715526490021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17862907498777149474613445 3349295156020715526490021)
                      ·
                        rfl

theorem cell23_6522729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_6522729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522729 prefixEnd_6522729 := by exact prefixLift 6522729
  have htrace : WordTrace (prefixWord ++ tailWord_6522729) baseStart_6522729 baseEnd_6522729 := by
    simpa [prefixWord, tailWord_6522729, baseEnd_6522729] using wordTrace_append hprefix tailTrace_6522729
  have hstable : (prefixWord ++ tailWord_6522729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522729).length < 2 ^ (prefixWord ++ tailWord_6522729).sum := by decide
  have hdescent : baseEnd_6522729 < baseStart_6522729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522733 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 1, 5, 2]
def baseStart_6522733 : Nat := 118140960795 + 6522733 * 2 ^ 59
def prefixEnd_6522733 : Nat := 4983230072969 + 3 ^ 40 * 6522733 * 2
def baseEnd_6522733 : Nat := 3349297209943333510840003

theorem tailTrace_6522733 : CollatzResearch.WordTrace tailWord_6522733 prefixEnd_6522733 3349297209943333510840003 := by
  unfold tailWord_6522733
  simp only [CollatzResearch.WordTrace]
  refine ⟨237903617078259809951908853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158602411385506539967939235 237903617078259809951908853)
  ·
    refine ⟨22303464101086857182991455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237903617078259809951908853 22303464101086857182991455)
    ·
      refine ⟨33455196151630285774487183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22303464101086857182991455 33455196151630285774487183)
      ·
        refine ⟨50182794227445428661730775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33455196151630285774487183 50182794227445428661730775)
        ·
          refine ⟨75274191341168142992596163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50182794227445428661730775 75274191341168142992596163)
          ·
            refine ⟨112911287011752214488894245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75274191341168142992596163 112911287011752214488894245)
            ·
              refine ⟨21170866314703540216667671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112911287011752214488894245 21170866314703540216667671)
              ·
                refine ⟨31756299472055310325001507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21170866314703540216667671 31756299472055310325001507)
                ·
                  refine ⟨47634449208082965487502261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31756299472055310325001507 47634449208082965487502261)
                  ·
                    refine ⟨4465729613257778014453337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47634449208082965487502261 4465729613257778014453337)
                    ·
                      refine ⟨3349297209943333510840003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4465729613257778014453337 3349297209943333510840003)
                      ·
                        rfl

theorem cell23_6522733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_6522733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522733 prefixEnd_6522733 := by exact prefixLift 6522733
  have htrace : WordTrace (prefixWord ++ tailWord_6522733) baseStart_6522733 baseEnd_6522733 := by
    simpa [prefixWord, tailWord_6522733, baseEnd_6522733] using wordTrace_append hprefix tailTrace_6522733
  have hstable : (prefixWord ++ tailWord_6522733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522733).length < 2 ^ (prefixWord ++ tailWord_6522733).sum := by decide
  have hdescent : baseEnd_6522733 < baseStart_6522733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522739 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 3, 6]
def baseStart_6522739 : Nat := 118140960795 + 6522739 * 2 ^ 59
def prefixEnd_6522739 : Nat := 4983230072969 + 3 ^ 40 * 6522739 * 2
def baseEnd_6522739 : Nat := 1116433430275753495788325

theorem tailTrace_6522739 : CollatzResearch.WordTrace tailWord_6522739 prefixEnd_6522739 1116433430275753495788325 := by
  unfold tailWord_6522739
  simp only [CollatzResearch.WordTrace]
  refine ⟨237903835916238072976627271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158602557277492048651084847 237903835916238072976627271)
  ·
    refine ⟨356855753874357109464940907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237903835916238072976627271 356855753874357109464940907)
    ·
      refine ⟨535283630811535664197411361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356855753874357109464940907 535283630811535664197411361)
      ·
        refine ⟨401462723108651748148058521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535283630811535664197411361 401462723108651748148058521)
        ·
          refine ⟨301097042331488811111043891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401462723108651748148058521 301097042331488811111043891)
          ·
            refine ⟨451645563497233216666565837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301097042331488811111043891 451645563497233216666565837)
            ·
              refine ⟨169367086311462456249962189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 451645563497233216666565837 169367086311462456249962189)
              ·
                refine ⟨63512657366798421093735821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169367086311462456249962189 63512657366798421093735821)
                ·
                  refine ⟨23817246512549407910150933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63512657366798421093735821 23817246512549407910150933)
                  ·
                    refine ⟨1116433430275753495788325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23817246512549407910150933 1116433430275753495788325)
                    ·
                      rfl

theorem cell23_6522739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 6].length) (baseStart_6522739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522739 prefixEnd_6522739 := by exact prefixLift 6522739
  have htrace : WordTrace (prefixWord ++ tailWord_6522739) baseStart_6522739 baseEnd_6522739 := by
    simpa [prefixWord, tailWord_6522739, baseEnd_6522739] using wordTrace_append hprefix tailTrace_6522739
  have hstable : (prefixWord ++ tailWord_6522739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522739).length < 2 ^ (prefixWord ++ tailWord_6522739).sum := by decide
  have hdescent : baseEnd_6522739 < baseStart_6522739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522757 : List Nat := [1, 3, 1, 1, 3, 2, 5, 2, 1, 1, 3]
def baseStart_6522757 : Nat := 118140960795 + 6522757 * 2 ^ 59
def prefixEnd_6522757 : Nat := 4983230072969 + 3 ^ 40 * 6522757 * 2
def baseEnd_6522757 : Nat := 3349309533479041416939893

theorem tailTrace_6522757 : CollatzResearch.WordTrace tailWord_6522757 prefixEnd_6522757 3349309533479041416939893 := by
  unfold tailWord_6522757
  simp only [CollatzResearch.WordTrace]
  refine ⟨237904492430172862050782525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158602994953448574700521683 237904492430172862050782525)
  ·
    refine ⟨89214184661314823269043447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237904492430172862050782525 89214184661314823269043447)
    ·
      refine ⟨133821276991972234903565171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89214184661314823269043447 133821276991972234903565171)
      ·
        refine ⟨200731915487958352355347757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133821276991972234903565171 200731915487958352355347757)
        ·
          refine ⟨75274468307984382133255409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200731915487958352355347757 75274468307984382133255409)
          ·
            refine ⟨56455851230988286599941557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75274468307984382133255409 56455851230988286599941557)
            ·
              refine ⟨5292736052905151868744521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56455851230988286599941557 5292736052905151868744521)
              ·
                refine ⟨3969552039678863901558391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5292736052905151868744521 3969552039678863901558391)
                ·
                  refine ⟨5954328059518295852337587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3969552039678863901558391 5954328059518295852337587)
                  ·
                    refine ⟨8931492089277443778506381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5954328059518295852337587 8931492089277443778506381)
                    ·
                      refine ⟨3349309533479041416939893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8931492089277443778506381 3349309533479041416939893)
                      ·
                        rfl

theorem cell23_6522757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 1, 1, 3].length) (baseStart_6522757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522757 prefixEnd_6522757 := by exact prefixLift 6522757
  have htrace : WordTrace (prefixWord ++ tailWord_6522757) baseStart_6522757 baseEnd_6522757 := by
    simpa [prefixWord, tailWord_6522757, baseEnd_6522757] using wordTrace_append hprefix tailTrace_6522757
  have hstable : (prefixWord ++ tailWord_6522757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522757).length < 2 ^ (prefixWord ++ tailWord_6522757).sum := by decide
  have hdescent : baseEnd_6522757 < baseStart_6522757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522769 : List Nat := [1, 2, 2, 1, 1, 1, 5, 10]
def baseStart_6522769 : Nat := 118140960795 + 6522769 * 2 ^ 59
def prefixEnd_6522769 : Nat := 4983230072969 + 3 ^ 40 * 6522769 * 2
def baseEnd_6522769 : Nat := 124048729453588717407031

theorem tailTrace_6522769 : CollatzResearch.WordTrace tailWord_6522769 prefixEnd_6522769 124048729453588717407031 := by
  unfold tailWord_6522769
  simp only [CollatzResearch.WordTrace]
  refine ⟨237904930106129388100219361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158603286737419592066812907 237904930106129388100219361)
  ·
    refine ⟨178428697579597041075164521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237904930106129388100219361 178428697579597041075164521)
    ·
      refine ⟨133821523184697780806373391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178428697579597041075164521 133821523184697780806373391)
      ·
        refine ⟨200732284777046671209560087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133821523184697780806373391 200732284777046671209560087)
        ·
          refine ⟨301098427165570006814340131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200732284777046671209560087 301098427165570006814340131)
          ·
            refine ⟨451647640748355010221510197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301098427165570006814340131 451647640748355010221510197)
            ·
              refine ⟨42341966320158282208266581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 451647640748355010221510197 42341966320158282208266581)
              ·
                refine ⟨124048729453588717407031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42341966320158282208266581 124048729453588717407031)
                ·
                  rfl

theorem cell23_6522769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 10].length) (baseStart_6522769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522769 prefixEnd_6522769 := by exact prefixLift 6522769
  have htrace : WordTrace (prefixWord ++ tailWord_6522769) baseStart_6522769 baseEnd_6522769 := by
    simpa [prefixWord, tailWord_6522769, baseEnd_6522769] using wordTrace_append hprefix tailTrace_6522769
  have hstable : (prefixWord ++ tailWord_6522769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522769).length < 2 ^ (prefixWord ++ tailWord_6522769).sum := by decide
  have hdescent : baseEnd_6522769 < baseStart_6522769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522773 : List Nat := [1, 3, 2, 1, 1, 3, 3, 3, 2, 4]
def baseStart_6522773 : Nat := 118140960795 + 6522773 * 2 ^ 59
def prefixEnd_6522773 : Nat := 4983230072969 + 3 ^ 40 * 6522773 * 2
def baseEnd_6522773 : Nat := 1116439249723171118113273

theorem tailTrace_6522773 : CollatzResearch.WordTrace tailWord_6522773 prefixEnd_6522773 1116439249723171118113273 := by
  unfold tailWord_6522773
  simp only [CollatzResearch.WordTrace]
  refine ⟨237905075998114896783364973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158603383998743264522243315 237905075998114896783364973)
  ·
    refine ⟨89214403499293086293761865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237905075998114896783364973 89214403499293086293761865)
    ·
      refine ⟨66910802624469814720321399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89214403499293086293761865 66910802624469814720321399)
      ·
        refine ⟨100366203936704722080482099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66910802624469814720321399 100366203936704722080482099)
        ·
          refine ⟨150549305905057083120723149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100366203936704722080482099 150549305905057083120723149)
          ·
            refine ⟨56455989714396406170271181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150549305905057083120723149 56455989714396406170271181)
            ·
              refine ⟨21170996142898652313851693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56455989714396406170271181 21170996142898652313851693)
              ·
                refine ⟨7939123553586994617694385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21170996142898652313851693 7939123553586994617694385)
                ·
                  refine ⟨5954342665190245963270789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7939123553586994617694385 5954342665190245963270789)
                  ·
                    refine ⟨1116439249723171118113273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5954342665190245963270789 1116439249723171118113273)
                    ·
                      rfl

theorem cell23_6522773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_6522773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522773 prefixEnd_6522773 := by exact prefixLift 6522773
  have htrace : WordTrace (prefixWord ++ tailWord_6522773) baseStart_6522773 baseEnd_6522773 := by
    simpa [prefixWord, tailWord_6522773, baseEnd_6522773] using wordTrace_append hprefix tailTrace_6522773
  have hstable : (prefixWord ++ tailWord_6522773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522773).length < 2 ^ (prefixWord ++ tailWord_6522773).sum := by decide
  have hdescent : baseEnd_6522773 < baseStart_6522773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522780 : List Nat := [2, 2, 3, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_6522780 : Nat := 118140960795 + 6522780 * 2 ^ 59
def prefixEnd_6522780 : Nat := 4983230072969 + 3 ^ 40 * 6522780 * 2
def baseEnd_6522780 : Nat := 3349321343534094826952287

theorem tailTrace_6522780 : CollatzResearch.WordTrace tailWord_6522780 prefixEnd_6522780 3349321343534094826952287 := by
  unfold tailWord_6522780
  simp only [CollatzResearch.WordTrace]
  refine ⟨118952665654544768489434897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158603554206059691319246529 118952665654544768489434897)
  ·
    refine ⟨89214499240908576367076173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118952665654544768489434897 89214499240908576367076173)
    ·
      refine ⟨33455437215340716137653565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89214499240908576367076173 33455437215340716137653565)
      ·
        refine ⟨12545788955752768551620087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33455437215340716137653565 12545788955752768551620087)
        ·
          refine ⟨18818683433629152827430131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12545788955752768551620087 18818683433629152827430131)
          ·
            refine ⟨28228025150443729241145197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18818683433629152827430131 28228025150443729241145197)
            ·
              refine ⟨10585509431416398465429449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28228025150443729241145197 10585509431416398465429449)
              ·
                refine ⟨7939132073562298849072087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10585509431416398465429449 7939132073562298849072087)
                ·
                  refine ⟨11908698110343448273608131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7939132073562298849072087 11908698110343448273608131)
                  ·
                    refine ⟨17863047165515172410412197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11908698110343448273608131 17863047165515172410412197)
                    ·
                      refine ⟨3349321343534094826952287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17863047165515172410412197 3349321343534094826952287)
                      ·
                        rfl

theorem cell23_6522780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_6522780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522780 prefixEnd_6522780 := by exact prefixLift 6522780
  have htrace : WordTrace (prefixWord ++ tailWord_6522780) baseStart_6522780 baseEnd_6522780 := by
    simpa [prefixWord, tailWord_6522780, baseEnd_6522780] using wordTrace_append hprefix tailTrace_6522780
  have hstable : (prefixWord ++ tailWord_6522780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522780).length < 2 ^ (prefixWord ++ tailWord_6522780).sum := by decide
  have hdescent : baseEnd_6522780 < baseStart_6522780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522814 : List Nat := [4, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2]
def baseStart_6522814 : Nat := 118140960795 + 6522814 * 2 ^ 59
def prefixEnd_6522814 : Nat := 4983230072969 + 3 ^ 40 * 6522814 * 2
def baseEnd_6522814 : Nat := 3349338801876347693927131

theorem tailTrace_6522814 : CollatzResearch.WordTrace tailWord_6522814 prefixEnd_6522814 3349338801876347693927131 := by
  unfold tailWord_6522814
  simp only [CollatzResearch.WordTrace]
  refine ⟨29738321423870795098200937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158604380927310907190404997 29738321423870795098200937)
  ·
    refine ⟨22303741067903096323650703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29738321423870795098200937 22303741067903096323650703)
    ·
      refine ⟨33455611601854644485476055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22303741067903096323650703 33455611601854644485476055)
      ·
        refine ⟨50183417402781966728214083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33455611601854644485476055 50183417402781966728214083)
        ·
          refine ⟨75275126104172950092321125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50183417402781966728214083 75275126104172950092321125)
          ·
            refine ⟨14114086144532428142310211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75275126104172950092321125 14114086144532428142310211)
            ·
              refine ⟨21171129216798642213465317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14114086144532428142310211 21171129216798642213465317)
              ·
                refine ⟨3969586728149745415024747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21171129216798642213465317 3969586728149745415024747)
                ·
                  refine ⟨5954380092224618122537121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3969586728149745415024747 5954380092224618122537121)
                  ·
                    refine ⟨4465785069168463591902841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5954380092224618122537121 4465785069168463591902841)
                    ·
                      refine ⟨3349338801876347693927131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4465785069168463591902841 3349338801876347693927131)
                      ·
                        rfl

theorem cell23_6522814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_6522814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522814 prefixEnd_6522814 := by exact prefixLift 6522814
  have htrace : WordTrace (prefixWord ++ tailWord_6522814) baseStart_6522814 baseEnd_6522814 := by
    simpa [prefixWord, tailWord_6522814, baseEnd_6522814] using wordTrace_append hprefix tailTrace_6522814
  have hstable : (prefixWord ++ tailWord_6522814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522814).length < 2 ^ (prefixWord ++ tailWord_6522814).sum := by decide
  have hdescent : baseEnd_6522814 < baseStart_6522814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522830 : List Nat := [4, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3]
def baseStart_6522830 : Nat := 118140960795 + 6522830 * 2 ^ 59
def prefixEnd_6522830 : Nat := 4983230072969 + 3 ^ 40 * 6522830 * 2
def baseEnd_6522830 : Nat := 3349347017566819631327057

theorem tailTrace_6522830 : CollatzResearch.WordTrace tailWord_6522830 prefixEnd_6522830 3349347017566819631327057 := by
  unfold tailWord_6522830
  simp only [CollatzResearch.WordTrace]
  refine ⟨29738394369863549439773743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158604769972605597012126629 29738394369863549439773743)
  ·
    refine ⟨44607591554795324159660615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29738394369863549439773743 44607591554795324159660615)
    ·
      refine ⟨66911387332192986239490923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44607591554795324159660615 66911387332192986239490923)
      ·
        refine ⟨100367080998289479359236385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66911387332192986239490923 100367080998289479359236385)
        ·
          refine ⟨75275310748717109519427289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100367080998289479359236385 75275310748717109519427289)
          ·
            refine ⟨56456483061537832139570467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75275310748717109519427289 56456483061537832139570467)
            ·
              refine ⟨84684724592306748209355701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56456483061537832139570467 84684724592306748209355701)
              ·
                refine ⟨7939192930528757644627097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84684724592306748209355701 7939192930528757644627097)
                ·
                  refine ⟨5954394697896568233470323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7939192930528757644627097 5954394697896568233470323)
                  ·
                    refine ⟨8931592046844852350205485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5954394697896568233470323 8931592046844852350205485)
                    ·
                      refine ⟨3349347017566819631327057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8931592046844852350205485 3349347017566819631327057)
                      ·
                        rfl

theorem cell23_6522830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_6522830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522830 prefixEnd_6522830 := by exact prefixLift 6522830
  have htrace : WordTrace (prefixWord ++ tailWord_6522830) baseStart_6522830 baseEnd_6522830 := by
    simpa [prefixWord, tailWord_6522830, baseEnd_6522830] using wordTrace_append hprefix tailTrace_6522830
  have hstable : (prefixWord ++ tailWord_6522830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522830).length < 2 ^ (prefixWord ++ tailWord_6522830).sum := by decide
  have hdescent : baseEnd_6522830 < baseStart_6522830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522840 : List Nat := [2, 1, 2, 2, 2, 2, 2, 4, 1, 3, 2]
def baseStart_6522840 : Nat := 118140960795 + 6522840 * 2 ^ 59
def prefixEnd_6522840 : Nat := 4983230072969 + 3 ^ 40 * 6522840 * 2
def baseEnd_6522840 : Nat := 3349352152373364592202011

theorem tailTrace_6522840 : CollatzResearch.WordTrace tailWord_6522840 prefixEnd_6522840 3349352152373364592202011 := by
  unfold tailWord_6522840
  simp only [CollatzResearch.WordTrace]
  refine ⟨118953759844436083613026987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158605013125914778150702649 118953759844436083613026987)
  ·
    refine ⟨178430639766654125419540481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118953759844436083613026987 178430639766654125419540481)
    ·
      refine ⟨133822979824990594064655361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178430639766654125419540481 133822979824990594064655361)
      ·
        refine ⟨100367234868742945548491521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133822979824990594064655361 100367234868742945548491521)
        ·
          refine ⟨75275426151557209161368641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100367234868742945548491521 75275426151557209161368641)
          ·
            refine ⟨56456569613667906871026481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75275426151557209161368641 56456569613667906871026481)
            ·
              refine ⟨42342427210250930153269861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56456569613667906871026481 42342427210250930153269861)
              ·
                refine ⟨7939205101922049403738099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42342427210250930153269861 7939205101922049403738099)
                ·
                  refine ⟨11908807652883074105607149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7939205101922049403738099 11908807652883074105607149)
                  ·
                    refine ⟨4465802869831152789602681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11908807652883074105607149 4465802869831152789602681)
                    ·
                      refine ⟨3349352152373364592202011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4465802869831152789602681 3349352152373364592202011)
                      ·
                        rfl

theorem cell23_6522840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_6522840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522840 prefixEnd_6522840 := by exact prefixLift 6522840
  have htrace : WordTrace (prefixWord ++ tailWord_6522840) baseStart_6522840 baseEnd_6522840 := by
    simpa [prefixWord, tailWord_6522840, baseEnd_6522840] using wordTrace_append hprefix tailTrace_6522840
  have hstable : (prefixWord ++ tailWord_6522840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522840).length < 2 ^ (prefixWord ++ tailWord_6522840).sum := by decide
  have hdescent : baseEnd_6522840 < baseStart_6522840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522856 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_6522856 : Nat := 118140960795 + 6522856 * 2 ^ 59
def prefixEnd_6522856 : Nat := 4983230072969 + 3 ^ 40 * 6522856 * 2
def baseEnd_6522856 : Nat := 3349360368063836529601937

theorem tailTrace_6522856 : CollatzResearch.WordTrace tailWord_6522856 prefixEnd_6522856 3349360368063836529601937 := by
  unfold tailWord_6522856
  simp only [CollatzResearch.WordTrace]
  refine ⟨118954051628407100979318211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158605402171209467972424281 118954051628407100979318211)
  ·
    refine ⟨178431077442610651468977317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118954051628407100979318211 178431077442610651468977317)
    ·
      refine ⟨33455827020489497150433247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178431077442610651468977317 33455827020489497150433247)
      ·
        refine ⟨50183740530734245725649871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33455827020489497150433247 50183740530734245725649871)
        ·
          refine ⟨75275610796101368588474807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50183740530734245725649871 75275610796101368588474807)
          ·
            refine ⟨112913416194152052882712211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75275610796101368588474807 112913416194152052882712211)
            ·
              refine ⟨169370124291228079324068317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112913416194152052882712211 169370124291228079324068317)
              ·
                refine ⟨63513796609210529746525619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169370124291228079324068317 63513796609210529746525619)
                ·
                  refine ⟨95270694913815794619788429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63513796609210529746525619 95270694913815794619788429)
                  ·
                    refine ⟨35726510592680922982420661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95270694913815794619788429 35726510592680922982420661)
                    ·
                      refine ⟨3349360368063836529601937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35726510592680922982420661 3349360368063836529601937)
                      ·
                        rfl

theorem cell23_6522856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_6522856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522856 prefixEnd_6522856 := by exact prefixLift 6522856
  have htrace : WordTrace (prefixWord ++ tailWord_6522856) baseStart_6522856 baseEnd_6522856 := by
    simpa [prefixWord, tailWord_6522856, baseEnd_6522856] using wordTrace_append hprefix tailTrace_6522856
  have hstable : (prefixWord ++ tailWord_6522856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522856).length < 2 ^ (prefixWord ++ tailWord_6522856).sum := by decide
  have hdescent : baseEnd_6522856 < baseStart_6522856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522887 : List Nat := [1, 1, 4, 3, 1, 4, 1, 1, 1, 4, 2]
def baseStart_6522887 : Nat := 118140960795 + 6522887 * 2 ^ 59
def prefixEnd_6522887 : Nat := 4983230072969 + 3 ^ 40 * 6522887 * 2
def baseEnd_6522887 : Nat := 3349376285964125908314295

theorem tailTrace_6522887 : CollatzResearch.WordTrace tailWord_6522887 prefixEnd_6522887 3349376285964125908314295 := by
  unfold tailWord_6522887
  simp only [CollatzResearch.WordTrace]
  refine ⟨237909233919701894253014915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158606155946467929502009943 237909233919701894253014915)
  ·
    refine ⟨356863850879552841379522373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237909233919701894253014915 356863850879552841379522373)
    ·
      refine ⟨66911972039916157758660445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 356863850879552841379522373 66911972039916157758660445)
      ·
        refine ⟨25091989514968559159497667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66911972039916157758660445 25091989514968559159497667)
        ·
          refine ⟨37637984272452838739246501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25091989514968559159497667 37637984272452838739246501)
          ·
            refine ⟨7057122051084907263608719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37637984272452838739246501 7057122051084907263608719)
            ·
              refine ⟨10585683076627360895413079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7057122051084907263608719 10585683076627360895413079)
              ·
                refine ⟨15878524614941041343119619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10585683076627360895413079 15878524614941041343119619)
                ·
                  refine ⟨23817786922411562014679429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15878524614941041343119619 23817786922411562014679429)
                  ·
                    refine ⟨4465835047952167877752393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23817786922411562014679429 4465835047952167877752393)
                    ·
                      refine ⟨3349376285964125908314295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4465835047952167877752393 3349376285964125908314295)
                      ·
                        rfl

theorem cell23_6522887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_6522887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522887 prefixEnd_6522887 := by exact prefixLift 6522887
  have htrace : WordTrace (prefixWord ++ tailWord_6522887) baseStart_6522887 baseEnd_6522887 := by
    simpa [prefixWord, tailWord_6522887, baseEnd_6522887] using wordTrace_append hprefix tailTrace_6522887
  have hstable : (prefixWord ++ tailWord_6522887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522887).length < 2 ^ (prefixWord ++ tailWord_6522887).sum := by decide
  have hdescent : baseEnd_6522887 < baseStart_6522887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522950 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_6522950 : Nat := 118140960795 + 6522950 * 2 ^ 59
def prefixEnd_6522950 : Nat := 4983230072969 + 3 ^ 40 * 6522950 * 2
def baseEnd_6522950 : Nat := 3349408635245359161826505

theorem tailTrace_6522950 : CollatzResearch.WordTrace tailWord_6522950 prefixEnd_6522950 3349408635245359161826505 := by
  unfold tailWord_6522950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7434735366202301750392447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158607687812315770675038869 7434735366202301750392447)
  ·
    refine ⟨11152103049303452625588671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7434735366202301750392447 11152103049303452625588671)
    ·
      refine ⟨16728154573955178938383007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11152103049303452625588671 16728154573955178938383007)
      ·
        refine ⟨25092231860932768407574511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16728154573955178938383007 25092231860932768407574511)
        ·
          refine ⟨37638347791399152611361767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25092231860932768407574511 37638347791399152611361767)
          ·
            refine ⟨56457521687098728917042651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37638347791399152611361767 56457521687098728917042651)
            ·
              refine ⟨84686282530648093375563977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56457521687098728917042651 84686282530648093375563977)
              ·
                refine ⟨63514711897986070031672983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84686282530648093375563977 63514711897986070031672983)
                ·
                  refine ⟨95272067846979105047509475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63514711897986070031672983 95272067846979105047509475)
                  ·
                    refine ⟨142908101770468657571264213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95272067846979105047509475 142908101770468657571264213)
                    ·
                      refine ⟨3349408635245359161826505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142908101770468657571264213 3349408635245359161826505)
                      ·
                        rfl

theorem cell23_6522950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_6522950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522950 prefixEnd_6522950 := by exact prefixLift 6522950
  have htrace : WordTrace (prefixWord ++ tailWord_6522950) baseStart_6522950 baseEnd_6522950 := by
    simpa [prefixWord, tailWord_6522950, baseEnd_6522950] using wordTrace_append hprefix tailTrace_6522950
  have hstable : (prefixWord ++ tailWord_6522950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522950).length < 2 ^ (prefixWord ++ tailWord_6522950).sum := by decide
  have hdescent : baseEnd_6522950 < baseStart_6522950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522953 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 5, 4]
def baseStart_6522953 : Nat := 118140960795 + 6522953 * 2 ^ 59
def prefixEnd_6522953 : Nat := 4983230072969 + 3 ^ 40 * 6522953 * 2
def baseEnd_6522953 : Nat := 1116470058562440883362997

theorem tailTrace_6522953 : CollatzResearch.WordTrace tailWord_6522953 prefixEnd_6522953 1116470058562440883362997 := by
  unfold tailWord_6522953
  simp only [CollatzResearch.WordTrace]
  refine ⟨237911641137462787524917513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158607760758308525016611675 237911641137462787524917513)
  ·
    refine ⟨178433730853097090643688135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237911641137462787524917513 178433730853097090643688135)
    ·
      refine ⟨267650596279645635965532203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178433730853097090643688135 267650596279645635965532203)
      ·
        refine ⟨401475894419468453948298305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267650596279645635965532203 401475894419468453948298305)
        ·
          refine ⟨301106920814601340461223729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401475894419468453948298305 301106920814601340461223729)
          ·
            refine ⟨225830190610951005345917797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301106920814601340461223729 225830190610951005345917797)
            ·
              refine ⟨42343160739553313502359587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225830190610951005345917797 42343160739553313502359587)
              ·
                refine ⟨63514741109329970253539381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42343160739553313502359587 63514741109329970253539381)
                ·
                  refine ⟨5954506978999684711269317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63514741109329970253539381 5954506978999684711269317)
                  ·
                    refine ⟨1116470058562440883362997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5954506978999684711269317 1116470058562440883362997)
                    ·
                      rfl

theorem cell23_6522953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 4].length) (baseStart_6522953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522953 prefixEnd_6522953 := by exact prefixLift 6522953
  have htrace : WordTrace (prefixWord ++ tailWord_6522953) baseStart_6522953 baseEnd_6522953 := by
    simpa [prefixWord, tailWord_6522953, baseEnd_6522953] using wordTrace_append hprefix tailTrace_6522953
  have hstable : (prefixWord ++ tailWord_6522953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522953).length < 2 ^ (prefixWord ++ tailWord_6522953).sum := by decide
  have hdescent : baseEnd_6522953 < baseStart_6522953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6522980 : List Nat := [2, 3, 1, 1, 2, 1, 4, 2, 2, 2, 3]
def baseStart_6522980 : Nat := 118140960795 + 6522980 * 2 ^ 59
def prefixEnd_6522980 : Nat := 4983230072969 + 3 ^ 40 * 6522980 * 2
def baseEnd_6522980 : Nat := 3349424039664994044451367

theorem tailTrace_6522980 : CollatzResearch.WordTrace tailWord_6522980 prefixEnd_6522980 3349424039664994044451367 := by
  unfold tailWord_6522980
  simp only [CollatzResearch.WordTrace]
  refine ⟨118956312954182485568075197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158608417272243314090766929 118956312954182485568075197)
  ·
    refine ⟨44608617357818432088028199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118956312954182485568075197 44608617357818432088028199)
    ·
      refine ⟨66912926036727648132042299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44608617357818432088028199 66912926036727648132042299)
      ·
        refine ⟨100369389055091472198063449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66912926036727648132042299 100369389055091472198063449)
        ·
          refine ⟨75277041791318604148547587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100369389055091472198063449 75277041791318604148547587)
          ·
            refine ⟨112915562686977906222821381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75277041791318604148547587 112915562686977906222821381)
            ·
              refine ⟨21171668003808357416779009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112915562686977906222821381 21171668003808357416779009)
              ·
                refine ⟨15878751002856268062584257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21171668003808357416779009 15878751002856268062584257)
                ·
                  refine ⟨11909063252142201046938193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15878751002856268062584257 11909063252142201046938193)
                  ·
                    refine ⟨8931797439106650785203645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11909063252142201046938193 8931797439106650785203645)
                    ·
                      refine ⟨3349424039664994044451367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8931797439106650785203645 3349424039664994044451367)
                      ·
                        rfl

theorem cell23_6522980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_6522980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6522980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6522980 prefixEnd_6522980 := by exact prefixLift 6522980
  have htrace : WordTrace (prefixWord ++ tailWord_6522980) baseStart_6522980 baseEnd_6522980 := by
    simpa [prefixWord, tailWord_6522980, baseEnd_6522980] using wordTrace_append hprefix tailTrace_6522980
  have hstable : (prefixWord ++ tailWord_6522980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6522980).length < 2 ^ (prefixWord ++ tailWord_6522980).sum := by decide
  have hdescent : baseEnd_6522980 < baseStart_6522980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6522980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523034 : List Nat := [3, 1, 1, 5, 3, 1, 1, 2, 6]
def baseStart_6523034 : Nat := 118140960795 + 6523034 * 2 ^ 59
def prefixEnd_6523034 : Nat := 4983230072969 + 3 ^ 40 * 6523034 * 2
def baseEnd_6523034 : Nat := 372161307513370759241791

theorem tailTrace_6523034 : CollatzResearch.WordTrace tailWord_6523034 prefixEnd_6523034 372161307513370759241791 := by
  unfold tailWord_6523034
  simp only [CollatzResearch.WordTrace]
  refine ⟨59478648862542334589654039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158609730300112892239077437 59478648862542334589654039)
  ·
    refine ⟨89217973293813501884481059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59478648862542334589654039 89217973293813501884481059)
    ·
      refine ⟨133826959940720252826721589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89217973293813501884481059 133826959940720252826721589)
      ·
        refine ⟨12546277494442523702505149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133826959940720252826721589 12546277494442523702505149)
        ·
          refine ⟨4704854060415946388439431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12546277494442523702505149 4704854060415946388439431)
          ·
            refine ⟨7057281090623919582659147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4704854060415946388439431 7057281090623919582659147)
            ·
              refine ⟨10585921635935879373988721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7057281090623919582659147 10585921635935879373988721)
              ·
                refine ⟨7939441226951909530491541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10585921635935879373988721 7939441226951909530491541)
                ·
                  refine ⟨372161307513370759241791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7939441226951909530491541 372161307513370759241791)
                  ·
                    rfl

theorem cell23_6523034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 6].length) (baseStart_6523034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523034 prefixEnd_6523034 := by exact prefixLift 6523034
  have htrace : WordTrace (prefixWord ++ tailWord_6523034) baseStart_6523034 baseEnd_6523034 := by
    simpa [prefixWord, tailWord_6523034, baseEnd_6523034] using wordTrace_append hprefix tailTrace_6523034
  have hstable : (prefixWord ++ tailWord_6523034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523034).length < 2 ^ (prefixWord ++ tailWord_6523034).sum := by decide
  have hdescent : baseEnd_6523034 < baseStart_6523034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523044 : List Nat := [2, 3, 1, 2, 4, 1, 2, 1, 3, 1, 3]
def baseStart_6523044 : Nat := 118140960795 + 6523044 * 2 ^ 59
def prefixEnd_6523044 : Nat := 4983230072969 + 3 ^ 40 * 6523044 * 2
def baseEnd_6523044 : Nat := 3349456902426881794051073

theorem tailTrace_6523044 : CollatzResearch.WordTrace tailWord_6523044 prefixEnd_6523044 3349456902426881794051073 := by
  unfold tailWord_6523044
  simp only [CollatzResearch.WordTrace]
  refine ⟨118957480090066555033240093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158609973453422073377653457 118957480090066555033240093)
  ·
    refine ⟨44609055033774958137465035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118957480090066555033240093 44609055033774958137465035)
    ·
      refine ⟨66913582550662437206197553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44609055033774958137465035 66913582550662437206197553)
      ·
        refine ⟨50185186912996827904648165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66913582550662437206197553 50185186912996827904648165)
        ·
          refine ⟨9409722546186905232121531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50185186912996827904648165 9409722546186905232121531)
          ·
            refine ⟨14114583819280357848182297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9409722546186905232121531 14114583819280357848182297)
            ·
              refine ⟨10585937864460268386136723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14114583819280357848182297 10585937864460268386136723)
              ·
                refine ⟨15878906796690402579205085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10585937864460268386136723 15878906796690402579205085)
                ·
                  refine ⟨5954590048758900967201907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15878906796690402579205085 5954590048758900967201907)
                  ·
                    refine ⟨8931885073138351450802861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5954590048758900967201907 8931885073138351450802861)
                    ·
                      refine ⟨3349456902426881794051073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8931885073138351450802861 3349456902426881794051073)
                      ·
                        rfl

theorem cell23_6523044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_6523044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523044 prefixEnd_6523044 := by exact prefixLift 6523044
  have htrace : WordTrace (prefixWord ++ tailWord_6523044) baseStart_6523044 baseEnd_6523044 := by
    simpa [prefixWord, tailWord_6523044, baseEnd_6523044] using wordTrace_append hprefix tailTrace_6523044
  have hstable : (prefixWord ++ tailWord_6523044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523044).length < 2 ^ (prefixWord ++ tailWord_6523044).sum := by decide
  have hdescent : baseEnd_6523044 < baseStart_6523044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523067 : List Nat := [1, 1, 1, 1, 1, 2, 5, 4, 3, 2, 2]
def baseStart_6523067 : Nat := 118140960795 + 6523067 * 2 ^ 59
def prefixEnd_6523067 : Nat := 4983230072969 + 3 ^ 40 * 6523067 * 2
def baseEnd_6523067 : Nat := 3349468712481935204063467

theorem tailTrace_6523067 : CollatzResearch.WordTrace tailWord_6523067 prefixEnd_6523067 3349468712481935204063467 := by
  unfold tailWord_6523067
  simp only [CollatzResearch.WordTrace]
  refine ⟨237915799059049784994567455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158610532706033189996378303 237915799059049784994567455)
  ·
    refine ⟨356873698588574677491851183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237915799059049784994567455 356873698588574677491851183)
    ·
      refine ⟨535310547882862016237776775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356873698588574677491851183 535310547882862016237776775)
      ·
        refine ⟨802965821824293024356665163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535310547882862016237776775 802965821824293024356665163)
        ·
          refine ⟨1204448732736439536534997745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802965821824293024356665163 1204448732736439536534997745)
          ·
            refine ⟨903336549552329652401248309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1204448732736439536534997745 903336549552329652401248309)
            ·
              refine ⟨84687801520530904912617029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 903336549552329652401248309 84687801520530904912617029)
              ·
                refine ⟨15878962785099544671115693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84687801520530904912617029 15878962785099544671115693)
                ·
                  refine ⟨5954611044412329251668385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15878962785099544671115693 5954611044412329251668385)
                  ·
                    refine ⟨4465958283309246938751289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5954611044412329251668385 4465958283309246938751289)
                    ·
                      refine ⟨3349468712481935204063467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4465958283309246938751289 3349468712481935204063467)
                      ·
                        rfl

theorem cell23_6523067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 2, 2].length) (baseStart_6523067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523067 prefixEnd_6523067 := by exact prefixLift 6523067
  have htrace : WordTrace (prefixWord ++ tailWord_6523067) baseStart_6523067 baseEnd_6523067 := by
    simpa [prefixWord, tailWord_6523067, baseEnd_6523067] using wordTrace_append hprefix tailTrace_6523067
  have hstable : (prefixWord ++ tailWord_6523067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523067).length < 2 ^ (prefixWord ++ tailWord_6523067).sum := by decide
  have hdescent : baseEnd_6523067 < baseStart_6523067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523090 : List Nat := [3, 2, 2, 2, 1, 4, 9]
def baseStart_6523090 : Nat := 118140960795 + 6523090 * 2 ^ 59
def prefixEnd_6523090 : Nat := 4983230072969 + 3 ^ 40 * 6523090 * 2
def baseEnd_6523090 : Nat := 41351611389345538445381

theorem tailTrace_6523090 : CollatzResearch.WordTrace tailWord_6523090 prefixEnd_6523090 41351611389345538445381 := by
  unfold tailWord_6523090
  simp only [CollatzResearch.WordTrace]
  refine ⟨59479159484491614980663681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158611091958644306615103149 59479159484491614980663681)
  ·
    refine ⟨44609369613368711235497761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59479159484491614980663681 44609369613368711235497761)
    ·
      refine ⟨33457027210026533426623321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44609369613368711235497761 33457027210026533426623321)
      ·
        refine ⟨25092770407519900069967491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33457027210026533426623321 25092770407519900069967491)
        ·
          refine ⟨37639155611279850104951237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25092770407519900069967491 37639155611279850104951237)
          ·
            refine ⟨7057341677114971894678357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37639155611279850104951237 7057341677114971894678357)
            ·
              refine ⟨41351611389345538445381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7057341677114971894678357 41351611389345538445381)
              ·
                rfl

theorem cell23_6523090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 9].length) (baseStart_6523090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523090 prefixEnd_6523090 := by exact prefixLift 6523090
  have htrace : WordTrace (prefixWord ++ tailWord_6523090) baseStart_6523090 baseEnd_6523090 := by
    simpa [prefixWord, tailWord_6523090, baseEnd_6523090] using wordTrace_append hprefix tailTrace_6523090
  have hstable : (prefixWord ++ tailWord_6523090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523090).length < 2 ^ (prefixWord ++ tailWord_6523090).sum := by decide
  have hdescent : baseEnd_6523090 < baseStart_6523090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523094 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_6523094 : Nat := 118140960795 + 6523094 * 2 ^ 59
def prefixEnd_6523094 : Nat := 4983230072969 + 3 ^ 40 * 6523094 * 2
def baseEnd_6523094 : Nat := 1116494192153202199475281

theorem tailTrace_6523094 : CollatzResearch.WordTrace tailWord_6523094 prefixEnd_6523094 1116494192153202199475281 := by
  unfold tailWord_6523094
  simp only [CollatzResearch.WordTrace]
  refine ⟨14869798989371998037862521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158611189219967979070533557 14869798989371998037862521)
  ·
    refine ⟨11152349242028998528396891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14869798989371998037862521 11152349242028998528396891)
    ·
      refine ⟨16728523863043497792595337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11152349242028998528396891 16728523863043497792595337)
      ·
        refine ⟨12546392897282623344446503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16728523863043497792595337 12546392897282623344446503)
        ·
          refine ⟨18819589345923935016669755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12546392897282623344446503 18819589345923935016669755)
          ·
            refine ⟨28229384018885902525004633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18819589345923935016669755 28229384018885902525004633)
            ·
              refine ⟨21172038014164426893753475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28229384018885902525004633 21172038014164426893753475)
              ·
                refine ⟨31758057021246640340630213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21172038014164426893753475 31758057021246640340630213)
                ·
                  refine ⟨5954635691483745063868165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31758057021246640340630213 5954635691483745063868165)
                  ·
                    refine ⟨1116494192153202199475281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5954635691483745063868165 1116494192153202199475281)
                    ·
                      rfl

theorem cell23_6523094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_6523094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523094 prefixEnd_6523094 := by exact prefixLift 6523094
  have htrace : WordTrace (prefixWord ++ tailWord_6523094) baseStart_6523094 baseEnd_6523094 := by
    simpa [prefixWord, tailWord_6523094, baseEnd_6523094] using wordTrace_append hprefix tailTrace_6523094
  have hstable : (prefixWord ++ tailWord_6523094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523094).length < 2 ^ (prefixWord ++ tailWord_6523094).sum := by decide
  have hdescent : baseEnd_6523094 < baseStart_6523094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523101 : List Nat := [1, 4, 3, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_6523101 : Nat := 118140960795 + 6523101 * 2 ^ 59
def prefixEnd_6523101 : Nat := 4983230072969 + 3 ^ 40 * 6523101 * 2
def baseEnd_6523101 : Nat := 3349486170824188071038311

theorem tailTrace_6523101 : CollatzResearch.WordTrace tailWord_6523101 prefixEnd_6523101 3349486170824188071038311 := by
  unfold tailWord_6523101
  simp only [CollatzResearch.WordTrace]
  refine ⟨237917039140926608801305157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158611359427284405867536771 237917039140926608801305157)
  ·
    refine ⟨44609444838923739150244717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237917039140926608801305157 44609444838923739150244717)
    ·
      refine ⟨16728541814596402181341769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44609444838923739150244717 16728541814596402181341769)
      ·
        refine ⟨12546406360947301636006327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16728541814596402181341769 12546406360947301636006327)
        ·
          refine ⟨18819609541420952454009491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12546406360947301636006327 18819609541420952454009491)
          ·
            refine ⟨28229414312131428681014237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18819609541420952454009491 28229414312131428681014237)
            ·
              refine ⟨10586030367049285755380339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28229414312131428681014237 10586030367049285755380339)
              ·
                refine ⟨15879045550573928633070509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10586030367049285755380339 15879045550573928633070509)
                ·
                  refine ⟨5954642081465223237401441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15879045550573928633070509 5954642081465223237401441)
                  ·
                    refine ⟨4465981561098917428051081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5954642081465223237401441 4465981561098917428051081)
                    ·
                      refine ⟨3349486170824188071038311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4465981561098917428051081 3349486170824188071038311)
                      ·
                        rfl

theorem cell23_6523101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_6523101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523101 prefixEnd_6523101 := by exact prefixLift 6523101
  have htrace : WordTrace (prefixWord ++ tailWord_6523101) baseStart_6523101 baseEnd_6523101 := by
    simpa [prefixWord, tailWord_6523101, baseEnd_6523101] using wordTrace_append hprefix tailTrace_6523101
  have hstable : (prefixWord ++ tailWord_6523101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523101).length < 2 ^ (prefixWord ++ tailWord_6523101).sum := by decide
  have hdescent : baseEnd_6523101 < baseStart_6523101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523103 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 2, 7]
def baseStart_6523103 : Nat := 118140960795 + 6523103 * 2 ^ 59
def prefixEnd_6523103 : Nat := 4983230072969 + 3 ^ 40 * 6523103 * 2
def baseEnd_6523103 : Nat := 1116495732595165687737767

theorem tailTrace_6523103 : CollatzResearch.WordTrace tailWord_6523103 prefixEnd_6523103 1116495732595165687737767 := by
  unfold tailWord_6523103
  simp only [CollatzResearch.WordTrace]
  refine ⟨237917112086919363142877963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158611408057946242095251975 237917112086919363142877963)
  ·
    refine ⟨356875668130379044714316945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237917112086919363142877963 356875668130379044714316945)
    ·
      refine ⟨267656751097784283535737709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356875668130379044714316945 267656751097784283535737709)
      ·
        refine ⟨100371281661669106325901641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267656751097784283535737709 100371281661669106325901641)
        ·
          refine ⟨75278461246251829744426231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100371281661669106325901641 75278461246251829744426231)
          ·
            refine ⟨112917691869377744616639347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75278461246251829744426231 112917691869377744616639347)
            ·
              refine ⟨169376537804066616924959021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112917691869377744616639347 169376537804066616924959021)
              ·
                refine ⟨63516201676524981346859633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169376537804066616924959021 63516201676524981346859633)
                ·
                  refine ⟨47637151257393736010144725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63516201676524981346859633 47637151257393736010144725)
                  ·
                    refine ⟨1116495732595165687737767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47637151257393736010144725 1116495732595165687737767)
                    ·
                      rfl

theorem cell23_6523103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 7].length) (baseStart_6523103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523103 prefixEnd_6523103 := by exact prefixLift 6523103
  have htrace : WordTrace (prefixWord ++ tailWord_6523103) baseStart_6523103 baseEnd_6523103 := by
    simpa [prefixWord, tailWord_6523103, baseEnd_6523103] using wordTrace_append hprefix tailTrace_6523103
  have hstable : (prefixWord ++ tailWord_6523103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523103).length < 2 ^ (prefixWord ++ tailWord_6523103).sum := by decide
  have hdescent : baseEnd_6523103 < baseStart_6523103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523107 : List Nat := [1, 1, 1, 8, 1, 1, 2, 8]
def baseStart_6523107 : Nat := 118140960795 + 6523107 * 2 ^ 59
def prefixEnd_6523107 : Nat := 4983230072969 + 3 ^ 40 * 6523107 * 2
def baseEnd_6523107 : Nat := 124055157470670927687529

theorem tailTrace_6523107 : CollatzResearch.WordTrace tailWord_6523107 prefixEnd_6523107 124055157470670927687529 := by
  unfold tailWord_6523107
  simp only [CollatzResearch.WordTrace]
  refine ⟨237917257978904871826023575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158611505319269914550682383 237917257978904871826023575)
  ·
    refine ⟨356875886968357307739035363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237917257978904871826023575 356875886968357307739035363)
    ·
      refine ⟨535313830452535961608553045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356875886968357307739035363 535313830452535961608553045)
      ·
        refine ⟨6273208950615655800100231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 535313830452535961608553045 6273208950615655800100231)
        ·
          refine ⟨9409813425923483700150347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6273208950615655800100231 9409813425923483700150347)
          ·
            refine ⟨14114720138885225550225521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9409813425923483700150347 14114720138885225550225521)
            ·
              refine ⟨10586040104163919162669141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14114720138885225550225521 10586040104163919162669141)
              ·
                refine ⟨124055157470670927687529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10586040104163919162669141 124055157470670927687529)
                ·
                  rfl

theorem cell23_6523107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 8].length) (baseStart_6523107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523107 prefixEnd_6523107 := by exact prefixLift 6523107
  have htrace : WordTrace (prefixWord ++ tailWord_6523107) baseStart_6523107 baseEnd_6523107 := by
    simpa [prefixWord, tailWord_6523107, baseEnd_6523107] using wordTrace_append hprefix tailTrace_6523107
  have hstable : (prefixWord ++ tailWord_6523107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523107).length < 2 ^ (prefixWord ++ tailWord_6523107).sum := by decide
  have hdescent : baseEnd_6523107 < baseStart_6523107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523111 : List Nat := [1, 1, 5, 3, 1, 3, 2, 1, 2, 4]
def baseStart_6523111 : Nat := 118140960795 + 6523111 * 2 ^ 59
def prefixEnd_6523111 : Nat := 4983230072969 + 3 ^ 40 * 6523111 * 2
def baseEnd_6523111 : Nat := 1116497101876911010637755

theorem tailTrace_6523111 : CollatzResearch.WordTrace tailWord_6523111 prefixEnd_6523111 1116497101876911010637755 := by
  unfold tailWord_6523111
  simp only [CollatzResearch.WordTrace]
  refine ⟨237917403870890380509169187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158611602580593587006112791 237917403870890380509169187)
  ·
    refine ⟨356876105806335570763753781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237917403870890380509169187 356876105806335570763753781)
    ·
      refine ⟨33457134919343959759101917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 356876105806335570763753781 33457134919343959759101917)
      ·
        refine ⟨12546425594753984909663219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33457134919343959759101917 12546425594753984909663219)
        ·
          refine ⟨18819638392130977364494829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12546425594753984909663219 18819638392130977364494829)
          ·
            refine ⟨7057364397049116511685561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18819638392130977364494829 7057364397049116511685561)
            ·
              refine ⟨5293023297786837383764171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7057364397049116511685561 5293023297786837383764171)
              ·
                refine ⟨7939534946680256075646257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5293023297786837383764171 7939534946680256075646257)
                ·
                  refine ⟨5954651210010192056734693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7939534946680256075646257 5954651210010192056734693)
                  ·
                    refine ⟨1116497101876911010637755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5954651210010192056734693 1116497101876911010637755)
                    ·
                      rfl

theorem cell23_6523111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_6523111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523111 prefixEnd_6523111 := by exact prefixLift 6523111
  have htrace : WordTrace (prefixWord ++ tailWord_6523111) baseStart_6523111 baseEnd_6523111 := by
    simpa [prefixWord, tailWord_6523111, baseEnd_6523111] using wordTrace_append hprefix tailTrace_6523111
  have hstable : (prefixWord ++ tailWord_6523111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523111).length < 2 ^ (prefixWord ++ tailWord_6523111).sum := by decide
  have hdescent : baseEnd_6523111 < baseStart_6523111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523113 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 4, 2, 5]
def baseStart_6523113 : Nat := 118140960795 + 6523113 * 2 ^ 59
def prefixEnd_6523113 : Nat := 4983230072969 + 3 ^ 40 * 6523113 * 2
def baseEnd_6523113 : Nat := 3349492332592042024088255

theorem tailTrace_6523113 : CollatzResearch.WordTrace tailWord_6523113 prefixEnd_6523113 3349492332592042024088255 := by
  unfold tailWord_6523113
  simp only [CollatzResearch.WordTrace]
  refine ⟨237917476816883134850741993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158611651211255423233827995 237917476816883134850741993)
  ·
    refine ⟨178438107612662351138056495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237917476816883134850741993 178438107612662351138056495)
    ·
      refine ⟨267657161418993526707084743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178438107612662351138056495 267657161418993526707084743)
      ·
        refine ⟨401485742128490290060627115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267657161418993526707084743 401485742128490290060627115)
        ·
          refine ⟨602228613192735435090940673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401485742128490290060627115 602228613192735435090940673)
          ·
            refine ⟨451671459894551576318205505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602228613192735435090940673 451671459894551576318205505)
            ·
              refine ⟨338753594920913682238654129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451671459894551576318205505 338753594920913682238654129)
              ·
                refine ⟨254065196190685261678990597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338753594920913682238654129 254065196190685261678990597)
                ·
                  refine ⟨47637224285753486564810737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 254065196190685261678990597 47637224285753486564810737)
                  ·
                    refine ⟨35727918214315114923608053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47637224285753486564810737 35727918214315114923608053)
                    ·
                      refine ⟨3349492332592042024088255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35727918214315114923608053 3349492332592042024088255)
                      ·
                        rfl

theorem cell23_6523113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_6523113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523113 prefixEnd_6523113 := by exact prefixLift 6523113
  have htrace : WordTrace (prefixWord ++ tailWord_6523113) baseStart_6523113 baseEnd_6523113 := by
    simpa [prefixWord, tailWord_6523113, baseEnd_6523113] using wordTrace_append hprefix tailTrace_6523113
  have hstable : (prefixWord ++ tailWord_6523113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523113).length < 2 ^ (prefixWord ++ tailWord_6523113).sum := by decide
  have hdescent : baseEnd_6523113 < baseStart_6523113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523150 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 2, 6]
def baseStart_6523150 : Nat := 118140960795 + 6523150 * 2 ^ 59
def prefixEnd_6523150 : Nat := 4983230072969 + 3 ^ 40 * 6523150 * 2
def baseEnd_6523150 : Nat := 1116503777125419459775195

theorem tailTrace_6523150 : CollatzResearch.WordTrace tailWord_6523150 prefixEnd_6523150 1116503777125419459775195 := by
  unfold tailWord_6523150
  simp only [CollatzResearch.WordTrace]
  refine ⟨29739853289718636271229863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158612550878499393446559269 29739853289718636271229863)
  ·
    refine ⟨44609779934577954406844795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29739853289718636271229863 44609779934577954406844795)
    ·
      refine ⟨66914669901866931610267193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44609779934577954406844795 66914669901866931610267193)
      ·
        refine ⟨50186002426400198707700395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66914669901866931610267193 50186002426400198707700395)
        ·
          refine ⟨75279003639600298061550593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50186002426400198707700395 75279003639600298061550593)
          ·
            refine ⟨56459252729700223546162945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75279003639600298061550593 56459252729700223546162945)
            ·
              refine ⟨42344439547275167659622209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56459252729700223546162945 42344439547275167659622209)
              ·
                refine ⟨31758329660456375744716657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42344439547275167659622209 31758329660456375744716657)
                ·
                  refine ⟨23818747245342281808537493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31758329660456375744716657 23818747245342281808537493)
                  ·
                    refine ⟨1116503777125419459775195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23818747245342281808537493 1116503777125419459775195)
                    ·
                      rfl

theorem cell23_6523150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_6523150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523150 prefixEnd_6523150 := by exact prefixLift 6523150
  have htrace : WordTrace (prefixWord ++ tailWord_6523150) baseStart_6523150 baseEnd_6523150 := by
    simpa [prefixWord, tailWord_6523150, baseEnd_6523150] using wordTrace_append hprefix tailTrace_6523150
  have hstable : (prefixWord ++ tailWord_6523150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523150).length < 2 ^ (prefixWord ++ tailWord_6523150).sum := by decide
  have hdescent : baseEnd_6523150 < baseStart_6523150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523160 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 1, 6, 3]
def baseStart_6523160 : Nat := 118140960795 + 6523160 * 2 ^ 59
def prefixEnd_6523160 : Nat := 4983230072969 + 3 ^ 40 * 6523160 * 2
def baseEnd_6523160 : Nat := 3349516466182803340200539

theorem tailTrace_6523160 : CollatzResearch.WordTrace tailWord_6523160 prefixEnd_6523160 3349516466182803340200539 := by
  unfold tailWord_6523160
  simp only [CollatzResearch.WordTrace]
  refine ⟨118959595523856430938851467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158612794031808574585135289 118959595523856430938851467)
  ·
    refine ⟨178439393285784646408277201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118959595523856430938851467 178439393285784646408277201)
    ·
      refine ⟨133829544964338484806207901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178439393285784646408277201 133829544964338484806207901)
      ·
        refine ⟨50186079361626931802327963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133829544964338484806207901 50186079361626931802327963)
        ·
          refine ⟨75279119042440397703491945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50186079361626931802327963 75279119042440397703491945)
          ·
            refine ⟨56459339281830298277618959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75279119042440397703491945 56459339281830298277618959)
            ·
              refine ⟨84689008922745447416428439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56459339281830298277618959 84689008922745447416428439)
              ·
                refine ⟨127033513384118171124642659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84689008922745447416428439 127033513384118171124642659)
                ·
                  refine ⟨190550270076177256686963989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127033513384118171124642659 190550270076177256686963989)
                  ·
                    refine ⟨8932043909820808907201437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 190550270076177256686963989 8932043909820808907201437)
                    ·
                      refine ⟨3349516466182803340200539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8932043909820808907201437 3349516466182803340200539)
                      ·
                        rfl

theorem cell23_6523160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_6523160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523160 prefixEnd_6523160 := by exact prefixLift 6523160
  have htrace : WordTrace (prefixWord ++ tailWord_6523160) baseStart_6523160 baseEnd_6523160 := by
    simpa [prefixWord, tailWord_6523160, baseEnd_6523160] using wordTrace_append hprefix tailTrace_6523160
  have hstable : (prefixWord ++ tailWord_6523160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523160).length < 2 ^ (prefixWord ++ tailWord_6523160).sum := by decide
  have hdescent : baseEnd_6523160 < baseStart_6523160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523247 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 4, 4, 2]
def baseStart_6523247 : Nat := 118140960795 + 6523247 * 2 ^ 59
def prefixEnd_6523247 : Nat := 4983230072969 + 3 ^ 40 * 6523247 * 2
def baseEnd_6523247 : Nat := 3349561138999744499812639

theorem tailTrace_6523247 : CollatzResearch.WordTrace tailWord_6523247 prefixEnd_6523247 3349561138999744499812639 := by
  unfold tailWord_6523247
  simp only [CollatzResearch.WordTrace]
  refine ⟨237922364198397675736119995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158614909465598450490746663 237922364198397675736119995)
  ·
    refine ⟨356883546297596513604179993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237922364198397675736119995 356883546297596513604179993)
    ·
      refine ⟨267662659723197385203134995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356883546297596513604179993 267662659723197385203134995)
      ·
        refine ⟨401493989584796077804702493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267662659723197385203134995 401493989584796077804702493)
        ·
          refine ⟨150560246094298529176763435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401493989584796077804702493 150560246094298529176763435)
          ·
            refine ⟨225840369141447793765145153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150560246094298529176763435 225840369141447793765145153)
            ·
              refine ⟨169380276856085845323858865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225840369141447793765145153 169380276856085845323858865)
              ·
                refine ⟨127035207642064383992894149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169380276856085845323858865 127035207642064383992894149)
                ·
                  refine ⟨23819101432887071998667653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127035207642064383992894149 23819101432887071998667653)
                  ·
                    refine ⟨4466081518666325999750185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23819101432887071998667653 4466081518666325999750185)
                    ·
                      refine ⟨3349561138999744499812639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4466081518666325999750185 3349561138999744499812639)
                      ·
                        rfl

theorem cell23_6523247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 4, 2].length) (baseStart_6523247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523247 prefixEnd_6523247 := by exact prefixLift 6523247
  have htrace : WordTrace (prefixWord ++ tailWord_6523247) baseStart_6523247 baseEnd_6523247 := by
    simpa [prefixWord, tailWord_6523247, baseEnd_6523247] using wordTrace_append hprefix tailTrace_6523247
  have hstable : (prefixWord ++ tailWord_6523247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523247).length < 2 ^ (prefixWord ++ tailWord_6523247).sum := by decide
  have hdescent : baseEnd_6523247 < baseStart_6523247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523260 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_6523260 : Nat := 118140960795 + 6523260 * 2 ^ 59
def prefixEnd_6523260 : Nat := 4983230072969 + 3 ^ 40 * 6523260 * 2
def baseEnd_6523260 : Nat := 3349567814248252948950079

theorem tailTrace_6523260 : CollatzResearch.WordTrace tailWord_6523260 prefixEnd_6523260 3349567814248252948950079 := by
  unfold tailWord_6523260
  simp only [CollatzResearch.WordTrace]
  refine ⟨118961419173675289478171617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158615225564900385970895489 118961419173675289478171617)
  ·
    refine ⟨89221064380256467108628713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118961419173675289478171617 89221064380256467108628713)
    ·
      refine ⟨66915798285192350331471535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89221064380256467108628713 66915798285192350331471535)
      ·
        refine ⟨100373697427788525497207303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66915798285192350331471535 100373697427788525497207303)
        ·
          refine ⟨150560546141682788245810955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100373697427788525497207303 150560546141682788245810955)
          ·
            refine ⟨225840819212524182368716433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150560546141682788245810955 225840819212524182368716433)
            ·
              refine ⟨169380614409393136776537325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225840819212524182368716433 169380614409393136776537325)
              ·
                refine ⟨63517730403522426291201497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169380614409393136776537325 63517730403522426291201497)
                ·
                  refine ⟨47638297802641819718401123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63517730403522426291201497 47638297802641819718401123)
                  ·
                    refine ⟨71457446703962729577601685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47638297802641819718401123 71457446703962729577601685)
                    ·
                      refine ⟨3349567814248252948950079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71457446703962729577601685 3349567814248252948950079)
                      ·
                        rfl

theorem cell23_6523260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_6523260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523260 prefixEnd_6523260 := by exact prefixLift 6523260
  have htrace : WordTrace (prefixWord ++ tailWord_6523260) baseStart_6523260 baseEnd_6523260 := by
    simpa [prefixWord, tailWord_6523260, baseEnd_6523260] using wordTrace_append hprefix tailTrace_6523260
  have hstable : (prefixWord ++ tailWord_6523260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523260).length < 2 ^ (prefixWord ++ tailWord_6523260).sum := by decide
  have hdescent : baseEnd_6523260 < baseStart_6523260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523337 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 3, 1, 4]
def baseStart_6523337 : Nat := 118140960795 + 6523337 * 2 ^ 59
def prefixEnd_6523337 : Nat := 4983230072969 + 3 ^ 40 * 6523337 * 2
def baseEnd_6523337 : Nat := 3349607352258649147687225

theorem tailTrace_6523337 : CollatzResearch.WordTrace tailWord_6523337 prefixEnd_6523337 3349607352258649147687225 := by
  unfold tailWord_6523337
  simp only [CollatzResearch.WordTrace]
  refine ⟨237925646768071621106896265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158617097845381080737930843 237925646768071621106896265)
  ·
    refine ⟨178444235076053715830172199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237925646768071621106896265 178444235076053715830172199)
    ·
      refine ⟨267666352614080573745258299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178444235076053715830172199 267666352614080573745258299)
      ·
        refine ⟨401499528921120860617887449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267666352614080573745258299 401499528921120860617887449)
        ·
          refine ⟨301124646690840645463415587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401499528921120860617887449 301124646690840645463415587)
          ·
            refine ⟨451686970036260968195123381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301124646690840645463415587 451686970036260968195123381)
            ·
              refine ⟨42345653440899465768292817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 451686970036260968195123381 42345653440899465768292817)
              ·
                refine ⟨31759240080674599326219613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42345653440899465768292817 31759240080674599326219613)
                ·
                  refine ⟨11909715030252974747332355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31759240080674599326219613 11909715030252974747332355)
                  ·
                    refine ⟨17864572545379462120998533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11909715030252974747332355 17864572545379462120998533)
                    ·
                      refine ⟨3349607352258649147687225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17864572545379462120998533 3349607352258649147687225)
                      ·
                        rfl

theorem cell23_6523337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 1, 4].length) (baseStart_6523337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523337 prefixEnd_6523337 := by exact prefixLift 6523337
  have htrace : WordTrace (prefixWord ++ tailWord_6523337) baseStart_6523337 baseEnd_6523337 := by
    simpa [prefixWord, tailWord_6523337, baseEnd_6523337] using wordTrace_append hprefix tailTrace_6523337
  have hstable : (prefixWord ++ tailWord_6523337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523337).length < 2 ^ (prefixWord ++ tailWord_6523337).sum := by decide
  have hdescent : baseEnd_6523337 < baseStart_6523337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523354 : List Nat := [3, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4]
def baseStart_6523354 : Nat := 118140960795 + 6523354 * 2 ^ 59
def prefixEnd_6523354 : Nat := 4983230072969 + 3 ^ 40 * 6523354 * 2
def baseEnd_6523354 : Nat := 3349616081429775581174647

theorem tailTrace_6523354 : CollatzResearch.WordTrace tailWord_6523354 prefixEnd_6523354 3349616081429775581174647 := by
  unfold tailWord_6523354
  simp only [CollatzResearch.WordTrace]
  refine ⟨59481566702252508252566279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158617511206006688673510077 59481566702252508252566279)
  ·
    refine ⟨89222350053378762378849419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59481566702252508252566279 89222350053378762378849419)
    ·
      refine ⟨133833525080068143568274129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89222350053378762378849419 133833525080068143568274129)
      ·
        refine ⟨100375143810051107676205597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133833525080068143568274129 100375143810051107676205597)
        ·
          refine ⟨37640678928769165378577099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100375143810051107676205597 37640678928769165378577099)
          ·
            refine ⟨56461018393153748067865649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37640678928769165378577099 56461018393153748067865649)
            ·
              refine ⟨42345763794865311050899237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56461018393153748067865649 42345763794865311050899237)
              ·
                refine ⟨7939830711537245822043607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42345763794865311050899237 7939830711537245822043607)
                ·
                  refine ⟨11909746067305868733065411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7939830711537245822043607 11909746067305868733065411)
                  ·
                    refine ⟨17864619100958803099598117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11909746067305868733065411 17864619100958803099598117)
                    ·
                      refine ⟨3349616081429775581174647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17864619100958803099598117 3349616081429775581174647)
                      ·
                        rfl

theorem cell23_6523354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_6523354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523354 prefixEnd_6523354 := by exact prefixLift 6523354
  have htrace : WordTrace (prefixWord ++ tailWord_6523354) baseStart_6523354 baseEnd_6523354 := by
    simpa [prefixWord, tailWord_6523354, baseEnd_6523354] using wordTrace_append hprefix tailTrace_6523354
  have hstable : (prefixWord ++ tailWord_6523354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523354).length < 2 ^ (prefixWord ++ tailWord_6523354).sum := by decide
  have hdescent : baseEnd_6523354 < baseStart_6523354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523365 : List Nat := [1, 3, 1, 5, 2, 1, 2, 3, 1, 1, 3]
def baseStart_6523365 : Nat := 118140960795 + 6523365 * 2 ^ 59
def prefixEnd_6523365 : Nat := 4983230072969 + 3 ^ 40 * 6523365 * 2
def baseEnd_6523365 : Nat := 3349621729716975038137097

theorem tailTrace_6523365 : CollatzResearch.WordTrace tailWord_6523365 prefixEnd_6523365 3349621729716975038137097 := by
  unfold tailWord_6523365
  simp only [CollatzResearch.WordTrace]
  refine ⟨237926668011970181888915549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158617778674646787925943699 237926668011970181888915549)
  ·
    refine ⟨89222500504488818208343331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237926668011970181888915549 89222500504488818208343331)
    ·
      refine ⟨133833750756733227312514997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89222500504488818208343331 133833750756733227312514997)
      ·
        refine ⟨12546914133443740060548281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133833750756733227312514997 12546914133443740060548281)
        ·
          refine ⟨9410185600082805045411211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12546914133443740060548281 9410185600082805045411211)
          ·
            refine ⟨14115278400124207568116817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9410185600082805045411211 14115278400124207568116817)
            ·
              refine ⟨10586458800093155676087613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14115278400124207568116817 10586458800093155676087613)
              ·
                refine ⟨3969922050034933378532855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10586458800093155676087613 3969922050034933378532855)
                ·
                  refine ⟨5954883075052400067799283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3969922050034933378532855 5954883075052400067799283)
                  ·
                    refine ⟨8932324612578600101698925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5954883075052400067799283 8932324612578600101698925)
                    ·
                      refine ⟨3349621729716975038137097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8932324612578600101698925 3349621729716975038137097)
                      ·
                        rfl

theorem cell23_6523365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_6523365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523365 prefixEnd_6523365 := by exact prefixLift 6523365
  have htrace : WordTrace (prefixWord ++ tailWord_6523365) baseStart_6523365 baseEnd_6523365 := by
    simpa [prefixWord, tailWord_6523365, baseEnd_6523365] using wordTrace_append hprefix tailTrace_6523365
  have hstable : (prefixWord ++ tailWord_6523365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523365).length < 2 ^ (prefixWord ++ tailWord_6523365).sum := by decide
  have hdescent : baseEnd_6523365 < baseStart_6523365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523405 : List Nat := [1, 7, 1, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_6523405 : Nat := 118140960795 + 6523405 * 2 ^ 59
def prefixEnd_6523405 : Nat := 4983230072969 + 3 ^ 40 * 6523405 * 2
def baseEnd_6523405 : Nat := 3349642268943154881636913

theorem tailTrace_6523405 : CollatzResearch.WordTrace tailWord_6523405 prefixEnd_6523405 3349642268943154881636913 := by
  unfold tailWord_6523405
  simp only [CollatzResearch.WordTrace]
  refine ⟨237928126931825268720371669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158618751287883512480247779 237928126931825268720371669)
  ·
    refine ⟨5576440474964654735633711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 237928126931825268720371669 5576440474964654735633711)
    ·
      refine ⟨8364660712446982103450567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5576440474964654735633711 8364660712446982103450567)
      ·
        refine ⟨12546991068670473155175851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8364660712446982103450567 12546991068670473155175851)
        ·
          refine ⟨18820486603005709732763777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12546991068670473155175851 18820486603005709732763777)
          ·
            refine ⟨14115364952254282299572833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18820486603005709732763777 14115364952254282299572833)
            ·
              refine ⟨10586523714190711724679625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14115364952254282299572833 10586523714190711724679625)
              ·
                refine ⟨7939892785643033793509719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10586523714190711724679625 7939892785643033793509719)
                ·
                  refine ⟨11909839178464550690264579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7939892785643033793509719 11909839178464550690264579)
                  ·
                    refine ⟨17864758767696826035396869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11909839178464550690264579 17864758767696826035396869)
                    ·
                      refine ⟨3349642268943154881636913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17864758767696826035396869 3349642268943154881636913)
                      ·
                        rfl

theorem cell23_6523405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_6523405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523405 prefixEnd_6523405 := by exact prefixLift 6523405
  have htrace : WordTrace (prefixWord ++ tailWord_6523405) baseStart_6523405 baseEnd_6523405 := by
    simpa [prefixWord, tailWord_6523405, baseEnd_6523405] using wordTrace_append hprefix tailTrace_6523405
  have hstable : (prefixWord ++ tailWord_6523405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523405).length < 2 ^ (prefixWord ++ tailWord_6523405).sum := by decide
  have hdescent : baseEnd_6523405 < baseStart_6523405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523421 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_6523421 : Nat := 118140960795 + 6523421 * 2 ^ 59
def prefixEnd_6523421 : Nat := 4983230072969 + 3 ^ 40 * 6523421 * 2
def baseEnd_6523421 : Nat := 3349650484633626819036839

theorem tailTrace_6523421 : CollatzResearch.WordTrace tailWord_6523421 prefixEnd_6523421 3349650484633626819036839 := by
  unfold tailWord_6523421
  simp only [CollatzResearch.WordTrace]
  refine ⟨237928710499767303452954117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158619140333178202301969411 237928710499767303452954117)
  ·
    refine ⟨44611633218706369397428897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237928710499767303452954117 44611633218706369397428897)
    ·
      refine ⟨33458724914029777048071673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44611633218706369397428897 33458724914029777048071673)
      ·
        refine ⟨25094043685522332786053755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33458724914029777048071673 25094043685522332786053755)
        ·
          refine ⟨37641065528283499179080633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25094043685522332786053755 37641065528283499179080633)
          ·
            refine ⟨28230799146212624384310475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37641065528283499179080633 28230799146212624384310475)
            ·
              refine ⟨42346198719318936576465713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28230799146212624384310475 42346198719318936576465713)
              ·
                refine ⟨31759649039489202432349285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42346198719318936576465713 31759649039489202432349285)
                ·
                  refine ⟨5954934194904225456065491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31759649039489202432349285 5954934194904225456065491)
                  ·
                    refine ⟨8932401292356338184098237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5954934194904225456065491 8932401292356338184098237)
                    ·
                      refine ⟨3349650484633626819036839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8932401292356338184098237 3349650484633626819036839)
                      ·
                        rfl

theorem cell23_6523421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_6523421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523421 prefixEnd_6523421 := by exact prefixLift 6523421
  have htrace : WordTrace (prefixWord ++ tailWord_6523421) baseStart_6523421 baseEnd_6523421 := by
    simpa [prefixWord, tailWord_6523421, baseEnd_6523421] using wordTrace_append hprefix tailTrace_6523421
  have hstable : (prefixWord ++ tailWord_6523421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523421).length < 2 ^ (prefixWord ++ tailWord_6523421).sum := by decide
  have hdescent : baseEnd_6523421 < baseStart_6523421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523447 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 5]
def baseStart_6523447 : Nat := 118140960795 + 6523447 * 2 ^ 59
def prefixEnd_6523447 : Nat := 4983230072969 + 3 ^ 40 * 6523447 * 2
def baseEnd_6523447 : Nat := 3349663835130643717311719

theorem tailTrace_6523447 : CollatzResearch.WordTrace tailWord_6523447 prefixEnd_6523447 3349663835130643717311719 := by
  unfold tailWord_6523447
  simp only [CollatzResearch.WordTrace]
  refine ⟨237929658797673109893400595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158619772531782073262267063 237929658797673109893400595)
  ·
    refine ⟨356894488196509664840100893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237929658797673109893400595 356894488196509664840100893)
    ·
      refine ⟨133835433073691124315037835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356894488196509664840100893 133835433073691124315037835)
      ·
        refine ⟨200753149610536686472556753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133835433073691124315037835 200753149610536686472556753)
        ·
          refine ⟨150564862207902514854417565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200753149610536686472556753 150564862207902514854417565)
          ·
            refine ⟨56461823327963443070406587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150564862207902514854417565 56461823327963443070406587)
            ·
              refine ⟨84692734991945164605609881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56461823327963443070406587 84692734991945164605609881)
              ·
                refine ⟨63519551243958873454207411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84692734991945164605609881 63519551243958873454207411)
                ·
                  refine ⟨95279326865938310181311117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63519551243958873454207411 95279326865938310181311117)
                  ·
                    refine ⟨35729747574726866317991669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95279326865938310181311117 35729747574726866317991669)
                    ·
                      refine ⟨3349663835130643717311719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35729747574726866317991669 3349663835130643717311719)
                      ·
                        rfl

theorem cell23_6523447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_6523447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523447 prefixEnd_6523447 := by exact prefixLift 6523447
  have htrace : WordTrace (prefixWord ++ tailWord_6523447) baseStart_6523447 baseEnd_6523447 := by
    simpa [prefixWord, tailWord_6523447, baseEnd_6523447] using wordTrace_append hprefix tailTrace_6523447
  have hstable : (prefixWord ++ tailWord_6523447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523447).length < 2 ^ (prefixWord ++ tailWord_6523447).sum := by decide
  have hdescent : baseEnd_6523447 < baseStart_6523447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523467 : List Nat := [1, 1, 1, 1, 3, 1, 4, 4, 7]
def baseStart_6523467 : Nat := 118140960795 + 6523467 * 2 ^ 59
def prefixEnd_6523467 : Nat := 4983230072969 + 3 ^ 40 * 6523467 * 2
def baseEnd_6523467 : Nat := 372186011638192626562403

theorem tailTrace_6523467 : CollatzResearch.WordTrace tailWord_6523467 prefixEnd_6523467 372186011638192626562403 := by
  unfold tailWord_6523467
  simp only [CollatzResearch.WordTrace]
  refine ⟨237930388257600653309128655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158620258838400435539419103 237930388257600653309128655)
  ·
    refine ⟨356895582386400979963692983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237930388257600653309128655 356895582386400979963692983)
    ·
      refine ⟨535343373579601469945539475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356895582386400979963692983 535343373579601469945539475)
      ·
        refine ⟨803015060369402204918309213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535343373579601469945539475 803015060369402204918309213)
        ·
          refine ⟨301130647638525826844365955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 803015060369402204918309213 301130647638525826844365955)
          ·
            refine ⟨451695971457788740266548933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301130647638525826844365955 451695971457788740266548933)
            ·
              refine ⟨84692994648335388799977925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 451695971457788740266548933 84692994648335388799977925)
              ·
                refine ⟨15879936496562885399995861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84692994648335388799977925 15879936496562885399995861)
                ·
                  refine ⟨372186011638192626562403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15879936496562885399995861 372186011638192626562403)
                  ·
                    rfl

theorem cell23_6523467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 7].length) (baseStart_6523467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523467 prefixEnd_6523467 := by exact prefixLift 6523467
  have htrace : WordTrace (prefixWord ++ tailWord_6523467) baseStart_6523467 baseEnd_6523467 := by
    simpa [prefixWord, tailWord_6523467, baseEnd_6523467] using wordTrace_append hprefix tailTrace_6523467
  have hstable : (prefixWord ++ tailWord_6523467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523467).length < 2 ^ (prefixWord ++ tailWord_6523467).sum := by decide
  have hdescent : baseEnd_6523467 < baseStart_6523467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523497 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 3, 7]
def baseStart_6523497 : Nat := 118140960795 + 6523497 * 2 ^ 59
def prefixEnd_6523497 : Nat := 4983230072969 + 3 ^ 40 * 6523497 * 2
def baseEnd_6523497 : Nat := 1116563169721122840562163

theorem tailTrace_6523497 : CollatzResearch.WordTrace tailWord_6523497 prefixEnd_6523497 1116563169721122840562163 := by
  unfold tailWord_6523497
  simp only [CollatzResearch.WordTrace]
  refine ⟨237931482447491968432720745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158620988298327978955147163 237931482447491968432720745)
  ·
    refine ⟨178448611835618976324540559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237931482447491968432720745 178448611835618976324540559)
    ·
      refine ⟨267672917753428464486810839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178448611835618976324540559 267672917753428464486810839)
      ·
        refine ⟨401509376630142696730216259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267672917753428464486810839 401509376630142696730216259)
        ·
          refine ⟨602264064945214045095324389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401509376630142696730216259 602264064945214045095324389)
          ·
            refine ⟨112924512177227633455373323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 602264064945214045095324389 112924512177227633455373323)
            ·
              refine ⟨169386768265841450183059985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112924512177227633455373323 169386768265841450183059985)
              ·
                refine ⟨127040076199381087637294989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169386768265841450183059985 127040076199381087637294989)
                ·
                  refine ⟨47640028574767907863985621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127040076199381087637294989 47640028574767907863985621)
                  ·
                    refine ⟨1116563169721122840562163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47640028574767907863985621 1116563169721122840562163)
                    ·
                      rfl

theorem cell23_6523497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 7].length) (baseStart_6523497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523497 prefixEnd_6523497 := by exact prefixLift 6523497
  have htrace : WordTrace (prefixWord ++ tailWord_6523497) baseStart_6523497 baseEnd_6523497 := by
    simpa [prefixWord, tailWord_6523497, baseEnd_6523497] using wordTrace_append hprefix tailTrace_6523497
  have hstable : (prefixWord ++ tailWord_6523497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523497).length < 2 ^ (prefixWord ++ tailWord_6523497).sum := by decide
  have hdescent : baseEnd_6523497 < baseStart_6523497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523507 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 7]
def baseStart_6523507 : Nat := 118140960795 + 6523507 * 2 ^ 59
def prefixEnd_6523507 : Nat := 4983230072969 + 3 ^ 40 * 6523507 * 2
def baseEnd_6523507 : Nat := 3349694643969913482561443

theorem tailTrace_6523507 : CollatzResearch.WordTrace tailWord_6523507 prefixEnd_6523507 3349694643969913482561443 := by
  unfold tailWord_6523507
  simp only [CollatzResearch.WordTrace]
  refine ⟨237931847177455740140584775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158621231451637160093723183 237931847177455740140584775)
  ·
    refine ⟨356897770766183610210877163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237931847177455740140584775 356897770766183610210877163)
    ·
      refine ⟨535346656149275415316315745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356897770766183610210877163 535346656149275415316315745)
      ·
        refine ⟨401509992111956561487236809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535346656149275415316315745 401509992111956561487236809)
        ·
          refine ⟨301132494083967421115427607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401509992111956561487236809 301132494083967421115427607)
          ·
            refine ⟨451698741125951131673141411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301132494083967421115427607 451698741125951131673141411)
            ·
              refine ⟨677548111688926697509712117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451698741125951131673141411 677548111688926697509712117)
              ·
                refine ⟨63520135470836877891535511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 677548111688926697509712117 63520135470836877891535511)
                ·
                  refine ⟨95280203206255316837303267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63520135470836877891535511 95280203206255316837303267)
                  ·
                    refine ⟨142920304809382975255954901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95280203206255316837303267 142920304809382975255954901)
                    ·
                      refine ⟨3349694643969913482561443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142920304809382975255954901 3349694643969913482561443)
                      ·
                        rfl

theorem cell23_6523507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_6523507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523507 prefixEnd_6523507 := by exact prefixLift 6523507
  have htrace : WordTrace (prefixWord ++ tailWord_6523507) baseStart_6523507 baseEnd_6523507 := by
    simpa [prefixWord, tailWord_6523507, baseEnd_6523507] using wordTrace_append hprefix tailTrace_6523507
  have hstable : (prefixWord ++ tailWord_6523507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523507).length < 2 ^ (prefixWord ++ tailWord_6523507).sum := by decide
  have hdescent : baseEnd_6523507 < baseStart_6523507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523521 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 2, 5, 2]
def baseStart_6523521 : Nat := 118140960795 + 6523521 * 2 ^ 59
def prefixEnd_6523521 : Nat := 4983230072969 + 3 ^ 40 * 6523521 * 2
def baseEnd_6523521 : Nat := 3349701832699076427786379

theorem tailTrace_6523521 : CollatzResearch.WordTrace tailWord_6523521 prefixEnd_6523521 3349701832699076427786379 := by
  unfold tailWord_6523521
  simp only [CollatzResearch.WordTrace]
  refine ⟨237932357799405020531594417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158621571866270013687729611 237932357799405020531594417)
  ·
    refine ⟨178449268349553765398695813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237932357799405020531594417 178449268349553765398695813)
    ·
      refine ⟨33459237815541331012255465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178449268349553765398695813 33459237815541331012255465)
      ·
        refine ⟨25094428361655998259191599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33459237815541331012255465 25094428361655998259191599)
        ·
          refine ⟨37641642542483997388787399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25094428361655998259191599 37641642542483997388787399)
          ·
            refine ⟨56462463813725996083181099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37641642542483997388787399 56462463813725996083181099)
            ·
              refine ⟨84693695720588994124771649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56462463813725996083181099 84693695720588994124771649)
              ·
                refine ⟨63520271790441745593578737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84693695720588994124771649 63520271790441745593578737)
                ·
                  refine ⟨47640203842831309195184053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63520271790441745593578737 47640203842831309195184053)
                  ·
                    refine ⟨4466269110265435237048505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47640203842831309195184053 4466269110265435237048505)
                    ·
                      refine ⟨3349701832699076427786379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4466269110265435237048505 3349701832699076427786379)
                      ·
                        rfl

theorem cell23_6523521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_6523521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523521 prefixEnd_6523521 := by exact prefixLift 6523521
  have htrace : WordTrace (prefixWord ++ tailWord_6523521) baseStart_6523521 baseEnd_6523521 := by
    simpa [prefixWord, tailWord_6523521, baseEnd_6523521] using wordTrace_append hprefix tailTrace_6523521
  have hstable : (prefixWord ++ tailWord_6523521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523521).length < 2 ^ (prefixWord ++ tailWord_6523521).sum := by decide
  have hdescent : baseEnd_6523521 < baseStart_6523521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523605 : List Nat := [1, 3, 2, 5, 1, 1, 1, 2, 2, 2, 3]
def baseStart_6523605 : Nat := 118140960795 + 6523605 * 2 ^ 59
def prefixEnd_6523605 : Nat := 4983230072969 + 3 ^ 40 * 6523605 * 2
def baseEnd_6523605 : Nat := 3349744965074054099135993

theorem tailTrace_6523605 : CollatzResearch.WordTrace tailWord_6523605 prefixEnd_6523605 3349744965074054099135993 := by
  unfold tailWord_6523605
  simp only [CollatzResearch.WordTrace]
  refine ⟨237935421531100702877652269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158623614354067135251768179 237935421531100702877652269)
  ·
    refine ⟨89225783074162763579119601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237935421531100702877652269 89225783074162763579119601)
    ·
      refine ⟨66919337305622072684339701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89225783074162763579119601 66919337305622072684339701)
      ·
        refine ⟨6273687872402069314156847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66919337305622072684339701 6273687872402069314156847)
        ·
          refine ⟨9410531808603103971235271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6273687872402069314156847 9410531808603103971235271)
          ·
            refine ⟨14115797712904655956852907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9410531808603103971235271 14115797712904655956852907)
            ·
              refine ⟨21173696569356983935279361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14115797712904655956852907 21173696569356983935279361)
              ·
                refine ⟨15880272427017737951459521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21173696569356983935279361 15880272427017737951459521)
                ·
                  refine ⟨11910204320263303463594641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15880272427017737951459521 11910204320263303463594641)
                  ·
                    refine ⟨8932653240197477597695981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11910204320263303463594641 8932653240197477597695981)
                    ·
                      refine ⟨3349744965074054099135993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8932653240197477597695981 3349744965074054099135993)
                      ·
                        rfl

theorem cell23_6523605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_6523605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523605 prefixEnd_6523605 := by exact prefixLift 6523605
  have htrace : WordTrace (prefixWord ++ tailWord_6523605) baseStart_6523605 baseEnd_6523605 := by
    simpa [prefixWord, tailWord_6523605, baseEnd_6523605] using wordTrace_append hprefix tailTrace_6523605
  have hstable : (prefixWord ++ tailWord_6523605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523605).length < 2 ^ (prefixWord ++ tailWord_6523605).sum := by decide
  have hdescent : baseEnd_6523605 < baseStart_6523605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523641 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 2, 6, 2]
def baseStart_6523641 : Nat := 118140960795 + 6523641 * 2 ^ 59
def prefixEnd_6523641 : Nat := 4983230072969 + 3 ^ 40 * 6523641 * 2
def baseEnd_6523641 : Nat := 3349763450377615958285827

theorem tailTrace_6523641 : CollatzResearch.WordTrace tailWord_6523641 prefixEnd_6523641 3349763450377615958285827 := by
  unfold tailWord_6523641
  simp only [CollatzResearch.WordTrace]
  refine ⟨237936734558970281025962777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158624489705980187350641851 237936734558970281025962777)
  ·
    refine ⟨178452550919227710769472083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237936734558970281025962777 178452550919227710769472083)
    ·
      refine ⟨267678826378841566154208125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178452550919227710769472083 267678826378841566154208125)
      ·
        refine ⟨100379559892065587307828047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267678826378841566154208125 100379559892065587307828047)
        ·
          refine ⟨150569339838098380961742071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100379559892065587307828047 150569339838098380961742071)
          ·
            refine ⟨225854009757147571442613107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150569339838098380961742071 225854009757147571442613107)
            ·
              refine ⟨338781014635721357163919661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225854009757147571442613107 338781014635721357163919661)
              ·
                refine ⟨127042880488395508936469873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 338781014635721357163919661 127042880488395508936469873)
                ·
                  refine ⟨95282160366296631702352405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127042880488395508936469873 95282160366296631702352405)
                  ·
                    refine ⟨4466351267170154611047769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95282160366296631702352405 4466351267170154611047769)
                    ·
                      refine ⟨3349763450377615958285827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4466351267170154611047769 3349763450377615958285827)
                      ·
                        rfl

theorem cell23_6523641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_6523641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523641 prefixEnd_6523641 := by exact prefixLift 6523641
  have htrace : WordTrace (prefixWord ++ tailWord_6523641) baseStart_6523641 baseEnd_6523641 := by
    simpa [prefixWord, tailWord_6523641, baseEnd_6523641] using wordTrace_append hprefix tailTrace_6523641
  have hstable : (prefixWord ++ tailWord_6523641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523641).length < 2 ^ (prefixWord ++ tailWord_6523641).sum := by decide
  have hdescent : baseEnd_6523641 < baseStart_6523641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523655 : List Nat := [1, 1, 4, 4, 1, 2, 3, 1, 1, 5]
def baseStart_6523655 : Nat := 118140960795 + 6523655 * 2 ^ 59
def prefixEnd_6523655 : Nat := 4983230072969 + 3 ^ 40 * 6523655 * 2
def baseEnd_6523655 : Nat := 1116590213035592967836921

theorem tailTrace_6523655 : CollatzResearch.WordTrace tailWord_6523655 prefixEnd_6523655 1116590213035592967836921 := by
  unfold tailWord_6523655
  simp only [CollatzResearch.WordTrace]
  refine ⟨237937245180919561416972419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158624830120613040944648279 237937245180919561416972419)
  ·
    refine ⟨356905867771379342125458629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237937245180919561416972419 356905867771379342125458629)
    ·
      refine ⟨66919850207133626648523493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 356905867771379342125458629 66919850207133626648523493)
      ·
        refine ⟨12547471913837554996598155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66919850207133626648523493 12547471913837554996598155)
        ·
          refine ⟨18821207870756332494897233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12547471913837554996598155 18821207870756332494897233)
          ·
            refine ⟨14115905903067249371172925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18821207870756332494897233 14115905903067249371172925)
            ·
              refine ⟨5293464713650218514189847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14115905903067249371172925 5293464713650218514189847)
              ·
                refine ⟨7940197070475327771284771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5293464713650218514189847 7940197070475327771284771)
                ·
                  refine ⟨11910295605712991656927157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7940197070475327771284771 11910295605712991656927157)
                  ·
                    refine ⟨1116590213035592967836921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11910295605712991656927157 1116590213035592967836921)
                    ·
                      rfl

theorem cell23_6523655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_6523655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523655 prefixEnd_6523655 := by exact prefixLift 6523655
  have htrace : WordTrace (prefixWord ++ tailWord_6523655) baseStart_6523655 baseEnd_6523655 := by
    simpa [prefixWord, tailWord_6523655, baseEnd_6523655] using wordTrace_append hprefix tailTrace_6523655
  have hstable : (prefixWord ++ tailWord_6523655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523655).length < 2 ^ (prefixWord ++ tailWord_6523655).sum := by decide
  have hdescent : baseEnd_6523655 < baseStart_6523655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523688 : List Nat := [2, 1, 5, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_6523688 : Nat := 118140960795 + 6523688 * 2 ^ 59
def prefixEnd_6523688 : Nat := 4983230072969 + 3 ^ 40 * 6523688 * 2
def baseEnd_6523688 : Nat := 3349787583968377274398111

theorem tailTrace_6523688 : CollatzResearch.WordTrace tailWord_6523688 prefixEnd_6523688 3349787583968377274398111 := by
  unfold tailWord_6523688
  simp only [CollatzResearch.WordTrace]
  refine ⟨118969224394900004026461859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158625632526533338701949145 118969224394900004026461859)
  ·
    refine ⟨178453836592350006039692789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118969224394900004026461859 178453836592350006039692789)
    ·
      refine ⟨16730047180532813066221199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178453836592350006039692789 16730047180532813066221199)
      ·
        refine ⟨25095070770799219599331799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16730047180532813066221199 25095070770799219599331799)
        ·
          refine ⟨37642606156198829398997699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25095070770799219599331799 37642606156198829398997699)
          ·
            refine ⟨56463909234298244098496549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37642606156198829398997699 56463909234298244098496549)
            ·
              refine ⟨10586982981430920768468103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56463909234298244098496549 10586982981430920768468103)
              ·
                refine ⟨15880474472146381152702155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10586982981430920768468103 15880474472146381152702155)
                ·
                  refine ⟨23820711708219571729053233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15880474472146381152702155 23820711708219571729053233)
                  ·
                    refine ⟨17865533781164678796789925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23820711708219571729053233 17865533781164678796789925)
                    ·
                      refine ⟨3349787583968377274398111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17865533781164678796789925 3349787583968377274398111)
                      ·
                        rfl

theorem cell23_6523688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_6523688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523688 prefixEnd_6523688 := by exact prefixLift 6523688
  have htrace : WordTrace (prefixWord ++ tailWord_6523688) baseStart_6523688 baseEnd_6523688 := by
    simpa [prefixWord, tailWord_6523688, baseEnd_6523688] using wordTrace_append hprefix tailTrace_6523688
  have hstable : (prefixWord ++ tailWord_6523688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523688).length < 2 ^ (prefixWord ++ tailWord_6523688).sum := by decide
  have hdescent : baseEnd_6523688 < baseStart_6523688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523691 : List Nat := [1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 3]
def baseStart_6523691 : Nat := 118140960795 + 6523691 * 2 ^ 59
def prefixEnd_6523691 : Nat := 4983230072969 + 3 ^ 40 * 6523691 * 2
def baseEnd_6523691 : Nat := 3349789124410340762660597

theorem tailTrace_6523691 : CollatzResearch.WordTrace tailWord_6523691 prefixEnd_6523691 3349789124410340762660597 := by
  unfold tailWord_6523691
  simp only [CollatzResearch.WordTrace]
  refine ⟨237938558208789139565282927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158625705472526093043521951 237938558208789139565282927)
  ·
    refine ⟨356907837313183709347924391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237938558208789139565282927 356907837313183709347924391)
    ·
      refine ⟨535361755969775564021886587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356907837313183709347924391 535361755969775564021886587)
      ·
        refine ⟨803042633954663346032829881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535361755969775564021886587 803042633954663346032829881)
        ·
          refine ⟨602281975465997509524622411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 803042633954663346032829881 602281975465997509524622411)
          ·
            refine ⟨903422963198996264286933617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602281975465997509524622411 903422963198996264286933617)
            ·
              refine ⟨677567222399247198215200213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 903422963198996264286933617 677567222399247198215200213)
              ·
                refine ⟨15880481774982356208168755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 677567222399247198215200213 15880481774982356208168755)
                ·
                  refine ⟨23820722662473534312253133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15880481774982356208168755 23820722662473534312253133)
                  ·
                    refine ⟨8932770998427575367094925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23820722662473534312253133 8932770998427575367094925)
                    ·
                      refine ⟨3349789124410340762660597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8932770998427575367094925 3349789124410340762660597)
                      ·
                        rfl

theorem cell23_6523691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 3].length) (baseStart_6523691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523691 prefixEnd_6523691 := by exact prefixLift 6523691
  have htrace : WordTrace (prefixWord ++ tailWord_6523691) baseStart_6523691 baseEnd_6523691 := by
    simpa [prefixWord, tailWord_6523691, baseEnd_6523691] using wordTrace_append hprefix tailTrace_6523691
  have hstable : (prefixWord ++ tailWord_6523691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523691).length < 2 ^ (prefixWord ++ tailWord_6523691).sum := by decide
  have hdescent : baseEnd_6523691 < baseStart_6523691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523708 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 4, 1, 3]
def baseStart_6523708 : Nat := 118140960795 + 6523708 * 2 ^ 59
def prefixEnd_6523708 : Nat := 4983230072969 + 3 ^ 40 * 6523708 * 2
def baseEnd_6523708 : Nat := 3349797853581467196148019

theorem tailTrace_6523708 : CollatzResearch.WordTrace tailWord_6523708 prefixEnd_6523708 3349797853581467196148019 := by
  unfold tailWord_6523708
  simp only [CollatzResearch.WordTrace]
  refine ⟨118969589124863775734325889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158626118833151700979101185 118969589124863775734325889)
  ·
    refine ⟨89227191843647831800744417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118969589124863775734325889 89227191843647831800744417)
    ·
      refine ⟨66920393882735873850558313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89227191843647831800744417 66920393882735873850558313)
      ·
        refine ⟨50190295412051905387918735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66920393882735873850558313 50190295412051905387918735)
        ·
          refine ⟨75285443118077858081878103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50190295412051905387918735 75285443118077858081878103)
          ·
            refine ⟨112928164677116787122817155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75285443118077858081878103 112928164677116787122817155)
            ·
              refine ⟨169392247015675180684225733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112928164677116787122817155 169392247015675180684225733)
              ·
                refine ⟨31761046315439096378292325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169392247015675180684225733 31761046315439096378292325)
                ·
                  refine ⟨5955196184144830570929811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31761046315439096378292325 5955196184144830570929811)
                  ·
                    refine ⟨8932794276217245856394717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5955196184144830570929811 8932794276217245856394717)
                    ·
                      refine ⟨3349797853581467196148019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8932794276217245856394717 3349797853581467196148019)
                      ·
                        rfl

theorem cell23_6523708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_6523708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523708 prefixEnd_6523708 := by exact prefixLift 6523708
  have htrace : WordTrace (prefixWord ++ tailWord_6523708) baseStart_6523708 baseEnd_6523708 := by
    simpa [prefixWord, tailWord_6523708, baseEnd_6523708] using wordTrace_append hprefix tailTrace_6523708
  have hstable : (prefixWord ++ tailWord_6523708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523708).length < 2 ^ (prefixWord ++ tailWord_6523708).sum := by decide
  have hdescent : baseEnd_6523708 < baseStart_6523708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523709 : List Nat := [1, 4, 1, 4, 3, 1, 2, 1, 1, 1, 4]
def baseStart_6523709 : Nat := 118140960795 + 6523709 * 2 ^ 59
def prefixEnd_6523709 : Nat := 4983230072969 + 3 ^ 40 * 6523709 * 2
def baseEnd_6523709 : Nat := 3349798367062121692235515

theorem tailTrace_6523709 : CollatzResearch.WordTrace tailWord_6523709 prefixEnd_6523709 3349798367062121692235515 := by
  unfold tailWord_6523709
  simp only [CollatzResearch.WordTrace]
  refine ⟨237939214722723928639438181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158626143148482619092958787 237939214722723928639438181)
  ·
    refine ⟨44613602760510736619894659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237939214722723928639438181 44613602760510736619894659)
    ·
      refine ⟨66920404140766104929841989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44613602760510736619894659 66920404140766104929841989)
      ·
        refine ⟨12547575776393644674345373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66920404140766104929841989 12547575776393644674345373)
        ·
          refine ⟨4705340916147616752879515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12547575776393644674345373 4705340916147616752879515)
          ·
            refine ⟨7058011374221425129319273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4705340916147616752879515 7058011374221425129319273)
            ·
              refine ⟨5293508530666068846989455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7058011374221425129319273 5293508530666068846989455)
              ·
                refine ⟨7940262795999103270484183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5293508530666068846989455 7940262795999103270484183)
                ·
                  refine ⟨11910394193998654905726275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7940262795999103270484183 11910394193998654905726275)
                  ·
                    refine ⟨17865591290997982358589413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11910394193998654905726275 17865591290997982358589413)
                    ·
                      refine ⟨3349798367062121692235515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17865591290997982358589413 3349798367062121692235515)
                      ·
                        rfl

theorem cell23_6523709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_6523709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523709 prefixEnd_6523709 := by exact prefixLift 6523709
  have htrace : WordTrace (prefixWord ++ tailWord_6523709) baseStart_6523709 baseEnd_6523709 := by
    simpa [prefixWord, tailWord_6523709, baseEnd_6523709] using wordTrace_append hprefix tailTrace_6523709
  have hstable : (prefixWord ++ tailWord_6523709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523709).length < 2 ^ (prefixWord ++ tailWord_6523709).sum := by decide
  have hdescent : baseEnd_6523709 < baseStart_6523709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523752 : List Nat := [2, 1, 4, 2, 1, 3, 2, 2, 1, 3, 2]
def baseStart_6523752 : Nat := 118140960795 + 6523752 * 2 ^ 59
def prefixEnd_6523752 : Nat := 4983230072969 + 3 ^ 40 * 6523752 * 2
def baseEnd_6523752 : Nat := 3349820446730265023997817

theorem tailTrace_6523752 : CollatzResearch.WordTrace tailWord_6523752 prefixEnd_6523752 3349820446730265023997817 := by
  unfold tailWord_6523752
  simp only [CollatzResearch.WordTrace]
  refine ⟨118970391530784073491626755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158627188707712097988835673 118970391530784073491626755)
  ·
    refine ⟨178455587296176110237440133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118970391530784073491626755 178455587296176110237440133)
    ·
      refine ⟨33460422618033020669520025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178455587296176110237440133 33460422618033020669520025)
      ·
        refine ⟨25095316963524765502140019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33460422618033020669520025 25095316963524765502140019)
        ·
          refine ⟨37642975445287148253210029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25095316963524765502140019 37642975445287148253210029)
          ·
            refine ⟨14116115791982680594953761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37642975445287148253210029 14116115791982680594953761)
            ·
              refine ⟨10587086843987010446215321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14116115791982680594953761 10587086843987010446215321)
              ·
                refine ⟨7940315132990257834661491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10587086843987010446215321 7940315132990257834661491)
                ·
                  refine ⟨11910472699485386751992237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7940315132990257834661491 11910472699485386751992237)
                  ·
                    refine ⟨4466427262307020031997089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11910472699485386751992237 4466427262307020031997089)
                    ·
                      refine ⟨3349820446730265023997817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4466427262307020031997089 3349820446730265023997817)
                      ·
                        rfl

theorem cell23_6523752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_6523752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523752 prefixEnd_6523752 := by exact prefixLift 6523752
  have htrace : WordTrace (prefixWord ++ tailWord_6523752) baseStart_6523752 baseEnd_6523752 := by
    simpa [prefixWord, tailWord_6523752, baseEnd_6523752] using wordTrace_append hprefix tailTrace_6523752
  have hstable : (prefixWord ++ tailWord_6523752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523752).length < 2 ^ (prefixWord ++ tailWord_6523752).sum := by decide
  have hdescent : baseEnd_6523752 < baseStart_6523752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523788 : List Nat := [2, 2, 1, 2, 1, 2, 2, 6, 5]
def baseStart_6523788 : Nat := 118140960795 + 6523788 * 2 ^ 59
def prefixEnd_6523788 : Nat := 4983230072969 + 3 ^ 40 * 6523788 * 2
def baseEnd_6523788 : Nat := 372204325781536320349739

theorem tailTrace_6523788 : CollatzResearch.WordTrace tailWord_6523788 prefixEnd_6523788 372204325781536320349739 := by
  unfold tailWord_6523788
  simp only [CollatzResearch.WordTrace]
  refine ⟨118971048044718862565782009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158628064059625150087709345 118971048044718862565782009)
  ·
    refine ⟨89228286033539146924336507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118971048044718862565782009 89228286033539146924336507)
    ·
      refine ⟨133842429050308720386504761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89228286033539146924336507 133842429050308720386504761)
      ·
        refine ⟨100381821787731540289878571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133842429050308720386504761 100381821787731540289878571)
        ·
          refine ⟨150572732681597310434817857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100381821787731540289878571 150572732681597310434817857)
          ·
            refine ⟨112929549511197982826113393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150572732681597310434817857 112929549511197982826113393)
            ·
              refine ⟨84697162133398487119585045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112929549511197982826113393 84697162133398487119585045)
              ·
                refine ⟨3970179475003054083730549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84697162133398487119585045 3970179475003054083730549)
                ·
                  refine ⟨372204325781536320349739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3970179475003054083730549 372204325781536320349739)
                  ·
                    rfl

theorem cell23_6523788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 5].length) (baseStart_6523788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523788 prefixEnd_6523788 := by exact prefixLift 6523788
  have htrace : WordTrace (prefixWord ++ tailWord_6523788) baseStart_6523788 baseEnd_6523788 := by
    simpa [prefixWord, tailWord_6523788, baseEnd_6523788] using wordTrace_append hprefix tailTrace_6523788
  have hstable : (prefixWord ++ tailWord_6523788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523788).length < 2 ^ (prefixWord ++ tailWord_6523788).sum := by decide
  have hdescent : baseEnd_6523788 < baseStart_6523788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523801 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 6, 5]
def baseStart_6523801 : Nat := 118140960795 + 6523801 * 2 ^ 59
def prefixEnd_6523801 : Nat := 4983230072969 + 3 ^ 40 * 6523801 * 2
def baseEnd_6523801 : Nat := 1116615202427445110761697

theorem tailTrace_6523801 : CollatzResearch.WordTrace tailWord_6523801 prefixEnd_6523801 1116615202427445110761697 := by
  unfold tailWord_6523801
  simp only [CollatzResearch.WordTrace]
  refine ⟨237942570238390628351787257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158628380158927085567858171 237942570238390628351787257)
  ·
    refine ⟨178456927678792971263840443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237942570238390628351787257 178456927678792971263840443)
    ·
      refine ⟨267685391518189456895760665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178456927678792971263840443 267685391518189456895760665)
      ·
        refine ⟨200764043638642092671820499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267685391518189456895760665 200764043638642092671820499)
        ·
          refine ⟨301146065457963139007730749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200764043638642092671820499 301146065457963139007730749)
          ·
            refine ⟨112929774546736177127899031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301146065457963139007730749 112929774546736177127899031)
            ·
              refine ⟨169394661820104265691848547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112929774546736177127899031 169394661820104265691848547)
              ·
                refine ⟨254091992730156398537772821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169394661820104265691848547 254091992730156398537772821)
                ·
                  refine ⟨11910562159226081181458101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 254091992730156398537772821 11910562159226081181458101)
                  ·
                    refine ⟨1116615202427445110761697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11910562159226081181458101 1116615202427445110761697)
                    ·
                      rfl

theorem cell23_6523801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 5].length) (baseStart_6523801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523801 prefixEnd_6523801 := by exact prefixLift 6523801
  have htrace : WordTrace (prefixWord ++ tailWord_6523801) baseStart_6523801 baseEnd_6523801 := by
    simpa [prefixWord, tailWord_6523801, baseEnd_6523801] using wordTrace_append hprefix tailTrace_6523801
  have hstable : (prefixWord ++ tailWord_6523801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523801).length < 2 ^ (prefixWord ++ tailWord_6523801).sum := by decide
  have hdescent : baseEnd_6523801 < baseStart_6523801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523846 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_6523846 : Nat := 118140960795 + 6523846 * 2 ^ 59
def prefixEnd_6523846 : Nat := 4983230072969 + 3 ^ 40 * 6523846 * 2
def baseEnd_6523846 : Nat := 3349868713911787656222385

theorem tailTrace_6523846 : CollatzResearch.WordTrace tailWord_6523846 prefixEnd_6523846 3349868713911787656222385 := by
  unfold tailWord_6523846
  simp only [CollatzResearch.WordTrace]
  refine ⟨7435756610100862532411731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158629474348818400691450261 7435756610100862532411731)
  ·
    refine ⟨11153634915151293798617597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7435756610100862532411731 11153634915151293798617597)
    ·
      refine ⟨4182613093181735174481599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11153634915151293798617597 4182613093181735174481599)
      ·
        refine ⟨6273919639772602761722399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4182613093181735174481599 6273919639772602761722399)
        ·
          refine ⟨9410879459658904142583599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6273919639772602761722399 9410879459658904142583599)
          ·
            refine ⟨14116319189488356213875399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9410879459658904142583599 14116319189488356213875399)
            ·
              refine ⟨21174478784232534320813099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14116319189488356213875399 21174478784232534320813099)
              ·
                refine ⟨31761718176348801481219649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21174478784232534320813099 31761718176348801481219649)
                ·
                  refine ⟨23821288632261601110914737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31761718176348801481219649 23821288632261601110914737)
                  ·
                    refine ⟨17865966474196200833186053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23821288632261601110914737 17865966474196200833186053)
                    ·
                      refine ⟨3349868713911787656222385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17865966474196200833186053 3349868713911787656222385)
                      ·
                        rfl

theorem cell23_6523846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_6523846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523846 prefixEnd_6523846 := by exact prefixLift 6523846
  have htrace : WordTrace (prefixWord ++ tailWord_6523846) baseStart_6523846 baseEnd_6523846 := by
    simpa [prefixWord, tailWord_6523846, baseEnd_6523846] using wordTrace_append hprefix tailTrace_6523846
  have hstable : (prefixWord ++ tailWord_6523846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523846).length < 2 ^ (prefixWord ++ tailWord_6523846).sum := by decide
  have hdescent : baseEnd_6523846 < baseStart_6523846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523855 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 2, 4, 2]
def baseStart_6523855 : Nat := 118140960795 + 6523855 * 2 ^ 59
def prefixEnd_6523855 : Nat := 4983230072969 + 3 ^ 40 * 6523855 * 2
def baseEnd_6523855 : Nat := 3349873335237678121009843

theorem tailTrace_6523855 : CollatzResearch.WordTrace tailWord_6523855 prefixEnd_6523855 3349873335237678121009843 := by
  unfold tailWord_6523855
  simp only [CollatzResearch.WordTrace]
  refine ⟨237944539780194995574253019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158629693186796663716168679 237944539780194995574253019)
  ·
    refine ⟨356916809670292493361379529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237944539780194995574253019 356916809670292493361379529)
    ·
      refine ⟨267687607252719370021034647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356916809670292493361379529 267687607252719370021034647)
      ·
        refine ⟨401531410879079055031551971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267687607252719370021034647 401531410879079055031551971)
        ·
          refine ⟨602297116318618582547327957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401531410879079055031551971 602297116318618582547327957)
          ·
            refine ⟨14116338663717623028452999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 602297116318618582547327957 14116338663717623028452999)
            ·
              refine ⟨21174507995576434542679499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14116338663717623028452999 21174507995576434542679499)
              ·
                refine ⟨31761761993364651814019249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21174507995576434542679499 31761761993364651814019249)
                ·
                  refine ⟨23821321495023488860514437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31761761993364651814019249 23821321495023488860514437)
                  ·
                    refine ⟨4466497780316904161346457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23821321495023488860514437 4466497780316904161346457)
                    ·
                      refine ⟨3349873335237678121009843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4466497780316904161346457 3349873335237678121009843)
                      ·
                        rfl

theorem cell23_6523855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 4, 2].length) (baseStart_6523855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523855 prefixEnd_6523855 := by exact prefixLift 6523855
  have htrace : WordTrace (prefixWord ++ tailWord_6523855) baseStart_6523855 baseEnd_6523855 := by
    simpa [prefixWord, tailWord_6523855, baseEnd_6523855] using wordTrace_append hprefix tailTrace_6523855
  have hstable : (prefixWord ++ tailWord_6523855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523855).length < 2 ^ (prefixWord ++ tailWord_6523855).sum := by decide
  have hdescent : baseEnd_6523855 < baseStart_6523855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523865 : List Nat := [1, 2, 1, 2, 5, 2, 1, 2, 3, 4]
def baseStart_6523865 : Nat := 118140960795 + 6523865 * 2 ^ 59
def prefixEnd_6523865 : Nat := 4983230072969 + 3 ^ 40 * 6523865 * 2
def baseEnd_6523865 : Nat := 1116626156681407693961599

theorem tailTrace_6523865 : CollatzResearch.WordTrace tailWord_6523865 prefixEnd_6523865 1116626156681407693961599 := by
  unfold tailWord_6523865
  simp only [CollatzResearch.WordTrace]
  refine ⟨237944904510158767282117049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158629936340105844854744699 237944904510158767282117049)
  ·
    refine ⟨178458678382619075461587787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237944904510158767282117049 178458678382619075461587787)
    ·
      refine ⟨267688017573928613192381681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178458678382619075461587787 267688017573928613192381681)
      ·
        refine ⟨200766013180446459894286261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267688017573928613192381681 200766013180446459894286261)
        ·
          refine ⟨18821813735666855615089337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200766013180446459894286261 18821813735666855615089337)
          ·
            refine ⟨14116360301750141711317003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18821813735666855615089337 14116360301750141711317003)
            ·
              refine ⟨21174540452625212566975505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14116360301750141711317003 21174540452625212566975505)
              ·
                refine ⟨15880905339468909425231629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21174540452625212566975505 15880905339468909425231629)
                ·
                  refine ⟨5955339502300841034461861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15880905339468909425231629 5955339502300841034461861)
                  ·
                    refine ⟨1116626156681407693961599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5955339502300841034461861 1116626156681407693961599)
                    ·
                      rfl

theorem cell23_6523865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 4].length) (baseStart_6523865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523865 prefixEnd_6523865 := by exact prefixLift 6523865
  have htrace : WordTrace (prefixWord ++ tailWord_6523865) baseStart_6523865 baseEnd_6523865 := by
    simpa [prefixWord, tailWord_6523865, baseEnd_6523865] using wordTrace_append hprefix tailTrace_6523865
  have hstable : (prefixWord ++ tailWord_6523865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523865).length < 2 ^ (prefixWord ++ tailWord_6523865).sum := by decide
  have hdescent : baseEnd_6523865 < baseStart_6523865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523881 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 5, 2, 6]
def baseStart_6523881 : Nat := 118140960795 + 6523881 * 2 ^ 59
def prefixEnd_6523881 : Nat := 4983230072969 + 3 ^ 40 * 6523881 * 2
def baseEnd_6523881 : Nat := 3349886685734695019284723

theorem tailTrace_6523881 : CollatzResearch.WordTrace tailWord_6523881 prefixEnd_6523881 3349886685734695019284723 := by
  unfold tailWord_6523881
  simp only [CollatzResearch.WordTrace]
  refine ⟨237945488078100802014699497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158630325385400534676466331 237945488078100802014699497)
  ·
    refine ⟨178459116058575601511024623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237945488078100802014699497 178459116058575601511024623)
    ·
      refine ⟨267688674087863402266536935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178459116058575601511024623 267688674087863402266536935)
      ·
        refine ⟨401533011131795103399805403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267688674087863402266536935 401533011131795103399805403)
        ·
          refine ⟨602299516697692655099708105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401533011131795103399805403 602299516697692655099708105)
          ·
            refine ⟨451724637523269491324781079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602299516697692655099708105 451724637523269491324781079)
            ·
              refine ⟨677586956284904236987171619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451724637523269491324781079 677586956284904236987171619)
              ·
                refine ⟨1016380434427356355480757429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677586956284904236987171619 1016380434427356355480757429)
                ·
                  refine ⟨95285665727564658326321009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1016380434427356355480757429 95285665727564658326321009)
                  ·
                    refine ⟨71464249295673493744740757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95285665727564658326321009 71464249295673493744740757)
                    ·
                      refine ⟨3349886685734695019284723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71464249295673493744740757 3349886685734695019284723)
                      ·
                        rfl

theorem cell23_6523881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_6523881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523881 prefixEnd_6523881 := by exact prefixLift 6523881
  have htrace : WordTrace (prefixWord ++ tailWord_6523881) baseStart_6523881 baseEnd_6523881 := by
    simpa [prefixWord, tailWord_6523881, baseEnd_6523881] using wordTrace_append hprefix tailTrace_6523881
  have hstable : (prefixWord ++ tailWord_6523881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523881).length < 2 ^ (prefixWord ++ tailWord_6523881).sum := by decide
  have hdescent : baseEnd_6523881 < baseStart_6523881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523882 : List Nat := [3, 1, 3, 1, 2, 2, 1, 5, 1, 4]
def baseStart_6523882 : Nat := 118140960795 + 6523882 * 2 ^ 59
def prefixEnd_6523882 : Nat := 4983230072969 + 3 ^ 40 * 6523882 * 2
def baseEnd_6523882 : Nat := 1116629066405116505124073

theorem tailTrace_6523882 : CollatzResearch.WordTrace tailWord_6523882 prefixEnd_6523882 1116629066405116505124073 := by
  unfold tailWord_6523882
  simp only [CollatzResearch.WordTrace]
  refine ⟨59486381137774294796371475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158630349700731452790323933 59486381137774294796371475)
  ·
    refine ⟨89229571706661442194557213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59486381137774294796371475 89229571706661442194557213)
    ·
      refine ⟨33461089389998040822958955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89229571706661442194557213 33461089389998040822958955)
      ·
        refine ⟨50191634084997061234438433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33461089389998040822958955 50191634084997061234438433)
        ·
          refine ⟨37643725563747795925828825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50191634084997061234438433 37643725563747795925828825)
          ·
            refine ⟨28232794172810846944371619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37643725563747795925828825 28232794172810846944371619)
            ·
              refine ⟨42349191259216270416557429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28232794172810846944371619 42349191259216270416557429)
              ·
                refine ⟨3970236680551525351552259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42349191259216270416557429 3970236680551525351552259)
                ·
                  refine ⟨5955355020827288027328389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3970236680551525351552259 5955355020827288027328389)
                  ·
                    refine ⟨1116629066405116505124073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5955355020827288027328389 1116629066405116505124073)
                    ·
                      rfl

theorem cell23_6523882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_6523882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523882 prefixEnd_6523882 := by exact prefixLift 6523882
  have htrace : WordTrace (prefixWord ++ tailWord_6523882) baseStart_6523882 baseEnd_6523882 := by
    simpa [prefixWord, tailWord_6523882, baseEnd_6523882] using wordTrace_append hprefix tailTrace_6523882
  have hstable : (prefixWord ++ tailWord_6523882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523882).length < 2 ^ (prefixWord ++ tailWord_6523882).sum := by decide
  have hdescent : baseEnd_6523882 < baseStart_6523882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523915 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 1, 5, 2]
def baseStart_6523915 : Nat := 118140960795 + 6523915 * 2 ^ 59
def prefixEnd_6523915 : Nat := 4983230072969 + 3 ^ 40 * 6523915 * 2
def baseEnd_6523915 : Nat := 3349904144076947886259567

theorem tailTrace_6523915 : CollatzResearch.WordTrace tailWord_6523915 prefixEnd_6523915 3349904144076947886259567 := by
  unfold tailWord_6523915
  simp only [CollatzResearch.WordTrace]
  refine ⟨237946728159977625821437199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158631152106651750547624799 237946728159977625821437199)
  ·
    refine ⟨356920092239966438732155799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237946728159977625821437199 356920092239966438732155799)
    ·
      refine ⟨535380138359949658098233699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356920092239966438732155799 535380138359949658098233699)
      ·
        refine ⟨803070207539924487147350549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535380138359949658098233699 803070207539924487147350549)
        ·
          refine ⟨37643915978433960335032057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 803070207539924487147350549 37643915978433960335032057)
          ·
            refine ⟨28232936983825470251274043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37643915978433960335032057 28232936983825470251274043)
            ·
              refine ⟨42349405475738205376911065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28232936983825470251274043 42349405475738205376911065)
              ·
                refine ⟨31762054106803654032683299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42349405475738205376911065 31762054106803654032683299)
                ·
                  refine ⟨47643081160205481049024949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31762054106803654032683299 47643081160205481049024949)
                  ·
                    refine ⟨4466538858769263848346089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47643081160205481049024949 4466538858769263848346089)
                    ·
                      refine ⟨3349904144076947886259567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4466538858769263848346089 3349904144076947886259567)
                      ·
                        rfl

theorem cell23_6523915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 5, 2].length) (baseStart_6523915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523915 prefixEnd_6523915 := by exact prefixLift 6523915
  have htrace : WordTrace (prefixWord ++ tailWord_6523915) baseStart_6523915 baseEnd_6523915 := by
    simpa [prefixWord, tailWord_6523915, baseEnd_6523915] using wordTrace_append hprefix tailTrace_6523915
  have hstable : (prefixWord ++ tailWord_6523915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523915).length < 2 ^ (prefixWord ++ tailWord_6523915).sum := by decide
  have hdescent : baseEnd_6523915 < baseStart_6523915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523925 : List Nat := [1, 3, 2, 1, 4, 1, 1, 4, 1, 5]
def baseStart_6523925 : Nat := 118140960795 + 6523925 * 2 ^ 59
def prefixEnd_6523925 : Nat := 4983230072969 + 3 ^ 40 * 6523925 * 2
def baseEnd_6523925 : Nat := 1116636426294497615711507

theorem tailTrace_6523925 : CollatzResearch.WordTrace tailWord_6523925 prefixEnd_6523925 1116636426294497615711507 := by
  unfold tailWord_6523925
  simp only [CollatzResearch.WordTrace]
  refine ⟨237947092889941397529301229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158631395259960931686200819 237947092889941397529301229)
  ·
    refine ⟨89230159833728024073487961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237947092889941397529301229 89230159833728024073487961)
    ·
      refine ⟨66922619875296018055115971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89230159833728024073487961 66922619875296018055115971)
      ·
        refine ⟨100383929812944027082673957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66922619875296018055115971 100383929812944027082673957)
        ·
          refine ⟨18821986839927005078001367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100383929812944027082673957 18821986839927005078001367)
          ·
            refine ⟨28232980259890507617002051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18821986839927005078001367 28232980259890507617002051)
            ·
              refine ⟨42349470389835761425503077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28232980259890507617002051 42349470389835761425503077)
              ·
                refine ⟨7940525698094205267281827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42349470389835761425503077 7940525698094205267281827)
                ·
                  refine ⟨11910788547141307900922741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7940525698094205267281827 11910788547141307900922741)
                  ·
                    refine ⟨1116636426294497615711507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11910788547141307900922741 1116636426294497615711507)
                    ·
                      rfl

theorem cell23_6523925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_6523925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523925 prefixEnd_6523925 := by exact prefixLift 6523925
  have htrace : WordTrace (prefixWord ++ tailWord_6523925) baseStart_6523925 baseEnd_6523925 := by
    simpa [prefixWord, tailWord_6523925, baseEnd_6523925] using wordTrace_append hprefix tailTrace_6523925
  have hstable : (prefixWord ++ tailWord_6523925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523925).length < 2 ^ (prefixWord ++ tailWord_6523925).sum := by decide
  have hdescent : baseEnd_6523925 < baseStart_6523925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523939 : List Nat := [1, 1, 1, 4, 3, 2, 3, 3, 1, 1, 3]
def baseStart_6523939 : Nat := 118140960795 + 6523939 * 2 ^ 59
def prefixEnd_6523939 : Nat := 4983230072969 + 3 ^ 40 * 6523939 * 2
def baseEnd_6523939 : Nat := 3349916467612655792359457

theorem tailTrace_6523939 : CollatzResearch.WordTrace tailWord_6523939 prefixEnd_6523939 3349916467612655792359457 := by
  unfold tailWord_6523939
  simp only [CollatzResearch.WordTrace]
  refine ⟨237947603511890677920310871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158631735674593785280207247 237947603511890677920310871)
  ·
    refine ⟨356921405267836016880466307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237947603511890677920310871 356921405267836016880466307)
    ·
      refine ⟨535382107901754025320699461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356921405267836016880466307 535382107901754025320699461)
      ·
        refine ⟨100384145231578879747631149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 535382107901754025320699461 100384145231578879747631149)
        ·
          refine ⟨37644054461842079905361681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100384145231578879747631149 37644054461842079905361681)
          ·
            refine ⟨28233040846381559929021261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37644054461842079905361681 28233040846381559929021261)
            ·
              refine ⟨10587390317393084973382973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28233040846381559929021261 10587390317393084973382973)
              ·
                refine ⟨3970271369022406865018615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10587390317393084973382973 3970271369022406865018615)
                ·
                  refine ⟨5955407053533610297527923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3970271369022406865018615 5955407053533610297527923)
                  ·
                    refine ⟨8933110580300415446291885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5955407053533610297527923 8933110580300415446291885)
                    ·
                      refine ⟨3349916467612655792359457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8933110580300415446291885 3349916467612655792359457)
                      ·
                        rfl

theorem cell23_6523939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 1, 1, 3].length) (baseStart_6523939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523939 prefixEnd_6523939 := by exact prefixLift 6523939
  have htrace : WordTrace (prefixWord ++ tailWord_6523939) baseStart_6523939 baseEnd_6523939 := by
    simpa [prefixWord, tailWord_6523939, baseEnd_6523939] using wordTrace_append hprefix tailTrace_6523939
  have hstable : (prefixWord ++ tailWord_6523939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523939).length < 2 ^ (prefixWord ++ tailWord_6523939).sum := by decide
  have hdescent : baseEnd_6523939 < baseStart_6523939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523955 : List Nat := [1, 1, 1, 2, 4, 1, 1, 6, 2, 4]
def baseStart_6523955 : Nat := 118140960795 + 6523955 * 2 ^ 59
def prefixEnd_6523955 : Nat := 4983230072969 + 3 ^ 40 * 6523955 * 2
def baseEnd_6523955 : Nat := 1116641561101042576586461

theorem tailTrace_6523955 : CollatzResearch.WordTrace tailWord_6523955 prefixEnd_6523955 1116641561101042576586461 := by
  unfold tailWord_6523955
  simp only [CollatzResearch.WordTrace]
  refine ⟨237948187079832712652893319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158632124719888475101928879 237948187079832712652893319)
  ·
    refine ⟨356922280619749068979339979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237948187079832712652893319 356922280619749068979339979)
    ·
      refine ⟨535383420929623603469009969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356922280619749068979339979 535383420929623603469009969)
      ·
        refine ⟨401537565697217702601757477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535383420929623603469009969 401537565697217702601757477)
        ·
          refine ⟨75288293568228319237829527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 401537565697217702601757477 75288293568228319237829527)
          ·
            refine ⟨112932440352342478856744291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75288293568228319237829527 112932440352342478856744291)
            ·
              refine ⟨169398660528513718285116437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112932440352342478856744291 169398660528513718285116437)
              ·
                refine ⟨7940562212274080544614833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 169398660528513718285116437 7940562212274080544614833)
                ·
                  refine ⟨5955421659205560408461125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7940562212274080544614833 5955421659205560408461125)
                  ·
                    refine ⟨1116641561101042576586461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5955421659205560408461125 1116641561101042576586461)
                    ·
                      rfl

theorem cell23_6523955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 4].length) (baseStart_6523955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523955 prefixEnd_6523955 := by exact prefixLift 6523955
  have htrace : WordTrace (prefixWord ++ tailWord_6523955) baseStart_6523955 baseEnd_6523955 := by
    simpa [prefixWord, tailWord_6523955, baseEnd_6523955] using wordTrace_append hprefix tailTrace_6523955
  have hstable : (prefixWord ++ tailWord_6523955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523955).length < 2 ^ (prefixWord ++ tailWord_6523955).sum := by decide
  have hdescent : baseEnd_6523955 < baseStart_6523955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523956 : List Nat := [2, 5, 1, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_6523956 : Nat := 118140960795 + 6523956 * 2 ^ 59
def prefixEnd_6523956 : Nat := 4983230072969 + 3 ^ 40 * 6523956 * 2
def baseEnd_6523956 : Nat := 3349925196783782225846879

theorem tailTrace_6523956 : CollatzResearch.WordTrace tailWord_6523956 prefixEnd_6523956 3349925196783782225846879 := by
  unfold tailWord_6523956
  simp only [CollatzResearch.WordTrace]
  refine ⟨118974111776414544911839861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158632149035219393215786481 118974111776414544911839861)
  ·
    refine ⟨11153822979038863585484987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118974111776414544911839861 11153822979038863585484987)
    ·
      refine ⟨16730734468558295378227481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11153822979038863585484987 16730734468558295378227481)
      ·
        refine ⟨12548050851418721533670611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16730734468558295378227481 12548050851418721533670611)
        ·
          refine ⟨18822076277128082300505917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12548050851418721533670611 18822076277128082300505917)
          ·
            refine ⟨7058278603923030862689719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18822076277128082300505917 7058278603923030862689719)
            ·
              refine ⟨10587417905884546294034579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7058278603923030862689719 10587417905884546294034579)
              ·
                refine ⟨15881126858826819441051869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10587417905884546294034579 15881126858826819441051869)
                ·
                  refine ⟨5955422572060057290394451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15881126858826819441051869 5955422572060057290394451)
                  ·
                    refine ⟨8933133858090085935591677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5955422572060057290394451 8933133858090085935591677)
                    ·
                      refine ⟨3349925196783782225846879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8933133858090085935591677 3349925196783782225846879)
                      ·
                        rfl

theorem cell23_6523956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_6523956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523956 prefixEnd_6523956 := by exact prefixLift 6523956
  have htrace : WordTrace (prefixWord ++ tailWord_6523956) baseStart_6523956 baseEnd_6523956 := by
    simpa [prefixWord, tailWord_6523956, baseEnd_6523956] using wordTrace_append hprefix tailTrace_6523956
  have hstable : (prefixWord ++ tailWord_6523956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523956).length < 2 ^ (prefixWord ++ tailWord_6523956).sum := by decide
  have hdescent : baseEnd_6523956 < baseStart_6523956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523965 : List Nat := [1, 4, 1, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_6523965 : Nat := 118140960795 + 6523965 * 2 ^ 59
def prefixEnd_6523965 : Nat := 4983230072969 + 3 ^ 40 * 6523965 * 2
def baseEnd_6523965 : Nat := 3349929818109672690634337

theorem tailTrace_6523965 : CollatzResearch.WordTrace tailWord_6523965 prefixEnd_6523965 3349929818109672690634337 := by
  unfold tailWord_6523965
  simp only [CollatzResearch.WordTrace]
  refine ⟨237948551809796484360757349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158632367873197656240504899 237948551809796484360757349)
  ·
    refine ⟨44615353464336840817642003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237948551809796484360757349 44615353464336840817642003)
    ·
      refine ⟨66923030196505261226463005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44615353464336840817642003 66923030196505261226463005)
      ·
        refine ⟨25096136323689472959923627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66923030196505261226463005 25096136323689472959923627)
        ·
          refine ⟨37644204485534209439885441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25096136323689472959923627 37644204485534209439885441)
          ·
            refine ⟨28233153364150657079914081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37644204485534209439885441 28233153364150657079914081)
            ·
              refine ⟨21174865023112992809935561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28233153364150657079914081 21174865023112992809935561)
              ·
                refine ⟨15881148767334744607451671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21174865023112992809935561 15881148767334744607451671)
                ·
                  refine ⟨23821723151002116911177507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15881148767334744607451671 23821723151002116911177507)
                  ·
                    refine ⟨35732584726503175366766261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23821723151002116911177507 35732584726503175366766261)
                    ·
                      refine ⟨3349929818109672690634337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35732584726503175366766261 3349929818109672690634337)
                      ·
                        rfl

theorem cell23_6523965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_6523965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523965 prefixEnd_6523965 := by exact prefixLift 6523965
  have htrace : WordTrace (prefixWord ++ tailWord_6523965) baseStart_6523965 baseEnd_6523965 := by
    simpa [prefixWord, tailWord_6523965, baseEnd_6523965] using wordTrace_append hprefix tailTrace_6523965
  have hstable : (prefixWord ++ tailWord_6523965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523965).length < 2 ^ (prefixWord ++ tailWord_6523965).sum := by decide
  have hdescent : baseEnd_6523965 < baseStart_6523965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523968 : List Nat := [2, 1, 1, 2, 2, 3, 4, 8]
def baseStart_6523968 : Nat := 118140960795 + 6523968 * 2 ^ 59
def prefixEnd_6523968 : Nat := 4983230072969 + 3 ^ 40 * 6523968 * 2
def baseEnd_6523968 : Nat := 124071531798208747366549

theorem tailTrace_6523968 : CollatzResearch.WordTrace tailWord_6523968 prefixEnd_6523968 124071531798208747366549 := by
  unfold tailWord_6523968
  simp only [CollatzResearch.WordTrace]
  refine ⟨118974330614392807936558279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158632440819190410582077705 118974330614392807936558279)
  ·
    refine ⟨178461495921589211904837419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118974330614392807936558279 178461495921589211904837419)
    ·
      refine ⟨267692243882383817857256129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178461495921589211904837419 267692243882383817857256129)
      ·
        refine ⟨200769182911787863392942097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267692243882383817857256129 200769182911787863392942097)
        ·
          refine ⟨150576887183840897544706573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200769182911787863392942097 150576887183840897544706573)
          ·
            refine ⟨56466332693940336579264965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150576887183840897544706573 56466332693940336579264965)
            ·
              refine ⟨10587437380113813108612181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56466332693940336579264965 10587437380113813108612181)
              ·
                refine ⟨124071531798208747366549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10587437380113813108612181 124071531798208747366549)
                ·
                  rfl

theorem cell23_6523968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 8].length) (baseStart_6523968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523968 prefixEnd_6523968 := by exact prefixLift 6523968
  have htrace : WordTrace (prefixWord ++ tailWord_6523968) baseStart_6523968 baseEnd_6523968 := by
    simpa [prefixWord, tailWord_6523968, baseEnd_6523968] using wordTrace_append hprefix tailTrace_6523968
  have hstable : (prefixWord ++ tailWord_6523968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523968).length < 2 ^ (prefixWord ++ tailWord_6523968).sum := by decide
  have hdescent : baseEnd_6523968 < baseStart_6523968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6523996 : List Nat := [2, 2, 4, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_6523996 : Nat := 118140960795 + 6523996 * 2 ^ 59
def prefixEnd_6523996 : Nat := 4983230072969 + 3 ^ 40 * 6523996 * 2
def baseEnd_6523996 : Nat := 3349945736009962069346695

theorem tailTrace_6523996 : CollatzResearch.WordTrace tailWord_6523996 prefixEnd_6523996 3349945736009962069346695 := by
  unfold tailWord_6523996
  simp only [CollatzResearch.WordTrace]
  refine ⟨118974841236342088327567921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158633121648456117770090561 118974841236342088327567921)
  ·
    refine ⟨89231130927256566245675941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118974841236342088327567921 89231130927256566245675941)
    ·
      refine ⟨16730837048860606171064239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89231130927256566245675941 16730837048860606171064239)
      ·
        refine ⟨25096255573290909256596359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16730837048860606171064239 25096255573290909256596359)
        ·
          refine ⟨37644383359936363884894539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25096255573290909256596359 37644383359936363884894539)
          ·
            refine ⟨56466575039904545827341809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37644383359936363884894539 56466575039904545827341809)
            ·
              refine ⟨42349931279928409370506357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56466575039904545827341809 42349931279928409370506357)
              ·
                refine ⟨3970306057493288378484971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42349931279928409370506357 3970306057493288378484971)
                ·
                  refine ⟨5955459086239932567727457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3970306057493288378484971 5955459086239932567727457)
                  ·
                    refine ⟨4466594314679949425795593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5955459086239932567727457 4466594314679949425795593)
                    ·
                      refine ⟨3349945736009962069346695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4466594314679949425795593 3349945736009962069346695)
                      ·
                        rfl

theorem cell23_6523996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_6523996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6523996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6523996 prefixEnd_6523996 := by exact prefixLift 6523996
  have htrace : WordTrace (prefixWord ++ tailWord_6523996) baseStart_6523996 baseEnd_6523996 := by
    simpa [prefixWord, tailWord_6523996, baseEnd_6523996] using wordTrace_append hprefix tailTrace_6523996
  have hstable : (prefixWord ++ tailWord_6523996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6523996).length < 2 ^ (prefixWord ++ tailWord_6523996).sum := by decide
  have hdescent : baseEnd_6523996 < baseStart_6523996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6523996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524013 : List Nat := [1, 5, 1, 1, 2, 2, 4, 2, 1, 2, 2]
def baseStart_6524013 : Nat := 118140960795 + 6524013 * 2 ^ 59
def prefixEnd_6524013 : Nat := 4983230072969 + 3 ^ 40 * 6524013 * 2
def baseEnd_6524013 : Nat := 3349954465181088502834117

theorem tailTrace_6524013 : CollatzResearch.WordTrace tailWord_6524013 prefixEnd_6524013 3349954465181088502834117 := by
  unfold tailWord_6524013
  simp only [CollatzResearch.WordTrace]
  refine ⟨237950302513622588558504693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158633535009081725705669795 237950302513622588558504693)
  ·
    refine ⟨22307840860652117677359815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237950302513622588558504693 22307840860652117677359815)
    ·
      refine ⟨33461761290978176516039723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22307840860652117677359815 33461761290978176516039723)
      ·
        refine ⟨50192641936467264774059585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33461761290978176516039723 50192641936467264774059585)
        ·
          refine ⟨37644481452350448580544689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50192641936467264774059585 37644481452350448580544689)
          ·
            refine ⟨28233361089262836435408517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37644481452350448580544689 28233361089262836435408517)
            ·
              refine ⟨5293755204236781831639097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28233361089262836435408517 5293755204236781831639097)
              ·
                refine ⟨3970316403177586373729323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5293755204236781831639097 3970316403177586373729323)
                ·
                  refine ⟨5955474604766379560593985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3970316403177586373729323 5955474604766379560593985)
                  ·
                    refine ⟨4466605953574784670445489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5955474604766379560593985 4466605953574784670445489)
                    ·
                      refine ⟨3349954465181088502834117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4466605953574784670445489 3349954465181088502834117)
                      ·
                        rfl

theorem cell23_6524013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_6524013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524013 prefixEnd_6524013 := by exact prefixLift 6524013
  have htrace : WordTrace (prefixWord ++ tailWord_6524013) baseStart_6524013 baseEnd_6524013 := by
    simpa [prefixWord, tailWord_6524013, baseEnd_6524013] using wordTrace_append hprefix tailTrace_6524013
  have hstable : (prefixWord ++ tailWord_6524013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524013).length < 2 ^ (prefixWord ++ tailWord_6524013).sum := by decide
  have hdescent : baseEnd_6524013 < baseStart_6524013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524030 : List Nat := [4, 2, 4, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_6524030 : Nat := 118140960795 + 6524030 * 2 ^ 59
def prefixEnd_6524030 : Nat := 4983230072969 + 3 ^ 40 * 6524030 * 2
def baseEnd_6524030 : Nat := 3349963194352214936321539

theorem tailTrace_6524030 : CollatzResearch.WordTrace tailWord_6524030 prefixEnd_6524030 3349963194352214936321539 := by
  unfold tailWord_6524030
  simp only [CollatzResearch.WordTrace]
  refine ⟨29743865319320125057734193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158633948369707333641249029 29743865319320125057734193)
  ·
    refine ⟨22307898989490093793300645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29743865319320125057734193 22307898989490093793300645)
    ·
      refine ⟨4182731060529392586243871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22307898989490093793300645 4182731060529392586243871)
      ·
        refine ⟨6274096590794088879365807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4182731060529392586243871 6274096590794088879365807)
        ·
          refine ⟨9411144886191133319048711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6274096590794088879365807 9411144886191133319048711)
          ·
            refine ⟨14116717329286699978573067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9411144886191133319048711 14116717329286699978573067)
            ·
              refine ⟨21175075993930049967859601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14116717329286699978573067 21175075993930049967859601)
              ·
                refine ⟨15881306995447537475894701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21175075993930049967859601 15881306995447537475894701)
                ·
                  refine ⟨5955490123292826553460513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15881306995447537475894701 5955490123292826553460513)
                  ·
                    refine ⟨4466617592469619915095385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5955490123292826553460513 4466617592469619915095385)
                    ·
                      refine ⟨3349963194352214936321539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4466617592469619915095385 3349963194352214936321539)
                      ·
                        rfl

theorem cell23_6524030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_6524030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524030 prefixEnd_6524030 := by exact prefixLift 6524030
  have htrace : WordTrace (prefixWord ++ tailWord_6524030) baseStart_6524030 baseEnd_6524030 := by
    simpa [prefixWord, tailWord_6524030, baseEnd_6524030] using wordTrace_append hprefix tailTrace_6524030
  have hstable : (prefixWord ++ tailWord_6524030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524030).length < 2 ^ (prefixWord ++ tailWord_6524030).sum := by decide
  have hdescent : baseEnd_6524030 < baseStart_6524030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524056 : List Nat := [2, 1, 2, 4, 2, 1, 4, 1, 1, 3, 2]
def baseStart_6524056 : Nat := 118140960795 + 6524056 * 2 ^ 59
def prefixEnd_6524056 : Nat := 4983230072969 + 3 ^ 40 * 6524056 * 2
def baseEnd_6524056 : Nat := 3349976544849231834596419

theorem tailTrace_6524056 : CollatzResearch.WordTrace tailWord_6524056 prefixEnd_6524056 3349976544849231834596419 := by
  unfold tailWord_6524056
  simp only [CollatzResearch.WordTrace]
  refine ⟨118975935426233403451160011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158634580568311204601546681 118975935426233403451160011)
  ·
    refine ⟨178463903139350105176740017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118975935426233403451160011 178463903139350105176740017)
    ·
      refine ⟨133847927354512578882555013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178463903139350105176740017 133847927354512578882555013)
      ·
        refine ⟨25096486378971108540479065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133847927354512578882555013 25096486378971108540479065)
        ·
          refine ⟨18822364784228331405359299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25096486378971108540479065 18822364784228331405359299)
          ·
            refine ⟨28233547176342497108038949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18822364784228331405359299 28233547176342497108038949)
            ·
              refine ⟨5293790095564218207757303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28233547176342497108038949 5293790095564218207757303)
              ·
                refine ⟨7940685143346327311635955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5293790095564218207757303 7940685143346327311635955)
                ·
                  refine ⟨11911027715019490967453933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7940685143346327311635955 11911027715019490967453933)
                  ·
                    refine ⟨4466635393132309112795225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11911027715019490967453933 4466635393132309112795225)
                    ·
                      refine ⟨3349976544849231834596419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4466635393132309112795225 3349976544849231834596419)
                      ·
                        rfl

theorem cell23_6524056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_6524056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524056 prefixEnd_6524056 := by exact prefixLift 6524056
  have htrace : WordTrace (prefixWord ++ tailWord_6524056) baseStart_6524056 baseEnd_6524056 := by
    simpa [prefixWord, tailWord_6524056, baseEnd_6524056] using wordTrace_append hprefix tailTrace_6524056
  have hstable : (prefixWord ++ tailWord_6524056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524056).length < 2 ^ (prefixWord ++ tailWord_6524056).sum := by decide
  have hdescent : baseEnd_6524056 < baseStart_6524056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524062 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_6524062 : Nat := 118140960795 + 6524062 * 2 ^ 59
def prefixEnd_6524062 : Nat := 4983230072969 + 3 ^ 40 * 6524062 * 2
def baseEnd_6524062 : Nat := 1116659875244386270373797

theorem tailTrace_6524062 : CollatzResearch.WordTrace tailWord_6524062 prefixEnd_6524062 1116659875244386270373797 := by
  unfold tailWord_6524062
  simp only [CollatzResearch.WordTrace]
  refine ⟨29744011211305633740879805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158634726460296713284692293 29744011211305633740879805)
  ·
    refine ⟨11154004204239612652829927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29744011211305633740879805 11154004204239612652829927)
    ·
      refine ⟨16731006306359418979244891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11154004204239612652829927 16731006306359418979244891)
      ·
        refine ⟨25096509459539128468867337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16731006306359418979244891 25096509459539128468867337)
        ·
          refine ⟨18822382094654346351650503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25096509459539128468867337 18822382094654346351650503)
          ·
            refine ⟨28233573141981519527475755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18822382094654346351650503 28233573141981519527475755)
            ·
              refine ⟨42350359712972279291213633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28233573141981519527475755 42350359712972279291213633)
              ·
                refine ⟨31762769784729209468410225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42350359712972279291213633 31762769784729209468410225)
                ·
                  refine ⟨23822077338546907101307669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31762769784729209468410225 23822077338546907101307669)
                  ·
                    refine ⟨1116659875244386270373797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23822077338546907101307669 1116659875244386270373797)
                    ·
                      rfl

theorem cell23_6524062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_6524062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524062 prefixEnd_6524062 := by exact prefixLift 6524062
  have htrace : WordTrace (prefixWord ++ tailWord_6524062) baseStart_6524062 baseEnd_6524062 := by
    simpa [prefixWord, tailWord_6524062, baseEnd_6524062] using wordTrace_append hprefix tailTrace_6524062
  have hstable : (prefixWord ++ tailWord_6524062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524062).length < 2 ^ (prefixWord ++ tailWord_6524062).sum := by decide
  have hdescent : baseEnd_6524062 < baseStart_6524062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524063 : List Nat := [1, 1, 2, 6, 3, 1, 1, 2, 2, 1, 3]
def baseStart_6524063 : Nat := 118140960795 + 6524063 * 2 ^ 59
def prefixEnd_6524063 : Nat := 4983230072969 + 3 ^ 40 * 6524063 * 2
def baseEnd_6524063 : Nat := 3349980139213813307208887

theorem tailTrace_6524063 : CollatzResearch.WordTrace tailWord_6524063 prefixEnd_6524063 3349980139213813307208887 := by
  unfold tailWord_6524063
  simp only [CollatzResearch.WordTrace]
  refine ⟨237952126163441447097824843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158634750775627631398549895 237952126163441447097824843)
  ·
    refine ⟨356928189245162170646737265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237952126163441447097824843 356928189245162170646737265)
    ·
      refine ⟨267696141933871627985052949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356928189245162170646737265 267696141933871627985052949)
      ·
        refine ⟨12548256653150232561799357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 267696141933871627985052949 12548256653150232561799357)
        ·
          refine ⟨4705596244931337210674759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12548256653150232561799357 4705596244931337210674759)
          ·
            refine ⟨7058394367397005816012139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4705596244931337210674759 7058394367397005816012139)
            ·
              refine ⟨10587591551095508724018209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7058394367397005816012139 10587591551095508724018209)
              ·
                refine ⟨7940693663321631543013657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10587591551095508724018209 7940693663321631543013657)
                ·
                  refine ⟨5955520247491223657260243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7940693663321631543013657 5955520247491223657260243)
                  ·
                    refine ⟨8933280371236835485890365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5955520247491223657260243 8933280371236835485890365)
                    ·
                      refine ⟨3349980139213813307208887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8933280371236835485890365 3349980139213813307208887)
                      ·
                        rfl

theorem cell23_6524063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_6524063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524063 prefixEnd_6524063 := by exact prefixLift 6524063
  have htrace : WordTrace (prefixWord ++ tailWord_6524063) baseStart_6524063 baseEnd_6524063 := by
    simpa [prefixWord, tailWord_6524063, baseEnd_6524063] using wordTrace_append hprefix tailTrace_6524063
  have hstable : (prefixWord ++ tailWord_6524063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524063).length < 2 ^ (prefixWord ++ tailWord_6524063).sum := by decide
  have hdescent : baseEnd_6524063 < baseStart_6524063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524065 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_6524065 : Nat := 118140960795 + 6524065 * 2 ^ 59
def prefixEnd_6524065 : Nat := 4983230072969 + 3 ^ 40 * 6524065 * 2
def baseEnd_6524065 : Nat := 3349981166175122299383877

theorem tailTrace_6524065 : CollatzResearch.WordTrace tailWord_6524065 prefixEnd_6524065 3349981166175122299383877 := by
  unfold tailWord_6524065
  simp only [CollatzResearch.WordTrace]
  refine ⟨237952199109434201439397649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158634799406289467626265099 237952199109434201439397649)
  ·
    refine ⟨178464149332075651079548237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237952199109434201439397649 178464149332075651079548237)
    ·
      refine ⟨66924055999528369154830589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178464149332075651079548237 66924055999528369154830589)
      ·
        refine ⟨25096520999823138433061471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66924055999528369154830589 25096520999823138433061471)
        ·
          refine ⟨37644781499734707649592207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25096520999823138433061471 37644781499734707649592207)
          ·
            refine ⟨56467172249602061474388311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37644781499734707649592207 56467172249602061474388311)
            ·
              refine ⟨84700758374403092211582467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56467172249602061474388311 84700758374403092211582467)
              ·
                refine ⟨127051137561604638317373701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84700758374403092211582467 127051137561604638317373701)
                ·
                  refine ⟨23822088292800869684507569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127051137561604638317373701 23822088292800869684507569)
                  ·
                    refine ⟨17866566219600652263380677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23822088292800869684507569 17866566219600652263380677)
                    ·
                      refine ⟨3349981166175122299383877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17866566219600652263380677 3349981166175122299383877)
                      ·
                        rfl

theorem cell23_6524065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_6524065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524065 prefixEnd_6524065 := by exact prefixLift 6524065
  have htrace : WordTrace (prefixWord ++ tailWord_6524065) baseStart_6524065 baseEnd_6524065 := by
    simpa [prefixWord, tailWord_6524065, baseEnd_6524065] using wordTrace_append hprefix tailTrace_6524065
  have hstable : (prefixWord ++ tailWord_6524065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524065).length < 2 ^ (prefixWord ++ tailWord_6524065).sum := by decide
  have hdescent : baseEnd_6524065 < baseStart_6524065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524069 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 4, 2, 2]
def baseStart_6524069 : Nat := 118140960795 + 6524069 * 2 ^ 59
def prefixEnd_6524069 : Nat := 4983230072969 + 3 ^ 40 * 6524069 * 2
def baseEnd_6524069 : Nat := 3349983220097740283733859

theorem tailTrace_6524069 : CollatzResearch.WordTrace tailWord_6524069 prefixEnd_6524069 3349983220097740283733859 := by
  unfold tailWord_6524069
  simp only [CollatzResearch.WordTrace]
  refine ⟨237952345001419710122543261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158634896667613140081695507 237952345001419710122543261)
  ·
    refine ⟨89232129375532391295953723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237952345001419710122543261 89232129375532391295953723)
    ·
      refine ⟨133848194063298586943930585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89232129375532391295953723 133848194063298586943930585)
      ·
        refine ⟨100386145547473940207947939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133848194063298586943930585 100386145547473940207947939)
        ·
          refine ⟨150579218321210910311921909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100386145547473940207947939 150579218321210910311921909)
          ·
            refine ⟨14116801717613522841742679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150579218321210910311921909 14116801717613522841742679)
            ·
              refine ⟨21175202576420284262614019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14116801717613522841742679 21175202576420284262614019)
              ·
                refine ⟨31762803864630426393921029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21175202576420284262614019 31762803864630426393921029)
                ·
                  refine ⟨5955525724618204948860193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31762803864630426393921029 5955525724618204948860193)
                  ·
                    refine ⟨4466644293463653711645145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5955525724618204948860193 4466644293463653711645145)
                    ·
                      refine ⟨3349983220097740283733859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4466644293463653711645145 3349983220097740283733859)
                      ·
                        rfl

theorem cell23_6524069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_6524069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524069 prefixEnd_6524069 := by exact prefixLift 6524069
  have htrace : WordTrace (prefixWord ++ tailWord_6524069) baseStart_6524069 baseEnd_6524069 := by
    simpa [prefixWord, tailWord_6524069, baseEnd_6524069] using wordTrace_append hprefix tailTrace_6524069
  have hstable : (prefixWord ++ tailWord_6524069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524069).length < 2 ^ (prefixWord ++ tailWord_6524069).sum := by decide
  have hdescent : baseEnd_6524069 < baseStart_6524069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524169 : List Nat := [1, 2, 1, 1, 3, 3, 2, 5, 1, 4]
def baseStart_6524169 : Nat := 118140960795 + 6524169 * 2 ^ 59
def prefixEnd_6524169 : Nat := 4983230072969 + 3 ^ 40 * 6524169 * 2
def baseEnd_6524169 : Nat := 1116678189387729964161133

theorem tailTrace_6524169 : CollatzResearch.WordTrace tailWord_6524169 prefixEnd_6524169 1116678189387729964161133 := by
  unfold tailWord_6524169
  simp only [CollatzResearch.WordTrace]
  refine ⟨237955992301057427201183561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158637328200704951467455707 237955992301057427201183561)
  ·
    refine ⟨178466994225793070400887671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237955992301057427201183561 178466994225793070400887671)
    ·
      refine ⟨267700491338689605601331507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178466994225793070400887671 267700491338689605601331507)
      ·
        refine ⟨401550737008034408401997261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267700491338689605601331507 401550737008034408401997261)
        ·
          refine ⟨150581526378012903150748973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401550737008034408401997261 150581526378012903150748973)
          ·
            refine ⟨56468072391754838681530865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150581526378012903150748973 56468072391754838681530865)
            ·
              refine ⟨42351054293816129011148149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56468072391754838681530865 42351054293816129011148149)
              ·
                refine ⟨3970411340045262094795139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42351054293816129011148149 3970411340045262094795139)
                ·
                  refine ⟨5955617010067893142192709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3970411340045262094795139 5955617010067893142192709)
                  ·
                    refine ⟨1116678189387729964161133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5955617010067893142192709 1116678189387729964161133)
                    ·
                      rfl

theorem cell23_6524169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 1, 4].length) (baseStart_6524169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524169 prefixEnd_6524169 := by exact prefixLift 6524169
  have htrace : WordTrace (prefixWord ++ tailWord_6524169) baseStart_6524169 baseEnd_6524169 := by
    simpa [prefixWord, tailWord_6524169, baseEnd_6524169] using wordTrace_append hprefix tailTrace_6524169
  have hstable : (prefixWord ++ tailWord_6524169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524169).length < 2 ^ (prefixWord ++ tailWord_6524169).sum := by decide
  have hdescent : baseEnd_6524169 < baseStart_6524169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524186 : List Nat := [3, 1, 1, 3, 3, 2, 1, 4, 1, 4]
def baseStart_6524186 : Nat := 118140960795 + 6524186 * 2 ^ 59
def prefixEnd_6524186 : Nat := 4983230072969 + 3 ^ 40 * 6524186 * 2
def baseEnd_6524186 : Nat := 1116681099111438775323607

theorem tailTrace_6524186 : CollatzResearch.WordTrace tailWord_6524186 prefixEnd_6524186 1116681099111438775323607 := by
  unfold tailWord_6524186
  simp only [CollatzResearch.WordTrace]
  refine ⟨59489153085498959776138103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158637741561330559403034941 59489153085498959776138103)
  ·
    refine ⟨89233729628248439664207155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59489153085498959776138103 89233729628248439664207155)
    ·
      refine ⟨133850594442372659496310733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89233729628248439664207155 133850594442372659496310733)
      ·
        refine ⟨50193972915889747311116525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133850594442372659496310733 50193972915889747311116525)
        ·
          refine ⟨18822739843458655241668697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50193972915889747311116525 18822739843458655241668697)
          ·
            refine ⟨14117054882593991431251523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18822739843458655241668697 14117054882593991431251523)
            ·
              refine ⟨21175582323890987146877285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14117054882593991431251523 21175582323890987146877285)
              ·
                refine ⟨3970421685729560090039491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21175582323890987146877285 3970421685729560090039491)
                ·
                  refine ⟨5955632528594340135059237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3970421685729560090039491 5955632528594340135059237)
                  ·
                    refine ⟨1116681099111438775323607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5955632528594340135059237 1116681099111438775323607)
                    ·
                      rfl

theorem cell23_6524186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 1, 4].length) (baseStart_6524186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524186 prefixEnd_6524186 := by exact prefixLift 6524186
  have htrace : WordTrace (prefixWord ++ tailWord_6524186) baseStart_6524186 baseEnd_6524186 := by
    simpa [prefixWord, tailWord_6524186, baseEnd_6524186] using wordTrace_append hprefix tailTrace_6524186
  have hstable : (prefixWord ++ tailWord_6524186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524186).length < 2 ^ (prefixWord ++ tailWord_6524186).sum := by decide
  have hdescent : baseEnd_6524186 < baseStart_6524186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524209 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 5, 1, 3]
def baseStart_6524209 : Nat := 118140960795 + 6524209 * 2 ^ 59
def prefixEnd_6524209 : Nat := 4983230072969 + 3 ^ 40 * 6524209 * 2
def baseEnd_6524209 : Nat := 3350055107389369735983215

theorem tailTrace_6524209 : CollatzResearch.WordTrace tailWord_6524209 prefixEnd_6524209 3350055107389369735983215 := by
  unfold tailWord_6524209
  simp only [CollatzResearch.WordTrace]
  refine ⟨237957451220912514032639681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158638300813941676021759787 237957451220912514032639681)
  ·
    refine ⟨178468088415684385524479761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237957451220912514032639681 178468088415684385524479761)
    ·
      refine ⟨133851066311763289143359821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178468088415684385524479761 133851066311763289143359821)
      ·
        refine ⟨50194149866911233428759933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133851066311763289143359821 50194149866911233428759933)
        ·
          refine ⟨18822806200091712535784975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50194149866911233428759933 18822806200091712535784975)
          ·
            refine ⟨28234209300137568803677463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18822806200091712535784975 28234209300137568803677463)
            ·
              refine ⟨42351313950206353205516195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28234209300137568803677463 42351313950206353205516195)
              ·
                refine ⟨63526970925309529808274293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42351313950206353205516195 63526970925309529808274293)
                ·
                  refine ⟨5955653524247768419525715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63526970925309529808274293 5955653524247768419525715)
                  ·
                    refine ⟨8933480286371652629288573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5955653524247768419525715 8933480286371652629288573)
                    ·
                      refine ⟨3350055107389369735983215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8933480286371652629288573 3350055107389369735983215)
                      ·
                        rfl

theorem cell23_6524209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_6524209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524209 prefixEnd_6524209 := by exact prefixLift 6524209
  have htrace : WordTrace (prefixWord ++ tailWord_6524209) baseStart_6524209 baseEnd_6524209 := by
    simpa [prefixWord, tailWord_6524209, baseEnd_6524209] using wordTrace_append hprefix tailTrace_6524209
  have hstable : (prefixWord ++ tailWord_6524209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524209).length < 2 ^ (prefixWord ++ tailWord_6524209).sum := by decide
  have hdescent : baseEnd_6524209 < baseStart_6524209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524255 : List Nat := [1, 1, 2, 3, 1, 2, 1, 12]
def baseStart_6524255 : Nat := 118140960795 + 6524255 * 2 ^ 59
def prefixEnd_6524255 : Nat := 4983230072969 + 3 ^ 40 * 6524255 * 2
def baseEnd_6524255 : Nat := 124076989907388020592889

theorem tailTrace_6524255 : CollatzResearch.WordTrace tailWord_6524255 prefixEnd_6524255 124076989907388020592889 := by
  unfold tailWord_6524255
  simp only [CollatzResearch.WordTrace]
  refine ⟨237959128978745863888814219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158639419319163909259209479 237959128978745863888814219)
  ·
    refine ⟨356938693468118795833221329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237959128978745863888814219 356938693468118795833221329)
    ·
      refine ⟨267704020101089096874915997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356938693468118795833221329 267704020101089096874915997)
      ·
        refine ⟨100389007537908411328093499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267704020101089096874915997 100389007537908411328093499)
        ·
          refine ⟨150583511306862616992140249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100389007537908411328093499 150583511306862616992140249)
          ·
            refine ⟨112937633480146962744105187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150583511306862616992140249 112937633480146962744105187)
            ·
              refine ⟨169406450220220444116157781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112937633480146962744105187 169406450220220444116157781)
              ·
                refine ⟨124076989907388020592889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 169406450220220444116157781 124076989907388020592889)
                ·
                  rfl

theorem cell23_6524255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 12].length) (baseStart_6524255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524255 prefixEnd_6524255 := by exact prefixLift 6524255
  have htrace : WordTrace (prefixWord ++ tailWord_6524255) baseStart_6524255 baseEnd_6524255 := by
    simpa [prefixWord, tailWord_6524255, baseEnd_6524255] using wordTrace_append hprefix tailTrace_6524255
  have hstable : (prefixWord ++ tailWord_6524255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524255).length < 2 ^ (prefixWord ++ tailWord_6524255).sum := by decide
  have hdescent : baseEnd_6524255 < baseStart_6524255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524259 : List Nat := [1, 1, 1, 5, 2, 4, 1, 1, 1, 6]
def baseStart_6524259 : Nat := 118140960795 + 6524259 * 2 ^ 59
def prefixEnd_6524259 : Nat := 4983230072969 + 3 ^ 40 * 6524259 * 2
def baseEnd_6524259 : Nat := 1116693593807364846785995

theorem tailTrace_6524259 : CollatzResearch.WordTrace tailWord_6524259 prefixEnd_6524259 1116693593807364846785995 := by
  unfold tailWord_6524259
  simp only [CollatzResearch.WordTrace]
  refine ⟨237959274870731372571959831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158639516580487581714639887 237959274870731372571959831)
  ·
    refine ⟨356938912306097058857939747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237959274870731372571959831 356938912306097058857939747)
    ·
      refine ⟨535408368459145588286909621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356938912306097058857939747 535408368459145588286909621)
      ·
        refine ⟨50194534543044898901897777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 535408368459145588286909621 50194534543044898901897777)
        ·
          refine ⟨37645900907283674176423333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50194534543044898901897777 37645900907283674176423333)
          ·
            refine ⟨7058606420115688908079375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37645900907283674176423333 7058606420115688908079375)
            ·
              refine ⟨10587909630173533362119063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7058606420115688908079375 10587909630173533362119063)
              ·
                refine ⟨15881864445260300043178595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10587909630173533362119063 15881864445260300043178595)
                ·
                  refine ⟨23822796667890450064767893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15881864445260300043178595 23822796667890450064767893)
                  ·
                    refine ⟨1116693593807364846785995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23822796667890450064767893 1116693593807364846785995)
                    ·
                      rfl

theorem cell23_6524259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 6].length) (baseStart_6524259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524259 prefixEnd_6524259 := by exact prefixLift 6524259
  have htrace : WordTrace (prefixWord ++ tailWord_6524259) baseStart_6524259 baseEnd_6524259 := by
    simpa [prefixWord, tailWord_6524259, baseEnd_6524259] using wordTrace_append hprefix tailTrace_6524259
  have hstable : (prefixWord ++ tailWord_6524259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524259).length < 2 ^ (prefixWord ++ tailWord_6524259).sum := by decide
  have hdescent : baseEnd_6524259 < baseStart_6524259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524277 : List Nat := [1, 3, 4, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_6524277 : Nat := 118140960795 + 6524277 * 2 ^ 59
def prefixEnd_6524277 : Nat := 4983230072969 + 3 ^ 40 * 6524277 * 2
def baseEnd_6524277 : Nat := 3350090024073875469932903

theorem tailTrace_6524277 : CollatzResearch.WordTrace tailWord_6524277 prefixEnd_6524277 3350090024073875469932903 := by
  unfold tailWord_6524277
  simp only [CollatzResearch.WordTrace]
  refine ⟨237959931384666161646115085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158639954256444107764076723 237959931384666161646115085)
  ·
    refine ⟨89234974269249810617293157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237959931384666161646115085 89234974269249810617293157)
    ·
      refine ⟨16731557675484339490742467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89234974269249810617293157 16731557675484339490742467)
      ·
        refine ⟨25097336513226509236113701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16731557675484339490742467 25097336513226509236113701)
        ·
          refine ⟨4705750596229970481771319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25097336513226509236113701 4705750596229970481771319)
          ·
            refine ⟨7058625894344955722656979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4705750596229970481771319 7058625894344955722656979)
            ·
              refine ⟨10587938841517433583985469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7058625894344955722656979 10587938841517433583985469)
              ·
                refine ⟨3970477065569037593994551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10587938841517433583985469 3970477065569037593994551)
                ·
                  refine ⟨5955715598353556390991827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3970477065569037593994551 5955715598353556390991827)
                  ·
                    refine ⟨8933573397530334586487741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5955715598353556390991827 8933573397530334586487741)
                    ·
                      refine ⟨3350090024073875469932903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8933573397530334586487741 3350090024073875469932903)
                      ·
                        rfl

theorem cell23_6524277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_6524277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524277 prefixEnd_6524277 := by exact prefixLift 6524277
  have htrace : WordTrace (prefixWord ++ tailWord_6524277) baseStart_6524277 baseEnd_6524277 := by
    simpa [prefixWord, tailWord_6524277, baseEnd_6524277] using wordTrace_append hprefix tailTrace_6524277
  have hstable : (prefixWord ++ tailWord_6524277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524277).length < 2 ^ (prefixWord ++ tailWord_6524277).sum := by decide
  have hdescent : baseEnd_6524277 < baseStart_6524277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524289 : List Nat := [1, 2, 4, 3, 2, 2, 9]
def baseStart_6524289 : Nat := 118140960795 + 6524289 * 2 ^ 59
def prefixEnd_6524289 : Nat := 4983230072969 + 3 ^ 40 * 6524289 * 2
def baseEnd_6524289 : Nat := 41359212170885548431887

theorem tailTrace_6524289 : CollatzResearch.WordTrace tailWord_6524289 prefixEnd_6524289 41359212170885548431887 := by
  unfold tailWord_6524289
  simp only [CollatzResearch.WordTrace]
  refine ⟨237960369060622687695551921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158640246040415125130367947 237960369060622687695551921)
  ·
    refine ⟨178470276795467015771663941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237960369060622687695551921 178470276795467015771663941)
    ·
      refine ⟨33463176899150065457186989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178470276795467015771663941 33463176899150065457186989)
      ·
        refine ⟨12548691337181274546445121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33463176899150065457186989 12548691337181274546445121)
        ·
          refine ⟨9411518502885955909833841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12548691337181274546445121 9411518502885955909833841)
          ·
            refine ⟨7058638877164466932375381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9411518502885955909833841 7058638877164466932375381)
            ·
              refine ⟨41359212170885548431887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7058638877164466932375381 41359212170885548431887)
              ·
                rfl

theorem cell23_6524289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 9].length) (baseStart_6524289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524289 prefixEnd_6524289 := by exact prefixLift 6524289
  have htrace : WordTrace (prefixWord ++ tailWord_6524289) baseStart_6524289 baseEnd_6524289 := by
    simpa [prefixWord, tailWord_6524289, baseEnd_6524289] using wordTrace_append hprefix tailTrace_6524289
  have hstable : (prefixWord ++ tailWord_6524289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524289).length < 2 ^ (prefixWord ++ tailWord_6524289).sum := by decide
  have hdescent : baseEnd_6524289 < baseStart_6524289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524299 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 4, 1, 3]
def baseStart_6524299 : Nat := 118140960795 + 6524299 * 2 ^ 59
def prefixEnd_6524299 : Nat := 4983230072969 + 3 ^ 40 * 6524299 * 2
def baseEnd_6524299 : Nat := 3350101320648274383857801

theorem tailTrace_6524299 : CollatzResearch.WordTrace tailWord_6524299 prefixEnd_6524299 3350101320648274383857801 := by
  unfold tailWord_6524299
  simp only [CollatzResearch.WordTrace]
  refine ⟨237960733790586459403415951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158640489193724306268943967 237960733790586459403415951)
  ·
    refine ⟨356941100685879689105123927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237960733790586459403415951 356941100685879689105123927)
    ·
      refine ⟨535411651028819533657685891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356941100685879689105123927 535411651028819533657685891)
      ·
        refine ⟨803117476543229300486528837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535411651028819533657685891 803117476543229300486528837)
        ·
          refine ⟨150584526851855493841224157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 803117476543229300486528837 150584526851855493841224157)
          ·
            refine ⟨56469197569445810190459059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150584526851855493841224157 56469197569445810190459059)
            ·
              refine ⟨84703796354168715285688589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56469197569445810190459059 84703796354168715285688589)
              ·
                refine ⟨31763923632813268232133221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84703796354168715285688589 31763923632813268232133221)
                ·
                  refine ⟨5955735681152487793524979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31763923632813268232133221 5955735681152487793524979)
                  ·
                    refine ⟨8933603521728731690287469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5955735681152487793524979 8933603521728731690287469)
                    ·
                      refine ⟨3350101320648274383857801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8933603521728731690287469 3350101320648274383857801)
                      ·
                        rfl

theorem cell23_6524299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 1, 3].length) (baseStart_6524299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524299 prefixEnd_6524299 := by exact prefixLift 6524299
  have htrace : WordTrace (prefixWord ++ tailWord_6524299) baseStart_6524299 baseEnd_6524299 := by
    simpa [prefixWord, tailWord_6524299, baseEnd_6524299] using wordTrace_append hprefix tailTrace_6524299
  have hstable : (prefixWord ++ tailWord_6524299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524299).length < 2 ^ (prefixWord ++ tailWord_6524299).sum := by decide
  have hdescent : baseEnd_6524299 < baseStart_6524299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524300 : List Nat := [2, 2, 1, 2, 1, 3, 5, 2, 1, 2, 2]
def baseStart_6524300 : Nat := 118140960795 + 6524300 * 2 ^ 59
def prefixEnd_6524300 : Nat := 4983230072969 + 3 ^ 40 * 6524300 * 2
def baseEnd_6524300 : Nat := 3350101834128928879945297

theorem tailTrace_6524300 : CollatzResearch.WordTrace tailWord_6524300 prefixEnd_6524300 3350101834128928879945297 := by
  unfold tailWord_6524300
  simp only [CollatzResearch.WordTrace]
  refine ⟨118980385131791418287101177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158640513509055224382801569 118980385131791418287101177)
  ·
    refine ⟨89235288848843563715325883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118980385131791418287101177 89235288848843563715325883)
    ·
      refine ⟨133852933273265345572988825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89235288848843563715325883 133852933273265345572988825)
      ·
        refine ⟨100389699954949009179741619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133852933273265345572988825 100389699954949009179741619)
        ·
          refine ⟨150584549932423513769612429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100389699954949009179741619 150584549932423513769612429)
          ·
            refine ⟨56469206224658817663604661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150584549932423513769612429 56469206224658817663604661)
            ·
              refine ⟨5293988083561764155962937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56469206224658817663604661 5293988083561764155962937)
              ·
                refine ⟨3970491062671323116972203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5293988083561764155962937 3970491062671323116972203)
                ·
                  refine ⟨5955736594006984675458305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3970491062671323116972203 5955736594006984675458305)
                  ·
                    refine ⟨4466802445505238506593729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5955736594006984675458305 4466802445505238506593729)
                    ·
                      refine ⟨3350101834128928879945297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4466802445505238506593729 3350101834128928879945297)
                      ·
                        rfl

theorem cell23_6524300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 1, 2, 2].length) (baseStart_6524300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524300 prefixEnd_6524300 := by exact prefixLift 6524300
  have htrace : WordTrace (prefixWord ++ tailWord_6524300) baseStart_6524300 baseEnd_6524300 := by
    simpa [prefixWord, tailWord_6524300, baseEnd_6524300] using wordTrace_append hprefix tailTrace_6524300
  have hstable : (prefixWord ++ tailWord_6524300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524300).length < 2 ^ (prefixWord ++ tailWord_6524300).sum := by decide
  have hdescent : baseEnd_6524300 < baseStart_6524300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524306 : List Nat := [3, 2, 3, 3, 1, 1, 2, 8]
def baseStart_6524306 : Nat := 118140960795 + 6524306 * 2 ^ 59
def prefixEnd_6524306 : Nat := 4983230072969 + 3 ^ 40 * 6524306 * 2
def baseEnd_6524306 : Nat := 124077959815290957647047

theorem tailTrace_6524306 : CollatzResearch.WordTrace tailWord_6524306 prefixEnd_6524306 124077959815290957647047 := by
  unfold tailWord_6524306
  simp only [CollatzResearch.WordTrace]
  refine ⟨59490247275390274899730193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158640659401040733065947181 59490247275390274899730193)
  ·
    refine ⟨44617685456542706174797645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59490247275390274899730193 44617685456542706174797645)
    ·
      refine ⟨16731632046203514815549117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44617685456542706174797645 16731632046203514815549117)
      ·
        refine ⟨6274362017326318055830919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16731632046203514815549117 6274362017326318055830919)
        ·
          refine ⟨9411543025989477083746379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6274362017326318055830919 9411543025989477083746379)
          ·
            refine ⟨14117314538984215625619569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9411543025989477083746379 14117314538984215625619569)
            ·
              refine ⟨10587985904238161719214677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14117314538984215625619569 10587985904238161719214677)
              ·
                refine ⟨124077959815290957647047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10587985904238161719214677 124077959815290957647047)
                ·
                  rfl

theorem cell23_6524306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 8].length) (baseStart_6524306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524306 prefixEnd_6524306 := by exact prefixLift 6524306
  have htrace : WordTrace (prefixWord ++ tailWord_6524306) baseStart_6524306 baseEnd_6524306 := by
    simpa [prefixWord, tailWord_6524306, baseEnd_6524306] using wordTrace_append hprefix tailTrace_6524306
  have hstable : (prefixWord ++ tailWord_6524306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524306).length < 2 ^ (prefixWord ++ tailWord_6524306).sum := by decide
  have hdescent : baseEnd_6524306 < baseStart_6524306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524343 : List Nat := [1, 1, 3, 1, 3, 2, 5, 1, 1, 3, 2]
def baseStart_6524343 : Nat := 118140960795 + 6524343 * 2 ^ 59
def prefixEnd_6524343 : Nat := 4983230072969 + 3 ^ 40 * 6524343 * 2
def baseEnd_6524343 : Nat := 3350123913797072211707599

theorem tailTrace_6524343 : CollatzResearch.WordTrace tailWord_6524343 prefixEnd_6524343 3350123913797072211707599 := by
  unfold tailWord_6524343
  simp only [CollatzResearch.WordTrace]
  refine ⟨237962338602427054918017683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158641559068284703278678455 237962338602427054918017683)
  ·
    refine ⟨356943507903640582377026525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237962338602427054918017683 356943507903640582377026525)
    ·
      refine ⟨133853815463865218391384947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356943507903640582377026525 133853815463865218391384947)
      ·
        refine ⟨200780723195797827587077421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133853815463865218391384947 200780723195797827587077421)
        ·
          refine ⟨75292771198424185345154033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200780723195797827587077421 75292771198424185345154033)
          ·
            refine ⟨56469578398818139008865525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75292771198424185345154033 56469578398818139008865525)
            ·
              refine ⟨5294022974889200532081143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56469578398818139008865525 5294022974889200532081143)
              ·
                refine ⟨7941034462333800798121715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5294022974889200532081143 7941034462333800798121715)
                ·
                  refine ⟨11911551693500701197182573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7941034462333800798121715 11911551693500701197182573)
                  ·
                    refine ⟨4466831885062762948943465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11911551693500701197182573 4466831885062762948943465)
                    ·
                      refine ⟨3350123913797072211707599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4466831885062762948943465 3350123913797072211707599)
                      ·
                        rfl

theorem cell23_6524343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 1, 3, 2].length) (baseStart_6524343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524343 prefixEnd_6524343 := by exact prefixLift 6524343
  have htrace : WordTrace (prefixWord ++ tailWord_6524343) baseStart_6524343 baseEnd_6524343 := by
    simpa [prefixWord, tailWord_6524343, baseEnd_6524343] using wordTrace_append hprefix tailTrace_6524343
  have hstable : (prefixWord ++ tailWord_6524343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524343).length < 2 ^ (prefixWord ++ tailWord_6524343).sum := by decide
  have hdescent : baseEnd_6524343 < baseStart_6524343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524373 : List Nat := [1, 3, 2, 3, 1, 1, 1, 5, 2, 2, 2]
def baseStart_6524373 : Nat := 118140960795 + 6524373 * 2 ^ 59
def prefixEnd_6524373 : Nat := 4983230072969 + 3 ^ 40 * 6524373 * 2
def baseEnd_6524373 : Nat := 3350139318216707094332461

theorem tailTrace_6524373 : CollatzResearch.WordTrace tailWord_6524373 prefixEnd_6524373 3350139318216707094332461 := by
  unfold tailWord_6524373
  simp only [CollatzResearch.WordTrace]
  refine ⟨237963432792318370041609773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158642288528212246694406515 237963432792318370041609773)
  ·
    refine ⟨89236287297119388765603665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237963432792318370041609773 89236287297119388765603665)
    ·
      refine ⟨66927215472839541574202749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89236287297119388765603665 66927215472839541574202749)
      ·
        refine ⟨25097705802314828090326031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66927215472839541574202749 25097705802314828090326031)
        ·
          refine ⟨37646558703472242135489047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25097705802314828090326031 37646558703472242135489047)
          ·
            refine ⟨56469838055208363203233571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37646558703472242135489047 56469838055208363203233571)
            ·
              refine ⟨84704757082812544804850357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56469838055208363203233571 84704757082812544804850357)
              ·
                refine ⟨7941070976513676075454721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84704757082812544804850357 7941070976513676075454721)
                ·
                  refine ⟨5955803232385257056591041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7941070976513676075454721 5955803232385257056591041)
                  ·
                    refine ⟨4466852424288942792443281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5955803232385257056591041 4466852424288942792443281)
                    ·
                      refine ⟨3350139318216707094332461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4466852424288942792443281 3350139318216707094332461)
                      ·
                        rfl

theorem cell23_6524373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_6524373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524373 prefixEnd_6524373 := by exact prefixLift 6524373
  have htrace : WordTrace (prefixWord ++ tailWord_6524373) baseStart_6524373 baseEnd_6524373 := by
    simpa [prefixWord, tailWord_6524373, baseEnd_6524373] using wordTrace_append hprefix tailTrace_6524373
  have hstable : (prefixWord ++ tailWord_6524373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524373).length < 2 ^ (prefixWord ++ tailWord_6524373).sum := by decide
  have hdescent : baseEnd_6524373 < baseStart_6524373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524406 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_6524406 : Nat := 118140960795 + 6524406 * 2 ^ 59
def prefixEnd_6524406 : Nat := 4983230072969 + 3 ^ 40 * 6524406 * 2
def baseEnd_6524406 : Nat := 3350156263078305465219809

theorem tailTrace_6524406 : CollatzResearch.WordTrace tailWord_6524406 prefixEnd_6524406 3350156263078305465219809 := by
  unfold tailWord_6524406
  simp only [CollatzResearch.WordTrace]
  refine ⟨14872789775074926042347567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158643090934132544451707381 14872789775074926042347567)
  ·
    refine ⟨22309184662612389063521351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14872789775074926042347567 22309184662612389063521351)
    ·
      refine ⟨33463776993918583595282027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22309184662612389063521351 33463776993918583595282027)
      ·
        refine ⟨50195665490877875392923041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33463776993918583595282027 50195665490877875392923041)
        ·
          refine ⟨37646749118158406544692281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50195665490877875392923041 37646749118158406544692281)
          ·
            refine ⟨28235061838618804908519211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37646749118158406544692281 28235061838618804908519211)
            ·
              refine ⟨42352592757928207362778817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28235061838618804908519211 42352592757928207362778817)
              ·
                refine ⟨31764444568446155522084113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42352592757928207362778817 31764444568446155522084113)
                ·
                  refine ⟨23823333426334616641563085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31764444568446155522084113 23823333426334616641563085)
                  ·
                    refine ⟨8933750034875481240586157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23823333426334616641563085 8933750034875481240586157)
                    ·
                      refine ⟨3350156263078305465219809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8933750034875481240586157 3350156263078305465219809)
                      ·
                        rfl

theorem cell23_6524406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_6524406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524406 prefixEnd_6524406 := by exact prefixLift 6524406
  have htrace : WordTrace (prefixWord ++ tailWord_6524406) baseStart_6524406 baseEnd_6524406 := by
    simpa [prefixWord, tailWord_6524406, baseEnd_6524406] using wordTrace_append hprefix tailTrace_6524406
  have hstable : (prefixWord ++ tailWord_6524406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524406).length < 2 ^ (prefixWord ++ tailWord_6524406).sum := by decide
  have hdescent : baseEnd_6524406 < baseStart_6524406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524469 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 8]
def baseStart_6524469 : Nat := 118140960795 + 6524469 * 2 ^ 59
def prefixEnd_6524469 : Nat := 4983230072969 + 3 ^ 40 * 6524469 * 2
def baseEnd_6524469 : Nat := 372243179151059857636891

theorem tailTrace_6524469 : CollatzResearch.WordTrace tailWord_6524469 prefixEnd_6524469 372243179151059857636891 := by
  unfold tailWord_6524469
  simp only [CollatzResearch.WordTrace]
  refine ⟨237966934199970578437104461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158644622799980385624736307 237966934199970578437104461)
  ·
    refine ⟨89237600324988966913914173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237966934199970578437104461 89237600324988966913914173)
    ·
      refine ⟨33464100121870862592717815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89237600324988966913914173 33464100121870862592717815)
      ·
        refine ⟨50196150182806293889076723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33464100121870862592717815 50196150182806293889076723)
        ·
          refine ⟨75294225274209440833615085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50196150182806293889076723 75294225274209440833615085)
          ·
            refine ⟨28235334477828540312605657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75294225274209440833615085 28235334477828540312605657)
            ·
              refine ⟨21176500858371405234454243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28235334477828540312605657 21176500858371405234454243)
              ·
                refine ⟨31764751287557107851681365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21176500858371405234454243 31764751287557107851681365)
                ·
                  refine ⟨372243179151059857636891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31764751287557107851681365 372243179151059857636891)
                  ·
                    rfl

theorem cell23_6524469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 8].length) (baseStart_6524469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524469 prefixEnd_6524469 := by exact prefixLift 6524469
  have htrace : WordTrace (prefixWord ++ tailWord_6524469) baseStart_6524469 baseEnd_6524469 := by
    simpa [prefixWord, tailWord_6524469, baseEnd_6524469] using wordTrace_append hprefix tailTrace_6524469
  have hstable : (prefixWord ++ tailWord_6524469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524469).length < 2 ^ (prefixWord ++ tailWord_6524469).sum := by decide
  have hdescent : baseEnd_6524469 < baseStart_6524469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524473 : List Nat := [1, 2, 1, 5, 1, 4, 1, 1, 3, 4]
def baseStart_6524473 : Nat := 118140960795 + 6524473 * 2 ^ 59
def prefixEnd_6524473 : Nat := 4983230072969 + 3 ^ 40 * 6524473 * 2
def baseEnd_6524473 : Nat := 1116730222094052234360667

theorem tailTrace_6524473 : CollatzResearch.WordTrace tailWord_6524473 prefixEnd_6524473 1116730222094052234360667 := by
  unfold tailWord_6524473
  simp only [CollatzResearch.WordTrace]
  refine ⟨237967080091956087120250073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158644720061304058080166715 237967080091956087120250073)
  ·
    refine ⟨178475310068967065340187555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237967080091956087120250073 178475310068967065340187555)
    ·
      refine ⟨267712965103450598010281333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178475310068967065340187555 267712965103450598010281333)
      ·
        refine ⟨25098090478448493563463875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 267712965103450598010281333 25098090478448493563463875)
        ·
          refine ⟨37647135717672740345195813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25098090478448493563463875 37647135717672740345195813)
          ·
            refine ⟨7058837947063638814724215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37647135717672740345195813 7058837947063638814724215)
            ·
              refine ⟨10588256920595458222086323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7058837947063638814724215 10588256920595458222086323)
              ·
                refine ⟨15882385380893187333129485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10588256920595458222086323 15882385380893187333129485)
                ·
                  refine ⟨5955894517834945249923557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15882385380893187333129485 5955894517834945249923557)
                  ·
                    refine ⟨1116730222094052234360667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5955894517834945249923557 1116730222094052234360667)
                    ·
                      rfl

theorem cell23_6524473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 4].length) (baseStart_6524473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524473 prefixEnd_6524473 := by exact prefixLift 6524473
  have htrace : WordTrace (prefixWord ++ tailWord_6524473) baseStart_6524473 baseEnd_6524473 := by
    simpa [prefixWord, tailWord_6524473, baseEnd_6524473] using wordTrace_append hprefix tailTrace_6524473
  have hstable : (prefixWord ++ tailWord_6524473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524473).length < 2 ^ (prefixWord ++ tailWord_6524473).sum := by decide
  have hdescent : baseEnd_6524473 < baseStart_6524473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524496 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 5, 1, 3]
def baseStart_6524496 : Nat := 118140960795 + 6524496 * 2 ^ 59
def prefixEnd_6524496 : Nat := 4983230072969 + 3 ^ 40 * 6524496 * 2
def baseEnd_6524496 : Nat := 3350202476337210113094395

theorem tailTrace_6524496 : CollatzResearch.WordTrace tailWord_6524496 prefixEnd_6524496 3350202476337210113094395 := by
  unfold tailWord_6524496
  simp only [CollatzResearch.WordTrace]
  refine ⟨118983959485436381024168671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158645279313915174698891561 118983959485436381024168671)
  ·
    refine ⟨178475939228154571536253007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118983959485436381024168671 178475939228154571536253007)
    ·
      refine ⟨267713908842231857304379511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178475939228154571536253007 267713908842231857304379511)
      ·
        refine ⟨401570863263347785956569267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267713908842231857304379511 401570863263347785956569267)
        ·
          refine ⟨602356294895021678934853901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401570863263347785956569267 602356294895021678934853901)
          ·
            refine ⟨225883610585633129600570213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 602356294895021678934853901 225883610585633129600570213)
            ·
              refine ⟨42353176984806211800106915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225883610585633129600570213 42353176984806211800106915)
              ·
                refine ⟨63529765477209317700160373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42353176984806211800106915 63529765477209317700160373)
                ·
                  refine ⟨5955915513488373534390035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63529765477209317700160373 5955915513488373534390035)
                  ·
                    refine ⟨8933873270232560301585053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5955915513488373534390035 8933873270232560301585053)
                    ·
                      refine ⟨3350202476337210113094395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8933873270232560301585053 3350202476337210113094395)
                      ·
                        rfl

theorem cell23_6524496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 5, 1, 3].length) (baseStart_6524496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524496 prefixEnd_6524496 := by exact prefixLift 6524496
  have htrace : WordTrace (prefixWord ++ tailWord_6524496) baseStart_6524496 baseEnd_6524496 := by
    simpa [prefixWord, tailWord_6524496, baseEnd_6524496] using wordTrace_append hprefix tailTrace_6524496
  have hstable : (prefixWord ++ tailWord_6524496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524496).length < 2 ^ (prefixWord ++ tailWord_6524496).sum := by decide
  have hdescent : baseEnd_6524496 < baseStart_6524496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524506 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2]
def baseStart_6524506 : Nat := 118140960795 + 6524506 * 2 ^ 59
def prefixEnd_6524506 : Nat := 4983230072969 + 3 ^ 40 * 6524506 * 2
def baseEnd_6524506 : Nat := 3350207611143755073969349

theorem tailTrace_6524506 : CollatzResearch.WordTrace tailWord_6524506 prefixEnd_6524506 3350207611143755073969349 := by
  unfold tailWord_6524506
  simp only [CollatzResearch.WordTrace]
  refine ⟨59492070925209133439050343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158645522467224355837467581 59492070925209133439050343)
  ·
    refine ⟨89238106387813700158575515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59492070925209133439050343 89238106387813700158575515)
    ·
      refine ⟨133857159581720550237863273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89238106387813700158575515 133857159581720550237863273)
      ·
        refine ⟨100392869686290412678397455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133857159581720550237863273 100392869686290412678397455)
        ·
          refine ⟨150589304529435619017596183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100392869686290412678397455 150589304529435619017596183)
          ·
            refine ⟨225883956794153428526394275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150589304529435619017596183 225883956794153428526394275)
            ·
              refine ⟨338825935191230142789591413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225883956794153428526394275 338825935191230142789591413)
              ·
                refine ⟨31764931424177825886524195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 338825935191230142789591413 31764931424177825886524195)
                ·
                  refine ⟨47647397136266738829786293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31764931424177825886524195 47647397136266738829786293)
                  ·
                    refine ⟨4466943481525006765292465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47647397136266738829786293 4466943481525006765292465)
                    ·
                      refine ⟨3350207611143755073969349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4466943481525006765292465 3350207611143755073969349)
                      ·
                        rfl

theorem cell23_6524506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_6524506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524506 prefixEnd_6524506 := by exact prefixLift 6524506
  have htrace : WordTrace (prefixWord ++ tailWord_6524506) baseStart_6524506 baseEnd_6524506 := by
    simpa [prefixWord, tailWord_6524506, baseEnd_6524506] using wordTrace_append hprefix tailTrace_6524506
  have hstable : (prefixWord ++ tailWord_6524506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524506).length < 2 ^ (prefixWord ++ tailWord_6524506).sum := by decide
  have hdescent : baseEnd_6524506 < baseStart_6524506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524539 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 5]
def baseStart_6524539 : Nat := 118140960795 + 6524539 * 2 ^ 59
def prefixEnd_6524539 : Nat := 4983230072969 + 3 ^ 40 * 6524539 * 2
def baseEnd_6524539 : Nat := 3350224556005353444856697

theorem tailTrace_6524539 : CollatzResearch.WordTrace tailWord_6524539 prefixEnd_6524539 3350224556005353444856697 := by
  unfold tailWord_6524539
  simp only [CollatzResearch.WordTrace]
  refine ⟨237969487309716980392152671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158646324873144653594768447 237969487309716980392152671)
  ·
    refine ⟨356954230964575470588229007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237969487309716980392152671 356954230964575470588229007)
    ·
      refine ⟨535431346446863205882343511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356954230964575470588229007 535431346446863205882343511)
      ·
        refine ⟨803147019670294808823515267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535431346446863205882343511 803147019670294808823515267)
        ·
          refine ⟨1204720529505442213235272901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 803147019670294808823515267 1204720529505442213235272901)
          ·
            refine ⟨225885099282270414981613669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1204720529505442213235272901 225885099282270414981613669)
            ·
              refine ⟨42353456115425702809052563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225885099282270414981613669 42353456115425702809052563)
              ·
                refine ⟨63530184173138554213578845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42353456115425702809052563 63530184173138554213578845)
                ·
                  refine ⟨23823819064926957830092067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63530184173138554213578845 23823819064926957830092067)
                  ·
                    refine ⟨35735728597390436745138101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23823819064926957830092067 35735728597390436745138101)
                    ·
                      refine ⟨3350224556005353444856697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35735728597390436745138101 3350224556005353444856697)
                      ·
                        rfl

theorem cell23_6524539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 5].length) (baseStart_6524539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524539 prefixEnd_6524539 := by exact prefixLift 6524539
  have htrace : WordTrace (prefixWord ++ tailWord_6524539) baseStart_6524539 baseEnd_6524539 := by
    simpa [prefixWord, tailWord_6524539, baseEnd_6524539] using wordTrace_append hprefix tailTrace_6524539
  have hstable : (prefixWord ++ tailWord_6524539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524539).length < 2 ^ (prefixWord ++ tailWord_6524539).sum := by decide
  have hdescent : baseEnd_6524539 < baseStart_6524539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524553 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 5, 2, 2]
def baseStart_6524553 : Nat := 118140960795 + 6524553 * 2 ^ 59
def prefixEnd_6524553 : Nat := 4983230072969 + 3 ^ 40 * 6524553 * 2
def baseEnd_6524553 : Nat := 3350231744734516390081633

theorem tailTrace_6524553 : CollatzResearch.WordTrace tailWord_6524553 prefixEnd_6524553 3350231744734516390081633 := by
  unfold tailWord_6524553
  simp only [CollatzResearch.WordTrace]
  refine ⟨237969997931666260783162313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158646665287777507188774875 237969997931666260783162313)
  ·
    refine ⟨178477498448749695587371735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237969997931666260783162313 178477498448749695587371735)
    ·
      refine ⟨267716247673124543381057603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178477498448749695587371735 267716247673124543381057603)
      ·
        refine ⟨401574371509686815071586405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267716247673124543381057603 401574371509686815071586405)
        ·
          refine ⟨75295194658066277825922451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 401574371509686815071586405 75295194658066277825922451)
          ·
            refine ⟨112942791987099416738883677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75295194658066277825922451 112942791987099416738883677)
            ·
              refine ⟨42353546995162281277081379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112942791987099416738883677 42353546995162281277081379)
              ·
                refine ⟨63530320492743421915622069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42353546995162281277081379 63530320492743421915622069)
                ·
                  refine ⟨5955967546194695804589569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63530320492743421915622069 5955967546194695804589569)
                  ·
                    refine ⟨4466975659646021853442177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5955967546194695804589569 4466975659646021853442177)
                    ·
                      refine ⟨3350231744734516390081633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4466975659646021853442177 3350231744734516390081633)
                      ·
                        rfl

theorem cell23_6524553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 2, 2].length) (baseStart_6524553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524553 prefixEnd_6524553 := by exact prefixLift 6524553
  have htrace : WordTrace (prefixWord ++ tailWord_6524553) baseStart_6524553 baseEnd_6524553 := by
    simpa [prefixWord, tailWord_6524553, baseEnd_6524553] using wordTrace_append hprefix tailTrace_6524553
  have hstable : (prefixWord ++ tailWord_6524553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524553).length < 2 ^ (prefixWord ++ tailWord_6524553).sum := by decide
  have hdescent : baseEnd_6524553 < baseStart_6524553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524556 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 3, 2, 3]
def baseStart_6524556 : Nat := 118140960795 + 6524556 * 2 ^ 59
def prefixEnd_6524556 : Nat := 4983230072969 + 3 ^ 40 * 6524556 * 2
def baseEnd_6524556 : Nat := 3350233285176479878344119

theorem tailTrace_6524556 : CollatzResearch.WordTrace tailWord_6524556 prefixEnd_6524556 3350233285176479878344119 := by
  unfold tailWord_6524556
  simp only [CollatzResearch.WordTrace]
  refine ⟨118985053675327696147760761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158646738233770261530347681 118985053675327696147760761)
  ·
    refine ⟨89238790256495772110820571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118985053675327696147760761 89238790256495772110820571)
    ·
      refine ⟨133858185384743658166230857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89238790256495772110820571 133858185384743658166230857)
      ·
        refine ⟨100393639038557743624673143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133858185384743658166230857 100393639038557743624673143)
        ·
          refine ⟨150590458557836615437009715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100393639038557743624673143 150590458557836615437009715)
          ·
            refine ⟨225885687836754923155514573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150590458557836615437009715 225885687836754923155514573)
            ·
              refine ⟨84707132938783096183317965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225885687836754923155514573 84707132938783096183317965)
              ·
                refine ⟨31765174852043661068744237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84707132938783096183317965 31765174852043661068744237)
                ·
                  refine ⟨11911940569516372900779089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31765174852043661068744237 11911940569516372900779089)
                  ·
                    refine ⟨8933955427137279675584317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11911940569516372900779089 8933955427137279675584317)
                    ·
                      refine ⟨3350233285176479878344119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8933955427137279675584317 3350233285176479878344119)
                      ·
                        rfl

theorem cell23_6524556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_6524556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524556 prefixEnd_6524556 := by exact prefixLift 6524556
  have htrace : WordTrace (prefixWord ++ tailWord_6524556) baseStart_6524556 baseEnd_6524556 := by
    simpa [prefixWord, tailWord_6524556, baseEnd_6524556] using wordTrace_append hprefix tailTrace_6524556
  have hstable : (prefixWord ++ tailWord_6524556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524556).length < 2 ^ (prefixWord ++ tailWord_6524556).sum := by decide
  have hdescent : baseEnd_6524556 < baseStart_6524556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524564 : List Nat := [2, 4, 2, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_6524564 : Nat := 118140960795 + 6524564 * 2 ^ 59
def prefixEnd_6524564 : Nat := 4983230072969 + 3 ^ 40 * 6524564 * 2
def baseEnd_6524564 : Nat := 3350237393021715847044083

theorem tailTrace_6524564 : CollatzResearch.WordTrace tailWord_6524564 prefixEnd_6524564 3350237393021715847044083 := by
  unfold tailWord_6524564
  simp only [CollatzResearch.WordTrace]
  refine ⟨118985199567313204830906373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158646932756417606441208497 118985199567313204830906373)
  ·
    refine ⟨22309724918871225905794945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118985199567313204830906373 22309724918871225905794945)
    ·
      refine ⟨16732293689153419429346209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22309724918871225905794945 16732293689153419429346209)
      ·
        refine ⟨12549220266865064572009657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16732293689153419429346209 12549220266865064572009657)
        ·
          refine ⟨9411915200148798429007243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12549220266865064572009657 9411915200148798429007243)
          ·
            refine ⟨14117872800223197643510865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9411915200148798429007243 14117872800223197643510865)
            ·
              refine ⟨10588404600167398232633149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14117872800223197643510865 10588404600167398232633149)
              ·
                refine ⟨3970651725062774337237431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10588404600167398232633149 3970651725062774337237431)
                ·
                  refine ⟨5955977587594161505856147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3970651725062774337237431 5955977587594161505856147)
                  ·
                    refine ⟨8933966381391242258784221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5955977587594161505856147 8933966381391242258784221)
                    ·
                      refine ⟨3350237393021715847044083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8933966381391242258784221 3350237393021715847044083)
                      ·
                        rfl

theorem cell23_6524564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_6524564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524564 prefixEnd_6524564 := by exact prefixLift 6524564
  have htrace : WordTrace (prefixWord ++ tailWord_6524564) baseStart_6524564 baseEnd_6524564 := by
    simpa [prefixWord, tailWord_6524564, baseEnd_6524564] using wordTrace_append hprefix tailTrace_6524564
  have hstable : (prefixWord ++ tailWord_6524564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524564).length < 2 ^ (prefixWord ++ tailWord_6524564).sum := by decide
  have hdescent : baseEnd_6524564 < baseStart_6524564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524580 : List Nat := [2, 3, 1, 2, 2, 4, 1, 2, 2, 4]
def baseStart_6524580 : Nat := 118140960795 + 6524580 * 2 ^ 59
def prefixEnd_6524580 : Nat := 4983230072969 + 3 ^ 40 * 6524580 * 2
def baseEnd_6524580 : Nat := 1116748536237395928148003

theorem tailTrace_6524580 : CollatzResearch.WordTrace tailWord_6524580 prefixEnd_6524580 1116748536237395928148003 := by
  unfold tailWord_6524580
  simp only [CollatzResearch.WordTrace]
  refine ⟨118985491351284222197197597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158647321801712296262930129 118985491351284222197197597)
  ·
    refine ⟨44619559256731583323949099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118985491351284222197197597 44619559256731583323949099)
    ·
      refine ⟨66929338885097374985923649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44619559256731583323949099 66929338885097374985923649)
      ·
        refine ⟨50197004163823031239442737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66929338885097374985923649 50197004163823031239442737)
        ·
          refine ⟨37647753122867273429582053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50197004163823031239442737 37647753122867273429582053)
          ·
            refine ⟨7058953710537613768046635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37647753122867273429582053 7058953710537613768046635)
            ·
              refine ⟨10588430565806420652069953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7058953710537613768046635 10588430565806420652069953)
              ·
                refine ⟨7941322924354815489052465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10588430565806420652069953 7941322924354815489052465)
                ·
                  refine ⟨5955992193266111616789349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7941322924354815489052465 5955992193266111616789349)
                  ·
                    refine ⟨1116748536237395928148003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5955992193266111616789349 1116748536237395928148003)
                    ·
                      rfl

theorem cell23_6524580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_6524580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524580 prefixEnd_6524580 := by exact prefixLift 6524580
  have htrace : WordTrace (prefixWord ++ tailWord_6524580) baseStart_6524580 baseEnd_6524580 := by
    simpa [prefixWord, tailWord_6524580, baseEnd_6524580] using wordTrace_append hprefix tailTrace_6524580
  have hstable : (prefixWord ++ tailWord_6524580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524580).length < 2 ^ (prefixWord ++ tailWord_6524580).sum := by decide
  have hdescent : baseEnd_6524580 < baseStart_6524580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524590 : List Nat := [4, 1, 4, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_6524590 : Nat := 118140960795 + 6524590 * 2 ^ 59
def prefixEnd_6524590 : Nat := 4983230072969 + 3 ^ 40 * 6524590 * 2
def baseEnd_6524590 : Nat := 3350250743518732745318963

theorem tailTrace_6524590 : CollatzResearch.WordTrace tailWord_6524590 prefixEnd_6524590 3350250743518732745318963 := by
  unfold tailWord_6524590
  simp only [CollatzResearch.WordTrace]
  refine ⟨29746418429066527012782403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158647564955021477401506149 29746418429066527012782403)
  ·
    refine ⟨44619627643599790519173605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29746418429066527012782403 44619627643599790519173605)
    ·
      refine ⟨8366180183174960722345051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44619627643599790519173605 8366180183174960722345051)
      ·
        refine ⟨12549270274762441083517577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8366180183174960722345051 12549270274762441083517577)
        ·
          refine ⟨9411952706071830812638183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12549270274762441083517577 9411952706071830812638183)
          ·
            refine ⟨14117929059107746218957275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9411952706071830812638183 14117929059107746218957275)
            ·
              refine ⟨21176893588661619328435913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14117929059107746218957275 21176893588661619328435913)
              ·
                refine ⟨15882670191496214496326935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21176893588661619328435913 15882670191496214496326935)
                ·
                  refine ⟨23824005287244321744490403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15882670191496214496326935 23824005287244321744490403)
                  ·
                    refine ⟨35736007930866482616735605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23824005287244321744490403 35736007930866482616735605)
                    ·
                      refine ⟨3350250743518732745318963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35736007930866482616735605 3350250743518732745318963)
                      ·
                        rfl

theorem cell23_6524590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_6524590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524590 prefixEnd_6524590 := by exact prefixLift 6524590
  have htrace : WordTrace (prefixWord ++ tailWord_6524590) baseStart_6524590 baseEnd_6524590 := by
    simpa [prefixWord, tailWord_6524590, baseEnd_6524590] using wordTrace_append hprefix tailTrace_6524590
  have hstable : (prefixWord ++ tailWord_6524590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524590).length < 2 ^ (prefixWord ++ tailWord_6524590).sum := by decide
  have hdescent : baseEnd_6524590 < baseStart_6524590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524597 : List Nat := [1, 3, 3, 3, 2, 1, 3, 1, 2, 4]
def baseStart_6524597 : Nat := 118140960795 + 6524597 * 2 ^ 59
def prefixEnd_6524597 : Nat := 4983230072969 + 3 ^ 40 * 6524597 * 2
def baseEnd_6524597 : Nat := 1116751445961104739310477

theorem tailTrace_6524597 : CollatzResearch.WordTrace tailWord_6524597 prefixEnd_6524597 1116751445961104739310477 := by
  unfold tailWord_6524597
  simp only [CollatzResearch.WordTrace]
  refine ⟨237971602743506856297764045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158647735162337904198509363 237971602743506856297764045)
  ·
    refine ⟨89239351028815071111661517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237971602743506856297764045 89239351028815071111661517)
    ·
      refine ⟨33464756635805651666873069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89239351028815071111661517 33464756635805651666873069)
      ·
        refine ⟨12549283738427119375077401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33464756635805651666873069 12549283738427119375077401)
        ·
          refine ⟨9411962803820339531308051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12549283738427119375077401 9411962803820339531308051)
          ·
            refine ⟨14117944205730509296962077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9411962803820339531308051 14117944205730509296962077)
            ·
              refine ⟨5294229077148940986360779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14117944205730509296962077 5294229077148940986360779)
              ·
                refine ⟨7941343615723411479541169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5294229077148940986360779 7941343615723411479541169)
                ·
                  refine ⟨5956007711792558609655877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7941343615723411479541169 5956007711792558609655877)
                  ·
                    refine ⟨1116751445961104739310477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5956007711792558609655877 1116751445961104739310477)
                    ·
                      rfl

theorem cell23_6524597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_6524597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524597 prefixEnd_6524597 := by exact prefixLift 6524597
  have htrace : WordTrace (prefixWord ++ tailWord_6524597) baseStart_6524597 baseEnd_6524597 := by
    simpa [prefixWord, tailWord_6524597, baseEnd_6524597] using wordTrace_append hprefix tailTrace_6524597
  have hstable : (prefixWord ++ tailWord_6524597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524597).length < 2 ^ (prefixWord ++ tailWord_6524597).sum := by decide
  have hdescent : baseEnd_6524597 < baseStart_6524597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524603 : List Nat := [1, 1, 1, 1, 1, 2, 3, 7, 2, 1, 3]
def baseStart_6524603 : Nat := 118140960795 + 6524603 * 2 ^ 59
def prefixEnd_6524603 : Nat := 4983230072969 + 3 ^ 40 * 6524603 * 2
def baseEnd_6524603 : Nat := 3350257418767241194456403

theorem tailTrace_6524603 : CollatzResearch.WordTrace tailWord_6524603 prefixEnd_6524603 3350257418767241194456403 := by
  unfold tailWord_6524603
  simp only [CollatzResearch.WordTrace]
  refine ⟨237971821581485119322482463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158647881054323412881654975 237971821581485119322482463)
  ·
    refine ⟨356957732372227678983723695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237971821581485119322482463 356957732372227678983723695)
    ·
      refine ⟨535436598558341518475585543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356957732372227678983723695 535436598558341518475585543)
      ·
        refine ⟨803154897837512277713378315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535436598558341518475585543 803154897837512277713378315)
        ·
          refine ⟨1204732346756268416570067473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 803154897837512277713378315 1204732346756268416570067473)
          ·
            refine ⟨903549260067201312427550605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1204732346756268416570067473 903549260067201312427550605)
            ·
              refine ⟨338830972525200492160331477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 903549260067201312427550605 338830972525200492160331477)
              ·
                refine ⟨7941350918559386535007769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 338830972525200492160331477 7941350918559386535007769)
                ·
                  refine ⟨5956013188919539901255827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7941350918559386535007769 5956013188919539901255827)
                  ·
                    refine ⟨8934019783379309851883741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5956013188919539901255827 8934019783379309851883741)
                    ·
                      refine ⟨3350257418767241194456403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8934019783379309851883741 3350257418767241194456403)
                      ·
                        rfl

theorem cell23_6524603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 1, 3].length) (baseStart_6524603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524603 prefixEnd_6524603 := by exact prefixLift 6524603
  have htrace : WordTrace (prefixWord ++ tailWord_6524603) baseStart_6524603 baseEnd_6524603 := by
    simpa [prefixWord, tailWord_6524603, baseEnd_6524603] using wordTrace_append hprefix tailTrace_6524603
  have hstable : (prefixWord ++ tailWord_6524603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524603).length < 2 ^ (prefixWord ++ tailWord_6524603).sum := by decide
  have hdescent : baseEnd_6524603 < baseStart_6524603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524619 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 1, 8]
def baseStart_6524619 : Nat := 118140960795 + 6524619 * 2 ^ 59
def prefixEnd_6524619 : Nat := 4983230072969 + 3 ^ 40 * 6524619 * 2
def baseEnd_6524619 : Nat := 1116755211485904377285443

theorem tailTrace_6524619 : CollatzResearch.WordTrace tailWord_6524619 prefixEnd_6524619 1116755211485904377285443 := by
  unfold tailWord_6524619
  simp only [CollatzResearch.WordTrace]
  refine ⟨237972405149427154055064911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158648270099618102703376607 237972405149427154055064911)
  ·
    refine ⟨356958607724140731082597367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237972405149427154055064911 356958607724140731082597367)
    ·
      refine ⟨535437911586211096623896051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356958607724140731082597367 535437911586211096623896051)
      ·
        refine ⟨803156867379316644935844077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535437911586211096623896051 803156867379316644935844077)
        ·
          refine ⟨301183825267243741850941529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 803156867379316644935844077 301183825267243741850941529)
          ·
            refine ⟨225887868950432806388206147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301183825267243741850941529 225887868950432806388206147)
            ·
              refine ⟨338831803425649209582309221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225887868950432806388206147 338831803425649209582309221)
              ·
                refine ⟨63530963142309226796682979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 338831803425649209582309221 63530963142309226796682979)
                ·
                  refine ⟨95296444713463840195024469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63530963142309226796682979 95296444713463840195024469)
                  ·
                    refine ⟨1116755211485904377285443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95296444713463840195024469 1116755211485904377285443)
                    ·
                      rfl

theorem cell23_6524619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 8].length) (baseStart_6524619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524619 prefixEnd_6524619 := by exact prefixLift 6524619
  have htrace : WordTrace (prefixWord ++ tailWord_6524619) baseStart_6524619 baseEnd_6524619 := by
    simpa [prefixWord, tailWord_6524619, baseEnd_6524619] using wordTrace_append hprefix tailTrace_6524619
  have hstable : (prefixWord ++ tailWord_6524619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524619).length < 2 ^ (prefixWord ++ tailWord_6524619).sum := by decide
  have hdescent : baseEnd_6524619 < baseStart_6524619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524621 : List Nat := [1, 6, 2, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_6524621 : Nat := 118140960795 + 6524621 * 2 ^ 59
def prefixEnd_6524621 : Nat := 4983230072969 + 3 ^ 40 * 6524621 * 2
def baseEnd_6524621 : Nat := 3350266661419022124031321

theorem tailTrace_6524621 : CollatzResearch.WordTrace tailWord_6524621 prefixEnd_6524621 3350266661419022124031321 := by
  unfold tailWord_6524621
  simp only [CollatzResearch.WordTrace]
  refine ⟨237972478095419908396637717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158648318730279938931091811 237972478095419908396637717)
  ·
    refine ⟨11154959910722808206092393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 237972478095419908396637717 11154959910722808206092393)
    ·
      refine ⟨8366219933042106154569295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11154959910722808206092393 8366219933042106154569295)
      ·
        refine ⟨12549329899563159231853943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8366219933042106154569295 12549329899563159231853943)
        ·
          refine ⟨18823994849344738847780915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12549329899563159231853943 18823994849344738847780915)
          ·
            refine ⟨28235992274017108271671373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18823994849344738847780915 28235992274017108271671373)
            ·
              refine ⟨10588497102756415601876765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28235992274017108271671373 10588497102756415601876765)
              ·
                refine ⟨3970686413533655850703787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10588497102756415601876765 3970686413533655850703787)
                ·
                  refine ⟨5956029620300483776055681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3970686413533655850703787 5956029620300483776055681)
                  ·
                    refine ⟨4467022215225362832041761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5956029620300483776055681 4467022215225362832041761)
                    ·
                      refine ⟨3350266661419022124031321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4467022215225362832041761 3350266661419022124031321)
                      ·
                        rfl

theorem cell23_6524621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_6524621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524621 prefixEnd_6524621 := by exact prefixLift 6524621
  have htrace : WordTrace (prefixWord ++ tailWord_6524621) baseStart_6524621 baseEnd_6524621 := by
    simpa [prefixWord, tailWord_6524621, baseEnd_6524621] using wordTrace_append hprefix tailTrace_6524621
  have hstable : (prefixWord ++ tailWord_6524621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524621).length < 2 ^ (prefixWord ++ tailWord_6524621).sum := by decide
  have hdescent : baseEnd_6524621 < baseStart_6524621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524703 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 1, 7, 2]
def baseStart_6524703 : Nat := 118140960795 + 6524703 * 2 ^ 59
def prefixEnd_6524703 : Nat := 4983230072969 + 3 ^ 40 * 6524703 * 2
def baseEnd_6524703 : Nat := 3350308766832690803205943

theorem tailTrace_6524703 : CollatzResearch.WordTrace tailWord_6524703 prefixEnd_6524703 3350308766832690803205943 := by
  unfold tailWord_6524703
  simp only [CollatzResearch.WordTrace]
  refine ⟨237975468881122836401122763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158650312587415224267415175 237975468881122836401122763)
  ·
    refine ⟨356963203321684254601684145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237975468881122836401122763 356963203321684254601684145)
    ·
      refine ⟨267722402491263190951263109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356963203321684254601684145 267722402491263190951263109)
      ·
        refine ⟨50197950467111848303361833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267722402491263190951263109 50197950467111848303361833)
        ·
          refine ⟨37648462850333886227521375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50197950467111848303361833 37648462850333886227521375)
          ·
            refine ⟨56472694275500829341282063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37648462850333886227521375 56472694275500829341282063)
            ·
              refine ⟨84709041413251244011923095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56472694275500829341282063 84709041413251244011923095)
              ·
                refine ⟨127063562119876866017884643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84709041413251244011923095 127063562119876866017884643)
                ·
                  refine ⟨190595343179815299026826965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127063562119876866017884643 190595343179815299026826965)
                  ·
                    refine ⟨4467078355776921070941257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 190595343179815299026826965 4467078355776921070941257)
                    ·
                      refine ⟨3350308766832690803205943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4467078355776921070941257 3350308766832690803205943)
                      ·
                        rfl

theorem cell23_6524703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_6524703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524703 prefixEnd_6524703 := by exact prefixLift 6524703
  have htrace : WordTrace (prefixWord ++ tailWord_6524703) baseStart_6524703 baseEnd_6524703 := by
    simpa [prefixWord, tailWord_6524703, baseEnd_6524703] using wordTrace_append hprefix tailTrace_6524703
  have hstable : (prefixWord ++ tailWord_6524703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524703).length < 2 ^ (prefixWord ++ tailWord_6524703).sum := by decide
  have hdescent : baseEnd_6524703 < baseStart_6524703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524730 : List Nat := [3, 1, 1, 1, 5, 3, 1, 1, 2, 5]
def baseStart_6524730 : Nat := 118140960795 + 6524730 * 2 ^ 59
def prefixEnd_6524730 : Nat := 4983230072969 + 3 ^ 40 * 6524730 * 2
def baseEnd_6524730 : Nat := 1116774210270120732522773

theorem tailTrace_6524730 : CollatzResearch.WordTrace tailWord_6524730 prefixEnd_6524730 1116774210270120732522773 := by
  unfold tailWord_6524730
  simp only [CollatzResearch.WordTrace]
  refine ⟨59494113413006255003088911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158650969101350013341570429 59494113413006255003088911)
  ·
    refine ⟨89241170119509382504633367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59494113413006255003088911 89241170119509382504633367)
    ·
      refine ⟨133861755179264073756950051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89241170119509382504633367 133861755179264073756950051)
      ·
        refine ⟨200792632768896110635425077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133861755179264073756950051 200792632768896110635425077)
        ·
          refine ⟨18824309322084010372071101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200792632768896110635425077 18824309322084010372071101)
          ·
            refine ⟨7059115995781503889526663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18824309322084010372071101 7059115995781503889526663)
            ·
              refine ⟨10588673993672255834289995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7059115995781503889526663 10588673993672255834289995)
              ·
                refine ⟨15883010990508383751434993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10588673993672255834289995 15883010990508383751434993)
                ·
                  refine ⟨11912258242881287813576245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15883010990508383751434993 11912258242881287813576245)
                  ·
                    refine ⟨1116774210270120732522773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11912258242881287813576245 1116774210270120732522773)
                    ·
                      rfl

theorem cell23_6524730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_6524730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524730 prefixEnd_6524730 := by exact prefixLift 6524730
  have htrace : WordTrace (prefixWord ++ tailWord_6524730) baseStart_6524730 baseEnd_6524730 := by
    simpa [prefixWord, tailWord_6524730, baseEnd_6524730] using wordTrace_append hprefix tailTrace_6524730
  have hstable : (prefixWord ++ tailWord_6524730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524730).length < 2 ^ (prefixWord ++ tailWord_6524730).sum := by decide
  have hdescent : baseEnd_6524730 < baseStart_6524730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524746 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_6524746 : Nat := 118140960795 + 6524746 * 2 ^ 59
def prefixEnd_6524746 : Nat := 4983230072969 + 3 ^ 40 * 6524746 * 2
def baseEnd_6524746 : Nat := 3350330846500834134968245

theorem tailTrace_6524746 : CollatzResearch.WordTrace tailWord_6524746 prefixEnd_6524746 3350330846500834134968245 := by
  unfold tailWord_6524746
  simp only [CollatzResearch.WordTrace]
  refine ⟨59494259304991763686234523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158651358146644703163292061 59494259304991763686234523)
  ·
    refine ⟨89241388957487645529351785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59494259304991763686234523 89241388957487645529351785)
    ·
      refine ⟨66931041718115734147013839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89241388957487645529351785 66931041718115734147013839)
      ·
        refine ⟨100396562577173601220520759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66931041718115734147013839 100396562577173601220520759)
        ·
          refine ⟨150594843865760401830781139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100396562577173601220520759 150594843865760401830781139)
          ·
            refine ⟨225892265798640602746171709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150594843865760401830781139 225892265798640602746171709)
            ·
              refine ⟨84709599674490226029814391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225892265798640602746171709 84709599674490226029814391)
              ·
                refine ⟨127064399511735339044721587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84709599674490226029814391 127064399511735339044721587)
                ·
                  refine ⟨190596599267603008567082381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127064399511735339044721587 190596599267603008567082381)
                  ·
                    refine ⟨71473724725351128212655893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 190596599267603008567082381 71473724725351128212655893)
                    ·
                      refine ⟨3350330846500834134968245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71473724725351128212655893 3350330846500834134968245)
                      ·
                        rfl

theorem cell23_6524746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_6524746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524746 prefixEnd_6524746 := by exact prefixLift 6524746
  have htrace : WordTrace (prefixWord ++ tailWord_6524746) baseStart_6524746 baseEnd_6524746 := by
    simpa [prefixWord, tailWord_6524746, baseEnd_6524746] using wordTrace_append hprefix tailTrace_6524746
  have hstable : (prefixWord ++ tailWord_6524746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524746).length < 2 ^ (prefixWord ++ tailWord_6524746).sum := by decide
  have hdescent : baseEnd_6524746 < baseStart_6524746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524770 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_6524770 : Nat := 118140960795 + 6524770 * 2 ^ 59
def prefixEnd_6524770 : Nat := 4983230072969 + 3 ^ 40 * 6524770 * 2
def baseEnd_6524770 : Nat := 3350343170036542041068135

theorem tailTrace_6524770 : CollatzResearch.WordTrace tailWord_6524770 prefixEnd_6524770 3350343170036542041068135 := by
  unfold tailWord_6524770
  simp only [CollatzResearch.WordTrace]
  refine ⟨59494478142970026710952941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158651941714586737895874509 59494478142970026710952941)
  ·
    refine ⟨22310429303613760016607353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59494478142970026710952941 22310429303613760016607353)
    ·
      refine ⟨16732821977710320012455515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22310429303613760016607353 16732821977710320012455515)
      ·
        refine ⟨25099232966565480018683273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16732821977710320012455515 25099232966565480018683273)
        ·
          refine ⟨18824424724924110014012455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25099232966565480018683273 18824424724924110014012455)
          ·
            refine ⟨28236637087386165021018683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18824424724924110014012455 28236637087386165021018683)
            ·
              refine ⟨42354955631079247531528025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28236637087386165021018683 42354955631079247531528025)
              ·
                refine ⟨31766216723309435648646019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42354955631079247531528025 31766216723309435648646019)
                ·
                  refine ⟨47649325084964153472969029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31766216723309435648646019 47649325084964153472969029)
                  ·
                    refine ⟨8934248453430778776181693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47649325084964153472969029 8934248453430778776181693)
                    ·
                      refine ⟨3350343170036542041068135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8934248453430778776181693 3350343170036542041068135)
                      ·
                        rfl

theorem cell23_6524770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_6524770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524770 prefixEnd_6524770 := by exact prefixLift 6524770
  have htrace : WordTrace (prefixWord ++ tailWord_6524770) baseStart_6524770 baseEnd_6524770 := by
    simpa [prefixWord, tailWord_6524770, baseEnd_6524770] using wordTrace_append hprefix tailTrace_6524770
  have hstable : (prefixWord ++ tailWord_6524770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524770).length < 2 ^ (prefixWord ++ tailWord_6524770).sum := by decide
  have hdescent : baseEnd_6524770 < baseStart_6524770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524817 : List Nat := [1, 2, 2, 1, 1, 1, 4, 6, 1, 1, 3]
def baseStart_6524817 : Nat := 118140960795 + 6524817 * 2 ^ 59
def prefixEnd_6524817 : Nat := 4983230072969 + 3 ^ 40 * 6524817 * 2
def baseEnd_6524817 : Nat := 3350367303627303357180419

theorem tailTrace_6524817 : CollatzResearch.WordTrace tailWord_6524817 prefixEnd_6524817 3350367303627303357180419 := by
  unfold tailWord_6524817
  simp only [CollatzResearch.WordTrace]
  refine ⟨237979626802709833870772705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158653084535139889247181803 237979626802709833870772705)
  ·
    refine ⟨178484720102032375403079529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237979626802709833870772705 178484720102032375403079529)
    ·
      refine ⟨133863540076524281552309647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178484720102032375403079529 133863540076524281552309647)
      ·
        refine ⟨200795310114786422328464471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133863540076524281552309647 200795310114786422328464471)
        ·
          refine ⟨301192965172179633492696707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200795310114786422328464471 301192965172179633492696707)
          ·
            refine ⟨451789447758269450239045061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301192965172179633492696707 451789447758269450239045061)
            ·
              refine ⟨84710521454675521919820949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 451789447758269450239045061 84710521454675521919820949)
              ·
                refine ⟨3970805693187915089991607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84710521454675521919820949 3970805693187915089991607)
                ·
                  refine ⟨5956208539781872634987411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3970805693187915089991607 5956208539781872634987411)
                  ·
                    refine ⟨8934312809672808952481117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5956208539781872634987411 8934312809672808952481117)
                    ·
                      refine ⟨3350367303627303357180419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8934312809672808952481117 3350367303627303357180419)
                      ·
                        rfl

theorem cell23_6524817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 1, 1, 3].length) (baseStart_6524817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524817 prefixEnd_6524817 := by exact prefixLift 6524817
  have htrace : WordTrace (prefixWord ++ tailWord_6524817) baseStart_6524817 baseEnd_6524817 := by
    simpa [prefixWord, tailWord_6524817, baseEnd_6524817] using wordTrace_append hprefix tailTrace_6524817
  have hstable : (prefixWord ++ tailWord_6524817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524817).length < 2 ^ (prefixWord ++ tailWord_6524817).sum := by decide
  have hdescent : baseEnd_6524817 < baseStart_6524817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524824 : List Nat := [2, 1, 2, 6, 1, 2, 2, 1, 6]
def baseStart_6524824 : Nat := 118140960795 + 6524824 * 2 ^ 59
def prefixEnd_6524824 : Nat := 4983230072969 + 3 ^ 40 * 6524824 * 2
def baseEnd_6524824 : Nat := 372263433110209425532543

theorem tailTrace_6524824 : CollatzResearch.WordTrace tailWord_6524824 prefixEnd_6524824 372263433110209425532543 := by
  unfold tailWord_6524824
  simp only [CollatzResearch.WordTrace]
  refine ⟨118989941056842237033138763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158653254742456316044185017 118989941056842237033138763)
  ·
    refine ⟨178484911585263355549708145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118989941056842237033138763 178484911585263355549708145)
    ·
      refine ⟨133863683688947516662281109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178484911585263355549708145 133863683688947516662281109)
      ·
        refine ⟨6274860172919414843544427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 133863683688947516662281109 6274860172919414843544427)
        ·
          refine ⟨9412290259379122265316641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6274860172919414843544427 9412290259379122265316641)
          ·
            refine ⟨7059217694534341698987481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9412290259379122265316641 7059217694534341698987481)
            ·
              refine ⟨5294413270900756274240611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7059217694534341698987481 5294413270900756274240611)
              ·
                refine ⟨7941619906351134411360917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5294413270900756274240611 7941619906351134411360917)
                ·
                  refine ⟨372263433110209425532543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7941619906351134411360917 372263433110209425532543)
                  ·
                    rfl

theorem cell23_6524824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 6].length) (baseStart_6524824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524824 prefixEnd_6524824 := by exact prefixLift 6524824
  have htrace : WordTrace (prefixWord ++ tailWord_6524824) baseStart_6524824 baseEnd_6524824 := by
    simpa [prefixWord, tailWord_6524824, baseEnd_6524824] using wordTrace_append hprefix tailTrace_6524824
  have hstable : (prefixWord ++ tailWord_6524824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524824).length < 2 ^ (prefixWord ++ tailWord_6524824).sum := by decide
  have hdescent : baseEnd_6524824 < baseStart_6524824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524857 : List Nat := [1, 2, 1, 4, 2, 1, 5, 1, 1, 1, 4]
def baseStart_6524857 : Nat := 118140960795 + 6524857 * 2 ^ 59
def prefixEnd_6524857 : Nat := 4983230072969 + 3 ^ 40 * 6524857 * 2
def baseEnd_6524857 : Nat := 3350387842853483200680235

theorem tailTrace_6524857 : CollatzResearch.WordTrace tailWord_6524857 prefixEnd_6524857 3350387842853483200680235 := by
  unfold tailWord_6524857
  simp only [CollatzResearch.WordTrace]
  refine ⟨237981085722564920702228825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158654057148376613801485883 237981085722564920702228825)
  ·
    refine ⟨178485814291923690526671619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237981085722564920702228825 178485814291923690526671619)
    ·
      refine ⟨267728721437885535790007429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178485814291923690526671619 267728721437885535790007429)
      ·
        refine ⟨50199135269603537960626393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267728721437885535790007429 50199135269603537960626393)
        ·
          refine ⟨37649351452202653470469795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50199135269603537960626393 37649351452202653470469795)
          ·
            refine ⟨56474027178303980205704693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37649351452202653470469795 56474027178303980205704693)
            ·
              refine ⟨5294440047965998144284815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56474027178303980205704693 5294440047965998144284815)
              ·
                refine ⟨7941660071948997216427223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5294440047965998144284815 7941660071948997216427223)
                ·
                  refine ⟨11912490107923495824640835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7941660071948997216427223 11912490107923495824640835)
                  ·
                    refine ⟨17868735161885243736961253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11912490107923495824640835 17868735161885243736961253)
                    ·
                      refine ⟨3350387842853483200680235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17868735161885243736961253 3350387842853483200680235)
                      ·
                        rfl

theorem cell23_6524857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_6524857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524857 prefixEnd_6524857 := by exact prefixLift 6524857
  have htrace : WordTrace (prefixWord ++ tailWord_6524857) baseStart_6524857 baseEnd_6524857 := by
    simpa [prefixWord, tailWord_6524857, baseEnd_6524857] using wordTrace_append hprefix tailTrace_6524857
  have hstable : (prefixWord ++ tailWord_6524857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524857).length < 2 ^ (prefixWord ++ tailWord_6524857).sum := by decide
  have hdescent : baseEnd_6524857 < baseStart_6524857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524923 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 2, 6]
def baseStart_6524923 : Nat := 118140960795 + 6524923 * 2 ^ 59
def prefixEnd_6524923 : Nat := 4983230072969 + 3 ^ 40 * 6524923 * 2
def baseEnd_6524923 : Nat := 1116807244192226647484977

theorem tailTrace_6524923 : CollatzResearch.WordTrace tailWord_6524923 prefixEnd_6524923 1116807244192226647484977 := by
  unfold tailWord_6524923
  simp only [CollatzResearch.WordTrace]
  refine ⟨237983492940325813974131423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158655661960217209316087615 237983492940325813974131423)
  ·
    refine ⟨356975239410488720961197135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237983492940325813974131423 356975239410488720961197135)
    ·
      refine ⟨535462859115733081441795703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356975239410488720961197135 535462859115733081441795703)
      ·
        refine ⟨803194288673599622162693555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535462859115733081441795703 803194288673599622162693555)
        ·
          refine ⟨1204791433010399433244040333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 803194288673599622162693555 1204791433010399433244040333)
          ·
            refine ⟨451796787378899787466515125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1204791433010399433244040333 451796787378899787466515125)
            ·
              refine ⟨42355948816771855074985793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 451796787378899787466515125 42355948816771855074985793)
              ·
                refine ⟨31766961612578891306239345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42355948816771855074985793 31766961612578891306239345)
                ·
                  refine ⟨23825221209434168479679509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31766961612578891306239345 23825221209434168479679509)
                  ·
                    refine ⟨1116807244192226647484977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23825221209434168479679509 1116807244192226647484977)
                    ·
                      rfl

theorem cell23_6524923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 6].length) (baseStart_6524923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524923 prefixEnd_6524923 := by exact prefixLift 6524923
  have htrace : WordTrace (prefixWord ++ tailWord_6524923) baseStart_6524923 baseEnd_6524923 := by
    simpa [prefixWord, tailWord_6524923, baseEnd_6524923] using wordTrace_append hprefix tailTrace_6524923
  have hstable : (prefixWord ++ tailWord_6524923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524923).length < 2 ^ (prefixWord ++ tailWord_6524923).sum := by decide
  have hdescent : baseEnd_6524923 < baseStart_6524923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524947 : List Nat := [1, 1, 1, 2, 1, 4, 5, 1, 1, 4, 2]
def baseStart_6524947 : Nat := 118140960795 + 6524947 * 2 ^ 59
def prefixEnd_6524947 : Nat := 4983230072969 + 3 ^ 40 * 6524947 * 2
def baseEnd_6524947 : Nat := 3350434056112387848554821

theorem tailTrace_6524947 : CollatzResearch.WordTrace tailWord_6524947 prefixEnd_6524947 3350434056112387848554821 := by
  unfold tailWord_6524947
  simp only [CollatzResearch.WordTrace]
  refine ⟨237984368292238866073005095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158656245528159244048670063 237984368292238866073005095)
  ·
    refine ⟨356976552438358299109507643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237984368292238866073005095 356976552438358299109507643)
    ·
      refine ⟨535464828657537448664261465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356976552438358299109507643 535464828657537448664261465)
      ·
        refine ⟨401598621493153086498196099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535464828657537448664261465 401598621493153086498196099)
        ·
          refine ⟨602397932239729629747294149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401598621493153086498196099 602397932239729629747294149)
          ·
            refine ⟨112949612294949305577617653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 602397932239729629747294149 112949612294949305577617653)
            ·
              refine ⟨10589026152651497397901655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112949612294949305577617653 10589026152651497397901655)
              ·
                refine ⟨15883539228977246096852483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10589026152651497397901655 15883539228977246096852483)
                ·
                  refine ⟨23825308843465869145278725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15883539228977246096852483 23825308843465869145278725)
                  ·
                    refine ⟨4467245408149850464739761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23825308843465869145278725 4467245408149850464739761)
                    ·
                      refine ⟨3350434056112387848554821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4467245408149850464739761 3350434056112387848554821)
                      ·
                        rfl

theorem cell23_6524947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 4, 2].length) (baseStart_6524947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524947 prefixEnd_6524947 := by exact prefixLift 6524947
  have htrace : WordTrace (prefixWord ++ tailWord_6524947) baseStart_6524947 baseEnd_6524947 := by
    simpa [prefixWord, tailWord_6524947, baseEnd_6524947] using wordTrace_append hprefix tailTrace_6524947
  have hstable : (prefixWord ++ tailWord_6524947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524947).length < 2 ^ (prefixWord ++ tailWord_6524947).sum := by decide
  have hdescent : baseEnd_6524947 < baseStart_6524947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524951 : List Nat := [1, 1, 3, 5, 2, 1, 2, 2, 1, 3, 2]
def baseStart_6524951 : Nat := 118140960795 + 6524951 * 2 ^ 59
def prefixEnd_6524951 : Nat := 4983230072969 + 3 ^ 40 * 6524951 * 2
def baseEnd_6524951 : Nat := 3350436110035005832904803

theorem tailTrace_6524951 : CollatzResearch.WordTrace tailWord_6524951 prefixEnd_6524951 3350436110035005832904803 := by
  unfold tailWord_6524951
  simp only [CollatzResearch.WordTrace]
  refine ⟨237984514184224374756150707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158656342789482916504100471 237984514184224374756150707)
  ·
    refine ⟨356976771276336562134226061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237984514184224374756150707 356976771276336562134226061)
    ·
      refine ⟨133866289228626210800334773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356976771276336562134226061 133866289228626210800334773)
      ·
        refine ⟨12549964615183707262531385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133866289228626210800334773 12549964615183707262531385)
        ·
          refine ⟨9412473461387780446898539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12549964615183707262531385 9412473461387780446898539)
          ·
            refine ⟨14118710192081670670347809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9412473461387780446898539 14118710192081670670347809)
            ·
              refine ⟨10589032644061253002760857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14118710192081670670347809 10589032644061253002760857)
              ·
                refine ⟨7941774483045939752070643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10589032644061253002760857 7941774483045939752070643)
                ·
                  refine ⟨11912661724568909628105965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7941774483045939752070643 11912661724568909628105965)
                  ·
                    refine ⟨4467248146713341110539737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11912661724568909628105965 4467248146713341110539737)
                    ·
                      refine ⟨3350436110035005832904803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4467248146713341110539737 3350436110035005832904803)
                      ·
                        rfl

theorem cell23_6524951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_6524951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524951 prefixEnd_6524951 := by exact prefixLift 6524951
  have htrace : WordTrace (prefixWord ++ tailWord_6524951) baseStart_6524951 baseEnd_6524951 := by
    simpa [prefixWord, tailWord_6524951, baseEnd_6524951] using wordTrace_append hprefix tailTrace_6524951
  have hstable : (prefixWord ++ tailWord_6524951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524951).length < 2 ^ (prefixWord ++ tailWord_6524951).sum := by decide
  have hdescent : baseEnd_6524951 < baseStart_6524951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6524998 : List Nat := [6, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_6524998 : Nat := 118140960795 + 6524998 * 2 ^ 59
def prefixEnd_6524998 : Nat := 4983230072969 + 3 ^ 40 * 6524998 * 2
def baseEnd_6524998 : Nat := 3350460243625767149017087

theorem tailTrace_6524998 : CollatzResearch.WordTrace tailWord_6524998 prefixEnd_6524998 3350460243625767149017087 := by
  unfold tailWord_6524998
  simp only [CollatzResearch.WordTrace]
  refine ⟨7437069637970440680722239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158657485610036067855407765 7437069637970440680722239)
  ·
    refine ⟨11155604456955661021083359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7437069637970440680722239 11155604456955661021083359)
    ·
      refine ⟨16733406685433491531625039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11155604456955661021083359 16733406685433491531625039)
      ·
        refine ⟨25100110028150237297437559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16733406685433491531625039 25100110028150237297437559)
        ·
          refine ⟨37650165042225355946156339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25100110028150237297437559 37650165042225355946156339)
          ·
            refine ⟨56475247563338033919234509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37650165042225355946156339 56475247563338033919234509)
            ·
              refine ⟨21178217836251762719712941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56475247563338033919234509 21178217836251762719712941)
              ·
                refine ⟨7941831688594411019892353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21178217836251762719712941 7941831688594411019892353)
                ·
                  refine ⟨5956373766445808264919265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7941831688594411019892353 5956373766445808264919265)
                  ·
                    refine ⟨4467280324834356198689449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5956373766445808264919265 4467280324834356198689449)
                    ·
                      refine ⟨3350460243625767149017087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4467280324834356198689449 3350460243625767149017087)
                      ·
                        rfl

theorem cell23_6524998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_6524998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6524998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6524998 prefixEnd_6524998 := by exact prefixLift 6524998
  have htrace : WordTrace (prefixWord ++ tailWord_6524998) baseStart_6524998 baseEnd_6524998 := by
    simpa [prefixWord, tailWord_6524998, baseEnd_6524998] using wordTrace_append hprefix tailTrace_6524998
  have hstable : (prefixWord ++ tailWord_6524998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6524998).length < 2 ^ (prefixWord ++ tailWord_6524998).sum := by decide
  have hdescent : baseEnd_6524998 < baseStart_6524998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6524998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525037 : List Nat := [1, 5, 1, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_6525037 : Nat := 118140960795 + 6525037 * 2 ^ 59
def prefixEnd_6525037 : Nat := 4983230072969 + 3 ^ 40 * 6525037 * 2
def baseEnd_6525037 : Nat := 3350480269371292496429407

theorem tailTrace_6525037 : CollatzResearch.WordTrace tailWord_6525037 prefixEnd_6525037 3350480269371292496429407 := by
  unfold tailWord_6525037
  simp only [CollatzResearch.WordTrace]
  refine ⟨237987650861912811443781365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158658433907941874295854243 237987650861912811443781365)
  ·
    refine ⟨22311342268304326072854503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237987650861912811443781365 22311342268304326072854503)
    ·
      refine ⟨33467013402456489109281755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22311342268304326072854503 33467013402456489109281755)
      ·
        refine ⟨50200520103684733663922633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33467013402456489109281755 50200520103684733663922633)
        ·
          refine ⟨37650390077763550247941975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50200520103684733663922633 37650390077763550247941975)
          ·
            refine ⟨56475585116645325371912963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37650390077763550247941975 56475585116645325371912963)
            ·
              refine ⟨84713377674967988057869445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56475585116645325371912963 84713377674967988057869445)
              ·
                refine ⟨15883758314056497760850521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84713377674967988057869445 15883758314056497760850521)
                ·
                  refine ⟨11912818735542373320637891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15883758314056497760850521 11912818735542373320637891)
                  ·
                    refine ⟨17869228103313559980956837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11912818735542373320637891 17869228103313559980956837)
                    ·
                      refine ⟨3350480269371292496429407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17869228103313559980956837 3350480269371292496429407)
                      ·
                        rfl

theorem cell23_6525037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_6525037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525037 prefixEnd_6525037 := by exact prefixLift 6525037
  have htrace : WordTrace (prefixWord ++ tailWord_6525037) baseStart_6525037 baseEnd_6525037 := by
    simpa [prefixWord, tailWord_6525037, baseEnd_6525037] using wordTrace_append hprefix tailTrace_6525037
  have hstable : (prefixWord ++ tailWord_6525037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525037).length < 2 ^ (prefixWord ++ tailWord_6525037).sum := by decide
  have hdescent : baseEnd_6525037 < baseStart_6525037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525064 : List Nat := [2, 1, 3, 4, 1, 2, 1, 2, 3, 4]
def baseStart_6525064 : Nat := 118140960795 + 6525064 * 2 ^ 59
def prefixEnd_6525064 : Nat := 4983230072969 + 3 ^ 40 * 6525064 * 2
def baseEnd_6525064 : Nat := 1116831377782987963597261

theorem tailTrace_6525064 : CollatzResearch.WordTrace tailWord_6525064 prefixEnd_6525064 1116831377782987963597261 := by
  unfold tailWord_6525064
  simp only [CollatzResearch.WordTrace]
  refine ⟨118994317816407497527507123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158659090421876663370009497 118994317816407497527507123)
  ·
    refine ⟨178491476724611246291260685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118994317816407497527507123 178491476724611246291260685)
    ·
      refine ⟨66934303771729217359222757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178491476724611246291260685 66934303771729217359222757)
      ·
        refine ⟨12550181957199228254854267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66934303771729217359222757 12550181957199228254854267)
        ·
          refine ⟨18825272935798842382281401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12550181957199228254854267 18825272935798842382281401)
          ·
            refine ⟨14118954701849131786711051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18825272935798842382281401 14118954701849131786711051)
            ·
              refine ⟨21178432052773697680066577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14118954701849131786711051 21178432052773697680066577)
              ·
                refine ⟨15883824039580273260049933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21178432052773697680066577 15883824039580273260049933)
                ·
                  refine ⟨5956434014842602472518725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15883824039580273260049933 5956434014842602472518725)
                  ·
                    refine ⟨1116831377782987963597261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5956434014842602472518725 1116831377782987963597261)
                    ·
                      rfl

theorem cell23_6525064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_6525064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525064 prefixEnd_6525064 := by exact prefixLift 6525064
  have htrace : WordTrace (prefixWord ++ tailWord_6525064) baseStart_6525064 baseEnd_6525064 := by
    simpa [prefixWord, tailWord_6525064, baseEnd_6525064] using wordTrace_append hprefix tailTrace_6525064
  have hstable : (prefixWord ++ tailWord_6525064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525064).length < 2 ^ (prefixWord ++ tailWord_6525064).sum := by decide
  have hdescent : baseEnd_6525064 < baseStart_6525064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525124 : List Nat := [2, 3, 3, 1, 2, 1, 1, 4, 1, 5]
def baseStart_6525124 : Nat := 118140960795 + 6525124 * 2 ^ 59
def prefixEnd_6525124 : Nat := 4983230072969 + 3 ^ 40 * 6525124 * 2
def baseEnd_6525124 : Nat := 1116841647396077885347169

theorem tailTrace_6525124 : CollatzResearch.WordTrace tailWord_6525124 prefixEnd_6525124 1116841647396077885347169 := by
  unfold tailWord_6525124
  simp only [CollatzResearch.WordTrace]
  refine ⟨118995412006298812651099213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158660549341731750201465617 118995412006298812651099213)
  ·
    refine ⟨44623279502362054744162205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118995412006298812651099213 44623279502362054744162205)
    ·
      refine ⟨16733729813385770529060827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44623279502362054744162205 16733729813385770529060827)
      ·
        refine ⟨25100594720078655793591241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16733729813385770529060827 25100594720078655793591241)
        ·
          refine ⟨18825446040058991845193431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25100594720078655793591241 18825446040058991845193431)
          ·
            refine ⟨28238169060088487767790147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18825446040058991845193431 28238169060088487767790147)
            ·
              refine ⟨42357253590132731651685221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28238169060088487767790147 42357253590132731651685221)
              ·
                refine ⟨7941985048149887184690979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42357253590132731651685221 7941985048149887184690979)
                ·
                  refine ⟨11912977572224830777036469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7941985048149887184690979 11912977572224830777036469)
                  ·
                    refine ⟨1116841647396077885347169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11912977572224830777036469 1116841647396077885347169)
                    ·
                      rfl

theorem cell23_6525124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_6525124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525124 prefixEnd_6525124 := by exact prefixLift 6525124
  have htrace : WordTrace (prefixWord ++ tailWord_6525124) baseStart_6525124 baseEnd_6525124 := by
    simpa [prefixWord, tailWord_6525124, baseEnd_6525124] using wordTrace_append hprefix tailTrace_6525124
  have hstable : (prefixWord ++ tailWord_6525124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525124).length < 2 ^ (prefixWord ++ tailWord_6525124).sum := by decide
  have hdescent : baseEnd_6525124 < baseStart_6525124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525137 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 4, 4]
def baseStart_6525137 : Nat := 118140960795 + 6525137 * 2 ^ 59
def prefixEnd_6525137 : Nat := 4983230072969 + 3 ^ 40 * 6525137 * 2
def baseEnd_6525137 : Nat := 1116843872478914035059649

theorem tailTrace_6525137 : CollatzResearch.WordTrace tailWord_6525137 prefixEnd_6525137 1116843872478914035059649 := by
  unfold tailWord_6525137
  simp only [CollatzResearch.WordTrace]
  refine ⟨237991298161550528522421665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158660865441033685681614443 237991298161550528522421665)
  ·
    refine ⟨178493473621162896391816249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237991298161550528522421665 178493473621162896391816249)
    ·
      refine ⟨133870105215872172293862187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178493473621162896391816249 133870105215872172293862187)
      ·
        refine ⟨200805157823808258440793281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133870105215872172293862187 200805157823808258440793281)
        ·
          refine ⟨150603868367856193830594961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200805157823808258440793281 150603868367856193830594961)
          ·
            refine ⟨112952901275892145372946221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150603868367856193830594961 112952901275892145372946221)
            ·
              refine ⟨42357337978459554514854833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112952901275892145372946221 42357337978459554514854833)
              ·
                refine ⟨31768003483844665886141125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42357337978459554514854833 31768003483844665886141125)
                ·
                  refine ⟨5956500653220874853651461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31768003483844665886141125 5956500653220874853651461)
                  ·
                    refine ⟨1116843872478914035059649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5956500653220874853651461 1116843872478914035059649)
                    ·
                      rfl

theorem cell23_6525137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_6525137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525137 prefixEnd_6525137 := by exact prefixLift 6525137
  have htrace : WordTrace (prefixWord ++ tailWord_6525137) baseStart_6525137 baseEnd_6525137 := by
    simpa [prefixWord, tailWord_6525137, baseEnd_6525137] using wordTrace_append hprefix tailTrace_6525137
  have hstable : (prefixWord ++ tailWord_6525137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525137).length < 2 ^ (prefixWord ++ tailWord_6525137).sum := by decide
  have hdescent : baseEnd_6525137 < baseStart_6525137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525138 : List Nat := [3, 2, 2, 2, 1, 2, 3, 3, 1, 1, 3]
def baseStart_6525138 : Nat := 118140960795 + 6525138 * 2 ^ 59
def prefixEnd_6525138 : Nat := 4983230072969 + 3 ^ 40 * 6525138 * 2
def baseEnd_6525138 : Nat := 3350532130917396601266443

theorem tailTrace_6525138 : CollatzResearch.WordTrace tailWord_6525138 prefixEnd_6525138 3350532130917396601266443 := by
  unfold tailWord_6525138
  simp only [CollatzResearch.WordTrace]
  refine ⟨59497833658636726423302017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158660889756364603795472045 59497833658636726423302017)
  ·
    refine ⟨44623375243977544817476513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59497833658636726423302017 44623375243977544817476513)
    ·
      refine ⟨33467531432983158613107385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44623375243977544817476513 33467531432983158613107385)
      ·
        refine ⟨25100648574737368959830539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33467531432983158613107385 25100648574737368959830539)
        ·
          refine ⟨37650972862106053439745809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25100648574737368959830539 37650972862106053439745809)
          ·
            refine ⟨28238229646579540079809357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37650972862106053439745809 28238229646579540079809357)
            ·
              refine ⟨10589336117467327529928509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28238229646579540079809357 10589336117467327529928509)
              ·
                refine ⟨3971001044050247823723191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10589336117467327529928509 3971001044050247823723191)
                ·
                  refine ⟨5956501566075371735584787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3971001044050247823723191 5956501566075371735584787)
                  ·
                    refine ⟨8934752349113057603377181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5956501566075371735584787 8934752349113057603377181)
                    ·
                      refine ⟨3350532130917396601266443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8934752349113057603377181 3350532130917396601266443)
                      ·
                        rfl

theorem cell23_6525138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_6525138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525138 prefixEnd_6525138 := by exact prefixLift 6525138
  have htrace : WordTrace (prefixWord ++ tailWord_6525138) baseStart_6525138 baseEnd_6525138 := by
    simpa [prefixWord, tailWord_6525138, baseEnd_6525138] using wordTrace_append hprefix tailTrace_6525138
  have hstable : (prefixWord ++ tailWord_6525138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525138).length < 2 ^ (prefixWord ++ tailWord_6525138).sum := by decide
  have hdescent : baseEnd_6525138 < baseStart_6525138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525144 : List Nat := [2, 1, 2, 2, 4, 1, 2, 3, 1, 1, 4]
def baseStart_6525144 : Nat := 118140960795 + 6525144 * 2 ^ 59
def prefixEnd_6525144 : Nat := 4983230072969 + 3 ^ 40 * 6525144 * 2
def baseEnd_6525144 : Nat := 3350535211801323577791415

theorem tailTrace_6525144 : CollatzResearch.WordTrace tailWord_6525144 prefixEnd_6525144 3350535211801323577791415 := by
  unfold tailWord_6525144
  simp only [CollatzResearch.WordTrace]
  refine ⟨118995776736262584358963243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158661035648350112478617657 118995776736262584358963243)
  ·
    refine ⟨178493665104393876538444865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118995776736262584358963243 178493665104393876538444865)
    ·
      refine ⟨133870248828295407403833649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178493665104393876538444865 133870248828295407403833649)
      ·
        refine ⟨100402686621221555552875237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133870248828295407403833649 100402686621221555552875237)
        ·
          refine ⟨18825503741479041666164107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100402686621221555552875237 18825503741479041666164107)
          ·
            refine ⟨28238255612218562499246161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18825503741479041666164107 28238255612218562499246161)
            ·
              refine ⟨21178691709163921874434621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28238255612218562499246161 21178691709163921874434621)
              ·
                refine ⟨7942009390936470702912983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21178691709163921874434621 7942009390936470702912983)
                ·
                  refine ⟨11913014086404706054369475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7942009390936470702912983 11913014086404706054369475)
                  ·
                    refine ⟨17869521129607059081554213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11913014086404706054369475 17869521129607059081554213)
                    ·
                      refine ⟨3350535211801323577791415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17869521129607059081554213 3350535211801323577791415)
                      ·
                        rfl

theorem cell23_6525144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_6525144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525144 prefixEnd_6525144 := by exact prefixLift 6525144
  have htrace : WordTrace (prefixWord ++ tailWord_6525144) baseStart_6525144 baseEnd_6525144 := by
    simpa [prefixWord, tailWord_6525144, baseEnd_6525144] using wordTrace_append hprefix tailTrace_6525144
  have hstable : (prefixWord ++ tailWord_6525144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525144).length < 2 ^ (prefixWord ++ tailWord_6525144).sum := by decide
  have hdescent : baseEnd_6525144 < baseStart_6525144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525155 : List Nat := [1, 1, 1, 8, 2, 1, 1, 1, 3, 1, 3]
def baseStart_6525155 : Nat := 118140960795 + 6525155 * 2 ^ 59
def prefixEnd_6525155 : Nat := 4983230072969 + 3 ^ 40 * 6525155 * 2
def baseEnd_6525155 : Nat := 3350540860088523034753865

theorem tailTrace_6525155 : CollatzResearch.WordTrace tailWord_6525155 prefixEnd_6525155 3350540860088523034753865 := by
  unfold tailWord_6525155
  simp only [CollatzResearch.WordTrace]
  refine ⟨237991954675485317596576919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158661303116990211731051279 237991954675485317596576919)
  ·
    refine ⟨356987932013227976394865379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237991954675485317596576919 356987932013227976394865379)
    ·
      refine ⟨535481898019841964592298069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356987932013227976394865379 535481898019841964592298069)
      ·
        refine ⟨6275178492420023022565993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 535481898019841964592298069 6275178492420023022565993)
        ·
          refine ⟨4706383869315017266924495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6275178492420023022565993 4706383869315017266924495)
          ·
            refine ⟨7059575803972525900386743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4706383869315017266924495 7059575803972525900386743)
            ·
              refine ⟨10589363705958788850580115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7059575803972525900386743 10589363705958788850580115)
              ·
                refine ⟨15884045558938183275870173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10589363705958788850580115 15884045558938183275870173)
                ·
                  refine ⟨5956517084601818728451315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15884045558938183275870173 5956517084601818728451315)
                  ·
                    refine ⟨8934775626902728092676973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5956517084601818728451315 8934775626902728092676973)
                    ·
                      refine ⟨3350540860088523034753865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8934775626902728092676973 3350540860088523034753865)
                      ·
                        rfl

theorem cell23_6525155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_6525155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525155 prefixEnd_6525155 := by exact prefixLift 6525155
  have htrace : WordTrace (prefixWord ++ tailWord_6525155) baseStart_6525155 baseEnd_6525155 := by
    simpa [prefixWord, tailWord_6525155, baseEnd_6525155] using wordTrace_append hprefix tailTrace_6525155
  have hstable : (prefixWord ++ tailWord_6525155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525155).length < 2 ^ (prefixWord ++ tailWord_6525155).sum := by decide
  have hdescent : baseEnd_6525155 < baseStart_6525155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525157 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 1, 1, 6]
def baseStart_6525157 : Nat := 118140960795 + 6525157 * 2 ^ 59
def prefixEnd_6525157 : Nat := 4983230072969 + 3 ^ 40 * 6525157 * 2
def baseEnd_6525157 : Nat := 3350541887049832026928855

theorem tailTrace_6525157 : CollatzResearch.WordTrace tailWord_6525157 prefixEnd_6525157 3350541887049832026928855 := by
  unfold tailWord_6525157
  simp only [CollatzResearch.WordTrace]
  refine ⟨237992027621478071938149725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158661351747652047958766483 237992027621478071938149725)
  ·
    refine ⟨89247010358054276976806147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237992027621478071938149725 89247010358054276976806147)
    ·
      refine ⟨133870515537081415465209221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89247010358054276976806147 133870515537081415465209221)
      ·
        refine ⟨25100721663202765399726729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133870515537081415465209221 25100721663202765399726729)
        ·
          refine ⟨18825541247402074049795047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25100721663202765399726729 18825541247402074049795047)
          ·
            refine ⟨28238311871103111074692571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18825541247402074049795047 28238311871103111074692571)
            ·
              refine ⟨42357467806654666612038857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28238311871103111074692571 42357467806654666612038857)
              ·
                refine ⟨31768100854990999959029143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42357467806654666612038857 31768100854990999959029143)
                ·
                  refine ⟨47652151282486499938543715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31768100854990999959029143 47652151282486499938543715)
                  ·
                    refine ⟨71478226923729749907815573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47652151282486499938543715 71478226923729749907815573)
                    ·
                      refine ⟨3350541887049832026928855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71478226923729749907815573 3350541887049832026928855)
                      ·
                        rfl

theorem cell23_6525157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_6525157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525157 prefixEnd_6525157 := by exact prefixLift 6525157
  have htrace : WordTrace (prefixWord ++ tailWord_6525157) baseStart_6525157 baseEnd_6525157 := by
    simpa [prefixWord, tailWord_6525157, baseEnd_6525157] using wordTrace_append hprefix tailTrace_6525157
  have hstable : (prefixWord ++ tailWord_6525157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525157).length < 2 ^ (prefixWord ++ tailWord_6525157).sum := by decide
  have hdescent : baseEnd_6525157 < baseStart_6525157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525167 : List Nat := [1, 1, 2, 1, 6, 2, 2, 8]
def baseStart_6525167 : Nat := 118140960795 + 6525167 * 2 ^ 59
def prefixEnd_6525167 : Nat := 4983230072969 + 3 ^ 40 * 6525167 * 2
def baseEnd_6525167 : Nat := 124094334142828777326067

theorem tailTrace_6525167 : CollatzResearch.WordTrace tailWord_6525167 prefixEnd_6525167 124094334142828777326067 := by
  unfold tailWord_6525167
  simp only [CollatzResearch.WordTrace]
  refine ⟨237992392351441843646013755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158661594900961229097342503 237992392351441843646013755)
  ·
    refine ⟨356988588527162765469020633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237992392351441843646013755 356988588527162765469020633)
    ·
      refine ⟨267741441395372074101765475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356988588527162765469020633 267741441395372074101765475)
      ·
        refine ⟨401612162093058111152648213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267741441395372074101765475 401612162093058111152648213)
        ·
          refine ⟨18825570098112098960280385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 401612162093058111152648213 18825570098112098960280385)
          ·
            refine ⟨14119177573584074220210289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18825570098112098960280385 14119177573584074220210289)
            ·
              refine ⟨10589383180188055665157717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14119177573584074220210289 10589383180188055665157717)
              ·
                refine ⟨124094334142828777326067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10589383180188055665157717 124094334142828777326067)
                ·
                  rfl

theorem cell23_6525167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 8].length) (baseStart_6525167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525167 prefixEnd_6525167 := by exact prefixLift 6525167
  have htrace : WordTrace (prefixWord ++ tailWord_6525167) baseStart_6525167 baseEnd_6525167 := by
    simpa [prefixWord, tailWord_6525167, baseEnd_6525167] using wordTrace_append hprefix tailTrace_6525167
  have hstable : (prefixWord ++ tailWord_6525167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525167).length < 2 ^ (prefixWord ++ tailWord_6525167).sum := by decide
  have hdescent : baseEnd_6525167 < baseStart_6525167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525191 : List Nat := [1, 1, 4, 5, 1, 1, 1, 2, 1, 2, 4]
def baseStart_6525191 : Nat := 118140960795 + 6525191 * 2 ^ 59
def prefixEnd_6525191 : Nat := 4983230072969 + 3 ^ 40 * 6525191 * 2
def baseEnd_6525191 : Nat := 3350559345392084893903699

theorem tailTrace_6525191 : CollatzResearch.WordTrace tailWord_6525191 prefixEnd_6525191 3350559345392084893903699 := by
  unfold tailWord_6525191
  simp only [CollatzResearch.WordTrace]
  refine ⟨237993267703354895744887427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158662178468903263829924951 237993267703354895744887427)
  ·
    refine ⟨356989901555032343617331141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237993267703354895744887427 356989901555032343617331141)
    ·
      refine ⟨66935606541568564428249589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 356989901555032343617331141 66935606541568564428249589)
      ·
        refine ⟨6275213113272052915148399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66935606541568564428249589 6275213113272052915148399)
        ·
          refine ⟨9412819669908079372722599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6275213113272052915148399 9412819669908079372722599)
          ·
            refine ⟨14119229504862119059083899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9412819669908079372722599 14119229504862119059083899)
            ·
              refine ⟨21178844257293178588625849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14119229504862119059083899 21178844257293178588625849)
              ·
                refine ⟨15884133192969883941469387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21178844257293178588625849 15884133192969883941469387)
                ·
                  refine ⟨23826199789454825912204081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15884133192969883941469387 23826199789454825912204081)
                  ·
                    refine ⟨17869649842091119434153061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23826199789454825912204081 17869649842091119434153061)
                    ·
                      refine ⟨3350559345392084893903699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17869649842091119434153061 3350559345392084893903699)
                      ·
                        rfl

theorem cell23_6525191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_6525191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525191 prefixEnd_6525191 := by exact prefixLift 6525191
  have htrace : WordTrace (prefixWord ++ tailWord_6525191) baseStart_6525191 baseEnd_6525191 := by
    simpa [prefixWord, tailWord_6525191, baseEnd_6525191] using wordTrace_append hprefix tailTrace_6525191
  have hstable : (prefixWord ++ tailWord_6525191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525191).length < 2 ^ (prefixWord ++ tailWord_6525191).sum := by decide
  have hdescent : baseEnd_6525191 < baseStart_6525191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525194 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3]
def baseStart_6525194 : Nat := 118140960795 + 6525194 * 2 ^ 59
def prefixEnd_6525194 : Nat := 4983230072969 + 3 ^ 40 * 6525194 * 2
def baseEnd_6525194 : Nat := 3350560885834048382166185

theorem tailTrace_6525194 : CollatzResearch.WordTrace tailWord_6525194 prefixEnd_6525194 3350560885834048382166185 := by
  unfold tailWord_6525194
  simp only [CollatzResearch.WordTrace]
  refine ⟨59498344280586006814311659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158662251414896018171497757 59498344280586006814311659)
  ·
    refine ⟨89247516420879010221467489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59498344280586006814311659 89247516420879010221467489)
    ·
      refine ⟨66935637315659257666100617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89247516420879010221467489 66935637315659257666100617)
      ·
        refine ⟨50201727986744443249575463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66935637315659257666100617 50201727986744443249575463)
        ·
          refine ⟨75302591980116664874363195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50201727986744443249575463 75302591980116664874363195)
          ·
            refine ⟨112953887970174997311544793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75302591980116664874363195 112953887970174997311544793)
            ·
              refine ⟨84715415977631247983658595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112953887970174997311544793 84715415977631247983658595)
              ·
                refine ⟨127073123966446871975487893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84715415977631247983658595 127073123966446871975487893)
                ·
                  refine ⟨5956552685927197123850995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127073123966446871975487893 5956552685927197123850995)
                  ·
                    refine ⟨8934829028890795685776493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5956552685927197123850995 8934829028890795685776493)
                    ·
                      refine ⟨3350560885834048382166185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8934829028890795685776493 3350560885834048382166185)
                      ·
                        rfl

theorem cell23_6525194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_6525194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525194 prefixEnd_6525194 := by exact prefixLift 6525194
  have htrace : WordTrace (prefixWord ++ tailWord_6525194) baseStart_6525194 baseEnd_6525194 := by
    simpa [prefixWord, tailWord_6525194, baseEnd_6525194] using wordTrace_append hprefix tailTrace_6525194
  have hstable : (prefixWord ++ tailWord_6525194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525194).length < 2 ^ (prefixWord ++ tailWord_6525194).sum := by decide
  have hdescent : baseEnd_6525194 < baseStart_6525194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525217 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_6525217 : Nat := 118140960795 + 6525217 * 2 ^ 59
def prefixEnd_6525217 : Nat := 4983230072969 + 3 ^ 40 * 6525217 * 2
def baseEnd_6525217 : Nat := 3350572695889101792178579

theorem tailTrace_6525217 : CollatzResearch.WordTrace tailWord_6525217 prefixEnd_6525217 3350572695889101792178579 := by
  unfold tailWord_6525217
  simp only [CollatzResearch.WordTrace]
  refine ⟨237994216001260702185333905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158662810667507134790222603 237994216001260702185333905)
  ·
    refine ⟨178495662000945526639000429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237994216001260702185333905 178495662000945526639000429)
    ·
      refine ⟨66935873250354572489625161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178495662000945526639000429 66935873250354572489625161)
      ·
        refine ⟨50201904937765929367218871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66935873250354572489625161 50201904937765929367218871)
        ·
          refine ⟨75302857406648894050828307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50201904937765929367218871 75302857406648894050828307)
          ·
            refine ⟨112954286109973341076242461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75302857406648894050828307 112954286109973341076242461)
            ·
              refine ⟨42357857291240002903590923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112954286109973341076242461 42357857291240002903590923)
              ·
                refine ⟨63536785936860004355386385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42357857291240002903590923 63536785936860004355386385)
                ·
                  refine ⟨47652589452645003266539789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63536785936860004355386385 47652589452645003266539789)
                  ·
                    refine ⟨17869721044741876224952421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47652589452645003266539789 17869721044741876224952421)
                    ·
                      refine ⟨3350572695889101792178579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17869721044741876224952421 3350572695889101792178579)
                      ·
                        rfl

theorem cell23_6525217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_6525217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525217 prefixEnd_6525217 := by exact prefixLift 6525217
  have htrace : WordTrace (prefixWord ++ tailWord_6525217) baseStart_6525217 baseEnd_6525217 := by
    simpa [prefixWord, tailWord_6525217, baseEnd_6525217] using wordTrace_append hprefix tailTrace_6525217
  have hstable : (prefixWord ++ tailWord_6525217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525217).length < 2 ^ (prefixWord ++ tailWord_6525217).sum := by decide
  have hdescent : baseEnd_6525217 < baseStart_6525217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525247 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 4]
def baseStart_6525247 : Nat := 118140960795 + 6525247 * 2 ^ 59
def prefixEnd_6525247 : Nat := 4983230072969 + 3 ^ 40 * 6525247 * 2
def baseEnd_6525247 : Nat := 3350588100308736674803441

theorem tailTrace_6525247 : CollatzResearch.WordTrace tailWord_6525247 prefixEnd_6525247 3350588100308736674803441 := by
  unfold tailWord_6525247
  simp only [CollatzResearch.WordTrace]
  refine ⟨237995310191152017308925995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158663540127434678205950663 237995310191152017308925995)
  ·
    refine ⟨356992965286728025963388993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237995310191152017308925995 356992965286728025963388993)
    ·
      refine ⟨267744723965046019472541745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356992965286728025963388993 267744723965046019472541745)
      ·
        refine ⟨200808542973784514604406309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267744723965046019472541745 200808542973784514604406309)
        ·
          refine ⟨37651601807584596488326183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200808542973784514604406309 37651601807584596488326183)
          ·
            refine ⟨56477402711376894732489275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37651601807584596488326183 56477402711376894732489275)
            ·
              refine ⟨84716104067065342098733913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56477402711376894732489275 84716104067065342098733913)
              ·
                refine ⟨63537078050299006574050435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84716104067065342098733913 63537078050299006574050435)
                ·
                  refine ⟨95305617075448509861075653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63537078050299006574050435 95305617075448509861075653)
                  ·
                    refine ⟨17869803201646595598951685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95305617075448509861075653 17869803201646595598951685)
                    ·
                      refine ⟨3350588100308736674803441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17869803201646595598951685 3350588100308736674803441)
                      ·
                        rfl

theorem cell23_6525247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_6525247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525247 prefixEnd_6525247 := by exact prefixLift 6525247
  have htrace : WordTrace (prefixWord ++ tailWord_6525247) baseStart_6525247 baseEnd_6525247 := by
    simpa [prefixWord, tailWord_6525247, baseEnd_6525247] using wordTrace_append hprefix tailTrace_6525247
  have hstable : (prefixWord ++ tailWord_6525247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525247).length < 2 ^ (prefixWord ++ tailWord_6525247).sum := by decide
  have hdescent : baseEnd_6525247 < baseStart_6525247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525268 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 4, 2, 2]
def baseStart_6525268 : Nat := 118140960795 + 6525268 * 2 ^ 59
def prefixEnd_6525268 : Nat := 4983230072969 + 3 ^ 40 * 6525268 * 2
def baseEnd_6525268 : Nat := 3350598883402481092640845

theorem tailTrace_6525268 : CollatzResearch.WordTrace tailWord_6525268 prefixEnd_6525268 3350598883402481092640845 := by
  unfold tailWord_6525268
  simp only [CollatzResearch.WordTrace]
  refine ⟨118998038062037968947720229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158664050749383958596960305 118998038062037968947720229)
  ·
    refine ⟨22312132136632119177697543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118998038062037968947720229 22312132136632119177697543)
    ·
      refine ⟨33468198204948178766546315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22312132136632119177697543 33468198204948178766546315)
      ·
        refine ⟨50202297307422268149819473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33468198204948178766546315 50202297307422268149819473)
        ·
          refine ⟨37651722980566701112364605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50202297307422268149819473 37651722980566701112364605)
          ·
            refine ⟨14119396117712512917136727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37651722980566701112364605 14119396117712512917136727)
            ·
              refine ⟨21179094176568769375705091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14119396117712512917136727 21179094176568769375705091)
              ·
                refine ⟨31768641264853154063557637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21179094176568769375705091 31768641264853154063557637)
                ·
                  refine ⟨5956620237159966386917057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31768641264853154063557637 5956620237159966386917057)
                  ·
                    refine ⟨4467465177869974790187793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5956620237159966386917057 4467465177869974790187793)
                    ·
                      refine ⟨3350598883402481092640845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4467465177869974790187793 3350598883402481092640845)
                      ·
                        rfl

theorem cell23_6525268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_6525268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525268 prefixEnd_6525268 := by exact prefixLift 6525268
  have htrace : WordTrace (prefixWord ++ tailWord_6525268) baseStart_6525268 baseEnd_6525268 := by
    simpa [prefixWord, tailWord_6525268, baseEnd_6525268] using wordTrace_append hprefix tailTrace_6525268
  have hstable : (prefixWord ++ tailWord_6525268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525268).length < 2 ^ (prefixWord ++ tailWord_6525268).sum := by decide
  have hdescent : baseEnd_6525268 < baseStart_6525268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525284 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 2, 3, 3]
def baseStart_6525284 : Nat := 118140960795 + 6525284 * 2 ^ 59
def prefixEnd_6525284 : Nat := 4983230072969 + 3 ^ 40 * 6525284 * 2
def baseEnd_6525284 : Nat := 3350607099092953030040771

theorem tailTrace_6525284 : CollatzResearch.WordTrace tailWord_6525284 prefixEnd_6525284 3350607099092953030040771 := by
  unfold tailWord_6525284
  simp only [CollatzResearch.WordTrace]
  refine ⟨118998329846008986314011453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158664439794678648418681937 118998329846008986314011453)
  ·
    refine ⟨44624373692253369867754295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118998329846008986314011453 44624373692253369867754295)
    ·
      refine ⟨66936560538380054801631443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44624373692253369867754295 66936560538380054801631443)
      ·
        refine ⟨100404840807570082202447165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66936560538380054801631443 100404840807570082202447165)
        ·
          refine ⟨37651815302838780825917687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100404840807570082202447165 37651815302838780825917687)
          ·
            refine ⟨56477722954258171238876531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37651815302838780825917687 56477722954258171238876531)
            ·
              refine ⟨84716584431387256858314797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56477722954258171238876531 84716584431387256858314797)
              ·
                refine ⟨31768719161770221321868049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84716584431387256858314797 31768719161770221321868049)
                ·
                  refine ⟨23826539371327665991401037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31768719161770221321868049 23826539371327665991401037)
                  ·
                    refine ⟨8934952264247874746775389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23826539371327665991401037 8934952264247874746775389)
                    ·
                      refine ⟨3350607099092953030040771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8934952264247874746775389 3350607099092953030040771)
                      ·
                        rfl

theorem cell23_6525284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_6525284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525284 prefixEnd_6525284 := by exact prefixLift 6525284
  have htrace : WordTrace (prefixWord ++ tailWord_6525284) baseStart_6525284 baseEnd_6525284 := by
    simpa [prefixWord, tailWord_6525284, baseEnd_6525284] using wordTrace_append hprefix tailTrace_6525284
  have hstable : (prefixWord ++ tailWord_6525284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525284).length < 2 ^ (prefixWord ++ tailWord_6525284).sum := by decide
  have hdescent : baseEnd_6525284 < baseStart_6525284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525285 : List Nat := [1, 3, 1, 3, 1, 4, 3, 1, 2, 2, 2]
def baseStart_6525285 : Nat := 118140960795 + 6525285 * 2 ^ 59
def prefixEnd_6525285 : Nat := 4983230072969 + 3 ^ 40 * 6525285 * 2
def baseEnd_6525285 : Nat := 3350607612573607526128267

theorem tailTrace_6525285 : CollatzResearch.WordTrace tailWord_6525285 prefixEnd_6525285 3350607612573607526128267 := by
  unfold tailWord_6525285
  simp only [CollatzResearch.WordTrace]
  refine ⟨237996696165014349798809309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158664464110009566532539539 237996696165014349798809309)
  ·
    refine ⟨89248761061880381174553491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237996696165014349798809309 89248761061880381174553491)
    ·
      refine ⟨133873141592820571761830237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89248761061880381174553491 133873141592820571761830237)
      ·
        refine ⟨50202428097307714410686339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133873141592820571761830237 50202428097307714410686339)
        ·
          refine ⟨75303642145961571616029509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50202428097307714410686339 75303642145961571616029509)
          ·
            refine ⟨14119432902367794678005533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75303642145961571616029509 14119432902367794678005533)
            ·
              refine ⟨5294787338387923004252075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14119432902367794678005533 5294787338387923004252075)
              ·
                refine ⟨7942181007581884506378113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5294787338387923004252075 7942181007581884506378113)
                ·
                  refine ⟨5956635755686413379783585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7942181007581884506378113 5956635755686413379783585)
                  ·
                    refine ⟨4467476816764810034837689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5956635755686413379783585 4467476816764810034837689)
                    ·
                      refine ⟨3350607612573607526128267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4467476816764810034837689 3350607612573607526128267)
                      ·
                        rfl

theorem cell23_6525285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_6525285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525285 prefixEnd_6525285 := by exact prefixLift 6525285
  have htrace : WordTrace (prefixWord ++ tailWord_6525285) baseStart_6525285 baseEnd_6525285 := by
    simpa [prefixWord, tailWord_6525285, baseEnd_6525285] using wordTrace_append hprefix tailTrace_6525285
  have hstable : (prefixWord ++ tailWord_6525285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525285).length < 2 ^ (prefixWord ++ tailWord_6525285).sum := by decide
  have hdescent : baseEnd_6525285 < baseStart_6525285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525297 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 3, 2, 5]
def baseStart_6525297 : Nat := 118140960795 + 6525297 * 2 ^ 59
def prefixEnd_6525297 : Nat := 4983230072969 + 3 ^ 40 * 6525297 * 2
def baseEnd_6525297 : Nat := 3350613774341461479178211

theorem tailTrace_6525297 : CollatzResearch.WordTrace tailWord_6525297 prefixEnd_6525297 3350613774341461479178211 := by
  unfold tailWord_6525297
  simp only [CollatzResearch.WordTrace]
  refine ⟨237997133840970875848246145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158664755893980583898830763 237997133840970875848246145)
  ·
    refine ⟨178497850380728156886184609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237997133840970875848246145 178497850380728156886184609)
    ·
      refine ⟨133873387785546117664638457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178497850380728156886184609 133873387785546117664638457)
      ·
        refine ⟨100405040839159588248478843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133873387785546117664638457 100405040839159588248478843)
        ·
          refine ⟨150607561258739382372718265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100405040839159588248478843 150607561258739382372718265)
          ·
            refine ⟨112955670944054536779538699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150607561258739382372718265 112955670944054536779538699)
            ·
              refine ⟨169433506416081805169308049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112955670944054536779538699 169433506416081805169308049)
              ·
                refine ⟨127075129812061353876981037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169433506416081805169308049 127075129812061353876981037)
                ·
                  refine ⟨47653173679523007703867889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127075129812061353876981037 47653173679523007703867889)
                  ·
                    refine ⟨35739880259642255777900917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47653173679523007703867889 35739880259642255777900917)
                    ·
                      refine ⟨3350613774341461479178211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35739880259642255777900917 3350613774341461479178211)
                      ·
                        rfl

theorem cell23_6525297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_6525297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525297 prefixEnd_6525297 := by exact prefixLift 6525297
  have htrace : WordTrace (prefixWord ++ tailWord_6525297) baseStart_6525297 baseEnd_6525297 := by
    simpa [prefixWord, tailWord_6525297, baseEnd_6525297] using wordTrace_append hprefix tailTrace_6525297
  have hstable : (prefixWord ++ tailWord_6525297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525297).length < 2 ^ (prefixWord ++ tailWord_6525297).sum := by decide
  have hdescent : baseEnd_6525297 < baseStart_6525297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525324 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 4, 1, 4]
def baseStart_6525324 : Nat := 118140960795 + 6525324 * 2 ^ 59
def prefixEnd_6525324 : Nat := 4983230072969 + 3 ^ 40 * 6525324 * 2
def baseEnd_6525324 : Nat := 3350627638319132873540587

theorem tailTrace_6525324 : CollatzResearch.WordTrace tailWord_6525324 prefixEnd_6525324 3350627638319132873540587 := by
  unfold tailWord_6525324
  simp only [CollatzResearch.WordTrace]
  refine ⟨118999059305936529729739513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158665412407915372972986017 118999059305936529729739513)
  ·
    refine ⟨89249294479452397297304635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118999059305936529729739513 89249294479452397297304635)
    ·
      refine ⟨133873941719178595945956953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89249294479452397297304635 133873941719178595945956953)
      ·
        refine ⟨100405456289383946959467715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133873941719178595945956953 100405456289383946959467715)
        ·
          refine ⟨150608184434075920439201573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100405456289383946959467715 150608184434075920439201573)
          ·
            refine ⟨28239034581389235082350295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150608184434075920439201573 28239034581389235082350295)
            ·
              refine ⟨42358551872083852623525443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28239034581389235082350295 42358551872083852623525443)
              ·
                refine ⟨63537827808125778935288165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42358551872083852623525443 63537827808125778935288165)
                ·
                  refine ⟨11913342714023583550366531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63537827808125778935288165 11913342714023583550366531)
                  ·
                    refine ⟨17870014071035375325549797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11913342714023583550366531 17870014071035375325549797)
                    ·
                      refine ⟨3350627638319132873540587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17870014071035375325549797 3350627638319132873540587)
                      ·
                        rfl

theorem cell23_6525324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_6525324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525324 prefixEnd_6525324 := by exact prefixLift 6525324
  have htrace : WordTrace (prefixWord ++ tailWord_6525324) baseStart_6525324 baseEnd_6525324 := by
    simpa [prefixWord, tailWord_6525324, baseEnd_6525324] using wordTrace_append hprefix tailTrace_6525324
  have hstable : (prefixWord ++ tailWord_6525324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525324).length < 2 ^ (prefixWord ++ tailWord_6525324).sum := by decide
  have hdescent : baseEnd_6525324 < baseStart_6525324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525361 : List Nat := [1, 2, 2, 4, 1, 2, 1, 3, 2, 2, 3]
def baseStart_6525361 : Nat := 118140960795 + 6525361 * 2 ^ 59
def prefixEnd_6525361 : Nat := 4983230072969 + 3 ^ 40 * 6525361 * 2
def baseEnd_6525361 : Nat := 3350646637103349228777917

theorem tailTrace_6525361 : CollatzResearch.WordTrace tailWord_6525361 prefixEnd_6525361 3350646637103349228777917 := by
  unfold tailWord_6525361
  simp only [CollatzResearch.WordTrace]
  refine ⟨237999468112739014778575937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158666312075159343185717291 237999468112739014778575937)
  ·
    refine ⟨178499601084554261083931953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237999468112739014778575937 178499601084554261083931953)
    ·
      refine ⟨133874700813415695812948965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178499601084554261083931953 133874700813415695812948965)
      ·
        refine ⟨25101506402515442964927931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133874700813415695812948965 25101506402515442964927931)
        ·
          refine ⟨37652259603773164447391897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25101506402515442964927931 37652259603773164447391897)
          ·
            refine ⟨28239194702829873335543923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37652259603773164447391897 28239194702829873335543923)
            ·
              refine ⟨42358792054244810003315885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28239194702829873335543923 42358792054244810003315885)
              ·
                refine ⟨15884547020341803751243457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42358792054244810003315885 15884547020341803751243457)
                ·
                  refine ⟨11913410265256352813432593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15884547020341803751243457 11913410265256352813432593)
                  ·
                    refine ⟨8935057698942264610074445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11913410265256352813432593 8935057698942264610074445)
                    ·
                      refine ⟨3350646637103349228777917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8935057698942264610074445 3350646637103349228777917)
                      ·
                        rfl

theorem cell23_6525361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_6525361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525361 prefixEnd_6525361 := by exact prefixLift 6525361
  have htrace : WordTrace (prefixWord ++ tailWord_6525361) baseStart_6525361 baseEnd_6525361 := by
    simpa [prefixWord, tailWord_6525361, baseEnd_6525361] using wordTrace_append hprefix tailTrace_6525361
  have hstable : (prefixWord ++ tailWord_6525361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525361).length < 2 ^ (prefixWord ++ tailWord_6525361).sum := by decide
  have hdescent : baseEnd_6525361 < baseStart_6525361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525391 : List Nat := [1, 1, 2, 1, 1, 4, 1, 5, 3, 1, 3]
def baseStart_6525391 : Nat := 118140960795 + 6525391 * 2 ^ 59
def prefixEnd_6525391 : Nat := 4983230072969 + 3 ^ 40 * 6525391 * 2
def baseEnd_6525391 : Nat := 3350662041522984111402779

theorem tailTrace_6525391 : CollatzResearch.WordTrace tailWord_6525391 prefixEnd_6525391 3350662041522984111402779 := by
  unfold tailWord_6525391
  simp only [CollatzResearch.WordTrace]
  refine ⟨238000562302630329902168027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158667041535086886601445351 238000562302630329902168027)
  ·
    refine ⟨357000843453945494853252041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238000562302630329902168027 357000843453945494853252041)
    ·
      refine ⟨267750632590459121139939031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357000843453945494853252041 267750632590459121139939031)
      ·
        refine ⟨401625948885688681709908547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267750632590459121139939031 401625948885688681709908547)
        ·
          refine ⟨602438923328533022564862821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401625948885688681709908547 602438923328533022564862821)
          ·
            refine ⟨112957298124099941730911779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 602438923328533022564862821 112957298124099941730911779)
            ·
              refine ⟨169435947186149912596367669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112957298124099941730911779 169435947186149912596367669)
              ·
                refine ⟨15884620048701554305909469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169435947186149912596367669 15884620048701554305909469)
                ·
                  refine ⟨5956732518263082864716051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15884620048701554305909469 5956732518263082864716051)
                  ·
                    refine ⟨8935098777394624297074077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5956732518263082864716051 8935098777394624297074077)
                    ·
                      refine ⟨3350662041522984111402779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8935098777394624297074077 3350662041522984111402779)
                      ·
                        rfl

theorem cell23_6525391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 1, 3].length) (baseStart_6525391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525391 prefixEnd_6525391 := by exact prefixLift 6525391
  have htrace : WordTrace (prefixWord ++ tailWord_6525391) baseStart_6525391 baseEnd_6525391 := by
    simpa [prefixWord, tailWord_6525391, baseEnd_6525391] using wordTrace_append hprefix tailTrace_6525391
  have hstable : (prefixWord ++ tailWord_6525391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525391).length < 2 ^ (prefixWord ++ tailWord_6525391).sum := by decide
  have hdescent : baseEnd_6525391 < baseStart_6525391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525401 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 1, 5, 2]
def baseStart_6525401 : Nat := 118140960795 + 6525401 * 2 ^ 59
def prefixEnd_6525401 : Nat := 4983230072969 + 3 ^ 40 * 6525401 * 2
def baseEnd_6525401 : Nat := 3350667176329529072277733

theorem tailTrace_6525401 : CollatzResearch.WordTrace tailWord_6525401 prefixEnd_6525401 3350667176329529072277733 := by
  unfold tailWord_6525401
  simp only [CollatzResearch.WordTrace]
  refine ⟨238000927032594101610032057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158667284688396067740021371 238000927032594101610032057)
  ·
    refine ⟨178500695274445576207524043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238000927032594101610032057 178500695274445576207524043)
    ·
      refine ⟨267751042911668364311286065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178500695274445576207524043 267751042911668364311286065)
      ·
        refine ⟨200813282183751273233464549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267751042911668364311286065 200813282183751273233464549)
        ·
          refine ⟨37652490409453363731274603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200813282183751273233464549 37652490409453363731274603)
          ·
            refine ⟨56478735614180045596911905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37652490409453363731274603 56478735614180045596911905)
            ·
              refine ⟨42359051710635034197683929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56478735614180045596911905 42359051710635034197683929)
              ·
                refine ⟨31769288782976275648262947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42359051710635034197683929 31769288782976275648262947)
                ·
                  refine ⟨47653933174464413472394421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31769288782976275648262947 47653933174464413472394421)
                  ·
                    refine ⟨4467556235106038763036977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47653933174464413472394421 4467556235106038763036977)
                    ·
                      refine ⟨3350667176329529072277733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4467556235106038763036977 3350667176329529072277733)
                      ·
                        rfl

theorem cell23_6525401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 5, 2].length) (baseStart_6525401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525401 prefixEnd_6525401 := by exact prefixLift 6525401
  have htrace : WordTrace (prefixWord ++ tailWord_6525401) baseStart_6525401 baseEnd_6525401 := by
    simpa [prefixWord, tailWord_6525401, baseEnd_6525401] using wordTrace_append hprefix tailTrace_6525401
  have hstable : (prefixWord ++ tailWord_6525401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525401).length < 2 ^ (prefixWord ++ tailWord_6525401).sum := by decide
  have hdescent : baseEnd_6525401 < baseStart_6525401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525418 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 1, 5, 2]
def baseStart_6525418 : Nat := 118140960795 + 6525418 * 2 ^ 59
def prefixEnd_6525418 : Nat := 4983230072969 + 3 ^ 40 * 6525418 * 2
def baseEnd_6525418 : Nat := 3350675905500655505765155

theorem tailTrace_6525418 : CollatzResearch.WordTrace tailWord_6525418 prefixEnd_6525418 3350675905500655505765155 := by
  unfold tailWord_6525418
  simp only [CollatzResearch.WordTrace]
  refine ⟨59500386768383128378350227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158667698049021675675600605 59500386768383128378350227)
  ·
    refine ⟨89250580152574692567525341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59500386768383128378350227 89250580152574692567525341)
    ·
      refine ⟨33468967557215509712822003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89250580152574692567525341 33468967557215509712822003)
      ·
        refine ⟨50203451335823264569233005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33468967557215509712822003 50203451335823264569233005)
        ·
          refine ⟨18826294250933724213462377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50203451335823264569233005 18826294250933724213462377)
          ·
            refine ⟨14119720688200293160096783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18826294250933724213462377 14119720688200293160096783)
            ·
              refine ⟨21179581032300439740145175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14119720688200293160096783 21179581032300439740145175)
              ·
                refine ⟨31769371548450659610217763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21179581032300439740145175 31769371548450659610217763)
                ·
                  refine ⟨47654057322675989415326645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31769371548450659610217763 47654057322675989415326645)
                  ·
                    refine ⟨4467567874000874007686873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47654057322675989415326645 4467567874000874007686873)
                    ·
                      refine ⟨3350675905500655505765155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4467567874000874007686873 3350675905500655505765155)
                      ·
                        rfl

theorem cell23_6525418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_6525418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525418 prefixEnd_6525418 := by exact prefixLift 6525418
  have htrace : WordTrace (prefixWord ++ tailWord_6525418) baseStart_6525418 baseEnd_6525418 := by
    simpa [prefixWord, tailWord_6525418, baseEnd_6525418] using wordTrace_append hprefix tailTrace_6525418
  have hstable : (prefixWord ++ tailWord_6525418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525418).length < 2 ^ (prefixWord ++ tailWord_6525418).sum := by decide
  have hdescent : baseEnd_6525418 < baseStart_6525418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525424 : List Nat := [2, 1, 1, 1, 3, 3, 1, 4, 1, 6]
def baseStart_6525424 : Nat := 118140960795 + 6525424 * 2 ^ 59
def prefixEnd_6525424 : Nat := 4983230072969 + 3 ^ 40 * 6525424 * 2
def baseEnd_6525424 : Nat := 1116892995461527494096709

theorem tailTrace_6525424 : CollatzResearch.WordTrace tailWord_6525424 prefixEnd_6525424 1116892995461527494096709 := by
  unfold tailWord_6525424
  simp only [CollatzResearch.WordTrace]
  refine ⟨119000882955755388269059663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158667843941007184358746217 119000882955755388269059663)
  ·
    refine ⟨178501324433633082403589495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119000882955755388269059663 178501324433633082403589495)
    ·
      refine ⟨267751986650449623605384243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178501324433633082403589495 267751986650449623605384243)
      ·
        refine ⟨401627979975674435408076365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267751986650449623605384243 401627979975674435408076365)
        ·
          refine ⟨150610492490877913278028637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401627979975674435408076365 150610492490877913278028637)
          ·
            refine ⟨56478934684079217479260739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150610492490877913278028637 56478934684079217479260739)
            ·
              refine ⟨84718402026118826218891109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56478934684079217479260739 84718402026118826218891109)
              ·
                refine ⟨15884700379897279916042083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84718402026118826218891109 15884700379897279916042083)
                ·
                  refine ⟨23827050569845919874063125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15884700379897279916042083 23827050569845919874063125)
                  ·
                    refine ⟨1116892995461527494096709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23827050569845919874063125 1116892995461527494096709)
                    ·
                      rfl

theorem cell23_6525424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 1, 6].length) (baseStart_6525424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525424 prefixEnd_6525424 := by exact prefixLift 6525424
  have htrace : WordTrace (prefixWord ++ tailWord_6525424) baseStart_6525424 baseEnd_6525424 := by
    simpa [prefixWord, tailWord_6525424, baseEnd_6525424] using wordTrace_append hprefix tailTrace_6525424
  have hstable : (prefixWord ++ tailWord_6525424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525424).length < 2 ^ (prefixWord ++ tailWord_6525424).sum := by decide
  have hdescent : baseEnd_6525424 < baseStart_6525424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525425 : List Nat := [1, 2, 2, 2, 3, 1, 4, 3, 1, 1, 3]
def baseStart_6525425 : Nat := 118140960795 + 6525425 * 2 ^ 59
def prefixEnd_6525425 : Nat := 4983230072969 + 3 ^ 40 * 6525425 * 2
def baseEnd_6525425 : Nat := 3350679499865236978377623

theorem tailTrace_6525425 : CollatzResearch.WordTrace tailWord_6525425 prefixEnd_6525425 3350679499865236978377623 := by
  unfold tailWord_6525425
  simp only [CollatzResearch.WordTrace]
  refine ⟨238001802384507153708905729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158667868256338102472603819 238001802384507153708905729)
  ·
    refine ⟨178501351788380365281679297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238001802384507153708905729 178501351788380365281679297)
    ·
      refine ⟨133876013841285273961259473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178501351788380365281679297 133876013841285273961259473)
      ·
        refine ⟨100407010380963955470944605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133876013841285273961259473 100407010380963955470944605)
        ·
          refine ⟨37652628892861483301604227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100407010380963955470944605 37652628892861483301604227)
          ·
            refine ⟨56478943339292224952406341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37652628892861483301604227 56478943339292224952406341)
            ·
              refine ⟨10589801876117292178576189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56478943339292224952406341 10589801876117292178576189)
              ·
                refine ⟨3971175703543984566966071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10589801876117292178576189 3971175703543984566966071)
                ·
                  refine ⟨5956763555315976850449107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3971175703543984566966071 5956763555315976850449107)
                  ·
                    refine ⟨8935145332973965275673661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5956763555315976850449107 8935145332973965275673661)
                    ·
                      refine ⟨3350679499865236978377623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8935145332973965275673661 3350679499865236978377623)
                      ·
                        rfl

theorem cell23_6525425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 1, 1, 3].length) (baseStart_6525425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525425 prefixEnd_6525425 := by exact prefixLift 6525425
  have htrace : WordTrace (prefixWord ++ tailWord_6525425) baseStart_6525425 baseEnd_6525425 := by
    simpa [prefixWord, tailWord_6525425, baseEnd_6525425] using wordTrace_append hprefix tailTrace_6525425
  have hstable : (prefixWord ++ tailWord_6525425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525425).length < 2 ^ (prefixWord ++ tailWord_6525425).sum := by decide
  have hdescent : baseEnd_6525425 < baseStart_6525425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525442 : List Nat := [3, 4, 1, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_6525442 : Nat := 118140960795 + 6525442 * 2 ^ 59
def prefixEnd_6525442 : Nat := 4983230072969 + 3 ^ 40 * 6525442 * 2
def baseEnd_6525442 : Nat := 3350688229036363411865045

theorem tailTrace_6525442 : CollatzResearch.WordTrace tailWord_6525442 prefixEnd_6525442 3350688229036363411865045 := by
  unfold tailWord_6525442
  simp only [CollatzResearch.WordTrace]
  refine ⟨59500605606361391403068645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158668281616963710408183053 59500605606361391403068645)
  ·
    refine ⟨11156363551192760888075371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59500605606361391403068645 11156363551192760888075371)
    ·
      refine ⟨16734545326789141332113057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11156363551192760888075371 16734545326789141332113057)
      ·
        refine ⟨12550908995091855999084793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16734545326789141332113057 12550908995091855999084793)
        ·
          refine ⟨9413181746318891999313595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12550908995091855999084793 9413181746318891999313595)
          ·
            refine ⟨14119772619478337998970393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9413181746318891999313595 14119772619478337998970393)
            ·
              refine ⟨10589829464608753499227795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14119772619478337998970393 10589829464608753499227795)
              ·
                refine ⟨15884744196913130248841693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10589829464608753499227795 15884744196913130248841693)
                ·
                  refine ⟨5956779073842423843315635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15884744196913130248841693 5956779073842423843315635)
                  ·
                    refine ⟨8935168610763635764973453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5956779073842423843315635 8935168610763635764973453)
                    ·
                      refine ⟨3350688229036363411865045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8935168610763635764973453 3350688229036363411865045)
                      ·
                        rfl

theorem cell23_6525442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_6525442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525442 prefixEnd_6525442 := by exact prefixLift 6525442
  have htrace : WordTrace (prefixWord ++ tailWord_6525442) baseStart_6525442 baseEnd_6525442 := by
    simpa [prefixWord, tailWord_6525442, baseEnd_6525442] using wordTrace_append hprefix tailTrace_6525442
  have hstable : (prefixWord ++ tailWord_6525442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525442).length < 2 ^ (prefixWord ++ tailWord_6525442).sum := by decide
  have hdescent : baseEnd_6525442 < baseStart_6525442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525451 : List Nat := [1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 5]
def baseStart_6525451 : Nat := 118140960795 + 6525451 * 2 ^ 59
def prefixEnd_6525451 : Nat := 4983230072969 + 3 ^ 40 * 6525451 * 2
def baseEnd_6525451 : Nat := 3350692850362253876652503

theorem tailTrace_6525451 : CollatzResearch.WordTrace tailWord_6525451 prefixEnd_6525451 3350692850362253876652503 := by
  unfold tailWord_6525451
  simp only [CollatzResearch.WordTrace]
  refine ⟨238002750682412960149352207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158668500454941973432901471 238002750682412960149352207)
  ·
    refine ⟨357004126023619440224028311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238002750682412960149352207 357004126023619440224028311)
    ·
      refine ⟨535506189035429160336042467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357004126023619440224028311 535506189035429160336042467)
      ·
        refine ⟨803259283553143740504063701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535506189035429160336042467 803259283553143740504063701)
        ·
          refine ⟨18826389458276806418063993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 803259283553143740504063701 18826389458276806418063993)
          ·
            refine ⟨14119792093707604813547995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18826389458276806418063993 14119792093707604813547995)
            ·
              refine ⟨21179688140561407220321993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14119792093707604813547995 21179688140561407220321993)
              ·
                refine ⟨15884766105421055415241495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21179688140561407220321993 15884766105421055415241495)
                ·
                  refine ⟨23827149158131583122862243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15884766105421055415241495 23827149158131583122862243)
                  ·
                    refine ⟨35740723737197374684293365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23827149158131583122862243 35740723737197374684293365)
                    ·
                      refine ⟨3350692850362253876652503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35740723737197374684293365 3350692850362253876652503)
                      ·
                        rfl

theorem cell23_6525451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 5].length) (baseStart_6525451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525451 prefixEnd_6525451 := by exact prefixLift 6525451
  have htrace : WordTrace (prefixWord ++ tailWord_6525451) baseStart_6525451 baseEnd_6525451 := by
    simpa [prefixWord, tailWord_6525451, baseEnd_6525451] using wordTrace_append hprefix tailTrace_6525451
  have hstable : (prefixWord ++ tailWord_6525451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525451).length < 2 ^ (prefixWord ++ tailWord_6525451).sum := by decide
  have hdescent : baseEnd_6525451 < baseStart_6525451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525468 : List Nat := [2, 2, 3, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_6525468 : Nat := 118140960795 + 6525468 * 2 ^ 59
def prefixEnd_6525468 : Nat := 4983230072969 + 3 ^ 40 * 6525468 * 2
def baseEnd_6525468 : Nat := 3350701579533380310139925

theorem tailTrace_6525468 : CollatzResearch.WordTrace tailWord_6525468 prefixEnd_6525468 3350701579533380310139925 := by
  unfold tailWord_6525468
  simp only [CollatzResearch.WordTrace]
  refine ⟨119001685361675686026360529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158668913815567581368480705 119001685361675686026360529)
  ·
    refine ⟨89251264021256764519770397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119001685361675686026360529 89251264021256764519770397)
    ·
      refine ⟨33469224007971286694913899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89251264021256764519770397 33469224007971286694913899)
      ·
        refine ⟨50203836011956930042370849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33469224007971286694913899 50203836011956930042370849)
        ·
          refine ⟨37652877008967697531778137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50203836011956930042370849 37652877008967697531778137)
          ·
            refine ⟨28239657756725773148833603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37652877008967697531778137 28239657756725773148833603)
            ·
              refine ⟨42359486635088659723250405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28239657756725773148833603 42359486635088659723250405)
              ·
                refine ⟨7942403744079123698109451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42359486635088659723250405 7942403744079123698109451)
                ·
                  refine ⟨11913605616118685547164177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7942403744079123698109451 11913605616118685547164177)
                  ·
                    refine ⟨8935204212089014160373133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11913605616118685547164177 8935204212089014160373133)
                    ·
                      refine ⟨3350701579533380310139925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8935204212089014160373133 3350701579533380310139925)
                      ·
                        rfl

theorem cell23_6525468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_6525468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525468 prefixEnd_6525468 := by exact prefixLift 6525468
  have htrace : WordTrace (prefixWord ++ tailWord_6525468) baseStart_6525468 baseEnd_6525468 := by
    simpa [prefixWord, tailWord_6525468, baseEnd_6525468] using wordTrace_append hprefix tailTrace_6525468
  have hstable : (prefixWord ++ tailWord_6525468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525468).length < 2 ^ (prefixWord ++ tailWord_6525468).sum := by decide
  have hdescent : baseEnd_6525468 < baseStart_6525468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525476 : List Nat := [2, 3, 1, 5, 2, 1, 1, 3, 1, 1, 3]
def baseStart_6525476 : Nat := 118140960795 + 6525476 * 2 ^ 59
def prefixEnd_6525476 : Nat := 4983230072969 + 3 ^ 40 * 6525476 * 2
def baseEnd_6525476 : Nat := 3350705687378616278839889

theorem tailTrace_6525476 : CollatzResearch.WordTrace tailWord_6525476 prefixEnd_6525476 3350705687378616278839889 := by
  unfold tailWord_6525476
  simp only [CollatzResearch.WordTrace]
  refine ⟨119001831253661194709506141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158669108338214926279341521 119001831253661194709506141)
  ·
    refine ⟨44625686720122948016064803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119001831253661194709506141 44625686720122948016064803)
    ·
      refine ⟨66938530080184422024097205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44625686720122948016064803 66938530080184422024097205)
      ·
        refine ⟨6275487195017289564759113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66938530080184422024097205 6275487195017289564759113)
        ·
          refine ⟨4706615396262967173569335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6275487195017289564759113 4706615396262967173569335)
          ·
            refine ⟨7059923094394450760354003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4706615396262967173569335 7059923094394450760354003)
            ·
              refine ⟨10589884641591676140531005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7059923094394450760354003 10589884641591676140531005)
              ·
                refine ⟨3971206740596878552699127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10589884641591676140531005 3971206740596878552699127)
                ·
                  refine ⟨5956810110895317829048691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3971206740596878552699127 5956810110895317829048691)
                  ·
                    refine ⟨8935215166342976743573037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5956810110895317829048691 8935215166342976743573037)
                    ·
                      refine ⟨3350705687378616278839889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8935215166342976743573037 3350705687378616278839889)
                      ·
                        rfl

theorem cell23_6525476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_6525476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525476 prefixEnd_6525476 := by exact prefixLift 6525476
  have htrace : WordTrace (prefixWord ++ tailWord_6525476) baseStart_6525476 baseEnd_6525476 := by
    simpa [prefixWord, tailWord_6525476, baseEnd_6525476] using wordTrace_append hprefix tailTrace_6525476
  have hstable : (prefixWord ++ tailWord_6525476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525476).length < 2 ^ (prefixWord ++ tailWord_6525476).sum := by decide
  have hdescent : baseEnd_6525476 < baseStart_6525476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525498 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3]
def baseStart_6525498 : Nat := 118140960795 + 6525498 * 2 ^ 59
def prefixEnd_6525498 : Nat := 4983230072969 + 3 ^ 40 * 6525498 * 2
def baseEnd_6525498 : Nat := 3350716983953015192764787

theorem tailTrace_6525498 : CollatzResearch.WordTrace tailWord_6525498 prefixEnd_6525498 3350716983953015192764787 := by
  unfold tailWord_6525498
  simp only [CollatzResearch.WordTrace]
  refine ⟨59501116228310671794078287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158669643275495124784208765 59501116228310671794078287)
  ·
    refine ⟨89251674342466007691117431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59501116228310671794078287 89251674342466007691117431)
    ·
      refine ⟨133877511513699011536676147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89251674342466007691117431 133877511513699011536676147)
      ·
        refine ⟨200816267270548517305014221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133877511513699011536676147 200816267270548517305014221)
        ·
          refine ⟨75306100226455693989380333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200816267270548517305014221 75306100226455693989380333)
          ·
            refine ⟨28239787584920885246017625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75306100226455693989380333 28239787584920885246017625)
            ·
              refine ⟨21179840688690663934513219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28239787584920885246017625 21179840688690663934513219)
              ·
                refine ⟨31769761033035995901769829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21179840688690663934513219 31769761033035995901769829)
                ·
                  refine ⟨5956830193694249231581843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31769761033035995901769829 5956830193694249231581843)
                  ·
                    refine ⟨8935245290541373847372765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5956830193694249231581843 8935245290541373847372765)
                    ·
                      refine ⟨3350716983953015192764787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8935245290541373847372765 3350716983953015192764787)
                      ·
                        rfl

theorem cell23_6525498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3].length) (baseStart_6525498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525498 prefixEnd_6525498 := by exact prefixLift 6525498
  have htrace : WordTrace (prefixWord ++ tailWord_6525498) baseStart_6525498 baseEnd_6525498 := by
    simpa [prefixWord, tailWord_6525498, baseEnd_6525498] using wordTrace_append hprefix tailTrace_6525498
  have hstable : (prefixWord ++ tailWord_6525498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525498).length < 2 ^ (prefixWord ++ tailWord_6525498).sum := by decide
  have hdescent : baseEnd_6525498 < baseStart_6525498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525515 : List Nat := [1, 1, 1, 1, 3, 1, 8, 1, 2, 1, 3]
def baseStart_6525515 : Nat := 118140960795 + 6525515 * 2 ^ 59
def prefixEnd_6525515 : Nat := 4983230072969 + 3 ^ 40 * 6525515 * 2
def baseEnd_6525515 : Nat := 3350725713124141626252209

theorem tailTrace_6525515 : CollatzResearch.WordTrace tailWord_6525515 prefixEnd_6525515 3350725713124141626252209 := by
  unfold tailWord_6525515
  simp only [CollatzResearch.WordTrace]
  refine ⟨238005084954181099079681999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158670056636120732719787999 238005084954181099079681999)
  ·
    refine ⟨357007627431271648619522999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238005084954181099079681999 357007627431271648619522999)
    ·
      refine ⟨535511441146907472929284499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357007627431271648619522999 535511441146907472929284499)
      ·
        refine ⟨803267161720361209393926749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535511441146907472929284499 803267161720361209393926749)
        ·
          refine ⟨301225185645135453522722531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 803267161720361209393926749 301225185645135453522722531)
          ·
            refine ⟨451837778467703180284083797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301225185645135453522722531 451837778467703180284083797)
            ·
              refine ⟨5294973966418396643954107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 451837778467703180284083797 5294973966418396643954107)
              ·
                refine ⟨7942460949627594965931161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5294973966418396643954107 7942460949627594965931161)
                ·
                  refine ⟨5956845712220696224448371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7942460949627594965931161 5956845712220696224448371)
                  ·
                    refine ⟨8935268568331044336672557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5956845712220696224448371 8935268568331044336672557)
                    ·
                      refine ⟨3350725713124141626252209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8935268568331044336672557 3350725713124141626252209)
                      ·
                        rfl

theorem cell23_6525515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 2, 1, 3].length) (baseStart_6525515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525515 prefixEnd_6525515 := by exact prefixLift 6525515
  have htrace : WordTrace (prefixWord ++ tailWord_6525515) baseStart_6525515 baseEnd_6525515 := by
    simpa [prefixWord, tailWord_6525515, baseEnd_6525515] using wordTrace_append hprefix tailTrace_6525515
  have hstable : (prefixWord ++ tailWord_6525515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525515).length < 2 ^ (prefixWord ++ tailWord_6525515).sum := by decide
  have hdescent : baseEnd_6525515 < baseStart_6525515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525525 : List Nat := [1, 3, 2, 2, 1, 1, 5, 2, 1, 3, 2]
def baseStart_6525525 : Nat := 118140960795 + 6525525 * 2 ^ 59
def prefixEnd_6525525 : Nat := 4983230072969 + 3 ^ 40 * 6525525 * 2
def baseEnd_6525525 : Nat := 3350730847930686587127163

theorem tailTrace_6525525 : CollatzResearch.WordTrace tailWord_6525525 prefixEnd_6525525 3350730847930686587127163 := by
  unfold tailWord_6525525
  simp only [CollatzResearch.WordTrace]
  refine ⟨238005449684144870787546029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158670299789429913858364019 238005449684144870787546029)
  ·
    refine ⟨89252043631554326545329761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238005449684144870787546029 89252043631554326545329761)
    ·
      refine ⟨66939032723665744908997321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89252043631554326545329761 66939032723665744908997321)
      ·
        refine ⟨50204274542749308681747991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66939032723665744908997321 50204274542749308681747991)
        ·
          refine ⟨75306411814123963022621987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50204274542749308681747991 75306411814123963022621987)
          ·
            refine ⟨112959617721185944533932981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75306411814123963022621987 112959617721185944533932981)
            ·
              refine ⟨10589964161361182300056217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112959617721185944533932981 10589964161361182300056217)
              ·
                refine ⟨7942473121020886725042163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10589964161361182300056217 7942473121020886725042163)
                ·
                  refine ⟨11913709681531330087563245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7942473121020886725042163 11913709681531330087563245)
                  ·
                    refine ⟨4467641130574248782836217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11913709681531330087563245 4467641130574248782836217)
                    ·
                      refine ⟨3350730847930686587127163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4467641130574248782836217 3350730847930686587127163)
                      ·
                        rfl

theorem cell23_6525525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_6525525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525525 prefixEnd_6525525 := by exact prefixLift 6525525
  have htrace : WordTrace (prefixWord ++ tailWord_6525525) baseStart_6525525 baseEnd_6525525 := by
    simpa [prefixWord, tailWord_6525525, baseEnd_6525525] using wordTrace_append hprefix tailTrace_6525525
  have hstable : (prefixWord ++ tailWord_6525525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525525).length < 2 ^ (prefixWord ++ tailWord_6525525).sum := by decide
  have hdescent : baseEnd_6525525 < baseStart_6525525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525571 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 3]
def baseStart_6525571 : Nat := 118140960795 + 6525571 * 2 ^ 59
def prefixEnd_6525571 : Nat := 4983230072969 + 3 ^ 40 * 6525571 * 2
def baseEnd_6525571 : Nat := 3350754468040793407151951

theorem tailTrace_6525571 : CollatzResearch.WordTrace tailWord_6525571 prefixEnd_6525571 3350754468040793407151951 := by
  unfold tailWord_6525571
  simp only [CollatzResearch.WordTrace]
  refine ⟨238007127441978220643720567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158671418294652147095813711 238007127441978220643720567)
  ·
    refine ⟨357010691162967330965580851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238007127441978220643720567 357010691162967330965580851)
    ·
      refine ⟨535516036744450996448371277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357010691162967330965580851 535516036744450996448371277)
      ·
        refine ⟨200818513779169123668139229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 535516036744450996448371277 200818513779169123668139229)
        ·
          refine ⟨75306942667188421375552211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200818513779169123668139229 75306942667188421375552211)
          ·
            refine ⟨112960414000782632063328317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75306942667188421375552211 112960414000782632063328317)
            ·
              refine ⟨42360155250293487023748119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112960414000782632063328317 42360155250293487023748119)
              ·
                refine ⟨63540232875440230535622179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42360155250293487023748119 63540232875440230535622179)
                ·
                  refine ⟨95310349313160345803433269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63540232875440230535622179 95310349313160345803433269)
                  ·
                    refine ⟨8935345248108782419071869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95310349313160345803433269 8935345248108782419071869)
                    ·
                      refine ⟨3350754468040793407151951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8935345248108782419071869 3350754468040793407151951)
                      ·
                        rfl

theorem cell23_6525571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_6525571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525571 prefixEnd_6525571 := by exact prefixLift 6525571
  have htrace : WordTrace (prefixWord ++ tailWord_6525571) baseStart_6525571 baseEnd_6525571 := by
    simpa [prefixWord, tailWord_6525571, baseEnd_6525571] using wordTrace_append hprefix tailTrace_6525571
  have hstable : (prefixWord ++ tailWord_6525571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525571).length < 2 ^ (prefixWord ++ tailWord_6525571).sum := by decide
  have hdescent : baseEnd_6525571 < baseStart_6525571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525572 : List Nat := [2, 3, 2, 1, 3, 1, 2, 3, 2, 2, 2]
def baseStart_6525572 : Nat := 118140960795 + 6525572 * 2 ^ 59
def prefixEnd_6525572 : Nat := 4983230072969 + 3 ^ 40 * 6525572 * 2
def baseEnd_6525572 : Nat := 3350754981521447903239447

theorem tailTrace_6525572 : CollatzResearch.WordTrace tailWord_6525572 prefixEnd_6525572 3350754981521447903239447 := by
  unfold tailWord_6525572
  simp only [CollatzResearch.WordTrace]
  refine ⟨119003581957487298907253485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158671442609983065209671313 119003581957487298907253485)
  ·
    refine ⟨44626343234057737090220057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119003581957487298907253485 44626343234057737090220057)
    ·
      refine ⟨33469757425543302817665043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44626343234057737090220057 33469757425543302817665043)
      ·
        refine ⟨50204636138314954226497565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33469757425543302817665043 50204636138314954226497565)
        ·
          refine ⟨18826738551868107834936587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50204636138314954226497565 18826738551868107834936587)
          ·
            refine ⟨28240107827802161752404881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18826738551868107834936587 28240107827802161752404881)
            ·
              refine ⟨21180080870851621314303661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28240107827802161752404881 21180080870851621314303661)
              ·
                refine ⟨7942530326569357992863873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21180080870851621314303661 7942530326569357992863873)
                ·
                  refine ⟨5956897744927018494647905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7942530326569357992863873 5956897744927018494647905)
                  ·
                    refine ⟨4467673308695263870985929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5956897744927018494647905 4467673308695263870985929)
                    ·
                      refine ⟨3350754981521447903239447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4467673308695263870985929 3350754981521447903239447)
                      ·
                        rfl

theorem cell23_6525572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_6525572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525572 prefixEnd_6525572 := by exact prefixLift 6525572
  have htrace : WordTrace (prefixWord ++ tailWord_6525572) baseStart_6525572 baseEnd_6525572 := by
    simpa [prefixWord, tailWord_6525572, baseEnd_6525572] using wordTrace_append hprefix tailTrace_6525572
  have hstable : (prefixWord ++ tailWord_6525572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525572).length < 2 ^ (prefixWord ++ tailWord_6525572).sum := by decide
  have hdescent : baseEnd_6525572 < baseStart_6525572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525578 : List Nat := [3, 1, 2, 3, 3, 1, 1, 2, 7]
def baseStart_6525578 : Nat := 118140960795 + 6525578 * 2 ^ 59
def prefixEnd_6525578 : Nat := 4983230072969 + 3 ^ 40 * 6525578 * 2
def baseEnd_6525578 : Nat := 372306451378374986640491

theorem tailTrace_6525578 : CollatzResearch.WordTrace tailWord_6525578 prefixEnd_6525578 372306451378374986640491 := by
  unfold tailWord_6525578
  simp only [CollatzResearch.WordTrace]
  refine ⟨59501845688238215209806347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158671588501968573892816925 59501845688238215209806347)
  ·
    refine ⟨89252768532357322814709521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59501845688238215209806347 89252768532357322814709521)
    ·
      refine ⟨66939576399267992111032141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89252768532357322814709521 66939576399267992111032141)
      ·
        refine ⟨25102341149725497041637053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66939576399267992111032141 25102341149725497041637053)
        ·
          refine ⟨9413377931147061390613895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25102341149725497041637053 9413377931147061390613895)
          ·
            refine ⟨14120066896720592085920843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9413377931147061390613895 14120066896720592085920843)
            ·
              refine ⟨21180100345080888128881265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14120066896720592085920843 21180100345080888128881265)
              ·
                refine ⟨15885075258810666096660949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21180100345080888128881265 15885075258810666096660949)
                ·
                  refine ⟨372306451378374986640491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15885075258810666096660949 372306451378374986640491)
                  ·
                    rfl

theorem cell23_6525578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 7].length) (baseStart_6525578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525578 prefixEnd_6525578 := by exact prefixLift 6525578
  have htrace : WordTrace (prefixWord ++ tailWord_6525578) baseStart_6525578 baseEnd_6525578 := by
    simpa [prefixWord, tailWord_6525578, baseEnd_6525578] using wordTrace_append hprefix tailTrace_6525578
  have hstable : (prefixWord ++ tailWord_6525578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525578).length < 2 ^ (prefixWord ++ tailWord_6525578).sum := by decide
  have hdescent : baseEnd_6525578 < baseStart_6525578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525591 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 1, 7]
def baseStart_6525591 : Nat := 118140960795 + 6525591 * 2 ^ 59
def prefixEnd_6525591 : Nat := 4983230072969 + 3 ^ 40 * 6525591 * 2
def baseEnd_6525591 : Nat := 1116921579217961109633953

theorem tailTrace_6525591 : CollatzResearch.WordTrace tailWord_6525591 prefixEnd_6525591 1116921579217961109633953 := by
  unfold tailWord_6525591
  simp only [CollatzResearch.WordTrace]
  refine ⟨238007856901905764059448627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158671904601270509372965751 238007856901905764059448627)
  ·
    refine ⟨357011785352858646089172941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238007856901905764059448627 357011785352858646089172941)
    ·
      refine ⟨133879419507321992283439853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357011785352858646089172941 133879419507321992283439853)
      ·
        refine ⟨50204782315245747106289945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133879419507321992283439853 50204782315245747106289945)
        ·
          refine ⟨37653586736434310329717459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50204782315245747106289945 37653586736434310329717459)
          ·
            refine ⟨56480380104651465494576189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37653586736434310329717459 56480380104651465494576189)
            ·
              refine ⟨21180142539244299560466071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56480380104651465494576189 21180142539244299560466071)
              ·
                refine ⟨31770213808866449340699107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21180142539244299560466071 31770213808866449340699107)
                ·
                  refine ⟨47655320713299674011048661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31770213808866449340699107 47655320713299674011048661)
                  ·
                    refine ⟨1116921579217961109633953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47655320713299674011048661 1116921579217961109633953)
                    ·
                      rfl

theorem cell23_6525591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_6525591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525591 prefixEnd_6525591 := by exact prefixLift 6525591
  have htrace : WordTrace (prefixWord ++ tailWord_6525591) baseStart_6525591 baseEnd_6525591 := by
    simpa [prefixWord, tailWord_6525591, baseEnd_6525591] using wordTrace_append hprefix tailTrace_6525591
  have hstable : (prefixWord ++ tailWord_6525591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525591).length < 2 ^ (prefixWord ++ tailWord_6525591).sum := by decide
  have hdescent : baseEnd_6525591 < baseStart_6525591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525665 : List Nat := [1, 2, 3, 1, 4, 2, 1, 2, 2, 2, 3]
def baseStart_6525665 : Nat := 118140960795 + 6525665 * 2 ^ 59
def prefixEnd_6525665 : Nat := 4983230072969 + 3 ^ 40 * 6525665 * 2
def baseEnd_6525665 : Nat := 3350802735222316039376519

theorem tailTrace_6525665 : CollatzResearch.WordTrace tailWord_6525665 prefixEnd_6525665 3350802735222316039376519 := by
  unfold tailWord_6525665
  simp only [CollatzResearch.WordTrace]
  refine ⟨238010555903637674697642449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158673703935758449798428299 238010555903637674697642449)
  ·
    refine ⟨178507916927728256023231837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238010555903637674697642449 178507916927728256023231837)
    ·
      refine ⟨66940468847898096008711939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178507916927728256023231837 66940468847898096008711939)
      ·
        refine ⟨100410703271847144013067909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66940468847898096008711939 100410703271847144013067909)
        ·
          refine ⟨18827006863471339502450233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100410703271847144013067909 18827006863471339502450233)
          ·
            refine ⟨14120255147603504626837675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18827006863471339502450233 14120255147603504626837675)
            ·
              refine ⟨21180382721405256940256513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14120255147603504626837675 21180382721405256940256513)
              ·
                refine ⟨15885287041053942705192385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21180382721405256940256513 15885287041053942705192385)
                ·
                  refine ⟨11913965280790457028894289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15885287041053942705192385 11913965280790457028894289)
                  ·
                    refine ⟨8935473960592842771670717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11913965280790457028894289 8935473960592842771670717)
                    ·
                      refine ⟨3350802735222316039376519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8935473960592842771670717 3350802735222316039376519)
                      ·
                        rfl

theorem cell23_6525665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_6525665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525665 prefixEnd_6525665 := by exact prefixLift 6525665
  have htrace : WordTrace (prefixWord ++ tailWord_6525665) baseStart_6525665 baseEnd_6525665 := by
    simpa [prefixWord, tailWord_6525665, baseEnd_6525665] using wordTrace_append hprefix tailTrace_6525665
  have hstable : (prefixWord ++ tailWord_6525665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525665).length < 2 ^ (prefixWord ++ tailWord_6525665).sum := by decide
  have hdescent : baseEnd_6525665 < baseStart_6525665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525672 : List Nat := [2, 1, 4, 1, 4, 2, 1, 1, 3, 4]
def baseStart_6525672 : Nat := 118140960795 + 6525672 * 2 ^ 59
def prefixEnd_6525672 : Nat := 4983230072969 + 3 ^ 40 * 6525672 * 2
def baseEnd_6525672 : Nat := 1116935443195632503996329

theorem tailTrace_6525672 : CollatzResearch.WordTrace tailWord_6525672 prefixEnd_6525672 1116935443195632503996329 := by
  unfold tailWord_6525672
  simp only [CollatzResearch.WordTrace]
  refine ⟨119005405607306157446573635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158673874143074876595431513 119005405607306157446573635)
  ·
    refine ⟨178508108410959236169860453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119005405607306157446573635 178508108410959236169860453)
    ·
      refine ⟨33470270327054856781848835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178508108410959236169860453 33470270327054856781848835)
      ·
        refine ⟨50205405490582285172773253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33470270327054856781848835 50205405490582285172773253)
        ·
          refine ⟨9413513529484178469894985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50205405490582285172773253 9413513529484178469894985)
          ·
            refine ⟨7060135147113133852421239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9413513529484178469894985 7060135147113133852421239)
            ·
              refine ⟨10590202720669700778631859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7060135147113133852421239 10590202720669700778631859)
              ·
                refine ⟨15885304081004551167947789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10590202720669700778631859 15885304081004551167947789)
                ·
                  refine ⟨5956989030376706687980421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15885304081004551167947789 5956989030376706687980421)
                  ·
                    refine ⟨1116935443195632503996329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5956989030376706687980421 1116935443195632503996329)
                    ·
                      rfl

theorem cell23_6525672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_6525672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525672 prefixEnd_6525672 := by exact prefixLift 6525672
  have htrace : WordTrace (prefixWord ++ tailWord_6525672) baseStart_6525672 baseEnd_6525672 := by
    simpa [prefixWord, tailWord_6525672, baseEnd_6525672] using wordTrace_append hprefix tailTrace_6525672
  have hstable : (prefixWord ++ tailWord_6525672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525672).length < 2 ^ (prefixWord ++ tailWord_6525672).sum := by decide
  have hdescent : baseEnd_6525672 < baseStart_6525672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
